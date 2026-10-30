/**
 * @file test_validation_incr.c
 * @brief unit tests for functions from validation_incr.c
 *
 * Every test is differential: the same edit is validated fully and incrementally and the two runs must agree
 * on both the verdict and the resulting tree. A test that only checked the incremental run could pass while
 * silently accepting invalid data, which is the one failure mode that matters here.
 *
 * Copyright (c) 2026 Vecima Networks Inc.
 *
 * This source code is licensed under BSD 3-Clause License (the "License").
 * You may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *     https://opensource.org/licenses/BSD-3-Clause
 */
#define _UTEST_MAIN_
#include "utests.h"

#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include "libyang.h"
#include "validation_deps.h"

static const char *schema_a =
        "module a {\n"
        "    namespace urn:tests:a;\n"
        "    prefix a;\n"
        "    yang-version 1.1;\n"
        "\n"
        "    identity base-t;\n"
        "    identity eth { base base-t; }\n"
        "    identity ani { base base-t; }\n"
        "\n"
        "    container ifs {\n"
        "        list if {\n"
        "            key name;\n"
        "            unique alias;\n"
        "            leaf name { type string; }\n"
        "            leaf alias { type string; }\n"
        "            leaf type { type identityref { base base-t; } }\n"
        /* local: reads a sibling of the same list instance */
        "            leaf ani-id {\n"
        "                when \"derived-from-or-self(../type, 'a:ani')\";\n"
        "                type uint32;\n"
        "            }\n"
        "            list sub {\n"
        "                key id;\n"
        "                leaf id { type uint32; }\n"
        /* local: reads three levels up, still inside the same 'if' instance */
        "                leaf tag {\n"
        "                    must \"derived-from-or-self(../../type, 'a:eth')\";\n"
        "                    type uint32;\n"
        "                }\n"
        "            }\n"
        /* list-scope: counts a whole nested list of the same instance */
        "            leaf sub-limit {\n"
        "                must \"count(../sub) <= .\";\n"
        "                type uint32;\n"
        "            }\n"
        "        }\n"
        "    }\n"
        "\n"
        /* the shared forwarder of bbf-l2-forwarding: a global uniqueness count on a leaf of a doubly nested
         * list, next to a leafref confined to the outer list instance */
        "    container fwds {\n"
        "        list fwd {\n"
        "            key name;\n"
        "            leaf name { type string; }\n"
        "            container ports {\n"
        "                list port {\n"
        "                    key name;\n"
        "                    leaf name { type string; }\n"
        "                    leaf sub-if {\n"
        "                        type string;\n"
        "                        must \"count(/a:fwds/a:fwd/a:ports/a:port[a:sub-if = current()]) < 2\";\n"
        "                    }\n"
        "                }\n"
        "            }\n"
        "            leaf-list flood-port { type leafref { path \"../ports/port/name\"; } }\n"
        "        }\n"
        "    }\n"
        "\n"
        "    container svcs {\n"
        "        list svc {\n"
        "            key name;\n"
        "            leaf name { type string; }\n"
        /* bounded: an absolute path narrowed to one instance by a key predicate driven by current() */
        "            leaf uses {\n"
        "                must \"derived-from-or-self(/a:ifs/a:if[a:name = current()]/a:type, 'a:ani')\";\n"
        "                type string;\n"
        "            }\n"
        /* bounded: leafref */
        "            leaf ref {\n"
        "                type leafref { path \"/a:ifs/a:if/a:name\"; }\n"
        "            }\n"
        "        }\n"
        "        leaf any-ani {\n"
        /* unbounded: an absolute path with no predicate, reaching every 'if' instance */
        "            when \"derived-from-or-self(/a:ifs/a:if/a:type, 'a:ani')\";\n"
        "            type string;\n"
        "        }\n"
        "    }\n"
        "\n"
        /* a top-level default that only exists while its when holds */
        "    leaf dflt {\n"
        "        when \"/a:ifs/a:if[a:name = 'gate']\";\n"
        "        type string;\n"
        "        default \"here\";\n"
        "    }\n"
        "}";

/** @brief edits of the current random run, printed when the validators disagree */
static char edit_log[4096];

/** @brief NULL-terminated names of the modules check_same() validates, at most 4 */
static const char *check_mods[5] = {"a", NULL, NULL, NULL, NULL};

/** @brief extra options of every incremental run of check_same(), each one compared against the full run */
static const uint32_t incr_opt_sets[] = {0, LYD_VALIDATE_INCR_SHALLOW_DELETE};

/**
 * @brief Validate @p data both ways and require the two runs to agree.
 *
 * The incremental side runs once per ::incr_opt_sets, so every edit of every test also covers the narrow scope of
 * deleted instances.
 *
 * @param[in] state Test state.
 * @param[in] before Tree before the edit, already valid.
 * @param[in] after Tree after the edit, to be validated.
 * @param[in] allow_fallback Whether the edit may legitimately not be analysable, such as an edit that changes
 * nothing and so produces an empty diff.
 * @param[out] rc_out Optional shared verdict of the two runs.
 */
static void
check_same(void **state, const struct lyd_node *before, const struct lyd_node *after, ly_bool allow_fallback,
        LY_ERR *rc_out)
{
    struct lyd_node *diff = NULL, *full = NULL, *incr = NULL;
    const struct lys_module *mods[5] = {NULL};
    char *full_str = NULL, *incr_str = NULL;
    uint64_t fallbacks_before = 0, fallbacks_after = 0;
    uint32_t i, mod_count, s, opts;
    ly_bool self_deleted;
    char full_msg[256], incr_msg[256];
    LY_ERR rc_full, rc_incr;

    for (mod_count = 0; check_mods[mod_count]; ++mod_count) {
        mods[mod_count] = ly_ctx_get_module_implemented(UTEST_LYCTX, check_mods[mod_count]);
        assert_non_null(mods[mod_count]);
    }

    assert_int_equal(LY_SUCCESS, lyd_dup_siblings(after, NULL, LYD_DUP_RECURSIVE | LYD_DUP_WITH_FLAGS, &full));

    /* split into the two passes the same way sysrepo drives them */
    /* every module is validated, like sysrepo does for each module an edit may reach */
    rc_full = LY_SUCCESS;
    for (i = 0; !rc_full && (i < mod_count); ++i) {
        rc_full = lyd_validate_module(&full, mods[i], LYD_VALIDATE_NOT_FINAL, NULL);
    }
    for (i = 0; !rc_full && (i < mod_count); ++i) {
        rc_full = lyd_validate_module_final(full, mods[i], 0);
    }
    snprintf(full_msg, sizeof full_msg, "%s", ly_err_last(UTEST_LYCTX) ? ly_err_last(UTEST_LYCTX)->msg : "-");
    ly_err_clean((struct ly_ctx *)UTEST_LYCTX, NULL);
    if (!rc_full) {
        assert_int_equal(LY_SUCCESS, lyd_print_mem(&full_str, full, LYD_XML, LYD_PRINT_WITHSIBLINGS));
    }

    for (s = 0; s < sizeof incr_opt_sets / sizeof *incr_opt_sets; ++s) {
    opts = incr_opt_sets[s];
    self_deleted = 0;
    lyd_validate_incr_stats(UTEST_LYCTX, NULL, &fallbacks_before);
    assert_int_equal(LY_SUCCESS, lyd_diff_siblings(before, after, 0, &diff));
    assert_int_equal(LY_SUCCESS, lyd_dup_siblings(after, NULL, LYD_DUP_RECURSIVE | LYD_DUP_WITH_FLAGS, &incr));

    /* the changes the validation makes itself (autodeleted when, new defaults) are merged into the edit diff
     * before the next module and the final pass, as sysrepo does with its notify diff */
    rc_incr = LY_SUCCESS;
    for (i = 0; !rc_incr && (i < mod_count); ++i) {
        struct lyd_node *val_diff = NULL;

        rc_incr = lyd_validate_module_incr(&incr, mods[i], diff, opts | LYD_VALIDATE_NOT_FINAL, &val_diff);
        if (val_diff) {
            char *val_str = NULL;

            /* deleted defaults count too, and they are only printed with all the defaults */
            assert_int_equal(LY_SUCCESS, lyd_print_mem(&val_str, val_diff, LYD_XML,
                    LYD_PRINT_WITHSIBLINGS | LYD_PRINT_WD_ALL));
            if (val_str && strstr(val_str, "yang:operation=\"delete\"")) {
                self_deleted = 1;
            }
            free(val_str);
            assert_int_equal(LY_SUCCESS, lyd_diff_merge_all(&diff, val_diff, 0));
            lyd_free_all(val_diff);
        }
    }
    for (i = 0; !rc_incr && (i < mod_count); ++i) {
        rc_incr = lyd_validate_module_incr_final(incr, mods[i], diff, opts);
    }
    snprintf(incr_msg, sizeof incr_msg, "%s", ly_err_last(UTEST_LYCTX) ? ly_err_last(UTEST_LYCTX)->msg : "-");
    ly_err_clean((struct ly_ctx *)UTEST_LYCTX, NULL);

    if (rc_full != rc_incr) {
        char *diff_str = NULL;

        lyd_print_mem(&diff_str, diff, LYD_XML, LYD_PRINT_WITHSIBLINGS);
        print_message("[  MSG     ] full %d (%s) vs incremental %d with options 0x%x (%s), diff:\n%s\n", rc_full,
                full_msg, rc_incr, opts, incr_msg, diff_str);
        print_message("[  MSG     ] edits so far (path = last value used, not always relevant):\n%s\n", edit_log);
        free(diff_str);
    }
    assert_int_equal(rc_full, rc_incr);

    /* a node the validation deleted itself must force the full pass, anything else must not: a fallback would
     * make the comparison above prove nothing about the incremental path */
    lyd_validate_incr_stats(UTEST_LYCTX, NULL, &fallbacks_after);
    if (self_deleted) {
        /* an edit already rejected before the deletion was looked at needs no full pass */
        if (!rc_incr) {
            assert_true(fallbacks_after > fallbacks_before);
        }
    } else if (!allow_fallback) {
        assert_int_equal(fallbacks_before, fallbacks_after);
    }

    if (!rc_full) {
        assert_int_equal(LY_SUCCESS, lyd_print_mem(&incr_str, incr, LYD_XML, LYD_PRINT_WITHSIBLINGS));
        /* an edit that leaves no data at all prints nothing */
        assert_string_equal(full_str ? full_str : "", incr_str ? incr_str : "");
    }

    free(incr_str);
    incr_str = NULL;
    lyd_free_siblings(incr);
    incr = NULL;
    lyd_free_siblings(diff);
    diff = NULL;
    }

    if (rc_out) {
        *rc_out = rc_full;
    }

    free(full_str);
    lyd_free_siblings(full);
}

/**
 * @brief Validate an accepted edit in full, so the next one starts from the tree a datastore would have stored.
 *
 * The stored tree carries no new flags and none of the nodes the validation drops. Chaining the raw edited tree
 * instead lets the full run recheck nodes of earlier edits that no later diff mentions.
 */
static void
settle(void **state, struct lyd_node **tree)
{
    const struct lys_module *mod;
    uint32_t i;

    for (i = 0; check_mods[i]; ++i) {
        mod = ly_ctx_get_module_implemented(UTEST_LYCTX, check_mods[i]);
        assert_int_equal(LY_SUCCESS, lyd_validate_module(tree, mod, LYD_VALIDATE_NOT_FINAL, NULL));
    }
    for (i = 0; check_mods[i]; ++i) {
        mod = ly_ctx_get_module_implemented(UTEST_LYCTX, check_mods[i]);
        assert_int_equal(LY_SUCCESS, lyd_validate_module_final(*tree, mod, 0));
    }
}

/**
 * @brief Parse a valid starting tree.
 */
static struct lyd_node *
parse_valid(void **state, const char *xml)
{
    struct lyd_node *tree = NULL;

    assert_int_equal(LY_SUCCESS, lyd_parse_data_mem(UTEST_LYCTX, xml, LYD_XML, 0, LYD_VALIDATE_PRESENT, &tree));
    assert_non_null(tree);
    return tree;
}

/**
 * @brief Apply an edit to a duplicate of @p before and check both validators agree on the result.
 */
static void
check_edit(void **state, const struct lyd_node *before, const char *path, const char *value, LY_ERR expected)
{
    struct lyd_node *after = NULL;
    LY_ERR rc;

    assert_int_equal(LY_SUCCESS, lyd_dup_siblings(before, NULL, LYD_DUP_RECURSIVE | LYD_DUP_WITH_FLAGS, &after));
    assert_int_equal(LY_SUCCESS, lyd_new_path(after, UTEST_LYCTX, path, value, LYD_NEW_PATH_UPDATE, NULL));

    check_same(state, before, after, 0, &rc);
    if (expected != rc) {
        print_message("[  MSG     ] edit %s = %s: expected %d, got %d\n", path, value ? value : "(null)", expected, rc);
    }
    assert_int_equal(expected, rc);

    lyd_free_siblings(after);
}

/**
 * @brief Remove the single node @p path matches.
 */
static void
drop_node(struct lyd_node **tree, const char *path)
{
    struct ly_set *set = NULL;

    assert_int_equal(LY_SUCCESS, lyd_find_xpath(*tree, path, &set));
    assert_int_equal(1, set->count);
    if (set->dnodes[0] == *tree) {
        *tree = (*tree)->next;
    }
    lyd_free_tree(set->dnodes[0]);
    ly_set_free(set, NULL);
}

/**
 * @brief Delete a node from a duplicate of @p before and check both validators agree on the result.
 */
static void
check_delete(void **state, const struct lyd_node *before, const char *path, LY_ERR expected)
{
    struct lyd_node *after = NULL;
    LY_ERR rc;

    assert_int_equal(LY_SUCCESS, lyd_dup_siblings(before, NULL, LYD_DUP_RECURSIVE | LYD_DUP_WITH_FLAGS, &after));
    drop_node(&after, path);

    check_same(state, before, after, 0, &rc);
    if (expected != rc) {
        print_message("[  MSG     ] delete %s: expected %d, got %d\n", path, expected, rc);
    }
    assert_int_equal(expected, rc);

    lyd_free_siblings(after);
}

static const char *base_xml =
        "<ifs xmlns=\"urn:tests:a\">"
        "  <if><name>e1</name><alias>a1</alias><type>eth</type><sub-limit>2</sub-limit>"
        "    <sub><id>1</id><tag>10</tag></sub>"
        "  </if>"
        "  <if><name>n1</name><alias>a2</alias><type>ani</type><ani-id>7</ani-id></if>"
        "</ifs>"
        "<fwds xmlns=\"urn:tests:a\">"
        "  <fwd><name>f1</name>"
        "    <ports>"
        "      <port><name>p1</name><sub-if>v1</sub-if></port>"
        "      <port><name>p2</name><sub-if>v2</sub-if></port>"
        "    </ports>"
        "    <flood-port>p1</flood-port>"
        "  </fwd>"
        "  <fwd><name>f2</name>"
        "    <ports><port><name>p3</name><sub-if>v3</sub-if></port></ports>"
        "  </fwd>"
        "</fwds>"
        "<svcs xmlns=\"urn:tests:a\">"
        "  <svc><name>s1</name><uses>n1</uses><ref>e1</ref></svc>"
        "</svcs>";

static void
test_local_when(void **state)
{
    struct lyd_node *before;

    UTEST_ADD_MODULE(schema_a, LYS_IN_YANG, NULL, NULL);
    before = parse_valid(state, base_xml);

    /* a new instance whose when is satisfied */
    check_edit(state, before, "/a:ifs/if[name='n2']/type", "a:ani", LY_SUCCESS);

    /* the when of an existing instance turns false, which is an error rather than an autodelete because
     * the node it guards is not new */
    check_edit(state, before, "/a:ifs/if[name='n1']/type", "a:eth", LY_EVALID);

    lyd_free_siblings(before);
}

static void
test_local_must(void **state)
{
    struct lyd_node *before;

    UTEST_ADD_MODULE(schema_a, LYS_IN_YANG, NULL, NULL);
    before = parse_valid(state, base_xml);

    /* a sub with a tag under an 'eth' interface is fine */
    check_edit(state, before, "/a:ifs/if[name='e1']/sub[id='2']/tag", "20", LY_SUCCESS);

    /* the same under an 'ani' interface violates the must three levels up */
    check_edit(state, before, "/a:ifs/if[name='n1']/sub[id='2']/tag", "20", LY_EVALID);

    /* changing the type out from under an existing tag violates it too */
    check_edit(state, before, "/a:ifs/if[name='e1']/type", "a:ani", LY_EVALID);

    lyd_free_siblings(before);
}

static void
test_list_scope(void **state)
{
    struct lyd_node *before;

    UTEST_ADD_MODULE(schema_a, LYS_IN_YANG, NULL, NULL);
    before = parse_valid(state, base_xml);

    /* still within sub-limit */
    check_edit(state, before, "/a:ifs/if[name='e1']/sub[id='2']/tag", "20", LY_SUCCESS);

    /* over sub-limit, which only a count() over the whole nested list can see */
    check_edit(state, before, "/a:ifs/if[name='e1']/sub-limit", "0", LY_EVALID);

    /* the unique of the whole list is violated by a duplicate alias in another instance */
    check_edit(state, before, "/a:ifs/if[name='n1']/alias", "a1", LY_EVALID);

    lyd_free_siblings(before);
}

static void
test_bounded(void **state)
{
    struct lyd_node *before;

    UTEST_ADD_MODULE(schema_a, LYS_IN_YANG, NULL, NULL);
    before = parse_valid(state, base_xml);

    /* the referenced instance is an 'ani' */
    check_edit(state, before, "/a:svcs/svc[name='s2']/uses", "n1", LY_SUCCESS);

    /* the referenced instance is an 'eth' */
    check_edit(state, before, "/a:svcs/svc[name='s2']/uses", "e1", LY_EVALID);

    /* changing the referenced instance invalidates a service that was valid before the edit */
    check_edit(state, before, "/a:ifs/if[name='n1']/type", "a:eth", LY_EVALID);

    /* deleting the referenced instance leaves the same service dangling */
    check_delete(state, before, "/a:ifs/if[name='n1']", LY_EVALID);

    lyd_free_siblings(before);
}

static void
test_leafref(void **state)
{
    struct lyd_node *before;

    UTEST_ADD_MODULE(schema_a, LYS_IN_YANG, NULL, NULL);
    before = parse_valid(state, base_xml);

    /* a leafref to an existing instance */
    check_edit(state, before, "/a:svcs/svc[name='s2']/ref", "n1", LY_SUCCESS);

    /* a leafref to an instance that does not exist */
    check_edit(state, before, "/a:svcs/svc[name='s2']/ref", "nope", LY_EVALID);

    /* deleting the target of an existing leafref */
    check_delete(state, before, "/a:ifs/if[name='e1']", LY_EVALID);

    lyd_free_siblings(before);
}

static void
test_unbounded(void **state)
{
    struct lyd_node *before;

    UTEST_ADD_MODULE(schema_a, LYS_IN_YANG, NULL, NULL);
    before = parse_valid(state, base_xml);

    /* the when reaches every interface and one of them is an 'ani' */
    check_edit(state, before, "/a:svcs/any-ani", "x", LY_SUCCESS);

    /* removing the only 'ani' makes it false, so the node is autodeleted rather than kept */
    check_delete(state, before, "/a:ifs/if[name='n1']", LY_EVALID);

    lyd_free_siblings(before);
}

#define PORT_SUB_IF(fwd, port) "/a:fwds/fwd[name='" fwd "']/ports/port[name='" port "']/sub-if"

/**
 * @brief The global uniqueness count is the one constraint the value-keyed filter skips, so creating a port has
 * to keep seeing every other port that already holds the value.
 */
static void
test_shared_count_create(void **state)
{
    struct lyd_node *before;

    UTEST_ADD_MODULE(schema_a, LYS_IN_YANG, NULL, NULL);
    before = parse_valid(state, base_xml);

    /* a value nobody holds */
    check_edit(state, before, PORT_SUB_IF("f1", "p9"), "v9", LY_SUCCESS);

    /* a value held by a port of the same forwarder */
    check_edit(state, before, PORT_SUB_IF("f1", "p9"), "v1", LY_EVALID);

    /* a value held by a port of another forwarder, which no dirty root contains */
    check_edit(state, before, PORT_SUB_IF("f1", "p9"), "v3", LY_EVALID);
    check_edit(state, before, PORT_SUB_IF("f2", "p9"), "v1", LY_EVALID);

    lyd_free_siblings(before);
}

/**
 * @brief Moving a value has to count as touching both the old and the new one.
 */
static void
test_shared_count_replace(void **state)
{
    struct lyd_node *before, *mid = NULL, *after = NULL;
    LY_ERR rc;

    UTEST_ADD_MODULE(schema_a, LYS_IN_YANG, NULL, NULL);
    before = parse_valid(state, base_xml);

    /* onto a free value */
    check_edit(state, before, PORT_SUB_IF("f1", "p1"), "v9", LY_SUCCESS);

    /* onto a value held by the same forwarder, then by another one */
    check_edit(state, before, PORT_SUB_IF("f1", "p1"), "v2", LY_EVALID);
    check_edit(state, before, PORT_SUB_IF("f1", "p1"), "v3", LY_EVALID);

    /* freeing a value and reusing it in one edit: only the old value of the moved port makes the reuse legal,
     * so this passes only if a replaced value counts as touched */
    assert_int_equal(LY_SUCCESS, lyd_dup_siblings(before, NULL, LYD_DUP_RECURSIVE | LYD_DUP_WITH_FLAGS, &after));
    assert_int_equal(LY_SUCCESS, lyd_new_path(after, UTEST_LYCTX, PORT_SUB_IF("f1", "p1"), "v9",
            LYD_NEW_PATH_UPDATE, NULL));
    assert_int_equal(LY_SUCCESS, lyd_new_path(after, UTEST_LYCTX, PORT_SUB_IF("f1", "p2"), "v1",
            LYD_NEW_PATH_UPDATE, NULL));
    check_same(state, before, after, 0, &rc);
    assert_int_equal(LY_SUCCESS, rc);
    lyd_free_siblings(after);
    after = NULL;

    /* the same in two edits, so the second one sees a value freed by an earlier apply */
    assert_int_equal(LY_SUCCESS, lyd_dup_siblings(before, NULL, LYD_DUP_RECURSIVE | LYD_DUP_WITH_FLAGS, &mid));
    assert_int_equal(LY_SUCCESS, lyd_new_path(mid, UTEST_LYCTX, PORT_SUB_IF("f2", "p3"), "v9",
            LYD_NEW_PATH_UPDATE, NULL));
    check_same(state, before, mid, 0, &rc);
    assert_int_equal(LY_SUCCESS, rc);
    check_edit(state, mid, PORT_SUB_IF("f1", "p1"), "v3", LY_SUCCESS);

    lyd_free_siblings(mid);
    lyd_free_siblings(before);
}

/**
 * @brief A deleted value becomes free, while the leafref confined to the forwarder still has to be checked.
 */
static void
test_shared_count_delete(void **state)
{
    struct lyd_node *before, *after = NULL;
    LY_ERR rc;

    UTEST_ADD_MODULE(schema_a, LYS_IN_YANG, NULL, NULL);
    before = parse_valid(state, base_xml);

    /* an unreferenced port */
    check_delete(state, before, "/a:fwds/fwd[name='f2']/ports/port[name='p3']", LY_SUCCESS);

    /* a port a flood-port of the same forwarder points at */
    check_delete(state, before, "/a:fwds/fwd[name='f1']/ports/port[name='p1']", LY_EVALID);

    /* deleting a port frees its value for a port of another forwarder */
    assert_int_equal(LY_SUCCESS, lyd_dup_siblings(before, NULL, LYD_DUP_RECURSIVE | LYD_DUP_WITH_FLAGS, &after));
    drop_node(&after, "/a:fwds/fwd[name='f1']/ports/port[name='p2']");
    assert_int_equal(LY_SUCCESS, lyd_new_path(after, UTEST_LYCTX, PORT_SUB_IF("f2", "p9"), "v2",
            LYD_NEW_PATH_UPDATE, NULL));
    check_same(state, before, after, 0, &rc);
    assert_int_equal(LY_SUCCESS, rc);
    lyd_free_siblings(after);
    after = NULL;

    /* deleting a whole forwarder frees the values of every port it held */
    assert_int_equal(LY_SUCCESS, lyd_dup_siblings(before, NULL, LYD_DUP_RECURSIVE | LYD_DUP_WITH_FLAGS, &after));
    drop_node(&after, "/a:fwds/fwd[name='f1']");
    assert_int_equal(LY_SUCCESS, lyd_new_path(after, UTEST_LYCTX, PORT_SUB_IF("f2", "p9"), "v1",
            LYD_NEW_PATH_UPDATE, NULL));
    check_same(state, before, after, 0, &rc);
    assert_int_equal(LY_SUCCESS, rc);
    lyd_free_siblings(after);

    lyd_free_siblings(before);
}

/**
 * @brief The filter has to actually fire, otherwise the tests above would pass on dead code.
 */
static void
test_shared_count_filter(void **state)
{
    struct lyd_node *before;
    uint64_t evals = 0, skips = 0, evals2 = 0, skips2 = 0;

    UTEST_ADD_MODULE(schema_a, LYS_IN_YANG, NULL, NULL);
    before = parse_valid(state, base_xml);

    lyd_validate_incr_must_stats(UTEST_LYCTX, &evals, &skips);
    check_edit(state, before, PORT_SUB_IF("f1", "p9"), "v9", LY_SUCCESS);
    lyd_validate_incr_must_stats(UTEST_LYCTX, &evals2, &skips2);

    /* the ports holding another value are not re-counted: the two inside the dirty root, which only a filter
     * reaching below a scope root can skip, and the one the extra pass picked up outside it */
    assert_true(skips2 - skips >= 3);

    /* and the ones that are counted are still counted */
    assert_true(evals2 > evals);

    lyd_free_siblings(before);
}

/**
 * @brief Random edit sequences: whatever the edits are, the incremental verdict must equal the full one.
 */
static void
test_random_edits(void **state)
{
    struct lyd_node *before = NULL, *after = NULL;
    const char *types[] = {"a:eth", "a:ani"};
    char path[128], value[32];
    uint32_t seed, i, step;
    LY_ERR rc;

    UTEST_ADD_MODULE(schema_a, LYS_IN_YANG, NULL, NULL);

    for (seed = 1; seed <= 40; ++seed) {
        srand(seed);
        before = parse_valid(state, base_xml);

        for (step = 0; step < 4; ++step) {
            assert_int_equal(LY_SUCCESS, lyd_dup_siblings(before, NULL, LYD_DUP_RECURSIVE | LYD_DUP_WITH_FLAGS, &after));

            switch (rand() % 9) {
            case 0:
                sprintf(path, "/a:ifs/if[name='x%d']/type", rand() % 3);
                assert_int_equal(LY_SUCCESS, lyd_new_path(after, UTEST_LYCTX, path, types[rand() % 2],
                        LYD_NEW_PATH_UPDATE, NULL));
                break;
            case 1:
                sprintf(path, "/a:ifs/if[name='e1']/sub[id='%d']/tag", rand() % 4);
                sprintf(value, "%d", rand() % 100);
                assert_int_equal(LY_SUCCESS, lyd_new_path(after, UTEST_LYCTX, path, value, LYD_NEW_PATH_UPDATE, NULL));
                break;
            case 2:
                sprintf(path, "/a:ifs/if[name='e1']/sub-limit");
                sprintf(value, "%d", rand() % 3);
                assert_int_equal(LY_SUCCESS, lyd_new_path(after, UTEST_LYCTX, path, value, LYD_NEW_PATH_UPDATE, NULL));
                break;
            case 3:
                sprintf(path, "/a:svcs/svc[name='s%d']/uses", rand() % 3);
                assert_int_equal(LY_SUCCESS, lyd_new_path(after, UTEST_LYCTX, path, (rand() % 2) ? "n1" : "e1",
                        LYD_NEW_PATH_UPDATE, NULL));
                break;
            case 4:
                sprintf(path, "/a:ifs/if[name='%s']/alias", (rand() % 2) ? "e1" : "n1");
                sprintf(value, "a%d", rand() % 3);
                assert_int_equal(LY_SUCCESS, lyd_new_path(after, UTEST_LYCTX, path, value, LYD_NEW_PATH_UPDATE, NULL));
                break;
            case 5:
                /* drawing from a small pool of values makes duplicates and value moves common */
                sprintf(path, "/a:fwds/fwd[name='f%d']/ports/port[name='p%d']/sub-if", rand() % 2 + 1, rand() % 4 + 1);
                sprintf(value, "v%d", rand() % 3 + 1);
                assert_int_equal(LY_SUCCESS, lyd_new_path(after, UTEST_LYCTX, path, value, LYD_NEW_PATH_UPDATE, NULL));
                break;
            case 6:
            case 7: {
                struct ly_set *set = NULL;

                if (rand() % 2) {
                    sprintf(path, "/a:fwds/fwd[name='f%d']/ports/port[name='p%d']", rand() % 2 + 1, rand() % 4 + 1);
                } else {
                    sprintf(path, "/a:fwds/fwd[name='f%d']", rand() % 2 + 1);
                }
                assert_int_equal(LY_SUCCESS, lyd_find_xpath(after, path, &set));
                for (i = 0; i < set->count; ++i) {
                    lyd_free_tree(set->dnodes[i]);
                }
                ly_set_free(set, NULL);
                break;
            }
            default: {
                struct ly_set *set = NULL;

                sprintf(path, "/a:ifs/if[name='%s']", (rand() % 2) ? "e1" : "n1");
                assert_int_equal(LY_SUCCESS, lyd_find_xpath(after, path, &set));
                for (i = 0; i < set->count; ++i) {
                    if (set->dnodes[i] == after) {
                        after = after->next;
                    }
                    lyd_free_tree(set->dnodes[i]);
                }
                ly_set_free(set, NULL);
                break;
            }
            }

            /* a random edit may well change nothing at all, which leaves an empty diff and no way to analyse it */
            check_same(state, before, after, 1, &rc);

            if (rc) {
                /* an invalid edit is rejected, the next step starts from the last valid tree again */
                lyd_free_siblings(after);
                after = NULL;
                continue;
            }

            settle(state, &after);
            lyd_free_siblings(before);
            before = after;
            after = NULL;
        }

        lyd_free_siblings(before);
        before = NULL;
    }
}

/**
 * @brief A top-level default is created by the validation itself, so the incremental pass has to treat it
 * as new data of its own rather than as something the edit already accounted for.
 */
static void
test_toplevel_default(void **state)
{
    struct lyd_node *before;

    UTEST_ADD_MODULE(schema_a, LYS_IN_YANG, NULL, NULL);
    before = parse_valid(state, base_xml);

    /* the when of the default is false, so it must be created and then dropped again */
    check_edit(state, before, "/a:ifs/if[name='n2']/type", "a:ani", LY_SUCCESS);

    /* the when of the default becomes true, so it must be created and kept */
    check_edit(state, before, "/a:ifs/if[name='gate']/type", "a:ani", LY_SUCCESS);

    lyd_free_siblings(before);
}

/**
 * @brief Data stored by an application that created defaults without validating them can contain a default
 * node whose "when" has never held. A full validation drops it, so the incremental one has to as well.
 */
static void
test_stale_default(void **state)
{
    struct lyd_node *before = NULL, *after = NULL;
    LY_ERR rc;

    UTEST_ADD_MODULE(schema_a, LYS_IN_YANG, NULL, NULL);

    /* parse without validating and add the defaults the way an application storing data would, which leaves
     * the default with the false when in the tree */
    assert_int_equal(LY_SUCCESS, lyd_parse_data_mem(UTEST_LYCTX, base_xml, LYD_XML, LYD_PARSE_ONLY, 0, &before));
    assert_int_equal(LY_SUCCESS, lyd_new_implicit_all(&before, UTEST_LYCTX, LYD_IMPLICIT_NO_STATE, NULL));

    assert_int_equal(LY_SUCCESS, lyd_dup_siblings(before, NULL, LYD_DUP_RECURSIVE | LYD_DUP_WITH_FLAGS, &after));
    assert_int_equal(LY_SUCCESS, lyd_new_path(after, UTEST_LYCTX, "/a:ifs/if[name='n2']/type", "a:ani",
            LYD_NEW_PATH_UPDATE, NULL));

    check_same(state, before, after, 0, &rc);
    assert_int_equal(LY_SUCCESS, rc);

    lyd_free_siblings(after);
    lyd_free_siblings(before);
}

static const char *schema_dw =
        "module dw {\n"
        "    namespace urn:tests:dw;\n"
        "    prefix dw;\n"
        "    yang-version 1.1;\n"
        "\n"
        "    container gate {\n"
        "        leaf on { type string; }\n"
        "        leaf off { type empty; }\n"
        "        leaf mode { type string; }\n"
        "    }\n"
        "    container items {\n"
        "        list item {\n"
        "            key name;\n"
        "            leaf name { type string; }\n"
        "            leaf limit { type uint32; }\n"
        /* nested defaults guarded by a when on another top-level tree, checked against their own instance */
        "            leaf speed {\n"
        "                when \"/dw:gate/dw:on = 'yes'\";\n"
        "                must \". <= ../limit\";\n"
        "                type uint32;\n"
        "                default 11;\n"
        "            }\n"
        "            leaf burst {\n"
        "                when \"not(/dw:gate/dw:off)\";\n"
        "                must \". <= ../limit\";\n"
        "                type uint32;\n"
        "                default 11;\n"
        "            }\n"
        /* the same, but the when reads only its own instance */
        "            leaf boost {\n"
        "                when \"../limit > 10\";\n"
        "                must \". <= ../limit\";\n"
        "                type uint32;\n"
        "                default 15;\n"
        "            }\n"
        "        }\n"
        "    }\n"
        "    container stats {\n"
        "        config false;\n"
        "        list s {\n"
        "            key n;\n"
        "            leaf n { type string; }\n"
        "            leaf rate {\n"
        "                when \"/dw:gate/dw:mode = 'fast'\";\n"
        "                type uint32;\n"
        "                default 1;\n"
        "            }\n"
        "        }\n"
        "    }\n"
        "    leaf note { type string; }\n"
        "}";

/**
 * @brief Validate an edited tree both ways, where the incremental run must fall back.
 */
static void
check_fallback(void **state, const struct lyd_node *before, const struct lyd_node *after, LY_ERR expected)
{
    uint64_t fb_before = 0, fb_after = 0;
    LY_ERR rc;

    lyd_validate_incr_stats(UTEST_LYCTX, NULL, &fb_before);
    check_same(state, before, after, 1, &rc);
    lyd_validate_incr_stats(UTEST_LYCTX, NULL, &fb_after);
    assert_int_equal(expected, rc);
    assert_true(fb_after > fb_before);
}

/**
 * @brief Validate a single edit both ways, where the incremental run must fall back.
 */
static void
check_edit_fallback(void **state, const struct lyd_node *before, const char *path, const char *value,
        LY_ERR expected)
{
    struct lyd_node *after = NULL;

    assert_int_equal(LY_SUCCESS, lyd_dup_siblings(before, NULL, LYD_DUP_RECURSIVE | LYD_DUP_WITH_FLAGS, &after));
    assert_int_equal(LY_SUCCESS, lyd_new_path(after, UTEST_LYCTX, path, value, LYD_NEW_PATH_UPDATE, NULL));
    check_fallback(state, before, after, expected);
    lyd_free_siblings(after);
}

/**
 * @brief A when that reads another top-level tree turns true, so a full validation creates the default in every
 * list instance, also in the ones the edit never touched, and checks it there.
 */
static void
test_dflt_when_remote(void **state)
{
    struct lyd_node *before, *after = NULL, *diff = NULL;
    const struct lys_module *mod;
    uint64_t fb[3] = {0};

    UTEST_ADD_MODULE(schema_dw, LYS_IN_YANG, NULL, NULL);
    check_mods[0] = "dw";

    before = parse_valid(state, "<gate xmlns=\"urn:tests:dw\"><on>no</on><off/></gate>"
            "<items xmlns=\"urn:tests:dw\"><item><name>i1</name><limit>20</limit></item>"
            "<item><name>i2</name><limit>5</limit></item></items>");

    /* the default 11 fits i1 but not the limit 5 of i2 */
    check_edit_fallback(state, before, "/dw:gate/on", "yes", LY_EVALID);

    /* a delete turns a when true just as well */
    assert_int_equal(LY_SUCCESS, lyd_dup_siblings(before, NULL, LYD_DUP_RECURSIVE | LYD_DUP_WITH_FLAGS, &after));
    drop_node(&after, "/dw:gate/off");
    check_fallback(state, before, after, LY_EVALID);
    lyd_free_siblings(after);

    /* a when reading its own instance turns true only in the edited one, the default 15 breaks the limit 12 */
    check_edit(state, before, "/dw:items/item[name='i2']/limit", "12", LY_EVALID);
    check_edit(state, before, "/dw:items/item[name='i2']/limit", "30", LY_SUCCESS);

    /* edits the cross-instance whens do not read stay incremental */
    check_edit(state, before, "/dw:items/item[name='i2']/limit", "6", LY_SUCCESS);
    check_edit(state, before, "/dw:note", "x", LY_SUCCESS);

    lyd_free_siblings(before);

    /* without state data no state default is created, so its when needs no fallback */
    mod = ly_ctx_get_module_implemented(UTEST_LYCTX, "dw");
    assert_int_equal(LY_SUCCESS, lyd_parse_data_mem(UTEST_LYCTX,
            "<gate xmlns=\"urn:tests:dw\"><on>no</on><off/></gate>", LYD_XML, 0,
            LYD_VALIDATE_PRESENT | LYD_VALIDATE_NO_STATE, &before));
    assert_int_equal(LY_SUCCESS, lyd_dup_siblings(before, NULL, LYD_DUP_RECURSIVE | LYD_DUP_WITH_FLAGS, &after));
    assert_int_equal(LY_SUCCESS, lyd_new_path(after, UTEST_LYCTX, "/dw:gate/mode", "fast", 0, NULL));
    assert_int_equal(LY_SUCCESS, lyd_diff_siblings(before, after, 0, &diff));
    lyd_validate_incr_stats(UTEST_LYCTX, NULL, &fb[0]);
    assert_int_equal(LY_SUCCESS, lyd_validate_module_incr(&after, mod, diff, LYD_VALIDATE_NO_STATE, NULL));
    lyd_validate_incr_stats(UTEST_LYCTX, NULL, &fb[1]);
    assert_int_equal(LY_SUCCESS, lyd_validate_module_incr(&after, mod, diff, 0, NULL));
    lyd_validate_incr_stats(UTEST_LYCTX, NULL, &fb[2]);
    assert_int_equal(fb[0], fb[1]);
    assert_true(fb[2] > fb[1]);
    lyd_free_siblings(diff);
    lyd_free_siblings(after);
    lyd_free_siblings(before);

    /* every limit fits, the defaults appear everywhere */
    before = parse_valid(state, "<gate xmlns=\"urn:tests:dw\"><on>no</on><off/></gate>"
            "<items xmlns=\"urn:tests:dw\"><item><name>i1</name><limit>20</limit></item>"
            "<item><name>i2</name><limit>30</limit></item></items>");
    check_edit_fallback(state, before, "/dw:gate/on", "yes", LY_SUCCESS);
    lyd_free_siblings(before);

    check_mods[0] = "a";
}

/**
 * @brief The fallback counter has to move, otherwise a silent return to full validation is invisible.
 */
static void
test_stats(void **state)
{
    struct lyd_node *before, *after = NULL;
    const struct lys_module *mod;
    uint64_t calls = 0, fallbacks = 0, calls2 = 0, fallbacks2 = 0;

    UTEST_ADD_MODULE(schema_a, LYS_IN_YANG, NULL, NULL);
    before = parse_valid(state, base_xml);
    mod = ly_ctx_get_module_implemented(UTEST_LYCTX, "a");

    lyd_validate_incr_stats(UTEST_LYCTX, &calls, &fallbacks);

    /* no diff at all is the one case that always falls back */
    assert_int_equal(LY_SUCCESS, lyd_dup_siblings(before, NULL, LYD_DUP_RECURSIVE | LYD_DUP_WITH_FLAGS, &after));
    assert_int_equal(LY_SUCCESS, lyd_validate_module_incr(&after, mod, NULL, 0, NULL));

    lyd_validate_incr_stats(UTEST_LYCTX, &calls2, &fallbacks2);
    assert_int_equal(calls + 1, calls2);
    assert_int_equal(fallbacks + 1, fallbacks2);

    lyd_free_siblings(after);
    lyd_free_siblings(before);
}

/*
 * Shallow delete coverage. Every list here sits in a top-level container with no list above it, which is where a
 * deleted instance gets the narrow scope of LYD_VALIDATE_INCR_SHALLOW_DELETE, and each kind of rule that can see
 * the deleted instance from outside of it appears once.
 */
static const char *schema_sd =
        "module sd {\n"
        "    namespace urn:tests:sd;\n"
        "    prefix sd;\n"
        "    yang-version 1.1;\n"
        "\n"
        "    container top {\n"
        "        list item {\n"
        "            key name;\n"
        "            min-elements 1;\n"
        "            leaf name { type string; }\n"
        "        }\n"
        "        leaf-list tag { type string; }\n"
        "        container inner {\n"
        "            list x { key name; leaf name { type string; } }\n"
        "        }\n"
        "        choice mode {\n"
        "            default auto;\n"
        "            case auto { leaf auto { type string; default \"on\"; } }\n"
        "            case manual { list rule { key id; leaf id { type uint32; } } }\n"
        "        }\n"
        /* cross-instance rules of a sibling list that read the deleted instances */
        "        list peer {\n"
        "            key name;\n"
        "            leaf name { type string; }\n"
        "            leaf item-ref { type leafref { path \"../../item/name\"; } }\n"
        "            leaf tag-ref { type leafref { path \"../../tag\"; } }\n"
        "            leaf x-ref { type leafref { path \"../../inner/x/name\"; } }\n"
        "            leaf on {\n"
        "                when \"../../item[name = current()/../name]\";\n"
        "                type string;\n"
        "            }\n"
        "        }\n"
        "        list guard {\n"
        "            key name;\n"
        "            leaf name { type string; }\n"
        "            must \"count(../item) >= 2\";\n"
        "        }\n"
        "    }\n"
        "\n"
        /* a rule of the container itself, confined to no list instance */
        "    container counted {\n"
        "        presence \"only checked when there\";\n"
        "        must \"count(item) >= 2\";\n"
        "        list item { key name; leaf name { type string; } }\n"
        "    }\n"
        "\n"
        /* a rule with no atoms at all, which no extra pass can find */
        "    container blind {\n"
        "        must \"true()\";\n"
        "        list item { key name; leaf name { type string; } }\n"
        "    }\n"
        "}";

static const char *sd_xml =
        "<top xmlns=\"urn:tests:sd\">"
        "  <item><name>i1</name></item><item><name>i2</name></item><item><name>i3</name></item>"
        "  <tag>t1</tag><tag>t2</tag>"
        "  <inner><x><name>x1</name></x><x><name>x2</name></x></inner>"
        "  <rule><id>1</id></rule>"
        "  <peer><name>i1</name><item-ref>i1</item-ref><tag-ref>t1</tag-ref><x-ref>x1</x-ref><on>yes</on></peer>"
        "</top>"
        "<counted xmlns=\"urn:tests:sd\"><item><name>c1</name></item><item><name>c2</name></item>"
        "  <item><name>c3</name></item></counted>"
        "<blind xmlns=\"urn:tests:sd\"><item><name>b1</name></item><item><name>b2</name></item></blind>";

/**
 * @brief Delete a node both ways, see check_delete(), and require the narrow scope to be taken or not.
 */
static void
check_delete_shallow(void **state, const struct lyd_node *before, const char *path, LY_ERR expected, ly_bool shallow)
{
    uint64_t count = 0, count2 = 0;

    lyd_validate_incr_shallow_stats(UTEST_LYCTX, &count);
    check_delete(state, before, path, expected);
    lyd_validate_incr_shallow_stats(UTEST_LYCTX, &count2);
    if (shallow != (count2 > count)) {
        print_message("[  MSG     ] delete %s: narrow scope expected %d, taken %d times\n", path, shallow,
                (int)(count2 - count));
    }
    assert_int_equal(shallow, count2 > count);
}

/**
 * @brief Whatever a deleted instance breaks outside of itself is still found with the narrow scope.
 */
static void
test_shallow_delete(void **state)
{
    struct lyd_node *before, *start;

    UTEST_ADD_MODULE(schema_sd, LYS_IN_YANG, NULL, NULL);
    check_mods[0] = "sd";
    before = parse_valid(state, sd_xml);

    /* nothing refers to these */
    check_delete_shallow(state, before, "/sd:top/item[name='i3']", LY_SUCCESS, 1);
    check_delete_shallow(state, before, "/sd:top/tag[.='t2']", LY_SUCCESS, 1);
    check_delete_shallow(state, before, "/sd:top/inner/x[name='x2']", LY_SUCCESS, 1);

    /* the targets of leafrefs in a sibling list instance */
    check_delete_shallow(state, before, "/sd:top/tag[.='t1']", LY_EVALID, 1);
    check_delete_shallow(state, before, "/sd:top/inner/x[name='x1']", LY_EVALID, 1);

    /* the leafref and the when of a peer both read this one */
    check_delete_shallow(state, before, "/sd:top/item[name='i1']", LY_EVALID, 1);

    /* the last instance of the manual case: the parent gets the default case back */
    check_delete_shallow(state, before, "/sd:top/rule[id='1']", LY_SUCCESS, 1);

    /* a rule of the parent container itself and a rule with no atoms keep the wide scope */
    check_delete_shallow(state, before, "/sd:counted/item[name='c3']", LY_SUCCESS, 0);
    check_delete_shallow(state, before, "/sd:blind/item[name='b2']", LY_SUCCESS, 0);

    lyd_free_siblings(before);

    /* a min-elements of the parent and a count in a sibling list instance; the tag keeps the parent from turning
     * into an empty default container, whose diff deletes the parent itself */
    before = parse_valid(state, "<top xmlns=\"urn:tests:sd\"><item><name>i1</name></item><tag>t</tag></top>");
    check_delete_shallow(state, before, "/sd:top/item[name='i1']", LY_EVALID, 1);
    lyd_free_siblings(before);

    before = parse_valid(state, "<top xmlns=\"urn:tests:sd\"><item><name>i1</name></item><item><name>i2</name></item>"
            "<guard><name>g</name></guard></top>");
    check_delete_shallow(state, before, "/sd:top/item[name='i2']", LY_EVALID, 1);
    lyd_free_siblings(before);

    /* the rule of the parent container breaks, found by the wide scope */
    before = parse_valid(state, "<top xmlns=\"urn:tests:sd\"><item><name>i1</name></item></top>"
            "<counted xmlns=\"urn:tests:sd\"><item><name>c1</name></item><item><name>c2</name></item></counted>");
    check_delete_shallow(state, before, "/sd:counted/item[name='c2']", LY_EVALID, 0);
    lyd_free_siblings(before);

    /* the when of an existing peer is not evaluated again by either validation */
    before = parse_valid(state, "<top xmlns=\"urn:tests:sd\"><item><name>i1</name></item><item><name>i2</name></item>"
            "<peer><name>i2</name><on>yes</on></peer></top>");
    check_delete_shallow(state, before, "/sd:top/item[name='i2']", LY_SUCCESS, 1);

    /* the peer whose when reads the item is gone with it */
    assert_int_equal(LY_SUCCESS, lyd_dup_siblings(before, NULL, LYD_DUP_RECURSIVE | LYD_DUP_WITH_FLAGS, &start));
    drop_node(&start, "/sd:top/peer[name='i2']");
    drop_node(&start, "/sd:top/item[name='i2']");
    check_same(state, before, start, 0, NULL);
    lyd_free_siblings(start);

    /* a new peer leaf whose when reads the deleted item is dropped by the validation itself */
    assert_int_equal(LY_SUCCESS, lyd_dup_siblings(before, NULL, LYD_DUP_RECURSIVE | LYD_DUP_WITH_FLAGS, &start));
    drop_node(&start, "/sd:top/peer[name='i2']");
    drop_node(&start, "/sd:top/item[name='i2']");
    assert_int_equal(LY_SUCCESS, lyd_new_path(start, UTEST_LYCTX, "/sd:top/peer[name='i2']/on", "yes", 0, NULL));
    check_same(state, before, start, 0, NULL);
    lyd_free_siblings(start);
    lyd_free_siblings(before);

    check_mods[0] = "a";
}

/**
 * @brief Validate an edited tree in full, and incrementally against a hand-made edit diff with the narrow scope.
 *
 * Unlike check_same() the diff is not computed from the two trees, so it can describe the edit differently from
 * the data, which is what a diff merged from several steps may do.
 */
static void
check_diff_shallow(void **state, const struct lyd_node *after, const char *diff_xml, LY_ERR expected, ly_bool shallow)
{
    const struct lys_module *mod = ly_ctx_get_module_implemented(UTEST_LYCTX, "sd");
    struct lyd_node *full = NULL, *incr = NULL, *diff = NULL, *val_diff = NULL;
    uint64_t count = 0, count2 = 0;
    LY_ERR rc_full, rc_incr;

    assert_non_null(mod);

    assert_int_equal(LY_SUCCESS, lyd_dup_siblings(after, NULL, LYD_DUP_RECURSIVE | LYD_DUP_WITH_FLAGS, &full));
    rc_full = lyd_validate_module(&full, mod, 0, NULL);
    ly_err_clean((struct ly_ctx *)UTEST_LYCTX, NULL);

    assert_int_equal(LY_SUCCESS, lyd_dup_siblings(after, NULL, LYD_DUP_RECURSIVE | LYD_DUP_WITH_FLAGS, &incr));
    assert_int_equal(LY_SUCCESS, lyd_parse_data_mem(UTEST_LYCTX, diff_xml, LYD_XML, LYD_PARSE_ONLY, 0, &diff));
    lyd_validate_incr_shallow_stats(UTEST_LYCTX, &count);
    rc_incr = lyd_validate_module_incr(&incr, mod, diff, LYD_VALIDATE_INCR_SHALLOW_DELETE | LYD_VALIDATE_NOT_FINAL,
            &val_diff);
    if (!rc_incr) {
        rc_incr = lyd_validate_module_incr_final(incr, mod, diff, LYD_VALIDATE_INCR_SHALLOW_DELETE);
    }
    lyd_validate_incr_shallow_stats(UTEST_LYCTX, &count2);
    ly_err_clean((struct ly_ctx *)UTEST_LYCTX, NULL);

    assert_int_equal(expected, rc_full);
    assert_int_equal(rc_full, rc_incr);
    if (shallow != (count2 > count)) {
        print_message("[  MSG     ] narrow scope expected %d, taken %d times\n", shallow, (int)(count2 - count));
    }
    assert_int_equal(shallow, count2 > count);

    lyd_free_all(val_diff);
    lyd_free_siblings(diff);
    lyd_free_siblings(incr);
    lyd_free_siblings(full);
}

#define SD_DIFF_NS "xmlns=\"urn:tests:sd\" xmlns:yang=\"urn:ietf:params:xml:ns:yang:1\""

/**
 * @brief The narrow scope needs the surviving node to be the direct parent of the deleted instance.
 *
 * A diff that deletes an instance two levels below the node that still exists describes more missing data than the
 * parent checks look at, so it keeps the wide scope. The same delete one level below a surviving parent does not.
 */
static void
test_shallow_levels(void **state)
{
    struct lyd_node *before, *after = NULL;

    UTEST_ADD_MODULE(schema_sd, LYS_IN_YANG, NULL, NULL);
    check_mods[0] = "sd";
    before = parse_valid(state, sd_xml);

    /* the surviving node is the parent: top/inner exists, only x1 is gone; the peer that refers to x1 is found */
    assert_int_equal(LY_SUCCESS, lyd_dup_siblings(before, NULL, LYD_DUP_RECURSIVE | LYD_DUP_WITH_FLAGS, &after));
    drop_node(&after, "/sd:top/inner/x[name='x1']");
    check_diff_shallow(state, after, "<top " SD_DIFF_NS " yang:operation=\"none\"><inner yang:operation=\"none\">"
            "<x yang:operation=\"delete\"><name>x1</name></x></inner></top>", LY_EVALID, 1);
    lyd_free_siblings(after);
    after = NULL;

    /* the same instance, but the diff places it below an inner node that is not in the data: the surviving node is
     * top, two levels above the deleted instance */
    assert_int_equal(LY_SUCCESS, lyd_dup_siblings(before, NULL, LYD_DUP_RECURSIVE | LYD_DUP_WITH_FLAGS, &after));
    drop_node(&after, "/sd:top/inner");
    check_diff_shallow(state, after, "<top " SD_DIFF_NS " yang:operation=\"none\"><inner yang:operation=\"none\">"
            "<x yang:operation=\"delete\"><name>x1</name></x></inner></top>", LY_EVALID, 0);
    lyd_free_siblings(after);

    lyd_free_siblings(before);
    check_mods[0] = "a";
}

/**
 * @brief Only list and leaf-list instances with no list instance above them get the narrow scope.
 */
static void
test_shallow_gate(void **state)
{
    struct lyd_node *before;

    UTEST_ADD_MODULE(schema_a, LYS_IN_YANG, NULL, NULL);
    before = parse_valid(state, base_xml);

    /* the leafref of a service still finds the deleted interface, and the top-level default with a when is checked
     * as an extra node whatever the scope is */
    check_delete_shallow(state, before, "/a:ifs/if[name='e1']", LY_EVALID, 1);

    /* a port has a forwarder instance above it */
    check_delete_shallow(state, before, "/a:fwds/fwd[name='f2']/ports/port[name='p3']", LY_SUCCESS, 0);

    /* a whole forwarder has none */
    check_delete_shallow(state, before, "/a:fwds/fwd[name='f2']", LY_SUCCESS, 1);

    /* the only service leaves an empty default container, so the diff deletes the container instead */
    check_delete_shallow(state, before, "/a:svcs/svc[name='s1']", LY_SUCCESS, 0);

    lyd_free_siblings(before);
}

/*
 * Augment coverage. Module b augments the list of module a (data and a when on the augment itself) and
 * adds a top-level container of its own, module c only refers into a and b. An edit that touches a single
 * module can therefore break a constraint of another one, which is exactly what a per-module,
 * diff-driven validator could miss.
 */
static const char *schema_b =
        "module b {\n"
        "    namespace urn:tests:b;\n"
        "    prefix b;\n"
        "    yang-version 1.1;\n"
        "    import a { prefix a; }\n"
        "\n"
        "    augment \"/a:ifs/a:if\" {\n"
        "        container b-cfg {\n"
        "            when \"derived-from-or-self(../a:type, 'a:eth')\";\n"
        "            leaf speed { type uint32; default 100; }\n"
        "            leaf mtu { type uint32; must \"../speed <= .\"; }\n"
        "            leaf peer { type leafref { path \"/a:ifs/a:if/a:name\"; } }\n"
        /* creating the m2 case makes the validation delete the default m1 case */
        "            choice mode {\n"
        "                default m1;\n"
        "                case m1 { leaf m1-val { type uint32; default 1; } }\n"
        "                case m2 { leaf m2-val { type uint32; } }\n"
        "            }\n"
        "        }\n"
        /* a leafref of one interface into the when-guarded container of another one */
        "        leaf peer-speed { type leafref { path \"/a:ifs/a:if/b:b-cfg/b:speed\"; } }\n"
        "        container b-pc {\n"
        "            presence \"p\";\n"
        "            leaf mode { type string; mandatory true; }\n"
        "        }\n"
        "        list b-addr {\n"
        "            key id;\n"
        "            unique ip;\n"
        "            leaf id { type uint32; }\n"
        "            leaf ip { type string; }\n"
        "        }\n"
        "        choice b-kind {\n"
        "            case x { leaf x-val { type string; } }\n"
        "            case y { leaf y-val { type string; } }\n"
        "        }\n"
        "    }\n"
        /* a when on the augment itself guards everything inside it */
        "    augment \"/a:ifs/a:if\" {\n"
        "        when \"derived-from-or-self(a:type, 'a:ani')\";\n"
        "        container b-ani { leaf serial { type string; } }\n"
        "    }\n"
        "\n"
        /* the constraint lives in b, the data it reads lives in a */
        "    container b-top {\n"
        "        list b-chk {\n"
        "            key name;\n"
        "            leaf name { type string; }\n"
        "            leaf ifname { type leafref { path \"/a:ifs/a:if/a:name\"; } }\n"
        "            leaf need {\n"
        "                type string;\n"
        "                must \"derived-from-or-self(/a:ifs/a:if[a:name = current()/../ifname]/a:type, 'a:eth')\";\n"
        "            }\n"
        /* a first-pass reader in the same module that creates the default b-cfg */
        "            leaf hi {\n"
        "                when \"not(/a:ifs/a:if[a:name = current()/../ifname]/b:b-cfg/b:speed < 500)\";\n"
        "                type string;\n"
        "            }\n"
        "            leaf hi2 {\n"
        "                when \"not(/a:ifs/a:if[a:name = current()/../ifname]/b:b-cfg/b:m1-val)\";\n"
        "                type string;\n"
        "            }\n"
        "        }\n"
        "    }\n"
        "}";

static const char *schema_c =
        "module c {\n"
        "    namespace urn:tests:c;\n"
        "    prefix c;\n"
        "    yang-version 1.1;\n"
        "    import a { prefix a; }\n"
        "    import b { prefix b; }\n"
        "\n"
        "    container c-refs {\n"
        "        list c-ref {\n"
        "            key name;\n"
        "            leaf name { type string; }\n"
        "            leaf ifname { type leafref { path \"/a:ifs/a:if/a:name\"; } }\n"
        "            leaf addr-id {\n"
        "                type leafref { path \"/a:ifs/a:if[a:name = current()/../ifname]/b:b-addr/b:id\"; }\n"
        "            }\n"
        "            leaf fast {\n"
        "                type string;\n"
        "                must \"/a:ifs/a:if[a:name = current()/../ifname]/b:b-cfg/b:speed >= 1000\";\n"
        "            }\n"
        /* holds while the container is absent, fails once a default one with speed 100 shows up */
        "            leaf nolow {\n"
        "                type string;\n"
        "                must \"not(/a:ifs/a:if[a:name = current()/../ifname]/b:b-cfg/b:speed < 500)\";\n"
        "            }\n"
        /* fails once the default m1 case of the interface is replaced */
        "            leaf m1need {\n"
        "                type string;\n"
        "                must \"/a:ifs/a:if[a:name = current()/../ifname]/b:b-cfg/b:m1-val = 1\";\n"
        "            }\n"
        "            leaf nom1 {\n"
        "                type string;\n"
        "                must \"not(/a:ifs/a:if[a:name = current()/../ifname]/b:b-cfg/b:m1-val)\";\n"
        "            }\n"
        /* the first ip of the interface: a node that appears in front of it changes the value, so creating data
         * is not safe for this one, unlike the plain comparison */
        "            leaf ipfirst {\n"
        "                type string;\n"
        "                must \"contains(/a:ifs/a:if[a:name = current()/../ifname]/b:b-addr/b:ip, '10.')\";\n"
        "            }\n"
        "            leaf idmath {\n"
        "                type string;\n"
        "                must \"/a:ifs/a:if[a:name = current()/../ifname]/b:b-addr/b:id + 0 > 1\";\n"
        "            }\n"
        "            leaf ipany {\n"
        "                type string;\n"
        "                must \"/a:ifs/a:if[a:name = current()/../ifname]/b:b-addr/b:ip = '10.0.0.1'\";\n"
        "            }\n"
        /* a first-pass reader of data that module b autodeletes */
        "            leaf cs { type leafref { path \"/a:ifs/a:if/b:b-cfg/b:speed\"; } }\n"
        "        }\n"
        "    }\n"
        "}";

static const char *aug_xml =
        "<ifs xmlns=\"urn:tests:a\">"
        "  <if><name>e1</name><alias>a1</alias><type>eth</type>"
        "    <b-cfg xmlns=\"urn:tests:b\"><speed>1000</speed><mtu>1500</mtu><peer>n1</peer></b-cfg>"
        "    <b-addr xmlns=\"urn:tests:b\"><id>1</id><ip>10.0.0.1</ip></b-addr>"
        "    <b-addr xmlns=\"urn:tests:b\"><id>2</id><ip>10.0.0.2</ip></b-addr>"
        "    <x-val xmlns=\"urn:tests:b\">v</x-val>"
        "  </if>"
        "  <if><name>n1</name><alias>a2</alias><type>ani</type><ani-id>7</ani-id>"
        "    <b-ani xmlns=\"urn:tests:b\"><serial>S1</serial></b-ani>"
        "  </if>"
        "  <if><name>x1</name><alias>a3</alias><type>eth</type></if>"
        "</ifs>"
        "<b-top xmlns=\"urn:tests:b\">"
        "  <b-chk><name>k1</name><ifname>e1</ifname><need>x</need></b-chk>"
        "  <b-chk><name>k2</name><ifname>x1</ifname><need>y</need></b-chk>"
        "</b-top>"
        "<c-refs xmlns=\"urn:tests:c\">"
        "  <c-ref><name>r1</name><ifname>e1</ifname><addr-id>1</addr-id><fast>y</fast></c-ref>"
        "</c-refs>";

static void
aug_setup(void **state)
{
    UTEST_ADD_MODULE(schema_a, LYS_IN_YANG, NULL, NULL);
    UTEST_ADD_MODULE(schema_b, LYS_IN_YANG, NULL, NULL);
    UTEST_ADD_MODULE(schema_c, LYS_IN_YANG, NULL, NULL);
    check_mods[0] = "a";
    check_mods[1] = "b";
    check_mods[2] = "c";
    check_mods[3] = NULL;
}

static void
aug_done(void)
{
    check_mods[1] = NULL;
}

/**
 * @brief Apply several edits (path, value; NULL path ends the list; a path with the '-' marker deletes it) to a
 * duplicate of @p before, without validating.
 */
static struct lyd_node *
aug_apply(void **state, const struct lyd_node *before, const char *const *edits)
{
    struct lyd_node *after = NULL;
    uint32_t i;

    assert_int_equal(LY_SUCCESS, lyd_dup_siblings(before, NULL, LYD_DUP_RECURSIVE | LYD_DUP_WITH_FLAGS, &after));
    for (i = 0; edits[i]; i += 2) {
        if (edits[i][0] == '-') {
            drop_node(&after, edits[i] + 1);
        } else {
            assert_int_equal(LY_SUCCESS, lyd_new_path(after, UTEST_LYCTX, edits[i], edits[i + 1],
                    LYD_NEW_PATH_UPDATE, NULL));
        }
    }
    return after;
}

/**
 * @brief Build a valid starting tree from @p before and some edits.
 */
static struct lyd_node *
aug_start(void **state, const struct lyd_node *before, const char *const *edits)
{
    struct lyd_node *start;

    start = aug_apply(state, before, edits);
    assert_int_equal(LY_SUCCESS, lyd_validate_all(&start, NULL, LYD_VALIDATE_PRESENT, NULL));
    return start;
}

/**
 * @brief Apply several edits at once (see aug_apply()) to a duplicate of @p before and check the validators agree.
 */
static void
aug_check_multi(void **state, const struct lyd_node *before, const char *const *edits, LY_ERR expected)
{
    struct lyd_node *after;
    LY_ERR rc;

    after = aug_apply(state, before, edits);
    check_same(state, before, after, 0, &rc);
    assert_int_equal(expected, rc);
    lyd_free_siblings(after);
}

static void
test_aug_add(void **state)
{
    struct lyd_node *before;

    aug_setup(state);
    before = parse_valid(state, aug_xml);

    /* a whole new target instance, the augment when is true so a default container appears */
    check_edit(state, before, "/a:ifs/if[name='e2']/type", "a:eth", LY_SUCCESS);
    check_edit(state, before, "/a:ifs/if[name='n2']/type", "a:ani", LY_SUCCESS);

    /* new augmented list instance, then the same ip again, which the unique of that list rejects */
    check_edit(state, before, "/a:ifs/if[name='e1']/b:b-addr[id='3']/ip", "10.0.0.3", LY_SUCCESS);
    check_edit(state, before, "/a:ifs/if[name='e1']/b:b-addr[id='3']/ip", "10.0.0.1", LY_EVALID);

    /* unique is per parent instance, the same ip under another interface is fine */
    check_edit(state, before, "/a:ifs/if[name='x1']/b:b-addr[id='1']/ip", "10.0.0.1", LY_SUCCESS);

    /* presence container with a mandatory leaf */
    check_edit(state, before, "/a:ifs/if[name='e1']/b:b-pc", NULL, LY_EVALID);
    check_edit(state, before, "/a:ifs/if[name='e1']/b:b-pc/mode", "m", LY_SUCCESS);

    /* a must inside the augment reads the sibling speed, from either side */
    check_edit(state, before, "/a:ifs/if[name='e1']/b:b-cfg/mtu", "500", LY_EVALID);
    check_edit(state, before, "/a:ifs/if[name='e1']/b:b-cfg/speed", "2000", LY_EVALID);
    check_edit(state, before, "/a:ifs/if[name='e1']/b:b-cfg/speed", "1200", LY_SUCCESS);
    /* below what c-ref/fast of another module needs */
    check_edit(state, before, "/a:ifs/if[name='e1']/b:b-cfg/speed", "900", LY_EVALID);

    /* leafref inside the augment */
    check_edit(state, before, "/a:ifs/if[name='e1']/b:b-cfg/peer", "x1", LY_SUCCESS);
    check_edit(state, before, "/a:ifs/if[name='e1']/b:b-cfg/peer", "nope", LY_EVALID);

    /* an augment guarded by its own when: a node under a false when is an error, a true one is fine */
    check_edit(state, before, "/a:ifs/if[name='x1']/b:b-ani/serial", "S", LY_EVALID);
    check_edit(state, before, "/a:ifs/if[name='n1']/b:b-ani/serial", "S2", LY_SUCCESS);

    /* choice: switching the case is a rewrite of the data, not an error */
    check_edit(state, before, "/a:ifs/if[name='e1']/b:y-val", "w", LY_SUCCESS);

    lyd_free_siblings(before);
    aug_done();
}

static void
test_aug_delete(void **state)
{
    struct lyd_node *before;

    aug_setup(state);
    before = parse_valid(state, aug_xml);

    check_delete(state, before, "/a:ifs/a:if[a:name='e1']/b:b-cfg/b:mtu", LY_SUCCESS);
    check_delete(state, before, "/a:ifs/a:if[a:name='e1']/b:b-cfg/b:peer", LY_SUCCESS);
    check_delete(state, before, "/a:ifs/a:if[a:name='e1']/b:x-val", LY_SUCCESS);
    check_delete(state, before, "/a:ifs/a:if[a:name='n1']/b:b-ani", LY_SUCCESS);

    /* the container is gone but its when still holds, so a default one comes back with speed 100
     * and the cross-module must of c-ref/fast needs 1000 */
    check_delete(state, before, "/a:ifs/a:if[a:name='e1']/b:b-cfg", LY_EVALID);

    /* an unreferenced list entry and a referenced one */
    check_delete(state, before, "/a:ifs/a:if[a:name='e1']/b:b-addr[b:id='2']", LY_SUCCESS);
    check_delete(state, before, "/a:ifs/a:if[a:name='e1']/b:b-addr[b:id='1']", LY_EVALID);

    /* deleting a target instance takes its augmented children along, but not the references to it */
    check_delete(state, before, "/a:ifs/a:if[a:name='e1']", LY_EVALID);
    check_delete(state, before, "/a:ifs/a:if[a:name='n1']", LY_EVALID);

    /* x1 is only read by a must of b-chk, which needs it to exist */
    check_delete(state, before, "/a:ifs/a:if[a:name='x1']", LY_EVALID);

    /* deleting the referrer as well makes it consistent again */
    {
        const char *edits[] = {"-/a:ifs/a:if[a:name='x1']", NULL, "-/b:b-top/b:b-chk[b:name='k2']", NULL, NULL};

        aug_check_multi(state, before, edits, LY_SUCCESS);
    }
    {
        const char *edits[] = {"-/a:ifs/a:if[a:name='e1']", NULL, "-/b:b-top/b:b-chk[b:name='k1']", NULL,
            "-/c:c-refs/c:c-ref[c:name='r1']", NULL, NULL};

        /* n1 no longer is a peer target because e1 holding the peer is gone */
        aug_check_multi(state, before, edits, LY_SUCCESS);
    }

    lyd_free_siblings(before);
    aug_done();
}

static void
test_aug_when_flip(void **state)
{
    struct lyd_node *before;

    aug_setup(state);
    before = parse_valid(state, aug_xml);

    /* the when of an existing augmented container turns false: error, both validators */
    check_edit(state, before, "/a:ifs/if[name='e1']/type", "a:ani", LY_EVALID);
    check_edit(state, before, "/a:ifs/if[name='n1']/type", "a:eth", LY_SUCCESS);

    /* x1 only has the implicit default b-cfg, which simply disappears, but the b-chk must reads its type */
    check_edit(state, before, "/a:ifs/if[name='x1']/type", "a:ani", LY_EVALID);

    {
        /* a consistent flip ani -> eth: everything guarded by the old type is removed in the same edit, the
         * default b-cfg must appear */
        const char *edits[] = {"-/a:ifs/a:if[a:name='n1']/b:b-ani", NULL, "-/a:ifs/a:if[a:name='n1']/a:ani-id", NULL,
            "/a:ifs/if[name='n1']/type", "a:eth", NULL, NULL};

        aug_check_multi(state, before, edits, LY_SUCCESS);
    }
    {
        /* the reverse flip eth -> ani on x1, with its referrer dropped */
        const char *edits[] = {"-/b:b-top/b:b-chk[b:name='k2']", NULL, "/a:ifs/if[name='x1']/type", "a:ani", NULL, NULL};

        aug_check_multi(state, before, edits, LY_SUCCESS);
    }

    lyd_free_siblings(before);
    aug_done();
}

static void
test_aug_cross_module(void **state)
{
    struct lyd_node *before;

    aug_setup(state);
    before = parse_valid(state, aug_xml);

    /* module a is the only one edited, the broken rule is in b */
    check_edit(state, before, "/a:ifs/if[name='x1']/type", "a:ani", LY_EVALID);

    /* module b is edited, the rule that reads it is in c */
    check_edit(state, before, "/b:b-top/b-chk[name='k3']/ifname", "e1", LY_SUCCESS);
    check_edit(state, before, "/b:b-top/b-chk[name='k3']/ifname", "n1", LY_SUCCESS);
    check_edit(state, before, "/c:c-refs/c-ref[name='r2']/ifname", "x1", LY_SUCCESS);

    /* c-ref/fast needs the speed of the augmented container in b */
    check_edit(state, before, "/a:ifs/if[name='e1']/b:b-cfg/speed", "500", LY_EVALID);
    check_edit(state, before, "/a:ifs/if[name='e1']/b:b-cfg/speed", "1500", LY_SUCCESS);
    check_edit(state, before, "/c:c-refs/c-ref[name='r1']/addr-id", "2", LY_SUCCESS);
    check_edit(state, before, "/c:c-refs/c-ref[name='r1']/addr-id", "9", LY_EVALID);

    lyd_free_siblings(before);
    aug_done();
}

/**
 * @brief A when that turns false removes a node the edit never mentions, and a rule of another module reads it.
 *
 * The flip of e1 deletes the explicit b-cfg through the when of b (the diff only holds the type), and the must of
 * c-ref/fast reads b-cfg/speed. In the plain base data the must of b-top/b-chk[k1] reads the type and fails first,
 * so k1 is dropped here to leave the must of c-ref as the only rule that can catch it.
 */
static void
test_aug_when_cascade(void **state)
{
    struct lyd_node *before;
    const char *edits[] = {"-/b:b-top/b:b-chk[b:name='k1']", NULL, "/a:ifs/if[name='e1']/type", "a:ani", NULL, NULL};

    aug_setup(state);
    before = parse_valid(state, aug_xml);
    aug_check_multi(state, before, edits, LY_EVALID);
    lyd_free_siblings(before);
    aug_done();
}

/**
 * @brief The same cascade caught by a leafref of another instance of the same module data.
 *
 * Leafrefs are resolved in the first pass, so merging the validation diff for the final pass does not help, the
 * pass that autodeletes has to notice it itself.
 */
static void
test_aug_when_cascade_leafref(void **state)
{
    struct lyd_node *before;
    const char *setup[] = {"-/b:b-top/b:b-chk[b:name='k1']", NULL, "-/c:c-refs/c:c-ref[c:name='r1']", NULL,
        "/a:ifs/if[name='x1']/b:peer-speed", "1000", NULL, NULL};
    const char *flip[] = {"/a:ifs/if[name='e1']/type", "a:ani", NULL, NULL};
    struct lyd_node *start = NULL;
    uint32_t i;

    aug_setup(state);
    before = parse_valid(state, aug_xml);

    /* the starting point is valid: x1 points at the speed of e1 */
    assert_int_equal(LY_SUCCESS, lyd_dup_siblings(before, NULL, LYD_DUP_RECURSIVE | LYD_DUP_WITH_FLAGS, &start));
    for (i = 0; setup[i]; i += 2) {
        if (setup[i][0] == '-') {
            drop_node(&start, setup[i] + 1);
        } else {
            assert_int_equal(LY_SUCCESS, lyd_new_path(start, UTEST_LYCTX, setup[i], setup[i + 1],
                    LYD_NEW_PATH_UPDATE, NULL));
        }
    }
    assert_int_equal(LY_SUCCESS, lyd_validate_all(&start, NULL, LYD_VALIDATE_PRESENT, NULL));

    /* the flip removes b-cfg of e1 and leaves the leafref of x1 dangling */
    aug_check_multi(state, start, flip, LY_EVALID);

    lyd_free_siblings(start);
    lyd_free_siblings(before);
    aug_done();
}

/**
 * @brief A when that turns true makes validation create a default node, and a rule of another module reads it.
 *
 * Mirror of the cascade tests: the flip of n1 to eth makes b-cfg appear with the default speed 100 (the diff only
 * holds the type change and the removal of the ani-only data), and the must of c-ref/nolow, which was true while
 * b-cfg was absent, reads that speed.
 *
 * The must is only checked in the final pass, by when the validation diff of b has been merged into the edit diff,
 * so the created speed counts as touched. The same flip is then read by a when of b itself, which runs in the first
 * pass of b and only sees the edit diff.
 */
static void
test_aug_when_create(void **state)
{
    struct lyd_node *before, *start;
    const char *setup[] = {"-/b:b-top/b:b-chk[b:name='k1']", NULL,
        "/c:c-refs/c-ref[name='r3']/ifname", "n1", "/c:c-refs/c-ref[name='r3']/nolow", "y", NULL, NULL};
    const char *setup_when[] = {"-/b:b-top/b:b-chk[b:name='k1']", NULL,
        "/b:b-top/b-chk[name='k3']/ifname", "n1", "/b:b-top/b-chk[name='k3']/hi", "y", NULL, NULL};
    const char *flip[] = {"-/a:ifs/a:if[a:name='n1']/b:b-ani", NULL, "-/a:ifs/a:if[a:name='n1']/a:ani-id", NULL,
        "/a:ifs/if[name='n1']/type", "a:eth", NULL, NULL};
    uint64_t fb_before = 0, fb_after = 0;

    aug_setup(state);
    before = parse_valid(state, aug_xml);

    start = aug_start(state, before, setup);
    lyd_validate_incr_stats(UTEST_LYCTX, NULL, &fb_before);
    aug_check_multi(state, start, flip, LY_EVALID);
    lyd_validate_incr_stats(UTEST_LYCTX, NULL, &fb_after);
    assert_int_equal(fb_before, fb_after);
    lyd_free_siblings(start);

    /* full validation autodeletes k3/hi, check_same() compares the trees */
    start = aug_start(state, before, setup_when);
    aug_check_multi(state, start, flip, LY_SUCCESS);
    lyd_free_siblings(start);

    lyd_free_siblings(before);
    aug_done();
}

/**
 * @brief The validation replaces data the edit did not name: a default comes back for a deleted value, or a default
 * case is replaced by the case the edit created.
 */
static void
test_aug_dflt_replace(void **state)
{
    struct lyd_node *before, *start;
    const char *del_speed[] = {"-/a:ifs/a:if[a:name='e1']/b:b-cfg/b:speed", NULL, NULL, NULL};
    const char *setup_when[] = {"-/b:b-top/b:b-chk[b:name='k1']", NULL, "-/c:c-refs/c:c-ref[c:name='r1']", NULL,
        "/b:b-top/b-chk[name='k4']/ifname", "e1", "/b:b-top/b-chk[name='k4']/hi", "y", NULL, NULL};
    const char *setup_m1x[] = {"/c:c-refs/c-ref[name='r4']/ifname", "x1", "/c:c-refs/c-ref[name='r4']/m1need", "y",
        "/a:ifs/if[name='x1']/b:b-cfg/speed", "200", NULL, NULL};
    const char *to_m2_e1[] = {"/a:ifs/if[name='e1']/b:b-cfg/m2-val", "5", NULL, NULL};
    const char *to_m2_x1[] = {"/a:ifs/if[name='x1']/b:b-cfg/m2-val", "5", NULL, NULL};
    const char *to_m1[] = {"/a:ifs/if[name='e1']/b:b-cfg/m1-val", "1", NULL, NULL};

    aug_setup(state);
    before = parse_valid(state, aug_xml);

    /* the default 100 replaces 1000, below what c-ref/fast of r1 needs */
    aug_check_multi(state, before, del_speed, LY_EVALID);

    /* the same replace read by a when of b, full validation autodeletes k4/hi */
    start = aug_start(state, before, setup_when);
    aug_check_multi(state, start, del_speed, LY_SUCCESS);
    lyd_free_siblings(start);

    /* m2 replaces the default m1 case: nobody reads it on e1, c-ref/m1need of r4 reads it on x1, whose b-cfg is
     * explicit here */
    aug_check_multi(state, before, to_m2_e1, LY_SUCCESS);
    start = aug_start(state, before, setup_m1x);
    aug_check_multi(state, start, to_m2_x1, LY_EVALID);
    aug_check_multi(state, start, to_m2_e1, LY_SUCCESS);
    lyd_free_siblings(start);

    /* an explicit value equal to the default replaces the default node */
    aug_check_multi(state, before, to_m1, LY_SUCCESS);

    lyd_free_siblings(before);
    aug_done();
}

/**
 * @brief A rule that reads the first node of a node-set is not safe to skip on creation, one that only asks
 * whether some node matches is.
 */
static void
test_aug_first_node_func(void **state)
{
    const struct lys_module *mod;
    const struct lyd_val_dep_index *index;
    const struct lyd_val_constraint *cons;
    uint32_t i, seen = 0;

    aug_setup(state);

    mod = ly_ctx_get_module_implemented(UTEST_LYCTX, "c");
    assert_int_equal(LY_SUCCESS, lyd_val_deps_get(mod, &index));
    for (i = 0; i < index->constraint_count; ++i) {
        cons = &index->constraints[i];
        if (!strcmp(cons->snode->name, "ipfirst") || !strcmp(cons->snode->name, "idmath")) {
            assert_false(cons->creation_safe);
            ++seen;
        } else if (!strcmp(cons->snode->name, "ipany")) {
            assert_true(cons->creation_safe);
            ++seen;
        }
    }
    assert_int_equal(3, seen);

    aug_done();
}

#define DEEP_LEVELS 70

/**
 * @brief A node deeper than the ancestor chain of the diff lookup used to be taken for a deleted top-level
 * instance, so nothing above it was revalidated.
 */
static void
test_aug_deep_delete(void **state)
{
    char schema[8192] = "module deep {\n    namespace urn:tests:deep;\n    prefix deep;\n    yang-version 1.1;\n";
    char path[4096] = "", xml[4096] = "", del[4096] = "-", tmp[64];
    struct lyd_node *before, *after;
    const char *edit[] = {del, NULL, NULL, NULL};
    uint64_t fb_before = 0, fb_after = 0;
    LY_ERR rc;
    int i, entry;

    /* only list instances can be left out of a scoped pass, so the deep node sits below one */
    strcat(schema, "list l {\nkey k;\nleaf k { type string; }\n");
    for (i = 1; i < DEEP_LEVELS; ++i) {
        snprintf(tmp, sizeof tmp, "container c%d {\n", i);
        strcat(schema, tmp);
    }
    strcat(schema, "leaf x { type string; }\nleaf m { type string; mandatory true; }\n");
    for (i = 1; i < DEEP_LEVELS; ++i) {
        strcat(schema, "}\n");
    }
    strcat(schema, "}\n}\n");

    UTEST_ADD_MODULE(schema, LYS_IN_YANG, NULL, NULL);
    check_mods[0] = "deep";
    check_mods[1] = NULL;

    strcpy(path, "/deep:l[k='1']");
    for (i = 1; i < DEEP_LEVELS; ++i) {
        snprintf(tmp, sizeof tmp, "/c%d", i);
        strcat(path, tmp);
    }
    for (entry = 0; entry < 2; ++entry) {
        strcat(xml, entry ? "<l xmlns=\"urn:tests:deep\"><k>2</k>" : "<l xmlns=\"urn:tests:deep\"><k>1</k>");
        for (i = 1; i < DEEP_LEVELS; ++i) {
            snprintf(tmp, sizeof tmp, "<c%d>", i);
            strcat(xml, tmp);
        }
        strcat(xml, "<x>1</x><m>2</m>");
        for (i = DEEP_LEVELS - 1; i >= 1; --i) {
            snprintf(tmp, sizeof tmp, "</c%d>", i);
            strcat(xml, tmp);
        }
        strcat(xml, "</l>");
    }
    strcat(del, path);
    strcat(del, "/m");

    before = parse_valid(state, xml);
    after = aug_apply(state, before, edit);
    lyd_validate_incr_stats(UTEST_LYCTX, NULL, &fb_before);
    check_same(state, before, after, 1, &rc);
    lyd_validate_incr_stats(UTEST_LYCTX, NULL, &fb_after);
    /* the mandatory leaf is gone, full validation says so and the incremental one has to as well, without
     * giving up: the lookup has to find the deleted node's parent */
    assert_int_equal(LY_EVALID, rc);
    assert_int_equal(fb_before, fb_after);

    lyd_free_siblings(after);
    lyd_free_siblings(before);
    check_mods[0] = "a";
}

/**
 * @brief Probe: the edit deletes the explicit case, so the validation brings the default case back.
 */
static void
test_aug_dflt_case_back(void **state)
{
    struct lyd_node *before, *start;
    const char *setup_must[] = {"/a:ifs/if[name='e1']/b:b-cfg/m2-val", "5",
        "/c:c-refs/c-ref[name='r7']/ifname", "e1", "/c:c-refs/c-ref[name='r7']/nom1", "y", NULL, NULL};
    const char *setup_when[] = {"/a:ifs/if[name='e1']/b:b-cfg/m2-val", "5",
        "/b:b-top/b-chk[name='k5']/ifname", "e1", "/b:b-top/b-chk[name='k5']/hi2", "y", NULL, NULL};
    const char *del_m2[] = {"-/a:ifs/a:if[a:name='e1']/b:b-cfg/b:m2-val", NULL, NULL, NULL};

    aug_setup(state);
    before = parse_valid(state, aug_xml);

    start = aug_start(state, before, setup_must);
    aug_check_multi(state, start, del_m2, LY_EVALID);
    lyd_free_siblings(start);

    start = aug_start(state, before, setup_when);
    aug_check_multi(state, start, del_m2, LY_SUCCESS);
    lyd_free_siblings(start);

    lyd_free_siblings(before);
    aug_done();
}

/**
 * @brief The default case is replaced inside a container that only existed as a default.
 *
 * The edit diff does not see default nodes, so it calls the whole b-cfg of x1 created, and the m1-val default that
 * the validation of b then deletes merges away into that create. The must of c-ref/m1need is creation-safe, yet
 * the created b-cfg replaced a default one, so it must not be skipped. The same holds for an explicit m1-val the
 * diff calls created while it replaced the default value.
 */
static void
test_aug_dflt_case_in_dflt(void **state)
{
    struct lyd_node *before, *start;
    const char *setup[] = {"/c:c-refs/c-ref[name='r4']/ifname", "x1", "/c:c-refs/c-ref[name='r4']/m1need", "y",
        NULL, NULL};
    const char *setup_x1[] = {"/c:c-refs/c-ref[name='r4']/ifname", "x1", "/c:c-refs/c-ref[name='r4']/m1need", "y",
        "/a:ifs/if[name='x1']/b:b-cfg/speed", "200", NULL, NULL};
    const char *to_m2[] = {"/a:ifs/if[name='x1']/b:b-cfg/m2-val", "5", NULL, NULL};
    const char *m1_2[] = {"/a:ifs/if[name='x1']/b:b-cfg/m1-val", "2", NULL, NULL};

    aug_setup(state);
    before = parse_valid(state, aug_xml);
    start = aug_start(state, before, setup);

    aug_check_multi(state, start, to_m2, LY_EVALID);
    aug_check_multi(state, start, m1_2, LY_EVALID);
    lyd_free_siblings(start);

    /* b-cfg is explicit, only the leaf replaces its default */
    start = aug_start(state, before, setup_x1);
    aug_check_multi(state, start, m1_2, LY_EVALID);

    lyd_free_siblings(start);
    lyd_free_siblings(before);
    aug_done();
}

/**
 * @brief Validate the same edit with the modules in several orders.
 *
 * Within one order the incremental run has to match the per-module full run, which check_same() asserts. Resolving
 * every module at once with lyd_validate_all() is printed alongside: a different verdict there is a property of
 * per-module validation itself, which sysrepo does in its own module order, not of the incremental path.
 */
static void
aug_check_orders(void **state, const struct lyd_node *before, const char *const *edits, LY_ERR expected_abc)
{
    const char *orders[][3] = {{"a", "b", "c"}, {"c", "b", "a"}, {"b", "c", "a"}, {"c", "a", "b"}};
    struct lyd_node *after, *all;
    LY_ERR rc, rc_all;
    uint32_t o;

    after = aug_apply(state, before, edits);

    assert_int_equal(LY_SUCCESS, lyd_dup_siblings(after, NULL, LYD_DUP_RECURSIVE | LYD_DUP_WITH_FLAGS, &all));
    rc_all = lyd_validate_all(&all, NULL, 0, NULL);
    ly_err_clean((struct ly_ctx *)UTEST_LYCTX, NULL);
    lyd_free_siblings(all);

    for (o = 0; o < sizeof orders / sizeof *orders; ++o) {
        check_mods[0] = orders[o][0];
        check_mods[1] = orders[o][1];
        check_mods[2] = orders[o][2];
        check_same(state, before, after, 0, &rc);
        if (!o) {
            assert_int_equal(expected_abc, rc);
        }
        if (rc != rc_all) {
            print_message("[  MSG     ] order %s,%s,%s: per-module %d, all modules at once %d\n", orders[o][0],
                    orders[o][1], orders[o][2], rc, rc_all);
        }
    }

    check_mods[0] = "a";
    check_mods[1] = "b";
    check_mods[2] = "c";
    lyd_free_siblings(after);
}

/**
 * @brief Module b autodeletes data that a leafref of module c reads, in every module order.
 */
static void
test_aug_module_order(void **state)
{
    struct lyd_node *before, *start;
    const char *setup[] = {"-/b:b-top/b:b-chk[b:name='k1']", NULL, "-/c:c-refs/c:c-ref[c:name='r1']", NULL,
        "/c:c-refs/c-ref[name='r5']/cs", "1000", NULL, NULL};
    const char *flip[] = {"/a:ifs/if[name='e1']/type", "a:ani", NULL, NULL};
    const char *speed[] = {"/a:ifs/if[name='e1']/b:b-cfg/speed", "1200", NULL, NULL};

    aug_setup(state);
    before = parse_valid(state, aug_xml);
    start = aug_start(state, before, setup);

    /* the flip removes b-cfg of e1 through the when of b, the value 1000 of c-ref/cs is gone */
    aug_check_orders(state, start, flip, LY_EVALID);

    /* the edit itself changes the value, no autodeletion involved */
    aug_check_orders(state, start, speed, LY_EVALID);

    lyd_free_siblings(start);
    lyd_free_siblings(before);
    aug_done();
}

/* a configuration instance-identifier names its target in the value, beyond what the dependency index describes */
static const char *schema_d =
        "module d {\n"
        "    namespace urn:tests:d;\n"
        "    prefix d;\n"
        "    yang-version 1.1;\n"
        "\n"
        "    container d-refs {\n"
        "        list d-ref {\n"
        "            key name;\n"
        "            leaf name { type string; }\n"
        /* require-instance is the default, the target has to exist like for a leafref */
        "            leaf iid { type instance-identifier; }\n"
        "            leaf loose { type instance-identifier { require-instance false; } }\n"
        "        }\n"
        "    }\n"
        "    container d-state {\n"
        "        config false;\n"
        "        leaf iid { type instance-identifier; }\n"
        "    }\n"
        "}";

/* the same, only with instance-identifiers that are never checked against configuration data */
static const char *schema_e =
        "module e {\n"
        "    namespace urn:tests:e;\n"
        "    prefix e;\n"
        "    yang-version 1.1;\n"
        "\n"
        "    container e-refs {\n"
        "        leaf loose { type instance-identifier { require-instance false; } }\n"
        "    }\n"
        "    container e-state {\n"
        "        config false;\n"
        "        leaf iid { type instance-identifier; }\n"
        "    }\n"
        "}";

/**
 * @brief An instance-identifier of module d points at data of module a that the edit deletes.
 *
 * Module d can only be validated in full; module e, whose instance-identifiers are not checked against
 * configuration, keeps the incremental path.
 */
static void
test_aug_instance_identifier(void **state)
{
    struct lyd_node *before, *start, *after;
    const struct lys_module *mod;
    const struct lyd_val_dep_index *index;
    const char *setup[] = {"/d:d-refs/d-ref[name='r6']/iid", "/a:ifs/if[name='x1']/alias", NULL, NULL};
    const char *del_alias[] = {"-/a:ifs/a:if[a:name='x1']/a:alias", NULL, NULL, NULL};
    const char *set_alias[] = {"/a:ifs/if[name='x1']/alias", "a9", NULL, NULL};
    uint64_t fb_before = 0, fb_after = 0;
    LY_ERR rc;

    aug_setup(state);
    UTEST_ADD_MODULE(schema_d, LYS_IN_YANG, NULL, NULL);
    UTEST_ADD_MODULE(schema_e, LYS_IN_YANG, NULL, NULL);

    mod = ly_ctx_get_module_implemented(UTEST_LYCTX, "d");
    assert_int_equal(LY_SUCCESS, lyd_val_deps_get(mod, &index));
    assert_true(index->unanalysable);
    mod = ly_ctx_get_module_implemented(UTEST_LYCTX, "e");
    assert_int_equal(LY_SUCCESS, lyd_val_deps_get(mod, &index));
    assert_false(index->unanalysable);

    before = parse_valid(state, aug_xml);
    start = aug_start(state, before, setup);
    check_mods[3] = "d";

    /* the target goes: full validation rejects, and so does module d through its fallback */
    after = aug_apply(state, start, del_alias);
    lyd_validate_incr_stats(UTEST_LYCTX, NULL, &fb_before);
    check_same(state, start, after, 1, &rc);
    lyd_validate_incr_stats(UTEST_LYCTX, NULL, &fb_after);
    /* a missing instance-identifier target is reported as not found */
    assert_int_equal(LY_ENOTFOUND, rc);
    assert_true(fb_after > fb_before);
    lyd_free_siblings(after);

    /* any other edit is accepted the same way */
    after = aug_apply(state, start, set_alias);
    check_same(state, start, after, 1, &rc);
    assert_int_equal(LY_SUCCESS, rc);
    lyd_free_siblings(after);

    check_mods[3] = NULL;
    lyd_free_siblings(start);
    lyd_free_siblings(before);
    aug_done();
}

static void
test_aug_random_edits(void **state)
{
    struct lyd_node *before = NULL, *after = NULL;
    const char *ifs[] = {"e1", "n1", "x1"};
    const char *types[] = {"a:eth", "a:ani"};
    char path[192], value[32];
    uint32_t seed, i, step;
    LY_ERR rc;

    aug_setup(state);

    for (seed = 1; seed <= 60; ++seed) {
        srand(seed);
        before = parse_valid(state, aug_xml);

        for (step = 0; step < 5; ++step) {
            assert_int_equal(LY_SUCCESS, lyd_dup_siblings(before, NULL, LYD_DUP_RECURSIVE | LYD_DUP_WITH_FLAGS, &after));

            switch (rand() % 12) {
            case 0:
                sprintf(path, "/a:ifs/if[name='%s']/type", ifs[rand() % 3]);
                assert_int_equal(LY_SUCCESS, lyd_new_path(after, UTEST_LYCTX, path, types[rand() % 2],
                        LYD_NEW_PATH_UPDATE, NULL));
                break;
            case 1:
                sprintf(path, "/a:ifs/if[name='%s']/b:b-cfg/speed", ifs[rand() % 3]);
                sprintf(value, "%d", 500 * (1 + rand() % 4));
                assert_int_equal(LY_SUCCESS, lyd_new_path(after, UTEST_LYCTX, path, value, LYD_NEW_PATH_UPDATE, NULL));
                break;
            case 2:
                sprintf(path, "/a:ifs/if[name='%s']/b:b-cfg/mtu", ifs[rand() % 3]);
                sprintf(value, "%d", 500 * (1 + rand() % 4));
                assert_int_equal(LY_SUCCESS, lyd_new_path(after, UTEST_LYCTX, path, value, LYD_NEW_PATH_UPDATE, NULL));
                break;
            case 3:
                sprintf(path, "/a:ifs/if[name='%s']/b:b-addr[id='%d']/ip", ifs[rand() % 3], 1 + rand() % 3);
                sprintf(value, "10.0.0.%d", 1 + rand() % 3);
                assert_int_equal(LY_SUCCESS, lyd_new_path(after, UTEST_LYCTX, path, value, LYD_NEW_PATH_UPDATE, NULL));
                break;
            case 4:
                sprintf(path, "/b:b-top/b-chk[name='k%d']/ifname", 1 + rand() % 3);
                assert_int_equal(LY_SUCCESS, lyd_new_path(after, UTEST_LYCTX, path, ifs[rand() % 3],
                        LYD_NEW_PATH_UPDATE, NULL));
                break;
            case 5:
                sprintf(path, "/b:b-top/b-chk[name='k%d']/need", 1 + rand() % 3);
                assert_int_equal(LY_SUCCESS, lyd_new_path(after, UTEST_LYCTX, path, "z", LYD_NEW_PATH_UPDATE, NULL));
                break;
            case 6:
                sprintf(path, "/c:c-refs/c-ref[name='r%d']/ifname", 1 + rand() % 2);
                assert_int_equal(LY_SUCCESS, lyd_new_path(after, UTEST_LYCTX, path, ifs[rand() % 3],
                        LYD_NEW_PATH_UPDATE, NULL));
                break;
            case 7:
                sprintf(path, "/c:c-refs/c-ref[name='r%d']/addr-id", 1 + rand() % 2);
                sprintf(value, "%d", 1 + rand() % 3);
                assert_int_equal(LY_SUCCESS, lyd_new_path(after, UTEST_LYCTX, path, value, LYD_NEW_PATH_UPDATE, NULL));
                break;
            case 8:
                sprintf(path, "/c:c-refs/c-ref[name='r%d']/fast", 1 + rand() % 2);
                assert_int_equal(LY_SUCCESS, lyd_new_path(after, UTEST_LYCTX, path, "y", LYD_NEW_PATH_UPDATE, NULL));
                break;
            default: {
                struct ly_set *set = NULL;

                switch (rand() % 6) {
                case 0:
                    sprintf(path, "/a:ifs/a:if[a:name='%s']", ifs[rand() % 3]);
                    break;
                case 1:
                    sprintf(path, "/a:ifs/a:if[a:name='%s']/b:b-cfg", ifs[rand() % 3]);
                    break;
                case 2:
                    sprintf(path, "/a:ifs/a:if[a:name='%s']/b:b-addr", ifs[rand() % 3]);
                    break;
                case 3:
                    sprintf(path, "/b:b-top/b:b-chk[b:name='k%d']", 1 + rand() % 3);
                    break;
                case 4:
                    sprintf(path, "/c:c-refs/c:c-ref[c:name='r%d']", 1 + rand() % 2);
                    break;
                default:
                    sprintf(path, "/a:ifs/a:if[a:name='%s']/b:b-ani", ifs[rand() % 3]);
                    break;
                }
                assert_int_equal(LY_SUCCESS, lyd_find_xpath(after, path, &set));
                for (i = 0; i < set->count; ++i) {
                    if (set->dnodes[i] == after) {
                        after = after->next;
                    }
                    lyd_free_tree(set->dnodes[i]);
                }
                ly_set_free(set, NULL);
                break;
            }
            }

            if (!after) {
                break;
            }
            if (!step) {
                edit_log[0] = '\0';
            }
            snprintf(edit_log + strlen(edit_log), sizeof edit_log - strlen(edit_log), "seed %u step %u: %s = %s\n", seed,
                    step, path, value);
            check_same(state, before, after, 1, &rc);

            if (rc) {
                lyd_free_siblings(after);
                after = NULL;
                continue;
            }

            settle(state, &after);
            lyd_free_siblings(before);
            before = after;
            after = NULL;
        }

        lyd_free_siblings(before);
        before = NULL;
    }

    aug_done();
}

/**
 * @brief The dependency index of a module is built on first use. A module loaded afterwards can augment it with
 * constraints the index has never seen, so the index has to follow the schema, otherwise the incremental validation
 * accepts an edit that the full one rejects.
 */
static void
test_schema_change(void **state)
{
    struct lyd_node *before;

    UTEST_ADD_MODULE(schema_a, LYS_IN_YANG, NULL, NULL);

    /* the first incremental validation builds the dependency index of module a */
    before = parse_valid(state, "<ifs xmlns=\"urn:tests:a\"><if><name>e1</name><alias>a1</alias><type>eth</type>"
            "</if></ifs>");
    check_edit(state, before, "/a:ifs/if[name='e1']/alias", "a9", LY_SUCCESS);
    lyd_free_siblings(before);

    /* module b adds a leafref into the list of module a that reads the speed of the other instances, so an edit of
     * one interface can break another one */
    UTEST_ADD_MODULE(schema_b, LYS_IN_YANG, NULL, NULL);
    check_mods[1] = "b";

    before = parse_valid(state, "<ifs xmlns=\"urn:tests:a\">"
            "<if><name>e1</name><alias>a1</alias><type>eth</type><b-cfg xmlns=\"urn:tests:b\"><speed>1000</speed>"
            "</b-cfg></if>"
            "<if><name>e2</name><alias>a2</alias><type>eth</type><peer-speed xmlns=\"urn:tests:b\">1000</peer-speed>"
            "</if></ifs>");

    /* e2 refers to the speed of e1, which no longer exists after the edit */
    check_edit(state, before, "/a:ifs/if[name='e1']/b:b-cfg/speed", "1001", LY_EVALID);
    check_edit(state, before, "/a:ifs/if[name='e2']/alias", "a9", LY_SUCCESS);

    lyd_free_siblings(before);
    aug_done();
}

/*
 * Delete coverage. A deletion breaks something in one of three ways: a rule elsewhere reads the deleted data (a
 * leafref, a must or a when, in the same or in another module), a rule of the surviving structure no longer holds
 * (min-elements, mandatory, a choice, a default, an emptied container), or the shape of the edit itself hides the
 * delete (several nodes at once, a delete next to a create, a whole top-level instance, module order). Module dl
 * holds every kind of reader and structure once, module dm reads and augments dl from outside.
 */
static const char *schema_dl =
        "module dl {\n"
        "    namespace urn:tests:dl;\n"
        "    prefix dl;\n"
        "    yang-version 1.1;\n"
        "\n"
        "    container top {\n"
        /* the data the readers look at */
        "        list item {\n"
        "            key name;\n"
        "            leaf name { type string; }\n"
        "            leaf val { type string; }\n"
        "            leaf dd { type string; default \"d\"; }\n"
        "        }\n"
        "        leaf-list tag { type string; }\n"
        "        leaf-list num { type uint32; }\n"
        "        list ou {\n"
        "            ordered-by user;\n"
        "            key name;\n"
        "            leaf name { type string; }\n"
        "        }\n"
        "        container inner {\n"
        "            leaf a { type string; }\n"
        "            list x { key name; leaf name { type string; } leaf chk { type string; must \"count(../../x) >= 2\"; } }\n"
        "        }\n"
        "        leaf-list dtag { type string; default \"d1\"; }\n"
        "        list pos { key name; leaf name { type string; }\n"
        "            leaf pp { type string; must \"count(../preceding-sibling::pos) >= 1\"; } }\n"
        "        list grp {\n"
        "            key name;\n"
        "            leaf name { type string; }\n"
        "            list mem { key name; leaf name { type string; } }\n"
        "            leaf need { type string; must \"count(../mem) >= 2\"; }\n"
        "            leaf xr { type string; must \"count(../../grp/mem) >= 3\"; }\n"
        "            leaf want { type string; }\n"
        "            leaf other { type string; }\n"
        "            leaf lv { type string; }\n"
        "            leaf nx { type string; must \"not(../../grp[name = current()/../other]/mem[name = current()/../want])\"; }\n"
        "            leaf nc { type string; must \"count(../../grp[name = current()/../other]/mem[name = current()/../want]) = 0\"; }\n"
        "            leaf nf { type string; must \"contains(../../grp[name = 'g2']/lv, 'ok')\"; }\n"
        "            leaf mv { type string; must \"../../grp[name = 'g2']/lv = 'ok'\"; }\n"
        "            leaf wn { type string; when \"not(../../grp[name = current()/../other]/mem[name = current()/../want])\"; }\n"
        /* climbs on after a predicate that compares, out of the grp instance */
        "            container pc { leaf np { type string; must \"count(../../mem[name = 'x']/../../grp[name = "
        "current()/../../other]/mem[name = current()/../../want]) = 0\"; } }\n"
        "        }\n"
        "        list tpl {\n"
        "            key name;\n"
        "            leaf name { type string; }\n"
        "            list comp { key name; leaf name { type string; } leaf cls { type string; } }\n"
        "            list ifc {\n"
        "                key name;\n"
        "                leaf name { type string; }\n"
        "                leaf hw { type string; must \"../../comp[name = current()]/cls = 'ok'\"; }\n"
        "            }\n"
        "        }\n"
        "        list kr {\n"
        "            key k;\n"
        "            leaf k { type leafref { path \"../../item/name\"; } }\n"
        "        }\n"
        "        list wr {\n"
        "            key name;\n"
        "            leaf name { type string; }\n"
        "            leaf wref { type leafref { path \"../../r/w-on\"; } }\n"
        "        }\n"
        /* a when on a case, and a leafref into the case */
        "        choice wc {\n"
        "            case wcase {\n"
        "                when \"item[name = 'gate']\";\n"
        "                leaf wc-v { type string; }\n"
        "            }\n"
        "            case oc { leaf oc-v { type string; } }\n"
        "        }\n"
        "        leaf wcr { type leafref { path \"../wc-v\"; } }\n"
        /* one reader per leaf, so one data instance exercises one rule */
        "        list r {\n"
        "            key name;\n"
        "            leaf name { type string; }\n"
        "            leaf sel { type string; }\n"
        "            leaf lref { type leafref { path \"../../item/name\"; } }\n"
        "            leaf tref { type leafref { path \"../../tag\"; } }\n"
        "            leaf uref {\n"
        "                type union {\n"
        "                    type leafref { path \"../../item/name\"; }\n"
        "                    type enumeration { enum none; }\n"
        "                }\n"
        "            }\n"
        "            leaf-list lrefs { type leafref { path \"../../item/name\"; } }\n"
        "            leaf dref { type leafref { path \"../../item[name = current()/../sel]/val\"; } }\n"
        "            leaf m-exist { type string; must \"../../item[name = current()/../sel]\"; }\n"
        "            leaf m-val { type string; must \"../../item[name = current()/../sel]/val = 'good'\"; }\n"
        "            leaf m-count { type string; must \"count(../../item) >= 2\"; }\n"
        "            leaf m-sum { type string; must \"sum(../../num) >= 5\"; }\n"
        "            leaf m-first { type string; must \"contains(../../item/val, 'k')\"; }\n"
        "            leaf m-ou1 { type string; must \"../../ou[1]/name = 'first'\"; }\n"
        "            leaf m-oul { type string; must \"../../ou[last()]/name = 'tail'\"; }\n"
        "            leaf m-dd { type string; must \"../../item[name = 'i1']/dd = 'z'\"; }\n"
        "            leaf m-np { type string; must \"/dl:c-np/dl:l\"; }\n"
        "            leaf m-desc { type string; must \"count(../../inner//dl:name) >= 2\"; }\n"
        "            leaf lrf { type leafref { path \"../../item/name\"; require-instance false; } }\n"
        "            leaf m-der { type string; must \"deref(../lrf)/../val = 'good'\"; }\n"
        "            leaf m-dflt { type string; must \"../../dtag = 'x'\"; }\n"
        "            leaf m-fs { type string; must \"count(../following-sibling::r) >= 1\"; }\n"
        "            leaf m-ttag { type string; must \"count(../../tag[. = 't1']) = 1\"; }\n"
        "            leaf m-alln { type string; must \"count(/dl:top/*) >= 7\"; }\n"
        /* these two read a container, which is an ancestor of what the edit deletes */
        "            leaf m-anc { type string; must \"contains(string(../../inner), 'x1')\"; }\n"
        "            leaf m-anc2 { type string; must \"count(../../inner/*) >= 3\"; }\n"
        "            leaf m-anc3 { type string; must \"not(contains(string(../../inner), 'bad'))\"; }\n"
        "            leaf m-cap { type string; must \"count(/dl:top/dl:item) <= 3\"; }\n"
        "            leaf sw { type string; }\n"
        "            leaf dep { type string; when \"../sw = 'on'\"; }\n"
        "            leaf m-dep { type string; must \"../dep\"; }\n"
        "            leaf w-on { type string; when \"../../item[name = 'gate']\"; }\n"
        /* a default that exists only while its when holds, which reads w-on, which the validation itself drops once
         * the gate is gone */
        "            leaf dw { type string; default \"d\"; when \"../w-on\"; }\n"
        "        }\n"
        "    }\n"
        "\n"
        /* what the surviving structure demands */
        "    container c-mn { presence \"p\"; leaf keep { type string; } list mn { min-elements 2; key name; leaf name { type string; } } }\n"
        "    container c-mt { presence \"p\"; leaf keep { type string; } leaf-list mt { min-elements 1; type string; } }\n"
        "    container c-mp { presence \"p\"; leaf m { type string; mandatory true; } list l { key name; leaf name { type string; } } }\n"
        "    container c-mc {\n"
        "        presence \"p\";\n"
        "        leaf keep { type string; }\n"
        "        choice k {\n"
        "            mandatory true;\n"
        "            case ca { list la { key name; leaf name { type string; } } }\n"
        "            case cb { leaf-list lb { type string; } }\n"
        "        }\n"
        "    }\n"
        "    container c-dc {\n"
        "        leaf keep { type string; }\n"
        "        choice mode {\n"
        "            default auto;\n"
        "            case auto { leaf auto { type string; default \"on\"; } }\n"
        "            case manual { list rule { key id; leaf id { type uint32; } } }\n"
        "        }\n"
        "    }\n"
        "    container c-pc { presence \"p\"; list l { key name; leaf name { type string; } } }\n"
        "    container c-np { list l { key name; leaf name { type string; } } }\n"
        "    container c-vk {\n"
        "        list vk {\n"
        "            key name;\n"
        "            leaf name { type string; }\n"
        "            leaf grp { type string; must \"count(../../vk[grp = current()]) >= 2\"; }\n"
        "        }\n"
        "    }\n"
        /* rules a deletion can never break */
        "    container c-neg {\n"
        "        list un { key name; unique u; max-elements 3; leaf name { type string; } leaf u { type string; } }\n"
        "        leaf-list mx { max-elements 3; type string; }\n"
        "    }\n"
        "    container lone { list li { key name; leaf name { type string; } } }\n"
        "    container st {\n"
        "        config false;\n"
        "        list s { key name; leaf name { type string; } leaf sref { type leafref { path \"/dl:top/dl:item/dl:name\"; } } }\n"
        "    }\n"
        "identity cap-base;\n"
        "identity cap-download { base cap-base; }\n"
        "identity cap-sub { base cap-download; }\n"
        "identity cap-other { base cap-base; }\n"
        "identity fmt-base;\n"
        "identity fmt-ssh { base fmt-base; }\n"
        "identity fmt-other { base fmt-base; }\n"
        "\n"
        "container pr {\n"
        "    list shaper { key name; leaf name { type string; } leaf single { type string; } leaf two { type string; } }\n"
        "    list qprof {\n"
        "        key name;\n"
        "        leaf name { type string; }\n"
        "        container queues {\n"
        "            list queue {\n"
        "                key name;\n"
        "                leaf name { type string; }\n"
        "                leaf dual { type string; }\n"
        "                leaf shaper-name {\n"
        "                    type leafref { path \"/dl:pr/dl:shaper/dl:name\"; }\n"
        "                    must \"(not(boolean(current()/../dual)) and boolean(/dl:pr/dl:shaper[dl:name=current()]/dl:single)) or (boolean(current()/../dual) and boolean(/dl:pr/dl:shaper[dl:name=current()]/dl:two))\";\n"
        "                }\n"
        "            }\n"
        "        }\n"
        "    }\n"
        "    list bq {\n"
        "        key name;\n"
        "        leaf name { type string; }\n"
        "        leaf sref { type leafref { path \"/dl:pr/dl:shaper/dl:name\"; } }\n"
        "        leaf burst { type string; when \"boolean(/dl:pr/dl:shaper[dl:name=current()/../sref]/dl:single)\"; }\n"
        "    }\n"
        "    list tmpl { key name; leaf name { type string; } list ifc { key name; leaf name { type string; } leaf v4 { type string; } leaf v6 { type string; } } }\n"
        "    list onu {\n"
        "        key name;\n"
        "        leaf name { type string; }\n"
        "        leaf tref { type string; }\n"
        "        list term {\n"
        "            key name;\n"
        "            leaf name { type string; }\n"
        "            leaf peer { type leafref { path \"../../term/name\"; } }\n"
        "            leaf ipif {\n"
        "                type string;\n"
        "                must \"boolean(/dl:pr/dl:tmpl[dl:name=current()/ancestor::dl:onu/dl:tref]/dl:ifc[dl:name=current()]/dl:v4) or boolean(/dl:pr/dl:tmpl[dl:name=current()/ancestor::dl:onu/dl:tref]/dl:ifc[dl:name=current()]/dl:v6)\";\n"
        "            }\n"
        "        }\n"
        "    }\n"
        "    list comp {\n"
        "        key name;\n"
        "        leaf name { type string; }\n"
        "        container revs {\n"
        "            leaf cap { type string; }\n"
        "            leaf dcap { type identityref { base cap-base; } }\n"
        "            list rev {\n"
        "                key name;\n"
        "                leaf name { type string; }\n"
        "                leaf state { type string; }\n"
        "                leaf alias { type string; when \"boolean(../../cap='alias')\"; }\n"
        "                leaf act { type string; when \"boolean(../../cap='act') and (../state='available' or ../state='in-use')\"; }\n"
        "                leaf fin { type string; when \"derived-from(../../dcap, 'dl:cap-download') and ../state != 'downloading'\"; }\n"
        "            }\n"
        "            leaf download { type string; when \"derived-from(../dcap, 'dl:cap-download') and count(../rev[state='downloading'])=0\"; }\n"
        "        }\n"
        "    }\n"
        "    list tp {\n"
        "        key name;\n"
        "        leaf name { type string; }\n"
        "        container tcs {\n"
        "            must \"not(boolean(tc)) or tc[not(../tc/position > position)]/position <= count(current()/tc)\";\n"
        "            list tc { key position; leaf position { type uint32; } leaf duration { type string; } }\n"
        "            leaf rb { type string; when \"(count(../tc) > 1) and ../tc[position=count(../tc)]/duration != 'continuous'\"; }\n"
        "        }\n"
        "    }\n"
        "    list tsb { key name; leaf name { type string; } list pk { key name; leaf name { type string; } leaf fmt { type identityref { base fmt-base; } } } }\n"
        "    list usr {\n"
        "        key name;\n"
        "        leaf name { type string; }\n"
        "        leaf ref {\n"
        "            type leafref { path \"/dl:pr/dl:tsb/dl:name\"; }\n"
        "            must \"not(deref(.)/../dl:pk/dl:fmt[not(derived-from-or-self(., 'dl:fmt-ssh'))])\";\n"
        "        }\n"
        "    }\n"
        "}\n"
        "}";

static const char *schema_dm =
        "module dm {\n"
        "    namespace urn:tests:dm;\n"
        "    prefix dm;\n"
        "    yang-version 1.1;\n"
        "    import dl { prefix dl; }\n"
        "\n"
        "    container mtop {\n"
        "        list mr {\n"
        "            key name;\n"
        "            leaf name { type string; }\n"
        "            leaf iref { type leafref { path \"/dl:top/dl:item/dl:name\"; } }\n"
        "            leaf lone-ref { type leafref { path \"/dl:lone/dl:li/dl:name\"; } }\n"
        "            leaf mcnt { type string; must \"count(/dl:top/dl:tag) >= 1\"; }\n"
        "            leaf manc { type string; must \"contains(string(/dl:top/dl:inner), 'x1')\"; }\n"
        "            leaf manc2 { type string; must \"not(contains(string(/dl:top/dl:inner), 'bad'))\"; }\n"
        "        }\n"
        "    }\n"
        /* a leaf of dm inside a list instance of dl, reading data of dl */
        "    augment \"/dl:top/dl:item\" {\n"
        "        leaf aug-ref { type leafref { path \"/dl:top/dl:tag\"; } }\n"
        "    }\n"
        "}";

/*
 * Defaults that exist only while a rule that reads another instance holds. A module with such a node has to be
 * validated in full whenever an edit touches what the rule reads, so they live in a module of their own: next to
 * the readers of dl they would turn every edit of the item list into a full validation, and the cases would no
 * longer test the incremental path.
 */
static const char *schema_dz =
        "module dz {\n"
        "    namespace urn:tests:dz;\n"
        "    prefix dz;\n"
        "    yang-version 1.1;\n"
        "    import dl { prefix dl; }\n"
        "\n"
        "    container zt {\n"
        "        list zr {\n"
        "            key name;\n"
        "            leaf name { type string; }\n"
        "            leaf dgate { type string; default \"d\"; when \"/dl:top/dl:item[dl:name = 'gate']\"; }\n"
        "            leaf dopen { type string; default \"d\"; when \"not(/dl:top/dl:item[dl:name = 'gate'])\"; }\n"
        "        }\n"
        "    }\n"
        "}";

#define DZ_Z "<zt xmlns=\"urn:tests:dz\"><zr><name>z</name></zr></zt>"

#define DL_T(x) "<top xmlns=\"urn:tests:dl\">" x "</top>"
#define DL_C(c, x) "<" c " xmlns=\"urn:tests:dl\">" x "</" c ">"
#define DL_I(n, v) "<item><name>" n "</name><val>" v "</val></item>"
#define DL_R(n, x) "<r><name>" n "</name>" x "</r>"
#define DL_GATE "<item><name>gate</name></item>"
#define DM_M(x) "<mtop xmlns=\"urn:tests:dm\"><mr><name>m1</name>" x "</mr></mtop>"
#define DL_LONE DL_C("lone", "<li><name>l1</name></li>")

/** @brief every reader and every structure once, valid as a whole */
static const char *dl_xml =
        DL_T(
        "<item><name>i1</name><val>k1</val><dd>z</dd></item>" DL_I("i2", "good") DL_I("i3", "zz")
        "<item><name>i4</name><val>zz</val><aug-ref xmlns=\"urn:tests:dm\">t2</aug-ref></item>" DL_GATE
        "<tag>t1</tag><tag>t2</tag><num>3</num><num>4</num>"
        "<ou><name>first</name></ou><ou><name>mid</name></ou><ou><name>tail</name></ou>"
        "<inner><a>a</a><x><name>x1</name></x><x><name>x2</name></x></inner>"
        "<kr><k>i3</k></kr>"
        "<wc-v>cv</wc-v><wcr>cv</wcr>"
        DL_R("r-lref", "<lref>i1</lref>")
        DL_R("r-tref", "<tref>t1</tref>")
        DL_R("r-uref", "<uref>i2</uref>")
        DL_R("r-lrefs", "<lrefs>i2</lrefs><lrefs>i3</lrefs>")
        DL_R("r-dref", "<sel>i2</sel><dref>good</dref>")
        DL_R("r-mexist", "<sel>i3</sel><m-exist>y</m-exist>")
        DL_R("r-mval", "<sel>i2</sel><m-val>y</m-val>")
        DL_R("r-mcount", "<m-count>y</m-count>")
        DL_R("r-msum", "<m-sum>y</m-sum>")
        DL_R("r-mfirst", "<m-first>y</m-first>")
        DL_R("r-mou1", "<m-ou1>y</m-ou1>")
        DL_R("r-moul", "<m-oul>y</m-oul>")
        DL_R("r-mdd", "<m-dd>y</m-dd>")
        DL_R("r-mnp", "<m-np>y</m-np>")
        DL_R("r-manc", "<m-anc>y</m-anc>")
        DL_R("r-manc2", "<m-anc2>y</m-anc2>")
        DL_R("r-won", "<w-on>v1</w-on>")
        "<wr><name>w1</name><wref>v1</wref></wr>")
        DL_C("c-mn", "<keep>k</keep><mn><name>m1</name></mn><mn><name>m2</name></mn>")
        DL_C("c-mt", "<keep>k</keep><mt>t</mt>")
        DL_C("c-mp", "<m>x</m><l><name>a</name></l>")
        DL_C("c-mc", "<keep>k</keep><la><name>a1</name></la><la><name>a2</name></la>")
        DL_C("c-dc", "<keep>k</keep><rule><id>1</id></rule><rule><id>2</id></rule>")
        DL_C("c-pc", "<l><name>a</name></l>")
        DL_C("c-np", "<l><name>a</name></l><l><name>b</name></l>")
        DL_C("c-vk", "<vk><name>v1</name><grp>g1</grp></vk><vk><name>v2</name><grp>g1</grp></vk>"
        "<vk><name>v3</name><grp>g2</grp></vk><vk><name>v4</name><grp>g2</grp></vk>")
        DL_C("c-neg", "<un><name>a</name><u>u1</u></un><un><name>b</name><u>u2</u></un><mx>x</mx><mx>y</mx>")
        DL_LONE DZ_Z
        DL_C("st", "<s><name>n1</name><sref>i2</sref></s>")
        "<mtop xmlns=\"urn:tests:dm\"><mr><name>m1</name><iref>i1</iref></mr>"
        "<mr><name>m2</name><lone-ref>l1</lone-ref></mr><mr><name>m3</name><mcnt>y</mcnt></mr></mtop>";

static void
dl_setup(void **state)
{
    UTEST_ADD_MODULE(schema_dl, LYS_IN_YANG, NULL, NULL);
    UTEST_ADD_MODULE(schema_dm, LYS_IN_YANG, NULL, NULL);
    UTEST_ADD_MODULE(schema_dz, LYS_IN_YANG, NULL, NULL);
    check_mods[0] = "dl";
    check_mods[1] = "dm";
    check_mods[2] = "dz";
    check_mods[3] = NULL;
}

static void
dl_done(void)
{
    check_mods[0] = "a";
    check_mods[1] = NULL;
}

/**
 * @brief Validate an edited tree in full, and incrementally against a hand-made edit diff, for both option sets.
 *
 * A deleted list instance that a hand-made or merged diff names without its children has to find the rules that
 * read those children as well.
 */
static void
check_diff_dl(void **state, const struct lyd_node *after, const char *diff_xml, LY_ERR expected)
{
    const struct lys_module *mod = ly_ctx_get_module_implemented(UTEST_LYCTX, "dl");
    struct lyd_node *full = NULL, *incr = NULL, *diff = NULL, *val_diff = NULL;
    LY_ERR rc_full, rc_incr;
    uint32_t s;

    assert_non_null(mod);
    assert_int_equal(LY_SUCCESS, lyd_dup_siblings(after, NULL, LYD_DUP_RECURSIVE | LYD_DUP_WITH_FLAGS, &full));
    rc_full = lyd_validate_module(&full, mod, 0, NULL);
    ly_err_clean((struct ly_ctx *)UTEST_LYCTX, NULL);
    assert_int_equal(expected, rc_full);

    for (s = 0; s < sizeof incr_opt_sets / sizeof *incr_opt_sets; ++s) {
        assert_int_equal(LY_SUCCESS, lyd_dup_siblings(after, NULL, LYD_DUP_RECURSIVE | LYD_DUP_WITH_FLAGS, &incr));
        assert_int_equal(LY_SUCCESS, lyd_parse_data_mem(UTEST_LYCTX, diff_xml, LYD_XML, LYD_PARSE_ONLY, 0, &diff));
        rc_incr = lyd_validate_module_incr(&incr, mod, diff, incr_opt_sets[s] | LYD_VALIDATE_NOT_FINAL, &val_diff);
        if (!rc_incr) {
            rc_incr = lyd_validate_module_incr_final(incr, mod, diff, incr_opt_sets[s]);
        }
        ly_err_clean((struct ly_ctx *)UTEST_LYCTX, NULL);
        if (rc_full != rc_incr) {
            print_message("[  MSG     ] full %d vs incremental %d with options 0x%x\n", rc_full, rc_incr,
                    incr_opt_sets[s]);
        }
        assert_int_equal(rc_full, rc_incr);

        lyd_free_all(val_diff);
        val_diff = NULL;
        lyd_free_siblings(diff);
        diff = NULL;
        lyd_free_siblings(incr);
        incr = NULL;
    }
    lyd_free_siblings(full);
}

#define DL_DIFF_NS "xmlns=\"urn:tests:dl\" xmlns:yang=\"urn:ietf:params:xml:ns:yang:1\""

/**
 * @brief A diff that deletes a list instance and does not list its children.
 */
static void
test_del_childless_diff(void **state)
{
    struct lyd_node *before, *after;

    dl_setup(state);

    /* the first value is gone with the instance that held it */
    before = parse_valid(state, DL_T(DL_I("i1", "k1") DL_I("i2", "zz") DL_R("r", "<m-first>y</m-first>")));
    assert_int_equal(LY_SUCCESS, lyd_dup_siblings(before, NULL, LYD_DUP_RECURSIVE | LYD_DUP_WITH_FLAGS, &after));
    drop_node(&after, "/dl:top/item[name='i1']");
    check_diff_dl(state, after, "<top " DL_DIFF_NS " yang:operation=\"none\"><item yang:operation=\"delete\">"
            "<name>i1</name></item></top>", LY_EVALID);
    lyd_free_siblings(after);
    lyd_free_siblings(before);

    /* the value a must reads is a child of the deleted instance */
    before = parse_valid(state, DL_T("<item><name>i1</name><dd>z</dd></item>" DL_I("i2", "b")
            DL_R("r", "<m-dd>y</m-dd>")));
    assert_int_equal(LY_SUCCESS, lyd_dup_siblings(before, NULL, LYD_DUP_RECURSIVE | LYD_DUP_WITH_FLAGS, &after));
    drop_node(&after, "/dl:top/item[name='i1']");
    check_diff_dl(state, after, "<top " DL_DIFF_NS " yang:operation=\"none\"><item yang:operation=\"delete\">"
            "<name>i1</name></item></top>", LY_EVALID);
    lyd_free_siblings(after);
    lyd_free_siblings(before);

    /* an unrelated instance, with the same shape of diff, is fine */
    before = parse_valid(state, DL_T(DL_I("i1", "k1") DL_I("i2", "k2") DL_R("r", "<m-first>y</m-first>")));
    assert_int_equal(LY_SUCCESS, lyd_dup_siblings(before, NULL, LYD_DUP_RECURSIVE | LYD_DUP_WITH_FLAGS, &after));
    drop_node(&after, "/dl:top/item[name='i2']");
    check_diff_dl(state, after, "<top " DL_DIFF_NS " yang:operation=\"none\"><item yang:operation=\"delete\">"
            "<name>i2</name></item></top>", LY_SUCCESS);
    lyd_free_siblings(after);
    lyd_free_siblings(before);

    dl_done();
}

/** @brief seeds of the random delete sets, LY_DEL_SWEEP_SEEDS raises it for a longer run */
static uint32_t
dl_sweep_seeds(void)
{
    const char *env = getenv("LY_DEL_SWEEP_SEEDS");

    return env ? (uint32_t)strtoul(env, NULL, 10) : 2000;
}

#define DL_SWEEP_SEEDS dl_sweep_seeds()

/**
 * @brief One delete edit with the verdict it must get.
 *
 * @p edits is in the format of aug_apply(): a path starting with '-' deletes it, any other path is set to the
 * value next to it, and a NULL path ends the list.
 */
struct dl_case {
    const char *name;
    const char *xml;
    const char *edits[9];
    LY_ERR expected;
};

#define DL_P "/dl:top/"
#define E_BAD LY_EVALID
#define E_OK LY_SUCCESS

static const struct dl_case dl_cases[] = {
    /* leafrefs: the one the deleted instance is the target of, and one it is not */
    {"leafref target", DL_T(DL_I("i1", "a") DL_I("i2", "b") DL_R("r", "<lref>i1</lref>")),
        {"-" DL_P "item[name='i1']"}, E_BAD},
    {"leafref other instance", DL_T(DL_I("i1", "a") DL_I("i2", "b") DL_R("r", "<lref>i1</lref>")),
        {"-" DL_P "item[name='i2']"}, E_OK},
    {"leafref to a leaf-list instance", DL_T("<tag>t1</tag><tag>t2</tag>" DL_R("r", "<tref>t1</tref>")),
        {"-" DL_P "tag[.='t1']"}, E_BAD},
    {"leafref to another leaf-list instance", DL_T("<tag>t1</tag><tag>t2</tag>" DL_R("r", "<tref>t1</tref>")),
        {"-" DL_P "tag[.='t2']"}, E_OK},
    {"union leafref member", DL_T(DL_I("i1", "a") DL_I("i2", "b") DL_R("r", "<uref>i1</uref>")),
        {"-" DL_P "item[name='i1']"}, E_BAD},
    {"union enum member", DL_T(DL_I("i1", "a") DL_I("i2", "b") DL_R("r", "<uref>none</uref>")),
        {"-" DL_P "item[name='i1']"}, E_OK},
    {"key leafref", DL_T(DL_I("i1", "a") DL_I("i2", "b") "<kr><k>i1</k></kr>"),
        {"-" DL_P "item[name='i1']"}, E_BAD},
    {"leaf-list of leafrefs, one target", DL_T(DL_I("i1", "a") DL_I("i2", "b") DL_R("r", "<lrefs>i1</lrefs><lrefs>i2</lrefs>")),
        {"-" DL_P "item[name='i2']"}, E_BAD},
    {"leaf-list of leafrefs, not a target", DL_T(DL_I("i1", "a") DL_I("i2", "b") DL_I("i3", "c")
        DL_R("r", "<lrefs>i1</lrefs><lrefs>i2</lrefs>")), {"-" DL_P "item[name='i3']"}, E_OK},
    {"leafref picked by current(), the instance", DL_T(DL_I("i1", "a") DL_I("i2", "good")
        DL_R("r", "<sel>i2</sel><dref>good</dref>")), {"-" DL_P "item[name='i2']"}, E_BAD},
    {"leafref picked by current(), the target leaf", DL_T(DL_I("i1", "a") DL_I("i2", "good")
        DL_R("r", "<sel>i2</sel><dref>good</dref>")), {"-" DL_P "item[name='i2']/val"}, E_BAD},
    {"leafref picked by current(), another instance", DL_T(DL_I("i1", "a") DL_I("i2", "good")
        DL_R("r", "<sel>i2</sel><dref>good</dref>")), {"-" DL_P "item[name='i1']"}, E_OK},

    /* must: existence, value, counts, the first node, positions */
    {"must needs the instance", DL_T(DL_I("i1", "a") DL_I("i3", "c") DL_R("r", "<sel>i3</sel><m-exist>y</m-exist>")),
        {"-" DL_P "item[name='i3']"}, E_BAD},
    {"must needs the instance, another one goes", DL_T(DL_I("i1", "a") DL_I("i3", "c")
        DL_R("r", "<sel>i3</sel><m-exist>y</m-exist>")), {"-" DL_P "item[name='i1']"}, E_OK},
    {"must compares the value", DL_T(DL_I("i2", "good") DL_R("r", "<sel>i2</sel><m-val>y</m-val>") "<tag>t</tag>"),
        {"-" DL_P "item[name='i2']"}, E_BAD},
    {"count falls below the bound", DL_T(DL_I("i1", "a") DL_I("i2", "b") DL_R("r", "<m-count>y</m-count>")),
        {"-" DL_P "item[name='i1']"}, E_BAD},
    {"count stays above the bound", DL_T(DL_I("i1", "a") DL_I("i2", "b") DL_I("i3", "c") DL_R("r", "<m-count>y</m-count>")),
        {"-" DL_P "item[name='i1']"}, E_OK},
    {"sum falls below the bound", DL_T("<num>3</num><num>4</num>" DL_R("r", "<m-sum>y</m-sum>")),
        {"-" DL_P "num[.='3']"}, E_BAD},
    {"sum stays above the bound", DL_T("<num>3</num><num>4</num><num>5</num>" DL_R("r", "<m-sum>y</m-sum>")),
        {"-" DL_P "num[.='5']"}, E_OK},
    {"first node changes the string value", DL_T(DL_I("i1", "k1") DL_I("i2", "zz") DL_R("r", "<m-first>y</m-first>")),
        {"-" DL_P "item[name='i1']"}, E_BAD},
    {"first node changes but the value holds", DL_T(DL_I("i1", "k1") DL_I("i2", "k2") DL_R("r", "<m-first>y</m-first>")),
        {"-" DL_P "item[name='i1']"}, E_OK},
    {"a later node goes, the first one stays", DL_T(DL_I("i1", "k1") DL_I("i2", "zz") DL_R("r", "<m-first>y</m-first>")),
        {"-" DL_P "item[name='i2']"}, E_OK},
    {"first of an ordered-by-user list goes", DL_T("<ou><name>first</name></ou><ou><name>mid</name></ou>"
        "<ou><name>tail</name></ou>" DL_R("r", "<m-ou1>y</m-ou1>")), {"-" DL_P "ou[name='first']"}, E_BAD},
    {"middle of an ordered-by-user list goes", DL_T("<ou><name>first</name></ou><ou><name>mid</name></ou>"
        "<ou><name>tail</name></ou>" DL_R("r", "<m-ou1>y</m-ou1>")), {"-" DL_P "ou[name='mid']"}, E_OK},
    {"last of an ordered-by-user list goes", DL_T("<ou><name>first</name></ou><ou><name>mid</name></ou>"
        "<ou><name>tail</name></ou>" DL_R("r", "<m-oul>y</m-oul>")), {"-" DL_P "ou[name='tail']"}, E_BAD},
    {"middle goes, the last one stays", DL_T("<ou><name>first</name></ou><ou><name>mid</name></ou>"
        "<ou><name>tail</name></ou>" DL_R("r", "<m-oul>y</m-oul>")), {"-" DL_P "ou[name='mid']"}, E_OK},

    /* when: becoming false takes the node away, becoming true brings a default in */
    {"when turns true to false", DL_T(DL_GATE DL_R("r", "<w-on>v1</w-on>")), {"-" DL_P "item[name='gate']"}, E_OK},
    {"when turns false, a leafref reads the dropped node", DL_T(DL_GATE DL_R("r", "<w-on>v1</w-on>")
        "<wr><name>w1</name><wref>v1</wref></wr>"), {"-" DL_P "item[name='gate']"}, E_BAD},
    {"when turns false to true, a default appears", DL_T(DL_GATE DL_R("r", "<sel>x</sel>")) DZ_Z,
        {"-" DL_P "item[name='gate']"}, E_OK},
    {"default node whose when reads the deleted instance", DL_T(DL_GATE DL_R("r", "<sel>x</sel>")) DZ_Z,
        {"-" DL_P "item[name='gate']"}, E_OK},
    {"default node whose when reads a node the validation drops", DL_T(DL_GATE DL_R("r", "<w-on>v1</w-on>")) DZ_Z,
        {"-" DL_P "item[name='gate']"}, E_OK},
    {"when of a case turns false", DL_T(DL_GATE "<wc-v>cv</wc-v>") DL_LONE, {"-" DL_P "item[name='gate']"}, E_OK},
    {"when of a case turns false, a leafref reads it", DL_T(DL_GATE "<wc-v>cv</wc-v><wcr>cv</wcr>"),
        {"-" DL_P "item[name='gate']"}, E_BAD},

    /* the reader is in another module, or the data is */
    {"other module leafref", DL_T(DL_I("i1", "a") DL_I("i2", "b")) DM_M("<iref>i1</iref>"),
        {"-" DL_P "item[name='i1']"}, E_BAD},
    {"other module leafref, another instance", DL_T(DL_I("i1", "a") DL_I("i2", "b")) DM_M("<iref>i1</iref>"),
        {"-" DL_P "item[name='i2']"}, E_OK},
    {"other module leafref to a top-level list", DL_LONE DL_T(DL_I("i1", "a")) DM_M("<lone-ref>l1</lone-ref>"),
        {"-/dl:lone/li[name='l1']"}, E_BAD},
    {"other module leafref to a whole top-level container", DL_LONE DL_T(DL_I("i1", "a")) DM_M("<lone-ref>l1</lone-ref>"),
        {"-/dl:lone"}, E_BAD},
    {"a top-level container nobody reads", DL_LONE DL_T(DL_I("i1", "a")), {"-/dl:lone"}, E_OK},
    {"other module count", DL_T("<tag>t1</tag>") DM_M("<mcnt>y</mcnt>"), {"-" DL_P "tag[.='t1']"}, E_BAD},
    {"other module count, one left", DL_T("<tag>t1</tag><tag>t2</tag>") DM_M("<mcnt>y</mcnt>"),
        {"-" DL_P "tag[.='t1']"}, E_OK},
    {"augmented leaf reads the deleted instance", DL_T("<tag>t1</tag><tag>t2</tag><item><name>i1</name>"
        "<aug-ref xmlns=\"urn:tests:dm\">t1</aug-ref></item>"), {"-" DL_P "tag[.='t1']"}, E_BAD},
    {"augmented list instance is the one deleted", DL_T("<tag>t1</tag><item><name>i1</name>"
        "<aug-ref xmlns=\"urn:tests:dm\">t1</aug-ref></item>" DL_I("i2", "b")), {"-" DL_P "item[name='i1']"}, E_OK},
    {"a whole top-level container read from outside", DL_LONE DL_T(DL_I("i1", "a")) DM_M("<iref>i1</iref>"),
        {"-/dl:top"}, E_BAD},
    {"the reader of that container goes with it", DL_LONE DL_T(DL_I("i1", "a")) DM_M("<iref>i1</iref>"),
        {"-/dl:top", NULL, "-/dm:mtop"}, E_OK},
    {"state data reads the deleted instance", DL_T(DL_I("i1", "a") DL_I("i2", "b"))
        DL_C("st", "<s><name>n1</name><sref>i2</sref></s>"), {"-" DL_P "item[name='i2']"}, E_BAD},

    /* what the surviving structure demands */
    {"min-elements of a list", DL_C("c-mn", "<keep>k</keep><mn><name>m1</name></mn><mn><name>m2</name></mn>"),
        {"-/dl:c-mn/mn[name='m1']"}, E_BAD},
    {"min-elements of a list, enough left", DL_C("c-mn", "<keep>k</keep><mn><name>m1</name></mn><mn><name>m2</name></mn>"
        "<mn><name>m3</name></mn>"), {"-/dl:c-mn/mn[name='m1']"}, E_OK},
    {"min-elements of a leaf-list", DL_C("c-mt", "<keep>k</keep><mt>t</mt>"), {"-/dl:c-mt/mt[.='t']"}, E_BAD},
    {"min-elements of a leaf-list, enough left", DL_C("c-mt", "<keep>k</keep><mt>t</mt><mt>u</mt>"),
        {"-/dl:c-mt/mt[.='t']"}, E_OK},
    {"mandatory leaf", DL_C("c-mp", "<m>x</m><l><name>a</name></l>"), {"-/dl:c-mp/m"}, E_BAD},
    {"list next to a mandatory leaf", DL_C("c-mp", "<m>x</m><l><name>a</name></l>"), {"-/dl:c-mp/l[name='a']"}, E_OK},
    {"mandatory choice loses its only node", DL_C("c-mc", "<keep>k</keep><la><name>a1</name></la>"),
        {"-/dl:c-mc/la[name='a1']"}, E_BAD},
    {"mandatory choice keeps a node", DL_C("c-mc", "<keep>k</keep><la><name>a1</name></la><la><name>a2</name></la>"),
        {"-/dl:c-mc/la[name='a1']"}, E_OK},
    {"default case comes back", DL_C("c-dc", "<keep>k</keep><rule><id>1</id></rule>"), {"-/dl:c-dc/rule[id='1']"}, E_OK},
    {"default case does not come back", DL_C("c-dc", "<keep>k</keep><rule><id>1</id></rule><rule><id>2</id></rule>"),
        {"-/dl:c-dc/rule[id='1']"}, E_OK},
    {"both rules of the other case go", DL_C("c-dc", "<keep>k</keep><rule><id>1</id></rule><rule><id>2</id></rule>"),
        {"-/dl:c-dc/rule[id='1']", NULL, "-/dl:c-dc/rule[id='2']"}, E_OK},
    {"presence container is emptied", DL_C("c-pc", "<l><name>a</name></l>") DL_LONE, {"-/dl:c-pc/l[name='a']"}, E_OK},
    {"non-presence container is emptied and a rule reads it", DL_C("c-np", "<l><name>a</name></l>")
        DL_T(DL_R("r", "<m-np>y</m-np>")), {"-/dl:c-np/l[name='a']"}, E_BAD},
    {"non-presence container is emptied, nothing reads it", DL_C("c-np", "<l><name>a</name></l>") DL_LONE,
        {"-/dl:c-np/l[name='a']"}, E_OK},
    {"non-presence container keeps one", DL_C("c-np", "<l><name>a</name></l><l><name>b</name></l>")
        DL_T(DL_R("r", "<m-np>y</m-np>")), {"-/dl:c-np/l[name='a']"}, E_OK},
    {"explicit value goes back to its default", DL_T("<item><name>i1</name><dd>z</dd></item>"
        DL_R("r", "<m-dd>y</m-dd>")), {"-" DL_P "item[name='i1']/dd"}, E_BAD},
    {"explicit value goes back to its default, nobody reads it", DL_T("<item><name>i1</name><dd>z</dd></item>"),
        {"-" DL_P "item[name='i1']/dd"}, E_OK},
    {"count of one value breaks its partner", DL_C("c-vk", "<vk><name>v1</name><grp>g1</grp></vk>"
        "<vk><name>v2</name><grp>g1</grp></vk>"), {"-/dl:c-vk/vk[name='v1']"}, E_BAD},
    {"count of one value keeps enough", DL_C("c-vk", "<vk><name>v1</name><grp>g1</grp></vk>"
        "<vk><name>v2</name><grp>g1</grp></vk><vk><name>v3</name><grp>g1</grp></vk>"), {"-/dl:c-vk/vk[name='v1']"}, E_OK},
    {"unique and max-elements never break", DL_C("c-neg", "<un><name>a</name><u>u1</u></un><un><name>b</name><u>u2</u></un>"
        "<mx>x</mx><mx>y</mx>"), {"-/dl:c-neg/un[name='a']"}, E_OK},
    {"max-elements never breaks", DL_C("c-neg", "<un><name>a</name><u>u1</u></un><mx>x</mx><mx>y</mx>"),
        {"-/dl:c-neg/mx[.='x']"}, E_OK},

    /* the shape of the edit */
    {"reader and target go together", DL_T(DL_I("i1", "a") DL_I("i2", "b") DL_R("r", "<lref>i1</lref>")),
        {"-" DL_P "item[name='i1']", NULL, "-" DL_P "r[name='r']"}, E_OK},
    {"target and an unrelated reader go", DL_T(DL_I("i1", "a") DL_I("i2", "b") DL_R("r1", "<lref>i1</lref>")
        DL_R("r2", "<lref>i2</lref>")), {"-" DL_P "item[name='i1']", NULL, "-" DL_P "r[name='r2']"}, E_BAD},
    {"target goes and the reader is repointed", DL_T(DL_I("i1", "a") DL_I("i2", "b") DL_R("r", "<lref>i1</lref>")),
        {"-" DL_P "item[name='i1']", NULL, DL_P "r[name='r']/lref", "i2"}, E_OK},
    {"target goes and the reader is repointed to a new one", DL_T(DL_I("i1", "a") DL_I("i2", "b")
        DL_R("r", "<lref>i1</lref>")), {"-" DL_P "item[name='i1']", NULL, DL_P "item[name='i9']", NULL,
        DL_P "r[name='r']/lref", "i9"}, E_OK},
    {"one of two targets goes, the reader stays", DL_T(DL_I("i1", "a") DL_I("i2", "b") DL_R("r", "<lrefs>i1</lrefs>")),
        {"-" DL_P "item[name='i2']"}, E_OK},
    {"two targets go, one is read", DL_T(DL_I("i1", "a") DL_I("i2", "b") DL_I("i3", "c") DL_R("r", "<lrefs>i1</lrefs>")),
        {"-" DL_P "item[name='i2']", NULL, "-" DL_P "item[name='i1']"}, E_BAD},
    {"a whole subtree goes, only a descendant is read", DL_T("<inner><a>a</a><x><name>x1</name></x><x><name>x2</name></x></inner>"
        DL_R("r", "<m-anc2>y</m-anc2>")), {"-" DL_P "inner"}, E_BAD},
    {"a leaf reader is deleted", DL_T(DL_I("i1", "a") DL_R("r", "<lref>i1</lref>")), {"-" DL_P "r[name='r']/lref"}, E_OK},
};

/*
 * A rule that reads a container as a whole, while the edit deletes or changes a descendant of it. The edit touches
 * only the node and what is below it, so the rule must have the descendants of the container among its atoms.
 */
static const struct dl_case dl_ancestor_cases[] = {
    {"must counts the children of a container", DL_T("<inner><a>a</a><x><name>x1</name></x><x><name>x2</name></x></inner>"
        DL_R("r", "<m-anc2>y</m-anc2>")), {"-" DL_P "inner/x[name='x1']"}, E_BAD},
    {"must reads the string value of a container", DL_T("<inner><a>a</a><x><name>x1</name></x><x><name>x2</name></x></inner>"
        DL_R("r", "<m-anc>y</m-anc>")), {"-" DL_P "inner/x[name='x1']"}, E_BAD},
    {"rule of another module reads the string value of a container", DL_T("<inner><a>a</a><x><name>x1</name></x>"
        "<x><name>x2</name></x></inner>") DM_M("<manc>y</manc>"), {"-" DL_P "inner/x[name='x1']"}, E_BAD},
    {"a leaf below a container changes its string value", DL_T("<inner><a>a</a><x><name>x1</name></x></inner>"
        DL_R("r", "<m-anc3>y</m-anc3>")), {DL_P "inner/a", "bad"}, E_BAD},
    {"a leaf below a container changes the string value another module reads", DL_T("<inner><a>a</a>"
        "<x><name>x1</name></x></inner>") DM_M("<manc2>y</manc2>"), {DL_P "inner/a", "bad"}, E_BAD},
};

/**
 * @brief Run every case with the modules in both orders, so a reader that sits in the module validated first is
 * covered as well as one validated last.
 */
static void
dl_run(void **state, const struct dl_case *cases, uint32_t count)
{
    const char *order[2][4] = {{"dl", "dm", "dz", NULL}, {"dz", "dm", "dl", NULL}};
    struct lyd_node *before, *after;
    uint32_t i, o;
    LY_ERR rc;

    dl_setup(state);
    for (o = 0; o < 2; ++o) {
        check_mods[0] = order[o][0];
        check_mods[1] = order[o][1];
        check_mods[2] = order[o][2];
        for (i = 0; i < count; ++i) {
            print_message("[  CASE    ] %s\n", cases[i].name);
            before = parse_valid(state, cases[i].xml);
            after = aug_apply(state, before, cases[i].edits);
            check_same(state, before, after, 1, &rc);
            if (rc != cases[i].expected) {
                print_message("[  MSG     ] case \"%s\" (order %s,%s): expected %d, got %d\n", cases[i].name,
                        order[o][0], order[o][1], cases[i].expected, rc);
            }
            assert_int_equal(cases[i].expected, rc);
            lyd_free_siblings(after);
            lyd_free_siblings(before);
        }
    }
    dl_done();
}

static void
test_del_cases(void **state)
{
    dl_run(state, dl_cases, sizeof dl_cases / sizeof *dl_cases);
}

/** @brief constructs of the YANG language that no earlier case reads, each one a delete that full validation rejects */
static const struct dl_case dl_probe_cases[] = {
    {"descendant axis counts the nodes below a container", DL_T("<inner><x><name>x1</name></x><x><name>x2</name></x></inner>"
        DL_R("r", "<m-desc>y</m-desc>")), {"-" DL_P "inner/x[name='x1']"}, E_BAD},
    {"deref of a leafref without require-instance", DL_T(DL_I("i2", "good") DL_R("r", "<lrf>i2</lrf><m-der>y</m-der>")),
        {"-" DL_P "item[name='i2']"}, LY_EINVAL},
    {"a default leaf-list value appears when the explicit one goes", DL_T("<dtag>x</dtag>" DL_R("r", "<m-dflt>y</m-dflt>")),
        {"-" DL_P "dtag[.='x']"}, E_BAD},
    {"later sibling of the same list is read", DL_T(DL_R("r1", "<m-fs>y</m-fs>") DL_R("r2", "")),
        {"-" DL_P "r[name='r2']"}, E_BAD},
    {"earlier sibling is read by the preceding axis", DL_T("<pos><name>a</name></pos><pos><name>b</name><pp>y</pp></pos>"),
        {"-" DL_P "pos[name='a']"}, E_BAD},
    {"reader in the same list instance, member of a nested list", DL_T("<grp><name>g1</name><mem><name>a</name></mem>"
        "<mem><name>b</name></mem><need>y</need></grp>"), {"-" DL_P "grp[name='g1']/mem[name='a']"}, E_BAD},
    {"reader in another instance, member of a nested list", DL_T("<grp><name>g1</name><mem><name>a</name></mem>"
        "<mem><name>b</name></mem></grp><grp><name>g2</name><mem><name>c</name></mem><xr>y</xr></grp>"),
        {"-" DL_P "grp[name='g1']/mem[name='a']"}, E_BAD},
    {"reader inside a sibling list instance reads the list", DL_T("<inner><x><name>x1</name></x><x><name>x2</name>"
        "<chk>y</chk></x></inner>"), {"-" DL_P "inner/x[name='x1']"}, E_BAD},
    {"count of one leaf-list value", DL_T("<tag>t1</tag><tag>t2</tag>" DL_R("r", "<m-ttag>y</m-ttag>")),
        {"-" DL_P "tag[.='t1']"}, E_BAD},
    {"count of every child of the container", DL_T("<tag>t1</tag><tag>t2</tag><num>1</num><num>2</num><inner/>"
        DL_R("r", "<m-alln>y</m-alln>")), {"-" DL_P "tag[.='t1']"}, E_BAD},
};

/*
 * What an add can break, one case per class of rule and per way to break it. The expectation is what full validation
 * says; the case passes only if the incremental validation says the same. The page "Incremental YANG Validation:
 * Add and Modify" lists these cases by name.
 */
#define DL_G1 "<grp><name>g1</name><want>w1</want><other>g2</other>"
static const struct dl_case dl_add_cases[] = {
    /* LOCAL */
    {"add: LOCAL leafref without target", DL_T(DL_I("i1", "a")), {DL_P "wcr", "x"}, E_BAD},
    {"add: LOCAL leafref with target", DL_T(DL_GATE "<wc-v>x</wc-v>"), {DL_P "wcr", "x"}, E_OK},
    /* LIST_SCOPE */
    {"add: LIST_SCOPE must counts the children, too few", DL_T("<grp><name>g1</name><mem><name>a</name></mem></grp>"),
        {DL_P "grp[name='g1']/need", "y"}, E_BAD},
    {"add: LIST_SCOPE must counts the children, enough", DL_T("<grp><name>g1</name><mem><name>a</name></mem>"
        "<mem><name>b</name></mem></grp>"), {DL_P "grp[name='g1']/need", "y"}, E_OK},
    {"add: LIST_SCOPE reader of a template, component missing",
        DL_T("<tpl><name>t1</name><comp><name>c1</name><cls>ok</cls></comp></tpl>"),
        {DL_P "tpl[name='t1']/ifc[name='i1']/hw", "c9"}, E_BAD},
    {"add: LIST_SCOPE reader of a template, component there",
        DL_T("<tpl><name>t1</name><comp><name>c1</name><cls>ok</cls></comp></tpl>"),
        {DL_P "tpl[name='t1']/ifc[name='i1']/hw", "c1"}, E_OK},
    /* BOUNDED */
    {"add: BOUNDED not() over a relative path finds what was added", DL_T(DL_G1 "<nx>y</nx></grp>"
        "<grp><name>g2</name><mem><name>a</name></mem></grp>"), {DL_P "grp[name='g2']/mem[name='w1']", NULL}, E_BAD},
    {"add: BOUNDED count() over a relative path finds what was added", DL_T(DL_G1 "<nc>y</nc></grp>"
        "<grp><name>g2</name><mem><name>a</name></mem></grp>"), {DL_P "grp[name='g2']/mem[name='w1']", NULL}, E_BAD},
    {"add: BOUNDED count() climbs on after a predicate, finds what was added", DL_T(DL_G1 "<mem><name>x</name></mem>"
        "<pc><np>y</np></pc></grp><grp><name>g2</name><mem><name>a</name></mem></grp>"),
        {DL_P "grp[name='g2']/mem[name='w1']", NULL}, E_BAD},
    {"add: BOUNDED creation-safe reader, an unrelated instance is added",
        DL_T(DL_I("i1", "good") DL_R("r", "<sel>i1</sel><m-val>y</m-val>")),
        {DL_P "item[name='i2']/val", "bad"}, E_OK},
    {"add: BOUNDED reader added, its target is missing", DL_T(DL_I("i1", "good")),
        {DL_P "r[name='r2']/sel", "nope", DL_P "r[name='r2']/m-exist", "y"}, E_BAD},
    /* UNBOUNDED */
    {"add: UNBOUNDED upper bound count over an absolute path, one too many",
        DL_T(DL_I("i1", "a") DL_I("i2", "a") DL_I("i3", "a") DL_R("r", "<m-cap>y</m-cap>")),
        {DL_P "item[name='i4']/val", "a"}, E_BAD},
    {"add: UNBOUNDED upper bound count over an absolute path, at the limit",
        DL_T(DL_I("i1", "a") DL_I("i2", "a") DL_R("r", "<m-cap>y</m-cap>")), {DL_P "item[name='i3']/val", "a"}, E_OK},
    {"add: UNBOUNDED lower bound count, an instance is added", DL_T(DL_I("i1", "a") DL_I("i2", "a")
        DL_R("r", "<m-count>y</m-count>")), {DL_P "item[name='i3']/val", "a"}, E_OK},
    {"add: UNBOUNDED reader added, leafref without target", DL_T(DL_I("i1", "a")), {DL_P "r[name='n']/lref", "nope"}, E_BAD},
    {"add: UNBOUNDED when over another instance, the gate is missing", DL_T(DL_I("i1", "a") DL_R("r", "")),
        {DL_P "r[name='r']/w-on", "v"}, E_BAD},
    {"add: UNBOUNDED when over another instance, the gate is there", DL_T(DL_GATE DL_R("r", "")),
        {DL_P "r[name='r']/w-on", "v"}, E_OK},
    {"add: UNBOUNDED must counts the sibling instances, alone", DL_T("<inner><a>a</a></inner>"),
        {DL_P "inner/x[name='x1']/chk", "y"}, E_BAD},
    {"add: UNBOUNDED must counts the earlier siblings, first one", DL_T(DL_I("i1", "a")),
        {DL_P "pos[name='a']/pp", "y"}, E_BAD},
    {"add: structure, max-elements of a list", DL_C("c-neg", "<un><name>a</name></un><un><name>b</name></un>"
        "<un><name>c</name></un>"), {"/dl:c-neg/un[name='d']", NULL}, E_BAD},
    {"add: structure, unique value twice", DL_C("c-neg", "<un><name>a</name><u>1</u></un>"),
        {"/dl:c-neg/un[name='b']/u", "1"}, E_BAD},
    /* CASCADE */
    {"add: CASCADE the when turns false, the node goes", DL_T(DL_G1 "<wn>y</wn></grp>"
        "<grp><name>g2</name><mem><name>a</name></mem></grp>"), {DL_P "grp[name='g2']/mem[name='w1']", NULL}, E_OK},
    {"add: CASCADE a default appears and another goes", DL_T(DL_I("i1", "a")) DZ_Z,
        {DL_P "item[name='gate']/val", "a"}, E_OK},
    /* the first adds, kept */
    {"add a leaf in front of the one a rule reads", DL_T("<grp><name>g1</name><nf>y</nf></grp>"
        "<grp><name>g2</name><lv>ok</lv></grp>"), {DL_P "grp[name='g2']/lv", "no"}, E_BAD},
};

/*
 * What a modify can break. A modified leaf always re-checks the rules that read it, whatever the class and whether
 * or not the rule is creation-safe.
 */
static const struct dl_case dl_modify_cases[] = {
    /* LOCAL */
    {"modify: LOCAL leafref target changes", DL_T(DL_GATE "<wc-v>a</wc-v><wcr>a</wcr>"), {DL_P "wc-v", "b"}, E_BAD},
    {"modify: LOCAL leafref and target change together", DL_T(DL_GATE "<wc-v>a</wc-v><wcr>a</wcr>"),
        {DL_P "wc-v", "b", DL_P "wcr", "b"}, E_OK},
    /* LIST_SCOPE */
    {"modify: LIST_SCOPE component class changes, an interface uses it",
        DL_T("<tpl><name>t1</name><comp><name>c1</name><cls>ok</cls></comp>"
        "<ifc><name>i1</name><hw>c1</hw></ifc></tpl>"), {DL_P "tpl[name='t1']/comp[name='c1']/cls", "no"}, E_BAD},
    {"modify: LIST_SCOPE component class changes, nothing uses it",
        DL_T("<tpl><name>t1</name><comp><name>c1</name><cls>ok</cls></comp><comp><name>c2</name><cls>ok</cls></comp>"
        "<ifc><name>i1</name><hw>c1</hw></ifc></tpl>"), {DL_P "tpl[name='t1']/comp[name='c2']/cls", "no"}, E_OK},
    /* BOUNDED */
    {"modify: BOUNDED must reads the value of the instance it picks",
        DL_T(DL_I("i1", "good") DL_R("r", "<sel>i1</sel><m-val>y</m-val>")), {DL_P "item[name='i1']/val", "bad"}, E_BAD},
    {"modify: BOUNDED must, an unrelated instance changes",
        DL_T(DL_I("i1", "good") DL_I("i2", "x") DL_R("r", "<sel>i1</sel><m-val>y</m-val>")),
        {DL_P "item[name='i2']/val", "bad"}, E_OK},
    {"modify: BOUNDED leafref to the value of the instance it picks",
        DL_T(DL_I("i1", "v1") DL_R("r", "<sel>i1</sel><dref>v1</dref>")), {DL_P "item[name='i1']/val", "v2"}, E_BAD},
    {"modify: BOUNDED not() over a relative path, the leaf it names changes",
        DL_T(DL_G1 "<nx>y</nx></grp><grp><name>g2</name><mem><name>a</name></mem></grp>"),
        {DL_P "grp[name='g1']/want", "a"}, E_BAD},
    /* UNBOUNDED */
    {"modify: UNBOUNDED must reads a leaf of a named instance",
        DL_T("<item><name>i1</name><dd>z</dd></item>" DL_R("r", "<m-dd>y</m-dd>")), {DL_P "item[name='i1']/dd", "y"}, E_BAD},
    {"modify: UNBOUNDED must, another instance changes",
        DL_T("<item><name>i1</name><dd>z</dd></item>" DL_I("i2", "a") DL_R("r", "<m-dd>y</m-dd>")),
        {DL_P "item[name='i2']/dd", "y"}, E_OK},
    {"modify: UNBOUNDED must reads a leaf of another list instance",
        DL_T("<grp><name>g1</name><mv>y</mv></grp><grp><name>g2</name><lv>ok</lv></grp>"),
        {DL_P "grp[name='g2']/lv", "no"}, E_BAD},
    {"modify: UNBOUNDED must reads a leaf of another list instance, a different instance changes",
        DL_T("<grp><name>g1</name><mv>y</mv><lv>a</lv></grp><grp><name>g2</name><lv>ok</lv></grp>"),
        {DL_P "grp[name='g1']/lv", "b"}, E_OK},
    {"modify: UNBOUNDED must reads the text of a container",
        DL_T("<inner><a>a</a><x><name>x1</name></x></inner>" DL_R("r", "<m-anc3>y</m-anc3>")),
        {DL_P "inner/a", "bad"}, E_BAD},
    {"modify: UNBOUNDED value keyed count, a value leaves its group",
        DL_C("c-vk", "<vk><name>a</name><grp>g</grp></vk><vk><name>b</name><grp>g</grp></vk>"
        "<vk><name>c</name><grp>g</grp></vk>"), {"/dl:c-vk/vk[name='c']/grp", "h"}, E_BAD},
    /* CASCADE */
    {"modify: CASCADE the when turns false, the node is dropped, a reader needs it",
        DL_T(DL_R("r", "<sw>on</sw><dep>x</dep><m-dep>y</m-dep>")), {DL_P "r[name='r']/sw", "off"}, E_BAD},
    {"modify: CASCADE the when turns false, the node is dropped, nothing reads it",
        DL_T(DL_R("r", "<sw>on</sw><dep>x</dep>")), {DL_P "r[name='r']/sw", "off"}, E_OK},
};

/*
 * Data an application stored without validating can hold a default node whose "when" never held. Whatever the edit
 * touches, full validation drops it, so the incremental pass has to as well.
 */
static void
test_stale_default_unrelated(void **state)
{
    const struct lys_module *mod;
    struct lyd_node *before = NULL, *after = NULL, *full = NULL, *incr = NULL, *diff = NULL, *val_diff = NULL, *node;
    uint32_t i;

    dl_setup(state);
    mod = ly_ctx_get_module_implemented(UTEST_LYCTX, "dl");
    assert_non_null(mod);
    assert_int_equal(LY_SUCCESS, lyd_parse_data_mem(UTEST_LYCTX, DL_T(DL_GATE DL_R("r", "<w-on>v</w-on>")) DL_LONE, LYD_XML,
            LYD_PARSE_ONLY, 0, &before));
    assert_int_equal(LY_SUCCESS, lyd_new_implicit_all(&before, UTEST_LYCTX, LYD_IMPLICIT_NO_STATE, NULL));
    assert_int_equal(LY_SUCCESS, lyd_find_path(before, DL_P "r[name='r']/dw", 0, &node));
    /* the leaf the default depends on is gone, no validation ran, the default stays with its "when" false */
    assert_int_equal(LY_SUCCESS, lyd_find_path(before, DL_P "r[name='r']/w-on", 0, &node));
    lyd_free_tree(node);
    assert_int_equal(LY_SUCCESS, lyd_dup_siblings(before, NULL, LYD_DUP_RECURSIVE | LYD_DUP_WITH_FLAGS, &after));
    assert_int_equal(LY_SUCCESS, lyd_new_path(after, UTEST_LYCTX, "/dl:lone/li[name='l2']", NULL, 0, NULL));

    assert_int_equal(LY_SUCCESS, lyd_dup_siblings(after, NULL, LYD_DUP_RECURSIVE | LYD_DUP_WITH_FLAGS, &full));
    assert_int_equal(LY_SUCCESS, lyd_validate_module(&full, mod, LYD_VALIDATE_NOT_FINAL, NULL));
    assert_int_equal(LY_SUCCESS, lyd_validate_module_final(full, mod, 0));
    assert_true(lyd_find_path(full, DL_P "r[name='r']/dw", 0, NULL) != LY_SUCCESS);

    for (i = 0; i < sizeof incr_opt_sets / sizeof *incr_opt_sets; ++i) {
        assert_int_equal(LY_SUCCESS, lyd_diff_siblings(before, after, 0, &diff));
        assert_int_equal(LY_SUCCESS, lyd_dup_siblings(after, NULL, LYD_DUP_RECURSIVE | LYD_DUP_WITH_FLAGS, &incr));
        assert_int_equal(LY_SUCCESS, lyd_validate_module_incr(&incr, mod, diff,
                incr_opt_sets[i] | LYD_VALIDATE_NOT_FINAL, &val_diff));
        if (val_diff) {
            assert_int_equal(LY_SUCCESS, lyd_diff_merge_all(&diff, val_diff, 0));
            lyd_free_all(val_diff);
            val_diff = NULL;
        }
        assert_int_equal(LY_SUCCESS, lyd_validate_module_incr_final(incr, mod, diff, incr_opt_sets[i]));
        assert_true(lyd_find_path(incr, DL_P "r[name='r']/dw", 0, NULL) != LY_SUCCESS);
        lyd_free_siblings(incr);
        incr = NULL;
        lyd_free_siblings(diff);
        diff = NULL;
    }

    lyd_free_siblings(full);
    lyd_free_siblings(after);
    lyd_free_siblings(before);
    ly_err_clean((struct ly_ctx *)UTEST_LYCTX, NULL);
    dl_done();
}

static void
test_add_relative_readers(void **state)
{
    dl_run(state, dl_add_cases, sizeof dl_add_cases / sizeof *dl_add_cases);
}

static void
test_modify_rules(void **state)
{
    dl_run(state, dl_modify_cases, sizeof dl_modify_cases / sizeof *dl_modify_cases);
}

/*
 * The rules of the product schema, one shape each. The names are not the product names, the expressions are. Every
 * case is an add or a modify, and the expectation is what full validation says.
 */
#define PR_P "/dl:pr/"
#define PR_T(x) DL_C("pr", x)
#define PR_SH "<shaper><name>s1</name><single>y</single></shaper><shaper><name>s2</name><two>y</two></shaper>"
#define PR_Q(d, sh) "<qprof><name>q1</name><queues><queue><name>a</name>" d "<shaper-name>" sh "</shaper-name></queue></queues></qprof>"
#define PR_TM "<tmpl><name>t1</name><ifc><name>i1</name><v4>y</v4></ifc></tmpl><tmpl><name>t2</name><ifc><name>i1</name><v4>y</v4></ifc>" \
        "<ifc><name>i2</name><v4>y</v4></ifc></tmpl><tmpl><name>t3</name><ifc><name>i9</name><v4>y</v4></ifc></tmpl>"
#define PR_ONU(x) "<onu><name>o1</name><tref>t1</tref><term><name>x</name>" x "</term></onu>"
#define PR_REV(c, r) "<comp><name>c1</name><revs>" c r "</revs></comp>"
#define PR_TP(x) "<tp><name>p1</name><tcs>" x "</tcs></tp>"
#define PR_TC(n, d) "<tc><position>" n "</position><duration>" d "</duration></tc>"
#define PR_TS "<tsb><name>b1</name><pk><name>k1</name><fmt xmlns:dl=\"urn:tests:dl\">dl:fmt-ssh</fmt></pk></tsb><tsb><name>b2</name><pk><name>k2</name><fmt xmlns:dl=\"urn:tests:dl\">dl:fmt-other</fmt></pk></tsb>"
static const struct dl_case dl_prod_cases[] = {
    /* the queue shaper must: not(boolean(dual)) and boolean(shaper/single), or the same with dual and two */
    {"product QoS: dual added, the shaper has only a single bucket", PR_T(PR_SH PR_Q("", "s1")),
        {PR_P "qprof[name='q1']/queues/queue[name='a']/dual", "y"}, E_BAD},
    {"product QoS: dual added and the shaper moved to the two bucket one", PR_T(PR_SH PR_Q("", "s1")),
        {PR_P "qprof[name='q1']/queues/queue[name='a']/dual", "y", PR_P "qprof[name='q1']/queues/queue[name='a']/shaper-name", "s2"}, E_OK},
    {"product QoS: dual removed, the shaper has only a two bucket", PR_T(PR_SH PR_Q("<dual>y</dual>", "s2")),
        {"-" PR_P "qprof[name='q1']/queues/queue[name='a']/dual"}, E_BAD},
    {"product QoS: single bucket removed from the shaper in use", PR_T(PR_SH PR_Q("", "s1")),
        {"-" PR_P "shaper[name='s1']/single"}, E_BAD},
    {"product QoS: two bucket added to the shaper in use, the single one stays", PR_T(PR_SH PR_Q("", "s1")),
        {PR_P "shaper[name='s1']/two", "y"}, E_OK},
    {"product QoS: shaper moved to one with only a two bucket", PR_T(PR_SH PR_Q("", "s1")),
        {PR_P "qprof[name='q1']/queues/queue[name='a']/shaper-name", "s2"}, E_BAD},
    {"product QoS: a shaper nobody uses gets a bucket", PR_T(PR_SH "<shaper><name>s3</name></shaper>" PR_Q("", "s1")),
        {PR_P "shaper[name='s3']/two", "y"}, E_OK},
    /* when over an absolute path, bounded and creation-safe */
    {"product QoS: BOUNDED when, burst added, the shaper has a single bucket",
        PR_T(PR_SH "<bq><name>b</name><sref>s1</sref></bq>"), {PR_P "bq[name='b']/burst", "y"}, E_OK},
    {"product QoS: BOUNDED when, burst added, the shaper has no single bucket",
        PR_T(PR_SH "<bq><name>b</name><sref>s2</sref></bq>"), {PR_P "bq[name='b']/burst", "y"}, E_BAD},
    {"product QoS: CASCADE BOUNDED when, single bucket removed under a burst, the node is dropped",
        PR_T(PR_SH "<bq><name>b</name><sref>s1</sref><burst>y</burst></bq>"), {"-" PR_P "shaper[name='s1']/single"}, E_OK},
    {"product QoS: CASCADE BOUNDED when, sref moved under a burst, the node is dropped",
        PR_T(PR_SH "<bq><name>b</name><sref>s1</sref><burst>y</burst></bq>"), {PR_P "bq[name='b']/sref", "s2"}, E_OK},
    /* ancestor:: axis inside a predicate */
    {"product ONU: interface not in the template of the ONU", PR_T(PR_TM PR_ONU("")),
        {PR_P "onu[name='o1']/term[name='x']/ipif", "i2"}, E_BAD},
    {"product ONU: interface in the template of the ONU", PR_T(PR_TM PR_ONU("")),
        {PR_P "onu[name='o1']/term[name='x']/ipif", "i1"}, E_OK},
    {"product ONU: the address of the interface is removed from the template", PR_T(PR_TM PR_ONU("<ipif>i1</ipif>")),
        {"-" PR_P "tmpl[name='t1']/ifc[name='i1']/v4"}, E_BAD},
    {"product ONU: the v4 address is removed, a v6 one stays", PR_T(PR_TM PR_ONU("<ipif>i1</ipif>")),
        {PR_P "tmpl[name='t1']/ifc[name='i1']/v6", "y", "-" PR_P "tmpl[name='t1']/ifc[name='i1']/v4"}, E_OK},
    {"product ONU: the ONU moves to a template without the interface", PR_T(PR_TM PR_ONU("<ipif>i1</ipif>")),
        {PR_P "onu[name='o1']/tref", "t3"}, E_BAD},
    {"product ONU: the ONU moves to a template with the interface", PR_T(PR_TM PR_ONU("<ipif>i1</ipif>")),
        {PR_P "onu[name='o1']/tref", "t2"}, E_OK},
    {"product ONU: LOCAL leafref to a sibling instance, missing", PR_T(PR_TM PR_ONU("")),
        {PR_P "onu[name='o1']/term[name='y']/peer", "nope"}, E_BAD},
    {"product ONU: LOCAL leafref to a sibling instance, there", PR_T(PR_TM PR_ONU("")),
        {PR_P "onu[name='o1']/term[name='y']/peer", "x"}, E_OK},
    /* when with boolean(), derived-from() and count() over the siblings */
    {"product SWM: when boolean(capability=x), the leaf is added and the capability fits",
        PR_T(PR_REV("<cap>alias</cap>", "<rev><name>r1</name><state>available</state></rev>")),
        {PR_P "comp[name='c1']/revs/rev[name='r1']/alias", "y"}, E_OK},
    {"product SWM: when boolean(capability=x), the leaf is added and the capability does not fit",
        PR_T(PR_REV("<cap>other</cap>", "<rev><name>r1</name><state>available</state></rev>")),
        {PR_P "comp[name='c1']/revs/rev[name='r1']/alias", "y"}, E_BAD},
    {"product SWM: CASCADE when boolean(capability=x), the capability changes under the leaf, the node is dropped",
        PR_T(PR_REV("<cap>alias</cap>", "<rev><name>r1</name><state>available</state><alias>y</alias></rev>")),
        {PR_P "comp[name='c1']/revs/cap", "other"}, E_OK},
    {"product SWM: when with a state test, the state fits",
        PR_T(PR_REV("<cap>act</cap>", "<rev><name>r1</name><state>in-use</state></rev>")),
        {PR_P "comp[name='c1']/revs/rev[name='r1']/act", "y"}, E_OK},
    {"product SWM: when with a state test, the state does not fit",
        PR_T(PR_REV("<cap>act</cap>", "<rev><name>r1</name><state>new</state></rev>")),
        {PR_P "comp[name='c1']/revs/rev[name='r1']/act", "y"}, E_BAD},
    {"product SWM: CASCADE when with a state test, the state changes under the leaf, the node is dropped",
        PR_T(PR_REV("<cap>act</cap>", "<rev><name>r1</name><state>available</state><act>y</act></rev>")),
        {PR_P "comp[name='c1']/revs/rev[name='r1']/state", "new"}, E_OK},
    {"product SWM: CASCADE plain derived-from(), capability changes under the leaf, the node is dropped",
        PR_T(PR_REV("<dcap xmlns:dl=\"urn:tests:dl\">dl:cap-sub</dcap>", "<rev><name>r1</name><state>available</state><fin>y</fin></rev>")),
        {PR_P "comp[name='c1']/revs/dcap", "cap-other"}, E_OK},
    {"product SWM: derived-from() and count()=0, download added, nothing downloads",
        PR_T(PR_REV("<dcap xmlns:dl=\"urn:tests:dl\">dl:cap-sub</dcap>", "<rev><name>r1</name><state>available</state></rev>")),
        {PR_P "comp[name='c1']/revs/download", "y"}, E_OK},
    {"product SWM: derived-from() and count()=0, download added while a revision downloads",
        PR_T(PR_REV("<dcap xmlns:dl=\"urn:tests:dl\">dl:cap-sub</dcap>", "<rev><name>r1</name><state>downloading</state></rev>")),
        {PR_P "comp[name='c1']/revs/download", "y"}, E_BAD},
    {"product SWM: CASCADE count()=0, a revision starts to download under the leaf, the node is dropped",
        PR_T(PR_REV("<dcap xmlns:dl=\"urn:tests:dl\">dl:cap-sub</dcap>", "<rev><name>r1</name><state>available</state></rev><download>y</download>")),
        {PR_P "comp[name='c1']/revs/rev[name='r1']/state", "downloading"}, E_OK},
    {"product SWM: CASCADE count()=0, a revision that downloads is added under the leaf, the node is dropped",
        PR_T(PR_REV("<dcap xmlns:dl=\"urn:tests:dl\">dl:cap-sub</dcap>", "<rev><name>r1</name><state>available</state></rev><download>y</download>")),
        {PR_P "comp[name='c1']/revs/rev[name='r2']/state", "downloading"}, E_OK},
    {"product SWM: count()=0, a revision that does not download is added under the leaf",
        PR_T(PR_REV("<dcap xmlns:dl=\"urn:tests:dl\">dl:cap-sub</dcap>", "<rev><name>r1</name><state>available</state></rev><download>y</download>")),
        {PR_P "comp[name='c1']/revs/rev[name='r2']/state", "available"}, E_OK},
    {"product SWM: CASCADE derived-from(), capability changes under the download leaf, the node is dropped",
        PR_T(PR_REV("<dcap xmlns:dl=\"urn:tests:dl\">dl:cap-sub</dcap>", "<rev><name>r1</name><state>available</state></rev><download>y</download>")),
        {PR_P "comp[name='c1']/revs/dcap", "cap-other"}, E_OK},
    /* a list keyed by position, and rules that read the leaf named position */
    {"product tone: the next position is added", PR_T(PR_TP(PR_TC("1", "a") PR_TC("2", "b"))),
        {PR_P "tp[name='p1']/tcs/tc[position='3']/duration", "c"}, E_OK},
    {"product tone: a position is added after a gap", PR_T(PR_TP(PR_TC("1", "a") PR_TC("2", "b"))),
        {PR_P "tp[name='p1']/tcs/tc[position='5']/duration", "c"}, E_BAD},
    {"product tone: repetition added, the last component is not continuous", PR_T(PR_TP(PR_TC("1", "a") PR_TC("2", "b"))),
        {PR_P "tp[name='p1']/tcs/rb", "y"}, E_OK},
    {"product tone: repetition added, the last component is continuous", PR_T(PR_TP(PR_TC("1", "a") PR_TC("2", "continuous"))),
        {PR_P "tp[name='p1']/tcs/rb", "y"}, E_BAD},
    {"product tone: repetition added, only one component", PR_T(PR_TP(PR_TC("1", "a"))),
        {PR_P "tp[name='p1']/tcs/rb", "y"}, E_BAD},
    {"product tone: CASCADE the last component becomes continuous under the repetition, the node is dropped",
        PR_T(PR_TP(PR_TC("1", "a") PR_TC("2", "b") "<rb>y</rb>")),
        {PR_P "tp[name='p1']/tcs/tc[position='2']/duration", "continuous"}, E_OK},
    {"product tone: CASCADE a continuous component is added last under the repetition, the node is dropped",
        PR_T(PR_TP(PR_TC("1", "a") PR_TC("2", "b") "<rb>y</rb>")),
        {PR_P "tp[name='p1']/tcs/tc[position='3']/duration", "continuous"}, E_OK},
    /* deref() with a predicate that has not(derived-from-or-self()) inside */
    {"product truststore: the format of a key in use changes", PR_T(PR_TS "<usr><name>u1</name><ref>b1</ref></usr>"),
        {PR_P "tsb[name='b1']/pk[name='k1']/fmt", "fmt-other"}, E_BAD},
    {"product truststore: a key with another format is added to the bag in use", PR_T(PR_TS "<usr><name>u1</name><ref>b1</ref></usr>"),
        {PR_P "tsb[name='b1']/pk[name='k3']/fmt", "fmt-other"}, E_BAD},
    {"product truststore: a key with the right format is added to the bag in use", PR_T(PR_TS "<usr><name>u1</name><ref>b1</ref></usr>"),
        {PR_P "tsb[name='b1']/pk[name='k3']/fmt", "fmt-ssh"}, E_OK},
    {"product truststore: a bag with another format is not used, its key changes", PR_T(PR_TS "<usr><name>u1</name><ref>b1</ref></usr>"),
        {PR_P "tsb[name='b2']/pk[name='k2']/fmt", "fmt-ssh"}, E_OK},
    {"product truststore: a user is added on the good bag", PR_T(PR_TS "<usr><name>u1</name><ref>b1</ref></usr>"),
        {PR_P "usr[name='u2']/ref", "b1"}, E_OK},
    {"product truststore: a user is added on the bag with another format", PR_T(PR_TS "<usr><name>u1</name><ref>b1</ref></usr>"),
        {PR_P "usr[name='u2']/ref", "b2"}, E_BAD},
    {"product truststore: a user moves to the bag with another format", PR_T(PR_TS "<usr><name>u1</name><ref>b1</ref></usr>"),
        {PR_P "usr[name='u1']/ref", "b2"}, E_BAD},
};

static void
test_product_shapes(void **state)
{
    dl_run(state, dl_prod_cases, sizeof dl_prod_cases / sizeof *dl_prod_cases);
}

static void
test_del_yang_probe(void **state)
{
    dl_run(state, dl_probe_cases, sizeof dl_probe_cases / sizeof *dl_probe_cases);
}

static void
test_del_ancestor_reader(void **state)
{
    dl_run(state, dl_ancestor_cases, sizeof dl_ancestor_cases / sizeof *dl_ancestor_cases);
}

/**
 * @brief Paths of the nodes an edit can delete.
 *
 * Keys cannot go on their own and defaults are not stored, every other node counts: instances, containers and leaves.
 *
 * @param[in] inst_only Keep only list and leaf-list instances and containers.
 */
static char **
dl_paths(const struct lyd_node *tree, ly_bool inst_only, uint32_t *count)
{
    const struct lyd_node *top, *elem;
    char **paths = NULL;

    *count = 0;
    LY_LIST_FOR(tree, top) {
        LYD_TREE_DFS_BEGIN(top, elem) {
            if (!(elem->flags & LYD_DEFAULT) && !(elem->schema->flags & LYS_KEY) &&
                    (!inst_only || (elem->schema->nodetype & (LYS_LIST | LYS_LEAFLIST | LYS_CONTAINER)))) {
                paths = realloc(paths, (*count + 1) * sizeof *paths);
                assert_non_null(paths);
                paths[(*count)++] = lyd_path(elem, LYD_PATH_STD, NULL, 0);
                assert_non_null(paths[*count - 1]);
            }
            LYD_TREE_DFS_END(top, elem);
        }
    }
    return paths;
}

/**
 * @brief Delete @p path unless an earlier delete already took it along.
 *
 * @return Whether it was there.
 */
static ly_bool
dl_drop(struct lyd_node **tree, const char *path)
{
    struct ly_set *set = NULL;
    ly_bool found;

    assert_int_equal(LY_SUCCESS, lyd_find_xpath(*tree, path, &set));
    found = (set->count == 1);
    ly_set_free(set, NULL);
    if (found) {
        drop_node(tree, path);
    }
    return found;
}

/**
 * @brief Delete nodes of a tree holding every reader, and let the full validation say what breaks.
 *
 * Nothing is predicted here, which is the point: a reader the hand-written cases missed still shows as a verdict
 * or a tree that differs between the two validators. Every single node goes, then every pair of instances, then
 * seeded random sets of up to four nodes.
 */
static void
test_del_sweep(void **state)
{
    struct lyd_node *before, *after;
    char **all, **inst;
    uint32_t all_count, inst_count, i, j, k, n, seed, edits, rejected = 0, runs = 0;
    LY_ERR rc;

    dl_setup(state);
    before = parse_valid(state, dl_xml);
    all = dl_paths(before, 0, &all_count);
    inst = dl_paths(before, 1, &inst_count);

    /* every node alone */
    for (i = 0; i < all_count; ++i) {
        assert_int_equal(LY_SUCCESS, lyd_dup_siblings(before, NULL, LYD_DUP_RECURSIVE | LYD_DUP_WITH_FLAGS, &after));
        drop_node(&after, all[i]);
        check_same(state, before, after, 1, &rc);
        rejected += rc ? 1 : 0;
        ++runs;
        lyd_free_siblings(after);
    }
    print_message("[  MSG     ] sweep, single delete: %u nodes, %u rejected\n", runs, rejected);
    assert_true(runs > 100);
    assert_true(rejected > 20);
    assert_true(runs - rejected > 20);

    /* every pair of instances and containers */
    rejected = 0;
    runs = 0;
    for (i = 0; i < inst_count; ++i) {
        for (j = i + 1; j < inst_count; ++j) {
            assert_int_equal(LY_SUCCESS, lyd_dup_siblings(before, NULL, LYD_DUP_RECURSIVE | LYD_DUP_WITH_FLAGS, &after));
            if (dl_drop(&after, inst[i]) && dl_drop(&after, inst[j])) {
                check_same(state, before, after, 1, &rc);
                rejected += rc ? 1 : 0;
                ++runs;
            }
            lyd_free_siblings(after);
        }
    }
    print_message("[  MSG     ] sweep, pairs: %u edits, %u rejected\n", runs, rejected);
    assert_true(runs > 500);
    assert_true(rejected > 100);

    /* random sets, anything may go together */
    rejected = 0;
    runs = 0;
    for (seed = 1; seed <= DL_SWEEP_SEEDS; ++seed) {
        srand(seed);
        assert_int_equal(LY_SUCCESS, lyd_dup_siblings(before, NULL, LYD_DUP_RECURSIVE | LYD_DUP_WITH_FLAGS, &after));
        edits = 0;
        n = 2 + rand() % 3;
        for (k = 0; k < n; ++k) {
            edits += dl_drop(&after, all[rand() % all_count]);
        }
        if (edits) {
            check_same(state, before, after, 1, &rc);
            rejected += rc ? 1 : 0;
            ++runs;
        }
        lyd_free_siblings(after);
    }
    print_message("[  MSG     ] sweep, random sets: %u edits, %u rejected\n", runs, rejected);
    assert_true(runs > DL_SWEEP_SEEDS / 2);

    for (i = 0; i < all_count; ++i) {
        free(all[i]);
    }
    for (i = 0; i < inst_count; ++i) {
        free(inst[i]);
    }
    free(all);
    free(inst);
    lyd_free_siblings(before);
    dl_done();
}

/**
 * @brief A rule that reads data, and whether some single delete is known to break it.
 */
struct dl_reader {
    const char *name;
    const char *keep[3];    /**< what must stay for the rule to be there at all */
    ly_bool single;         /**< some single delete breaks it */
};

#define DL_RD(n, single) {n, {"/dl:top/r[name='" n "']"}, single}

static const struct dl_reader dl_readers[] = {
    DL_RD("r-lref", 1), DL_RD("r-tref", 1), DL_RD("r-uref", 1), DL_RD("r-lrefs", 1), DL_RD("r-dref", 1),
    DL_RD("r-mexist", 1), DL_RD("r-mval", 1), DL_RD("r-mcount", 1), DL_RD("r-msum", 1), DL_RD("r-mfirst", 1),
    DL_RD("r-mou1", 1), DL_RD("r-moul", 1), DL_RD("r-mdd", 1), DL_RD("r-manc", 1), DL_RD("r-manc2", 1),
    /* only emptying the container breaks it, which takes both lists, and a when only drops its node */
    DL_RD("r-mnp", 0), DL_RD("r-won", 0),
    {"kr", {"/dl:top/kr[k='i3']"}, 1},
    {"wr", {"/dl:top/wr[name='w1']", "/dl:top/r[name='r-won']"}, 1},
    {"wcr", {"/dl:top/wcr"}, 1},
    {"st", {"/dl:st"}, 1},
    {"m1", {"/dm:mtop/mr[name='m1']"}, 1},
    {"m2", {"/dm:mtop/mr[name='m2']"}, 1},
    {"m3", {"/dm:mtop/mr[name='m3']"}, 1},
    {"aug-ref", {"/dl:top/item[name='i4']/dm:aug-ref"}, 1},
};

/** @brief every rule the tree holds, so a variant can drop all but one */
static const char *const dl_reader_paths[] = {
    "/dl:top/r[name='r-lref']", "/dl:top/r[name='r-tref']", "/dl:top/r[name='r-uref']", "/dl:top/r[name='r-lrefs']",
    "/dl:top/r[name='r-dref']", "/dl:top/r[name='r-mexist']", "/dl:top/r[name='r-mval']", "/dl:top/r[name='r-mcount']",
    "/dl:top/r[name='r-msum']", "/dl:top/r[name='r-mfirst']", "/dl:top/r[name='r-mou1']", "/dl:top/r[name='r-moul']",
    "/dl:top/r[name='r-mdd']", "/dl:top/r[name='r-mnp']", "/dl:top/r[name='r-manc']", "/dl:top/r[name='r-manc2']",
    "/dl:top/r[name='r-won']", "/dl:top/kr[k='i3']", "/dl:top/wr[name='w1']", "/dl:top/wcr", "/dl:st",
    "/dm:mtop/mr[name='m1']", "/dm:mtop/mr[name='m2']", "/dm:mtop/mr[name='m3']",
    "/dl:top/item[name='i4']/dm:aug-ref",
};

/**
 * @brief Delete every node of a tree in which exactly one rule reads the data.
 *
 * The sweep of everything at once can hide a missed rule behind another one that rejects the same edit, because the
 * two validators then agree on the verdict. With one rule left, nothing else can reject, so a delete that rule
 * should have caught is the only thing that differs.
 */
static void
test_del_sweep_by_reader(void **state)
{
    struct lyd_node *base, *variant, *after;
    char **all;
    uint32_t r, i, j, k, count, rejected;
    ly_bool keep;
    LY_ERR rc;

    dl_setup(state);
    base = parse_valid(state, dl_xml);

    for (r = 0; r < sizeof dl_readers / sizeof *dl_readers; ++r) {
        assert_int_equal(LY_SUCCESS, lyd_dup_siblings(base, NULL, LYD_DUP_RECURSIVE | LYD_DUP_WITH_FLAGS, &variant));
        for (i = 0; i < sizeof dl_reader_paths / sizeof *dl_reader_paths; ++i) {
            keep = 0;
            for (k = 0; dl_readers[r].keep[k]; ++k) {
                keep |= !strcmp(dl_readers[r].keep[k], dl_reader_paths[i]);
            }
            if (!keep) {
                dl_drop(&variant, dl_reader_paths[i]);
            }
        }
        settle(state, &variant);

        all = dl_paths(variant, 0, &count);
        rejected = 0;
        for (j = 0; j < count; ++j) {
            assert_int_equal(LY_SUCCESS, lyd_dup_siblings(variant, NULL, LYD_DUP_RECURSIVE | LYD_DUP_WITH_FLAGS, &after));
            drop_node(&after, all[j]);
            check_same(state, variant, after, 1, &rc);
            rejected += rc ? 1 : 0;
            lyd_free_siblings(after);
            free(all[j]);
        }
        print_message("[  MSG     ] only %s: %u nodes, %u rejected\n", dl_readers[r].name, count, rejected);
        if (dl_readers[r].single) {
            assert_true(rejected > 0);
        }
        free(all);
        lyd_free_siblings(variant);
    }

    lyd_free_siblings(base);
    dl_done();
}

int
main(void)
{
    const struct CMUnitTest tests[] = {
        UTEST(test_local_when),
        UTEST(test_local_must),
        UTEST(test_list_scope),
        UTEST(test_bounded),
        UTEST(test_leafref),
        UTEST(test_unbounded),
        UTEST(test_shared_count_create),
        UTEST(test_shared_count_replace),
        UTEST(test_shared_count_delete),
        UTEST(test_shared_count_filter),
        UTEST(test_random_edits),
        UTEST(test_toplevel_default),
        UTEST(test_stale_default),
        UTEST(test_dflt_when_remote),
        UTEST(test_stats),
        UTEST(test_shallow_delete),
        UTEST(test_shallow_gate),
        UTEST(test_shallow_levels),
        UTEST(test_schema_change),
        UTEST(test_aug_add),
        UTEST(test_aug_delete),
        UTEST(test_aug_when_flip),
        UTEST(test_aug_cross_module),
        UTEST(test_aug_when_cascade),
        UTEST(test_aug_when_cascade_leafref),
        UTEST(test_aug_when_create),
        UTEST(test_aug_dflt_replace),
        UTEST(test_aug_dflt_case_in_dflt),
        UTEST(test_aug_dflt_case_back),
        UTEST(test_aug_first_node_func),
        UTEST(test_aug_deep_delete),
        UTEST(test_aug_module_order),
        UTEST(test_aug_instance_identifier),
        UTEST(test_aug_random_edits),
        UTEST(test_del_cases),
        UTEST(test_del_sweep),
        UTEST(test_del_sweep_by_reader),
        UTEST(test_del_childless_diff),
        UTEST(test_del_ancestor_reader),
        UTEST(test_del_yang_probe),
        UTEST(test_add_relative_readers),
        UTEST(test_modify_rules),
        UTEST(test_product_shapes),
        UTEST(test_stale_default_unrelated),
    };

    return cmocka_run_group_tests(tests, NULL, NULL);
}
