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

/**
 * @brief Validate @p data both ways and require the two runs to agree.
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
    uint32_t i, mod_count;
    ly_bool self_deleted = 0;
    char full_msg[256], incr_msg[256];
    LY_ERR rc_full, rc_incr;

    for (mod_count = 0; check_mods[mod_count]; ++mod_count) {
        mods[mod_count] = ly_ctx_get_module_implemented(UTEST_LYCTX, check_mods[mod_count]);
        assert_non_null(mods[mod_count]);
    }
    lyd_validate_incr_stats(UTEST_LYCTX, NULL, &fallbacks_before);

    assert_int_equal(LY_SUCCESS, lyd_diff_siblings(before, after, 0, &diff));
    assert_int_equal(LY_SUCCESS, lyd_dup_siblings(after, NULL, LYD_DUP_RECURSIVE | LYD_DUP_WITH_FLAGS, &full));
    assert_int_equal(LY_SUCCESS, lyd_dup_siblings(after, NULL, LYD_DUP_RECURSIVE | LYD_DUP_WITH_FLAGS, &incr));

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

    /* the changes the validation makes itself (autodeleted when, new defaults) are merged into the edit diff
     * before the next module and the final pass, as sysrepo does with its notify diff */
    rc_incr = LY_SUCCESS;
    for (i = 0; !rc_incr && (i < mod_count); ++i) {
        struct lyd_node *val_diff = NULL;

        rc_incr = lyd_validate_module_incr(&incr, mods[i], diff, LYD_VALIDATE_NOT_FINAL, &val_diff);
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
        rc_incr = lyd_validate_module_incr_final(incr, mods[i], diff, 0);
    }
    snprintf(incr_msg, sizeof incr_msg, "%s", ly_err_last(UTEST_LYCTX) ? ly_err_last(UTEST_LYCTX)->msg : "-");
    ly_err_clean((struct ly_ctx *)UTEST_LYCTX, NULL);

    if (rc_full != rc_incr) {
        char *diff_str = NULL;

        lyd_print_mem(&diff_str, diff, LYD_XML, LYD_PRINT_WITHSIBLINGS);
        print_message("[  MSG     ] full %d (%s) vs incremental %d (%s), diff:\n%s\n", rc_full, full_msg, rc_incr,
                incr_msg, diff_str);
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
        assert_int_equal(LY_SUCCESS, lyd_print_mem(&full_str, full, LYD_XML, LYD_PRINT_WITHSIBLINGS));
        assert_int_equal(LY_SUCCESS, lyd_print_mem(&incr_str, incr, LYD_XML, LYD_PRINT_WITHSIBLINGS));
        assert_string_equal(full_str, incr_str);
    }

    if (rc_out) {
        *rc_out = rc_full;
    }

    free(full_str);
    free(incr_str);
    lyd_free_siblings(full);
    lyd_free_siblings(incr);
    lyd_free_siblings(diff);
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
        UTEST(test_stats),
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
    };

    return cmocka_run_group_tests(tests, NULL, NULL);
}
