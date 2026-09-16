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
    const struct lys_module *mod;
    char *full_str = NULL, *incr_str = NULL;
    uint64_t fallbacks_before = 0, fallbacks_after = 0;
    LY_ERR rc_full, rc_incr;

    mod = ly_ctx_get_module_implemented(UTEST_LYCTX, "a");
    assert_non_null(mod);
    lyd_validate_incr_stats(UTEST_LYCTX, NULL, &fallbacks_before);

    assert_int_equal(LY_SUCCESS, lyd_diff_siblings(before, after, 0, &diff));
    assert_int_equal(LY_SUCCESS, lyd_dup_siblings(after, NULL, LYD_DUP_RECURSIVE | LYD_DUP_WITH_FLAGS, &full));
    assert_int_equal(LY_SUCCESS, lyd_dup_siblings(after, NULL, LYD_DUP_RECURSIVE | LYD_DUP_WITH_FLAGS, &incr));

    /* split into the two passes the same way sysrepo drives them */
    rc_full = lyd_validate_module(&full, mod, LYD_VALIDATE_NOT_FINAL, NULL);
    if (!rc_full) {
        rc_full = lyd_validate_module_final(full, mod, 0);
    }
    ly_err_clean((struct ly_ctx *)UTEST_LYCTX, NULL);

    rc_incr = lyd_validate_module_incr(&incr, mod, diff, LYD_VALIDATE_NOT_FINAL, NULL);
    if (!rc_incr) {
        rc_incr = lyd_validate_module_incr_final(incr, mod, diff, 0);
    }
    ly_err_clean((struct ly_ctx *)UTEST_LYCTX, NULL);

    assert_int_equal(rc_full, rc_incr);

    /* a fallback would make the comparison above prove nothing about the incremental path */
    lyd_validate_incr_stats(UTEST_LYCTX, NULL, &fallbacks_after);
    if (!allow_fallback) {
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
    };

    return cmocka_run_group_tests(tests, NULL, NULL);
}
