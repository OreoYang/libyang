/**
 * @file validation_incr.c
 * @brief Incremental validation driven by an edit diff.
 *
 * Copyright (c) 2026 Vecima Networks Inc.
 *
 * This source code is licensed under BSD 3-Clause License (the "License").
 * You may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *     https://opensource.org/licenses/BSD-3-Clause
 */

#define _GNU_SOURCE

#include <assert.h>
#include <stdint.h>
#include <stdlib.h>
#include <string.h>

#include "diff.h"
#include "ly_common.h"
#include "parser_data.h"
#include "plugins_exts/metadata.h"
#include "plugins_types.h"
#include "set.h"
#include "tree_data.h"
#include "tree_data_internal.h"
#include "tree_schema.h"
#include "validation.h"
#include "validation_deps.h"

/**
 * @brief Values of one value-keyed node that the edit created, deleted or replaced.
 *
 * A value-keyed constraint reads nothing but the instances sharing one value, so only the values listed here can
 * have changed its result, see ::lyd_val_constraint.value_keyed.
 */
struct lyd_val_incr_valset {
    const struct lysc_node *snode;  /**< value-keyed node the values belong to */
    const char **vals;              /**< values, borrowed from the edit diff */
    uint32_t val_count;
    ly_bool unknown;                /**< the diff touched the node without spelling out its value */
};

/**
 * @brief Everything the edit diff tells us about what may need revalidating.
 */
struct lyd_val_incr {
    const struct lys_module *mod;   /**< module being validated */
    const struct lyd_val_dep_index *index;  /**< dependency index of ::lyd_val_incr.mod, owned by the context */
    struct ly_set roots;        /**< data subtrees to validate in full */
    struct ly_set path;         /**< ::lyd_val_incr.roots and all their data ancestors */
    struct ly_set extra;        /**< individual nodes outside the scope whose cross-instance constraints
                                     the edit could have changed */
    struct ly_set created;      /**< schema nodes the edit only created */
    struct ly_set modified;     /**< schema nodes the edit deleted or whose value it replaced */
    struct lyd_val_incr_valset *valsets;    /**< edited values of every value-keyed node the edit touched */
    uint32_t valset_count;
    ly_bool fallback;           /**< the edit could not be analysed, validate the whole module */
};

static void
lyd_val_incr_valsets_erase(struct lyd_val_incr *incr)
{
    uint32_t i;

    for (i = 0; i < incr->valset_count; ++i) {
        free((void *)incr->valsets[i].vals);
    }
    free(incr->valsets);
    incr->valsets = NULL;
    incr->valset_count = 0;
}

static void
lyd_val_incr_erase(struct lyd_val_incr *incr)
{
    ly_set_erase(&incr->roots, NULL);
    ly_set_erase(&incr->path, NULL);
    ly_set_erase(&incr->extra, NULL);
    ly_set_erase(&incr->created, NULL);
    ly_set_erase(&incr->modified, NULL);
    lyd_val_incr_valsets_erase(incr);
}

/**
 * @brief Read the operation of a diff node, if it carries one of its own.
 */
static ly_bool
lyd_val_incr_diff_op(const struct lyd_node *diff_node, enum lyd_diff_op *op)
{
    const struct lyd_meta *meta;
    const struct lyd_attr *attr;
    const char *str = NULL;

    if (diff_node->schema) {
        LY_LIST_FOR(diff_node->meta, meta) {
            if (!strcmp(meta->name, "operation") && !strcmp(meta->annotation->module->name, "yang")) {
                str = lyd_get_meta_value(meta);
                break;
            }
        }
    } else {
        LY_LIST_FOR(((const struct lyd_node_opaq *)diff_node)->attr, attr) {
            if (!strcmp(attr->name.name, "operation")) {
                str = attr->value;
                break;
            }
        }
    }
    if (!str) {
        return 0;
    }

    switch (str[0]) {
    case 'c':
        *op = LYD_DIFF_OP_CREATE;
        return 1;
    case 'd':
        *op = LYD_DIFF_OP_DELETE;
        return 1;
    case 'r':
        *op = LYD_DIFF_OP_REPLACE;
        return 1;
    case 'n':
        *op = LYD_DIFF_OP_NONE;
        return 1;
    default:
        return 0;
    }
}

/**
 * @brief Add a schema node and everything below it to a set of touched schema nodes.
 */
static LY_ERR
lyd_val_incr_touch(struct ly_set *set, const struct lysc_node *snode)
{
    const struct lysc_node *elem;

    LYSC_TREE_DFS_BEGIN(snode, elem) {
        LY_CHECK_RET(ly_set_add(set, (void *)elem, 0, NULL));
        LYSC_TREE_DFS_END(snode, elem);
    }
    return LY_SUCCESS;
}

/**
 * @brief Whether @p anc is @p snode or one of its schema ancestors.
 */
static ly_bool
lyd_val_incr_snode_covers(const struct lysc_node *anc, const struct lysc_node *snode)
{
    for ( ; snode; snode = lysc_data_parent(snode)) {
        if (snode == anc) {
            return 1;
        }
    }
    return 0;
}

/**
 * @brief Value a replaced node held before the edit, if the diff says.
 */
static const char *
lyd_val_incr_orig_value(const struct lyd_node *node)
{
    const struct lyd_meta *meta;

    LY_LIST_FOR(node->meta, meta) {
        if (!strcmp(meta->name, "orig-value") && !strcmp(meta->annotation->module->name, "yang")) {
            return lyd_get_meta_value(meta);
        }
    }
    return NULL;
}

/**
 * @brief Get (adding it first if needed) the value set of a value-keyed node.
 */
static LY_ERR
lyd_val_incr_valset_get(struct lyd_val_incr *incr, const struct lysc_node *snode, struct lyd_val_incr_valset **vs)
{
    struct lyd_val_incr_valset *mem;
    uint32_t i;

    for (i = 0; i < incr->valset_count; ++i) {
        if (incr->valsets[i].snode == snode) {
            *vs = &incr->valsets[i];
            return LY_SUCCESS;
        }
    }

    mem = realloc(incr->valsets, (incr->valset_count + 1) * sizeof *incr->valsets);
    LY_CHECK_RET(!mem, LY_EMEM);
    incr->valsets = mem;

    *vs = &incr->valsets[incr->valset_count++];
    memset(*vs, 0, sizeof **vs);
    (*vs)->snode = snode;
    return LY_SUCCESS;
}

/**
 * @brief Remember one value the edit touched.
 */
static LY_ERR
lyd_val_incr_valset_add(struct lyd_val_incr_valset *vs, const char *val)
{
    const char **mem;
    uint32_t i;

    if (!val) {
        /* a node the diff carries without a value cannot be told apart from any other */
        vs->unknown = 1;
        return LY_SUCCESS;
    }
    for (i = 0; i < vs->val_count; ++i) {
        if (!strcmp(vs->vals[i], val)) {
            return LY_SUCCESS;
        }
    }

    mem = realloc((void *)vs->vals, (vs->val_count + 1) * sizeof *vs->vals);
    LY_CHECK_RET(!mem, LY_EMEM);
    vs->vals = mem;
    vs->vals[vs->val_count++] = val;
    return LY_SUCCESS;
}

/**
 * @brief Collect the values of every value-keyed node a diff node changed.
 *
 * A diff node that could hold an instance of a value-keyed node without spelling it out leaves the value set
 * unusable: the tree may well hold an instance the diff does not describe.
 */
static LY_ERR
lyd_val_incr_values(const struct lyd_val_dep_index *index, const struct lyd_node *diff_node,
        struct lyd_val_incr *incr)
{
    const struct lysc_node *snode;
    struct lyd_val_incr_valset *vs;
    const struct lyd_node *elem;
    const char *orig;
    enum lyd_diff_op op;
    ly_bool found;
    uint32_t i;

    for (i = 0; i < index->value_keyed_count; ++i) {
        snode = index->constraints[index->value_keyed[i]].snode;
        if (!lyd_val_incr_snode_covers(diff_node->schema, snode)) {
            /* nothing of this node can be in the changed subtree */
            continue;
        }

        LY_CHECK_RET(lyd_val_incr_valset_get(incr, snode, &vs));
        if (vs->unknown) {
            continue;
        }

        found = 0;
        LYD_TREE_DFS_BEGIN(diff_node, elem) {
            if (elem->schema == snode) {
                found = 1;
                LY_CHECK_RET(lyd_val_incr_valset_add(vs, lyd_get_value(elem)));

                /* a replaced instance frees its old value, which can make another instance valid */
                orig = lyd_val_incr_orig_value(elem);
                if (orig) {
                    LY_CHECK_RET(lyd_val_incr_valset_add(vs, orig));
                } else if (lyd_val_incr_diff_op(elem, &op) && (op == LYD_DIFF_OP_REPLACE)) {
                    /* the old value is not spelled out, so which value was freed is unknown */
                    vs->unknown = 1;
                }
            }
            LYD_TREE_DFS_END(diff_node, elem);
        }
        if (!found) {
            vs->unknown = 1;
        }
    }

    return LY_SUCCESS;
}

ly_bool
lyd_val_incr_must_skip(const struct lyd_val_incr *incr, const struct lyd_node *node, const struct lysc_must *must)
{
    const struct lyd_val_incr_valset *vs = NULL;
    uint32_t i;

    if (!incr || !incr->valset_count || !incr->index || !node->schema) {
        return 0;
    }

    for (i = 0; i < incr->valset_count; ++i) {
        if (incr->valsets[i].snode == node->schema) {
            vs = &incr->valsets[i];
            break;
        }
    }
    if (!vs || vs->unknown) {
        /* the edit may have changed an instance of this node without saying which value it held */
        return 0;
    }
    if (!(node->schema->nodetype & LYD_NODE_TERM) ||
            !lyd_val_deps_value_keyed(incr->index, node->schema, must->cond)) {
        return 0;
    }

    for (i = 0; i < vs->val_count; ++i) {
        if (!lyd_value_compare((const struct lyd_node_term *)node, vs->vals[i], strlen(vs->vals[i]))) {
            /* the edit added or removed an instance holding this value, so the count may have changed */
            return 0;
        }
    }

    /* no instance holding this value appeared or disappeared, so the count this instance sees is the one it
     * was already validated against */
    return 1;
}

/**
 * @brief Find the data node a diff node refers to, or its closest existing ancestor.
 *
 * Walks down the tree using the diff node's own ancestor chain, which keeps the lookup on libyang's hashed
 * sibling search instead of an XPath evaluation per diff node.
 *
 * @param[in] tree First top-level data node.
 * @param[in] diff_node Diff node to locate.
 * @param[out] match Node found, NULL if not even the first level matched.
 * @return Whether @p match is the node itself rather than an ancestor.
 */
static ly_bool
lyd_val_incr_find(const struct lyd_node *tree, const struct lyd_node *diff_node, struct lyd_node **match)
{
    const struct lyd_node *dnode, *level;
    struct lyd_node *cur = NULL, *found;
    const struct lyd_node *siblings;
    uint32_t depth = 0, i, j;

    *match = NULL;

    for (dnode = diff_node; dnode; dnode = lyd_parent(dnode)) {
        ++depth;
    }
    /* no depth limit: a node that is too deep to match would be taken for a deleted top-level instance */
    siblings = tree;
    for (i = depth; i > 0; --i) {
        level = diff_node;
        for (j = 1; j < i; ++j) {
            level = lyd_parent(level);
        }

        if (!level->schema) {
            /* opaque diff node, cannot be matched reliably */
            return 0;
        }
        if (lyd_find_sibling_first(siblings, level, &found) || !found) {
            *match = cur;
            return 0;
        }
        cur = found;
        siblings = lyd_child(cur);
    }

    *match = cur;
    return 1;
}

/**
 * @brief The subtree that has to be revalidated because something inside it changed.
 *
 * Normally the shallowest enclosing list instance: every confined constraint that can read @p node lives
 * inside the list that confines it, and that list is at or below this one. A node read by a constraint that
 * no list confines widens this to the whole top-level instance.
 */
static struct lyd_node *
lyd_val_incr_root_of(struct lyd_node *node, ly_bool toplevel)
{
    struct lyd_node *root = NULL, *iter;

    for (iter = node; iter; iter = lyd_parent(iter)) {
        if (!toplevel && iter->schema && (iter->schema->nodetype & (LYS_LIST | LYS_LEAFLIST))) {
            root = iter;
        } else if (!lyd_parent(iter) && !root) {
            root = iter;
        }
    }
    return root;
}

static LY_ERR
lyd_val_incr_add_root(struct lyd_val_incr *incr, struct lyd_node *root)
{
    struct lyd_node *iter;

    if (ly_set_contains(&incr->roots, root, NULL)) {
        return LY_SUCCESS;
    }
    LY_CHECK_RET(ly_set_add(&incr->roots, root, 1, NULL));

    for (iter = root; iter; iter = lyd_parent(iter)) {
        LY_CHECK_RET(ly_set_add(&incr->path, iter, 0, NULL));
    }
    return LY_SUCCESS;
}

/**
 * @brief Turn an edit diff into the set of subtrees to revalidate and the schema nodes it touched.
 */
static LY_ERR
lyd_val_incr_collect(const struct lyd_node *tree, const struct lys_module *mod, const struct lyd_val_dep_index *index,
        const struct lyd_node *edit_diff, struct lyd_val_incr *incr)
{
    const struct lyd_node *dtop, *diter;
    struct lyd_node *data, *root;
    enum lyd_diff_op op;
    ly_bool exact, toplevel;

    LY_LIST_FOR(edit_diff, dtop) {
        LYD_TREE_DFS_BEGIN(dtop, diter) {
            if (!lyd_val_incr_diff_op(diter, &op) || (op == LYD_DIFF_OP_NONE)) {
                goto next;
            }
            if (!diter->schema) {
                /* an opaque change cannot be classified */
                incr->fallback = 1;
                return LY_SUCCESS;
            }
            if ((diter->flags & LYD_EXT) || (LYD_CTX(diter) != mod->ctx)) {
                /* mounted data is validated by the extension plugin, out of reach of the dependency index */
                incr->fallback = 1;
                return LY_SUCCESS;
            }

            /* remember what the edit touched, for every module: a constraint of the validated module may well
             * read another module's data; a diff that does not describe defaults calls a node created even when
             * it replaced an implicit one, so such a create may have removed or changed default data */
            LY_CHECK_RET(lyd_val_incr_touch(((op == LYD_DIFF_OP_CREATE) && !lyd_val_deps_is_implicit(diter->schema)) ?
                    &incr->created : &incr->modified, diter->schema));

            /* collected for every module as well: the same value may be held by data of another module */
            LY_CHECK_RET(lyd_val_incr_values(index, diter, incr));

            if (lyd_owner_module(diter) != mod) {
                /* only this module's data is being validated */
                goto next;
            }

            exact = lyd_val_incr_find(tree, diter, &data);
            if (!data) {
                if (op == LYD_DIFF_OP_DELETE) {
                    /* the whole top-level instance is gone, nothing left to revalidate */
                    goto next;
                }
                /* a created or replaced node that is not in the tree means the diff does not describe it */
                incr->fallback = 1;
                return LY_SUCCESS;
            }
            if (!exact && (op != LYD_DIFF_OP_DELETE)) {
                incr->fallback = 1;
                return LY_SUCCESS;
            }

            toplevel = ly_set_contains(&index->toplevel_atoms, (void *)diter->schema, NULL);
            root = lyd_val_incr_root_of(data, toplevel);
            if (root) {
                LY_CHECK_RET(lyd_val_incr_add_root(incr, root));
            }

next:
            LYD_TREE_DFS_END(dtop, diter);
        }
    }

    return LY_SUCCESS;
}

/**
 * @brief Drop roots that already sit inside another root.
 */
static void
lyd_val_incr_prune_roots(struct lyd_val_incr *incr)
{
    const struct lyd_node *iter;
    uint32_t i = incr->roots.count;

    while (i) {
        --i;
        for (iter = lyd_parent(incr->roots.dnodes[i]); iter; iter = lyd_parent(iter)) {
            if (ly_set_contains(&incr->roots, (void *)iter, NULL)) {
                ly_set_rm_index(&incr->roots, i, NULL);
                break;
            }
        }
    }
}

/**
 * @brief Whether any atom of a constraint is among the schema nodes an edit touched.
 */
static ly_bool
lyd_val_incr_atoms_hit(const struct lyd_val_constraint *cons, const struct ly_set *touched)
{
    uint32_t i;

    if (!touched->count) {
        return 0;
    }
    for (i = 0; cons->atoms && cons->atoms[i]; ++i) {
        if (ly_set_contains(touched, (void *)cons->atoms[i], NULL)) {
            return 1;
        }
    }
    return 0;
}

/**
 * @brief Collect the schema nodes whose cross-instance constraints the edit could have changed.
 */
static LY_ERR
lyd_val_incr_wanted(const struct lyd_val_dep_index *index, const struct lyd_val_incr *incr, struct ly_set *wanted)
{
    const struct lyd_val_constraint *cons;
    uint32_t i;

    for (i = 0; i < index->nonlocal_count; ++i) {
        cons = &index->constraints[index->nonlocal[i]];

        if (!lyd_val_incr_atoms_hit(cons, &incr->modified) &&
                (cons->creation_safe || !lyd_val_incr_atoms_hit(cons, &incr->created))) {
            continue;
        }
        LY_CHECK_RET(ly_set_add(wanted, (void *)cons->snode, 0, NULL));
    }

    for (i = 0; i < index->dflt_when.count; ++i) {
        LY_CHECK_RET(ly_set_add(wanted, index->dflt_when.snodes[i], 0, NULL));
    }
    return LY_SUCCESS;
}

/**
 * @brief Collect @p wanted and every schema node between them and the data root.
 *
 * Lets the search for their instances skip whole subtrees that cannot contain one.
 */
static LY_ERR
lyd_val_incr_wanted_path(const struct ly_set *wanted, struct ly_set *path)
{
    const struct lysc_node *snode;
    uint32_t i;

    for (i = 0; i < wanted->count; ++i) {
        for (snode = wanted->snodes[i]; snode; snode = lysc_data_parent(snode)) {
            LY_CHECK_RET(ly_set_add(path, (void *)snode, 0, NULL));
        }
    }
    return LY_SUCCESS;
}

/**
 * @brief Find the instances of @p wanted schema nodes that the scoped passes would otherwise skip.
 */
static LY_ERR
lyd_val_incr_extra(const struct lyd_node *tree, const struct lys_module *mod, const struct ly_set *wanted,
        const struct ly_set *wanted_path, struct lyd_val_incr *incr)
{
    const struct lyd_node *first, *sibling, *elem;

    first = tree;
    lyd_first_module_sibling((struct lyd_node **)&first, mod);

    LY_LIST_FOR(first, sibling) {
        if (lyd_owner_module(sibling) != mod) {
            break;
        }
        LYD_TREE_DFS_BEGIN(sibling, elem) {
            if (!elem->schema || !ly_set_contains(wanted_path, (void *)elem->schema, NULL)) {
                /* nothing wanted can be in here */
                LYD_TREE_DFS_continue = 1;
            } else if (ly_set_contains(wanted, (void *)elem->schema, NULL) &&
                    !ly_set_contains(&incr->roots, (void *)elem, NULL)) {
                LY_CHECK_RET(ly_set_add(&incr->extra, (void *)elem, 0, NULL));
            }
            LYD_TREE_DFS_END(sibling, elem);
        }
    }

    return LY_SUCCESS;
}

/**
 * @brief Drop extra nodes that already sit inside a subtree scheduled for a full revalidation.
 */
static void
lyd_val_incr_prune_extra(struct lyd_val_incr *incr)
{
    const struct lyd_node *iter;
    uint32_t i = incr->extra.count;

    while (i) {
        --i;
        for (iter = incr->extra.dnodes[i]; iter; iter = lyd_parent(iter)) {
            if (ly_set_contains(&incr->roots, (void *)iter, NULL)) {
                ly_set_rm_index(&incr->extra, i, NULL);
                break;
            }
        }
    }
}

/**
 * @brief Work out what a change described by @p edit_diff makes necessary in @p mod.
 *
 * Only reads @p tree, so it may be repeated once the earlier validation passes have settled the tree.
 */
static LY_ERR
lyd_val_incr_analyze(const struct lyd_node *tree, const struct lys_module *mod, const struct lyd_node *edit_diff,
        struct lyd_val_incr *incr)
{
    const struct lyd_val_dep_index *index;
    LY_ERR rc;

    ly_set_erase(&incr->roots, NULL);
    ly_set_erase(&incr->path, NULL);
    lyd_val_incr_valsets_erase(incr);
    incr->mod = mod;

    rc = lyd_val_deps_get(mod, &index);
    if (rc || index->unanalysable) {
        incr->fallback = 1;
        return LY_SUCCESS;
    }
    incr->index = index;

    rc = lyd_val_incr_collect(tree, mod, index, edit_diff, incr);
    LY_CHECK_RET(rc);
    if (incr->fallback) {
        return LY_SUCCESS;
    }
    lyd_val_incr_prune_roots(incr);

    return LY_SUCCESS;
}

/**
 * @brief Find the nodes outside the scope roots that the change can still have invalidated.
 *
 * Has to run once the tree is settled: implicit defaults created by the earlier passes are exactly the kind of
 * node this looks for.
 */
static LY_ERR
lyd_val_incr_analyze_extra(const struct lyd_node *tree, const struct lys_module *mod, struct lyd_val_incr *incr)
{
    const struct lyd_val_dep_index *index;
    struct ly_set wanted = {0}, wanted_path = {0};
    LY_ERR rc;

    ly_set_erase(&incr->extra, NULL);

    rc = lyd_val_deps_get(mod, &index);
    if (rc) {
        incr->fallback = 1;
        return LY_SUCCESS;
    }

    rc = lyd_val_incr_wanted(index, incr, &wanted);
    LY_CHECK_GOTO(rc, cleanup);

    if (wanted.count) {
        rc = lyd_val_incr_wanted_path(&wanted, &wanted_path);
        LY_CHECK_GOTO(rc, cleanup);

        rc = lyd_val_incr_extra(tree, mod, &wanted, &wanted_path, incr);
        LY_CHECK_GOTO(rc, cleanup);
        lyd_val_incr_prune_extra(incr);
    }

cleanup:
    ly_set_erase(&wanted, NULL);
    ly_set_erase(&wanted_path, NULL);
    return rc;
}

/* a context is dropped and recreated on every schema change, so the totals of a whole run need to outlive it */
static pthread_mutex_t lyd_val_incr_glob_lock = PTHREAD_MUTEX_INITIALIZER;
static struct lyd_validate_incr_stats lyd_val_incr_glob;

/**
 * @brief Add counters to the totals of the context and of the process.
 */
static void
lyd_val_incr_stats_add(const struct ly_ctx *ctx, const struct lyd_validate_incr_stats *delta)
{
    struct ly_ctx *c = (struct ly_ctx *)ctx;
    struct lyd_validate_incr_stats *dst[2] = {&c->val_incr_stats, &lyd_val_incr_glob};
    pthread_mutex_t *lock[2] = {&c->val_deps_lock, &lyd_val_incr_glob_lock};
    uint32_t i;

    for (i = 0; i < 2; ++i) {
        pthread_mutex_lock(lock[i]);
        dst[i]->calls += delta->calls;
        dst[i]->fallbacks += delta->fallbacks;
        dst[i]->scope_roots += delta->scope_roots;
        dst[i]->extra_nodes += delta->extra_nodes;
        dst[i]->must_evals += delta->must_evals;
        dst[i]->must_skips += delta->must_skips;
        dst[i]->late_fallbacks += delta->late_fallbacks;
        pthread_mutex_unlock(lock[i]);
    }
}

static void
lyd_val_incr_count(const struct ly_ctx *ctx, const struct lyd_val_incr *incr, ly_bool fallback)
{
    struct lyd_validate_incr_stats delta = {0};

    delta.calls = 1;
    if (fallback) {
        delta.fallbacks = 1;
    } else {
        delta.scope_roots = incr->roots.count;
        delta.extra_nodes = incr->extra.count;
    }
    lyd_val_incr_stats_add(ctx, &delta);
}

/**
 * @brief Count a fallback decided after the call was already counted as incremental.
 */
static void
lyd_val_incr_count_late_fallback(const struct ly_ctx *ctx)
{
    struct lyd_validate_incr_stats delta = {0};

    delta.fallbacks = 1;
    delta.late_fallbacks = 1;
    lyd_val_incr_stats_add(ctx, &delta);
}

LIBYANG_API_DEF void
lyd_validate_incr_late_stats(const struct ly_ctx *ctx, uint64_t *late_fallbacks)
{
    struct ly_ctx *c = (struct ly_ctx *)ctx;
    pthread_mutex_t *lock = ctx ? &c->val_deps_lock : &lyd_val_incr_glob_lock;
    const struct lyd_validate_incr_stats *stats = ctx ? &c->val_incr_stats : &lyd_val_incr_glob;

    pthread_mutex_lock(lock);
    if (late_fallbacks) {
        *late_fallbacks = stats->late_fallbacks;
    }
    pthread_mutex_unlock(lock);
}

void
lyd_val_incr_must_count(const struct ly_ctx *ctx, uint64_t evals, uint64_t skips)
{
    struct lyd_validate_incr_stats delta = {0};

    if (!evals && !skips) {
        return;
    }

    delta.must_evals = evals;
    delta.must_skips = skips;
    lyd_val_incr_stats_add(ctx, &delta);
}

LIBYANG_API_DEF void
lyd_validate_incr_must_stats(const struct ly_ctx *ctx, uint64_t *evals, uint64_t *skips)
{
    struct ly_ctx *c = (struct ly_ctx *)ctx;
    pthread_mutex_t *lock = ctx ? &c->val_deps_lock : &lyd_val_incr_glob_lock;
    const struct lyd_validate_incr_stats *stats = ctx ? &c->val_incr_stats : &lyd_val_incr_glob;

    pthread_mutex_lock(lock);
    if (evals) {
        *evals = stats->must_evals;
    }
    if (skips) {
        *skips = stats->must_skips;
    }
    pthread_mutex_unlock(lock);
}

LIBYANG_API_DEF void
lyd_validate_incr_stats(const struct ly_ctx *ctx, uint64_t *calls, uint64_t *fallbacks)
{
    struct ly_ctx *c = (struct ly_ctx *)ctx;
    pthread_mutex_t *lock = ctx ? &c->val_deps_lock : &lyd_val_incr_glob_lock;
    const struct lyd_validate_incr_stats *stats = ctx ? &c->val_incr_stats : &lyd_val_incr_glob;

    pthread_mutex_lock(lock);
    if (calls) {
        *calls = stats->calls;
    }
    if (fallbacks) {
        *fallbacks = stats->fallbacks;
    }
    pthread_mutex_unlock(lock);
}

/**
 * @brief Re-register the unresolved parts of a node that the scoped subtree walk did not visit.
 */
static LY_ERR
lyd_val_incr_unres_extra(const struct lyd_val_incr *incr, struct ly_set *node_when, struct ly_set *node_types)
{
    struct lyd_node *node;
    uint32_t i;

    for (i = 0; i < incr->extra.count; ++i) {
        node = incr->extra.dnodes[i];

        /* the earlier passes may have queued the same node already and a duplicate would be used after the
         * autodeletion frees it */
        if (lysc_has_when(node->schema)) {
            LY_CHECK_RET(ly_set_add(node_when, node, 0, NULL));
        }
        if ((node->schema->nodetype & LYD_NODE_TERM) &&
                ((struct lysc_node_leaf *)node->schema)->type->plugin->validate) {
            LY_CHECK_RET(ly_set_add(node_types, node, 0, NULL));
        }
    }
    return LY_SUCCESS;
}

/**
 * @brief Run the sibling-level checks on the way down to the scope roots.
 *
 * Full validation reaches these through the subtree walk of every top-level node; the scoped walk starts at the
 * roots, so duplicate instance detection and default autodeletion above them have to be driven explicitly.
 *
 * Descends along the live tree rather than the collected node pointers, because the checks autodelete.
 */
static LY_ERR
lyd_val_incr_new_above(struct lyd_node *node, const struct lyd_val_incr *incr, uint32_t val_opts,
        struct ly_ht *getnext_ht, struct lyd_node **diff)
{
    LY_ERR r, rc = LY_SUCCESS;
    struct lyd_node *child;

    if (!(node->schema->nodetype & LYD_NODE_INNER)) {
        return LY_SUCCESS;
    }

    r = lyd_validate_new(lyd_node_child_p(node), node->schema, NULL, NULL, val_opts, 0, getnext_ht, diff);
    LY_VAL_ERR_GOTO(r, rc = r, val_opts, cleanup);

    LY_LIST_FOR(lyd_child(node), child) {
        /* the roots get this from their own subtree walk */
        if (ly_set_contains(&incr->path, child, NULL) && !ly_set_contains(&incr->roots, child, NULL)) {
            r = lyd_val_incr_new_above(child, incr, val_opts, getnext_ht, diff);
            LY_VAL_ERR_GOTO(r, rc = r, val_opts, cleanup);
        }
    }

cleanup:
    return rc;
}

/**
 * @brief Create the implicit nodes of @p mod, top level included.
 *
 * The full pass gets the nested ones from the subtree walk of every top-level node, which the scoped walk skips.
 * lyd_new_implicit_r() cannot be used on the top level directly, it would run past the module data into the
 * following siblings.
 */
static LY_ERR
lyd_val_incr_implicit(struct lyd_node **first2, const struct lys_module *mod, uint32_t impl_opts,
        struct ly_ht *getnext_ht, struct lyd_node **diff)
{
    struct lyd_node *child;

    LY_CHECK_RET(lyd_new_implicit(NULL, first2, NULL, mod, NULL, NULL, NULL, impl_opts, getnext_ht, diff));

    LY_LIST_FOR(*first2, child) {
        if (lyd_owner_module(child) != mod) {
            break;
        }
        if ((child->flags & LYD_DEFAULT) && (child->schema->nodetype == LYS_CONTAINER)) {
            LY_CHECK_RET(lyd_new_implicit_r(child, lyd_node_child_p(child), NULL, NULL, NULL, NULL, NULL, impl_opts,
                    getnext_ht, diff));
        }
    }

    return LY_SUCCESS;
}

/**
 * @brief Whether a validation diff deletes any node.
 */
static ly_bool
lyd_val_incr_diff_deletes(const struct lyd_node *val_diff)
{
    const struct lyd_node *dtop, *diter;
    enum lyd_diff_op op;

    LY_LIST_FOR(val_diff, dtop) {
        LYD_TREE_DFS_BEGIN(dtop, diter) {
            if (lyd_val_incr_diff_op(diter, &op) && (op == LYD_DIFF_OP_DELETE)) {
                return 1;
            }
            LYD_TREE_DFS_END(dtop, diter);
        }
    }
    return 0;
}

/**
 * @brief Validate the module in full on top of what the incremental passes did so far.
 *
 * Every check of the full pass runs on all data again, so starting from a partially validated tree is fine.
 *
 * @param[in,out] val_diff Changes made by the validation so far, the changes of the full pass are merged in.
 */
static LY_ERR
lyd_val_incr_full(struct lyd_node **tree, const struct lys_module *module, uint32_t val_opts,
        struct lyd_node **val_diff)
{
    struct lyd_node *full_diff = NULL;
    LY_ERR r, rc;

    rc = lyd_validate_module(tree, module, val_opts, &full_diff);
    if (full_diff) {
        r = lyd_diff_merge_all(val_diff, full_diff, 0);
        lyd_free_all(full_diff);
        if (r && !rc) {
            rc = r;
        }
    }
    return rc;
}

/**
 * @brief Rebuild the scope against the current tree, giving up on the incremental path if it no longer holds.
 *
 * Every pass that inserts or autodeletes nodes invalidates the collected node pointers.
 */
#define LYD_VAL_INCR_REANALYZE \
    first = *first2; \
    lyd_first_module_sibling(&first, module); \
    first2 = (!first || (first == *tree)) ? tree : &first; \
    r = lyd_val_incr_analyze(*tree, module, edit_diff, &incr); \
    LY_CHECK_ERR_GOTO(r, rc = r, cleanup); \
    if (incr.fallback) { \
        lyd_val_incr_count(module->ctx, &incr, 1); \
        rc = lyd_val_incr_full(tree, module, val_opts, &val_diff); \
        goto cleanup; \
    }

LIBYANG_API_DEF LY_ERR
lyd_validate_module_incr(struct lyd_node **tree, const struct lys_module *module, const struct lyd_node *edit_diff,
        uint32_t val_opts, struct lyd_node **diff)
{
    LY_ERR r, rc = LY_SUCCESS;
    struct lyd_val_incr incr = {0};
    struct lyd_val_scope scope;
    struct ly_set node_types = {0}, meta_types = {0}, node_when = {0}, ext_node = {0}, ext_val = {0};
    struct ly_ht *getnext_ht = NULL;
    struct lyd_node *first, **first2, *iter, *val_diff = NULL;
    uint32_t i, impl_opts;

    LY_CHECK_ARG_RET(NULL, tree, module, !(val_opts & LYD_VALIDATE_PRESENT), LY_EINVAL);
    LY_CHECK_CTX_EQUAL_RET(__func__, *tree ? LYD_CTX(*tree) : NULL, module->ctx, LY_EINVAL);

    if (diff) {
        *diff = NULL;
    }
    if (!edit_diff || !*tree) {
        lyd_val_incr_count(module->ctx, &incr, 1);
        return lyd_validate_module(tree, module, val_opts, diff);
    }

    rc = lyd_val_incr_analyze(*tree, module, edit_diff, &incr);
    LY_CHECK_GOTO(rc, cleanup);

    if (incr.fallback) {
        lyd_val_incr_count(module->ctx, &incr, 1);
        rc = lyd_val_incr_full(tree, module, val_opts, &val_diff);
        goto cleanup;
    }

    r = lyd_val_getnext_ht_new(&getnext_ht);
    LY_CHECK_ERR_GOTO(r, rc = r, cleanup);

    first = *tree;
    lyd_first_module_sibling(&first, module);
    first2 = (!first || (first == *tree)) ? tree : &first;

    /* the top level is walked in full: it is a single sibling list and everything on it is cheap to check */
    r = lyd_validate_new(first2, *first2 ? lysc_data_parent((*first2)->schema) : NULL, module, NULL, val_opts, 0,
            getnext_ht, &val_diff);
    LY_VAL_ERR_GOTO(r, rc = r, val_opts, cleanup);

    /* autodeletion above may have freed nodes the scope points at, so resolve the diff against the tree again */
    LYD_VAL_INCR_REANALYZE;

    LY_LIST_FOR(*first2, iter) {
        if (lyd_owner_module(iter) != module) {
            break;
        }
        if (ly_set_contains(&incr.path, iter, NULL) && !ly_set_contains(&incr.roots, iter, NULL)) {
            r = lyd_val_incr_new_above(iter, &incr, val_opts, getnext_ht, &val_diff);
            LY_VAL_ERR_GOTO(r, rc = r, val_opts, cleanup);
        }
    }

    impl_opts = 0;
    if (val_opts & LYD_VALIDATE_NO_STATE) {
        impl_opts |= LYD_IMPLICIT_NO_STATE;
    }
    if (val_opts & LYD_VALIDATE_NO_DEFAULTS) {
        impl_opts |= LYD_IMPLICIT_NO_DEFAULTS;
    }
    r = lyd_val_incr_implicit(first2, module, impl_opts, getnext_ht, &val_diff);
    LY_CHECK_ERR_GOTO(r, rc = r, cleanup);

    /* both passes above rearranged the tree, this is the last chance to build the scope */
    LYD_VAL_INCR_REANALYZE;

    /* implicit top-level defaults are new data of this module and need the same treatment as the edit */
    LY_LIST_FOR(*first2, iter) {
        if (lyd_owner_module(iter) != module) {
            break;
        }
        if ((iter->flags & LYD_NEW) && !ly_set_contains(&incr.roots, iter, NULL)) {
            r = lyd_val_incr_add_root(&incr, iter);
            LY_CHECK_ERR_GOTO(r, rc = r, cleanup);
        }
    }

    lyd_val_incr_count(module->ctx, &incr, 0);

    for (i = 0; i < incr.roots.count; ++i) {
        r = lyd_validate_subtree(incr.roots.dnodes[i], &node_when, &node_types, &meta_types, &ext_node, &ext_val,
                val_opts, 0, getnext_ht, &val_diff);
        LY_VAL_ERR_GOTO(r, rc = r, val_opts, cleanup);
    }

    /* the tree stops changing shape here, so the out-of-scope nodes to recheck can finally be looked up */
    r = lyd_val_incr_analyze_extra(*tree, module, &incr);
    LY_CHECK_ERR_GOTO(r, rc = r, cleanup);

    r = lyd_val_incr_unres_extra(&incr, &node_when, &node_types);
    LY_CHECK_ERR_GOTO(r, rc = r, cleanup);

    r = lyd_validate_unres(first2, module, LYD_TYPE_DATA_YANG, &node_when, 0, &node_types, &meta_types, &ext_node,
            &ext_val, val_opts, &val_diff);
    LY_VAL_ERR_GOTO(r, rc = r, val_opts, cleanup);

    /* a node the validation deleted itself (a when turned false, a default or a case replaced) is not in the edit
     * diff, so nothing reading it was scheduled for a recheck; only a full pass is sure to see every such reader */
    if (!rc && lyd_val_incr_diff_deletes(val_diff)) {
        lyd_val_incr_count_late_fallback(module->ctx);
        rc = lyd_val_incr_full(tree, module, val_opts, &val_diff);
        goto cleanup;
    }

    if (!(val_opts & LYD_VALIDATE_NOT_FINAL)) {
        /* "when" resolution above autodeletes, the extra nodes have to be looked up once more */
        r = lyd_val_incr_analyze_extra(*tree, module, &incr);
        LY_CHECK_ERR_GOTO(r, rc = r, cleanup);

        scope.roots = &incr.roots;
        scope.path = &incr.path;
        scope.incr = &incr;
        r = lyd_validate_final_r(*first2, NULL, NULL, module, NULL, val_opts, 0, 0, getnext_ht, &scope);
        LY_VAL_ERR_GOTO(r, rc = r, val_opts, cleanup);

        for (i = 0; i < incr.extra.count; ++i) {
            r = lyd_validate_must(incr.extra.dnodes[i], val_opts, 0, 0, &incr);
            LY_VAL_ERR_GOTO(r, rc = r, val_opts, cleanup);
        }
    }

cleanup:
    if (diff) {
        *diff = val_diff;
    } else {
        lyd_free_all(val_diff);
    }
    ly_set_erase(&node_when, NULL);
    ly_set_erase(&node_types, NULL);
    ly_set_erase(&meta_types, NULL);
    ly_set_erase(&ext_node, free);
    ly_set_erase(&ext_val, free);
    lyd_val_getnext_ht_free(getnext_ht);
    lyd_val_incr_erase(&incr);
    return rc;
}

LIBYANG_API_DEF LY_ERR
lyd_validate_module_incr_final(struct lyd_node *tree, const struct lys_module *module,
        const struct lyd_node *edit_diff, uint32_t val_opts)
{
    LY_ERR r, rc = LY_SUCCESS;
    struct lyd_val_incr incr = {0};
    struct lyd_val_scope scope;
    struct ly_ht *getnext_ht = NULL;
    struct lyd_node *first;
    const struct lys_module *mod;
    uint32_t i, idx = 0;

    LY_CHECK_ARG_RET(NULL, module, !(val_opts & (LYD_VALIDATE_PRESENT | LYD_VALIDATE_NOT_FINAL)), LY_EINVAL);
    LY_CHECK_CTX_EQUAL_RET(__func__, tree ? LYD_CTX(tree) : NULL, module->ctx, LY_EINVAL);

    if (!edit_diff || !tree) {
        return lyd_validate_module_final(tree, module, val_opts);
    }

    rc = lyd_val_incr_analyze(tree, module, edit_diff, &incr);
    LY_CHECK_GOTO(rc, cleanup);

    if (!incr.fallback) {
        rc = lyd_val_incr_analyze_extra(tree, module, &incr);
        LY_CHECK_GOTO(rc, cleanup);
    }
    if (incr.fallback) {
        rc = lyd_validate_module_final(tree, module, val_opts);
        goto cleanup;
    }

    mod = lyd_mod_next_module(tree, module, module->ctx, &idx, &first);
    assert(mod);

    r = lyd_val_getnext_ht_new(&getnext_ht);
    LY_CHECK_ERR_GOTO(r, rc = r, cleanup);

    scope.roots = &incr.roots;
    scope.path = &incr.path;
    scope.incr = &incr;
    r = lyd_validate_final_r(first, NULL, NULL, mod, NULL, val_opts, 0, 0, getnext_ht, &scope);
    LY_VAL_ERR_GOTO(r, rc = r, val_opts, cleanup);

    for (i = 0; i < incr.extra.count; ++i) {
        r = lyd_validate_must(incr.extra.dnodes[i], val_opts, 0, 0, &incr);
        LY_VAL_ERR_GOTO(r, rc = r, val_opts, cleanup);
    }

cleanup:
    lyd_val_getnext_ht_free(getnext_ht);
    lyd_val_incr_erase(&incr);
    return rc;
}
