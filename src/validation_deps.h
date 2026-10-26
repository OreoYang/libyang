/**
 * @file validation_deps.h
 * @brief Dependency classification and indexing for incremental validation.
 *
 * Copyright (c) 2026 Vecima Networks Inc.
 *
 * This source code is licensed under BSD 3-Clause License (the "License").
 * You may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *     https://opensource.org/licenses/BSD-3-Clause
 */

#ifndef LY_VALIDATION_DEPS_H_
#define LY_VALIDATION_DEPS_H_

#include <stdint.h>

#include "log.h"
#include "set.h"
#include "tree_data.h"
#include "tree_schema.h"

struct ly_ctx;
struct lys_module;
struct lysc_node;
struct lysc_prefix;
struct lyxp_expr;

/**
 * @brief How far the data a constraint reads can reach.
 *
 * The unit of reasoning is the *top-level data instance*: the subtree rooted at the topmost data node
 * containing the constrained node. An edit that does not touch a given top-level instance cannot change
 * the result of a ::LYD_VAL_DEP_LOCAL or ::LYD_VAL_DEP_LIST_SCOPE constraint evaluated inside it.
 */
enum lyd_val_dep_class {
    LYD_VAL_DEP_LOCAL = 0,      /**< reads only the constraint's own instance and its ancestors */
    LYD_VAL_DEP_LIST_SCOPE,     /**< reads a whole nested list, but still inside the same top-level instance */
    LYD_VAL_DEP_BOUNDED,        /**< reaches other top-level instances, but only ones selected by key
                                     predicates driven by current() or by deref() */
    LYD_VAL_DEP_UNBOUNDED       /**< cannot be reduced to a finite set of instances */
};

#define LYD_VAL_DEP_CLASS_COUNT 4

/**
 * @brief Why a constraint exists, only used for reporting.
 */
enum lyd_val_dep_kind {
    LYD_VAL_DEP_WHEN = 0,
    LYD_VAL_DEP_MUST,
    LYD_VAL_DEP_LEAFREF,
    LYD_VAL_DEP_UNIQUE
};

/**
 * @brief One classified constraint.
 */
struct lyd_val_constraint {
    const struct lysc_node *snode;      /**< node the constraint is attached to */
    const char *expr;                   /**< expression text, not owned */
    const struct lyxp_expr *cond;       /**< parsed expression, only set for a value-keyed constraint */
    const struct lysc_node **atoms;     /**< NULL-terminated schema nodes the expression reads */
    enum lyd_val_dep_kind kind;
    enum lyd_val_dep_class cls;

    /**
     * @brief Whether the constraint only counts the instances of ::lyd_val_constraint.snode that share the value
     * of the instance it is evaluated on.
     *
     * Such a constraint reads nothing but one value bucket, so an edit that leaves a bucket alone cannot turn it
     * from satisfied to violated on any instance holding that value. Recognised shape:
     * "count(<path>[<snode> = current()]) <cmp> <number>".
     */
    ly_bool value_keyed;

    /**
     * @brief Whether creating data can never turn this constraint from satisfied to violated.
     *
     * True for require-instance leafrefs, whose check is a pure existence test over a node set that
     * creation can only grow, and for cross-instance when/must that select their target through list key
     * predicates and combine the results without negation: a created list instance necessarily carries a
     * new key, so it cannot become the target of an already existing referrer, and an existing referrer
     * that selected nothing would already have been rejected before the edit.
     */
    ly_bool creation_safe;

    /**
     * @brief List instance the constraint is confined to, NULL for the whole top-level instance.
     *
     * Only meaningful for ::LYD_VAL_DEP_LOCAL and ::LYD_VAL_DEP_LIST_SCOPE.
     */
    const struct lysc_node *unit;
};

/**
 * @brief Per-module classification of every constraint reachable from the module's compiled tree.
 *
 * Built lazily, cached in the context, freed with the context.
 */
struct lyd_val_dep_index {
    const struct lys_module *mod;
    uint16_t change_count;              /**< change count of the context the index was built for, a later schema
                                             change (an augment or a deviation of another module, a feature)
                                             makes the index stale */
    struct lyd_val_constraint *constraints;
    uint32_t constraint_count;

    uint32_t *nonlocal;                 /**< indices of ::LYD_VAL_DEP_BOUNDED / ::LYD_VAL_DEP_UNBOUNDED constraints */
    uint32_t nonlocal_count;

    uint32_t *value_keyed;              /**< indices of constraints with ::lyd_val_constraint.value_keyed set */
    uint32_t value_keyed_count;

    /**
     * @brief Schema nodes read by a constraint that no list confines.
     *
     * Touching one of these means the revalidated subtree has to be the whole top-level instance; every other
     * confined constraint is covered by revalidating the topmost list instance around the change.
     */
    struct ly_set toplevel_atoms;

    /**
     * @brief Schema nodes carrying a "when" that can be instantiated as an implicit default.
     *
     * A full validation evaluates every "when" in the module, so it also drops a default node whose "when"
     * has never held. Data stored by an application that creates defaults without validating them can contain
     * such nodes, so they are revalidated regardless of what the edit touched.
     */
    struct ly_set dflt_when;

    /**
     * @brief The module holds a constraint the index cannot describe, so its data is always validated in full.
     *
     * Set for a configuration instance-identifier that requires its instance: the target is named by the value,
     * so no schema atoms say which edits can delete it.
     */
    ly_bool unanalysable;

    uint32_t class_count[LYD_VAL_DEP_CLASS_COUNT];
};

/**
 * @brief Classify a single compiled XPath expression.
 *
 * @param[in] ctx_node Schema context node the expression is evaluated from, NULL for the data root.
 * @param[in] cur_mod Module the expression was written in.
 * @param[in] expr Parsed expression.
 * @param[in] prefixes Compiled prefixes of the expression.
 * @param[out] atoms Optional set of schema nodes the expression reads, caller frees with ::ly_set_free().
 * @param[out] creation_safe Optional flag, see ::lyd_val_constraint.creation_safe.
 * @param[out] unit Optional confining list, see ::lyd_val_constraint.unit.
 * @return Dependency class, ::LYD_VAL_DEP_UNBOUNDED whenever the expression cannot be analysed.
 */
enum lyd_val_dep_class lyd_val_dep_classify_expr(const struct lysc_node *ctx_node, const struct lys_module *cur_mod,
        const struct lyxp_expr *expr, const struct lysc_prefix *prefixes, struct ly_set **atoms,
        ly_bool *creation_safe, const struct lysc_node **unit);

/**
 * @brief Get (building it first if needed) the dependency index of a module.
 *
 * @param[in] mod Module to index.
 * @param[out] index Cached index, owned by the context.
 * @return LY_ERR value.
 */
LY_ERR lyd_val_deps_get(const struct lys_module *mod, const struct lyd_val_dep_index **index);

/**
 * @brief Whether a specific constraint of a node is value-keyed.
 *
 * @param[in] index Dependency index of the node's module.
 * @param[in] snode Node the constraint is attached to.
 * @param[in] cond Parsed expression of the constraint.
 * @return Whether the constraint was classified as value-keyed, see ::lyd_val_constraint.value_keyed.
 */
ly_bool lyd_val_deps_value_keyed(const struct lyd_val_dep_index *index, const struct lysc_node *snode,
        const struct lyxp_expr *cond);

/**
 * @brief Whether a node can appear in the data without anyone asking for it.
 *
 * @param[in] snode Schema node to check.
 * @return Whether its instance can be an implicit default (a non-presence container, a leaf or leaf-list with a
 * default).
 */
ly_bool lyd_val_deps_is_implicit(const struct lysc_node *snode);

/**
 * @brief Free the cached dependency indexes of a context that is being destroyed.
 *
 * A printed context shares them with every other printed context at the same address, those keep them alive.
 *
 * @param[in] ctx Context being destroyed, not a context with a parent context.
 */
void lyd_val_deps_ctx_release(struct ly_ctx *ctx);

/**
 * @brief Name of a dependency class, for reports and logs.
 *
 * @param[in] cls Class to name.
 * @return Static string.
 */
const char *lyd_val_dep_class_str(enum lyd_val_dep_class cls);

/**
 * @brief Name of a constraint kind, for reports and logs.
 *
 * @param[in] kind Kind to name.
 * @return Static string.
 */
const char *lyd_val_dep_kind_str(enum lyd_val_dep_kind kind);

#endif /* LY_VALIDATION_DEPS_H_ */
