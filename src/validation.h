/**
 * @file validation.h
 * @author Michal Vasko <mvasko@cesnet.cz>
 * @brief Validation routines.
 *
 * Copyright (c) 2019 - 2026 CESNET, z.s.p.o.
 *
 * This source code is licensed under BSD 3-Clause License (the "License").
 * You may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *     https://opensource.org/licenses/BSD-3-Clause
 */

#ifndef LY_VALIDATION_H_
#define LY_VALIDATION_H_

#include <stdint.h>

#include "diff.h"
#include "log.h"
#include "parser_data.h"

struct ly_ctx;
struct ly_set;
struct lyd_node;
struct lyd_val_incr;
struct lys_module;
struct lysc_must;
struct lysc_node;

/**
 * @brief Check validation error taking into account multi-error validation.
 *
 * @param[in] r Local return value.
 * @param[in] err_cmd Command to perform on any error.
 * @param[in] val_opts Validation options.
 * @param[in] label Label to go to on fatal error.
 */
#define LY_VAL_ERR_GOTO(r, err_cmd, val_opts, label) \
        if (r) { \
            err_cmd; \
            if ((r != LY_EVALID) || !(val_opts & LYD_VALIDATE_MULTI_ERROR)) { \
                goto label; \
            } \
        }

/**
 * @brief Part of the data tree that the final validation of an incremental validation has to look at.
 */
struct lyd_val_scope {
    const struct ly_set *roots;         /**< data subtrees to validate in full */
    const struct ly_set *path;          /**< ::lyd_val_scope.roots and all their data ancestors */
    const struct lyd_val_incr *incr;    /**< incremental validation state, for the "must" counters and filtering */
};

/**
 * @brief Check whether the edit could not have violated a "must" condition, so it need not be evaluated.
 *
 * @param[in] incr Incremental validation state, NULL when validating in full.
 * @param[in] node Data node the condition belongs to.
 * @param[in] must Condition to check.
 * @return Whether the evaluation can be skipped.
 */
ly_bool lyd_val_incr_must_skip(const struct lyd_val_incr *incr, const struct lyd_node *node,
        const struct lysc_must *must);

/**
 * @brief Count the "must" conditions evaluated and skipped for a node.
 *
 * @param[in] incr Incremental validation state.
 * @param[in] evals Conditions evaluated.
 * @param[in] skips Conditions skipped.
 */
void lyd_val_incr_must_count(const struct lyd_val_incr *incr, uint64_t evals, uint64_t skips);

/**
 * @brief Cached getnext schema nodes stored in a validation HT.
 */
struct lyd_val_getnext {
    const struct lysc_node *sparent;    /**< schema parent, NULL for top-level nodes */
    const struct lysc_node **snodes;    /**< array of schema node children excluding choices terminated by NULL */
    const struct lysc_node **choices;   /**< array of choice schema node children terminated by NULL */
};

/**
 * @brief Create a getnext cached schema node validation HT.
 *
 * @param[out] getnext_ht_p Created getnext HT.
 * @return LY_ERR value.
 */
LY_ERR lyd_val_getnext_ht_new(struct ly_ht **getnext_ht_p);

/**
 * @brief Free a getnext cached schema node validation HT.
 *
 * @param[in] getnext_ht Getnext HT to free.
 */
void lyd_val_getnext_ht_free(struct ly_ht *getnext_ht);

/**
 * @brief Get the schema children of a schema parent.
 *
 * Getnext structure cannot be returned because the pointer may become invalid on HT resize.
 *
 * @param[in] snode First schema node to use.
 * @param[in] sparent Schema parent to use.
 * @param[in] mod Module to use.
 * @param[in] output Whether to traverse operation output instead of input nodes.
 * @param[in,out] getnext_ht Getnext HT to use, new @p sparent is added to it.
 * @param[out] choices Array of getnext choices of @p sparent.
 * @param[out] snodes Array of getnext schema nodes except for choices of @p sparent.
 * @return LY_ERR value.
 */
LY_ERR lyd_val_getnext_get(const struct lysc_node *snode, const struct lysc_node *sparent, const struct lys_module *mod,
        ly_bool output, struct ly_ht *getnext_ht, const struct lysc_node ***choices, const struct lysc_node ***snodes);

/**
 * @brief Add new changes into a diff. They are always merged.
 *
 * @param[in] node Node/subtree to add.
 * @param[in] op Operation of the change.
 * @param[in,out] diff Diff to update.
 * @return LY_ERR value.
 */
LY_ERR lyd_val_diff_add(const struct lyd_node *node, enum lyd_diff_op op, struct lyd_node **diff);

/**
 * @brief Finish validation of nodes and attributes. Specifically, when (is processed first) and type validation.
 *
 * !! It is assumed autodeleted nodes cannot be in the unresolved node type set !!
 *
 * @param[in,out] tree Data tree, is updated if some nodes are autodeleted.
 * @param[in] mod Module of the @p tree to take into consideration when deleting @p tree and moving it.
 * If set, it is expected @p tree should point to the first node of @p mod. Otherwise it will simply be
 * the first top-level sibling.
 * @param[in] data_type Validate data type.
 * @param[in] node_when Set with nodes with "when" conditions, can be NULL.
 * @param[in] when_xp_opts Additional XPath options to use for evaluating "when".
 * @param[in] node_types Set with nodes with unresolved types, can be NULL
 * @param[in] meta_types Set with metadata with unresolved types, can be NULL.
 * @param[in] ext_val Set with extension data to validate, can be NULL.
 * @param[in] val_opts Validation options, see @ref datavalidationoptions.
 * @param[in,out] diff Validation diff.
 * @return LY_ERR value.
 */
LY_ERR lyd_validate_unres(struct lyd_node **tree, const struct lys_module *mod, enum lyd_type data_type,
        struct ly_set *node_when, uint32_t when_xp_opts, struct ly_set *node_types, struct ly_set *meta_types,
        struct ly_set *ext_val, uint32_t val_opts, struct lyd_node **diff);

/**
 * @brief Validate new siblings. Specifically, check duplicated instances, autodelete default values and cases.
 *
 * !! It is assumed autodeleted nodes cannot yet be in the unresolved node type set !!
 *
 * @param[in,out] first First sibling.
 * @param[in] sparent Schema parent of the siblings, NULL for top-level siblings.
 * @param[in] mod Module of the siblings, NULL for nested siblings.
 * @param[in] val_opts Validation options.
 * @param[in] int_opts Internal parser options.
 * @param[in,out] getnext_ht Getnext HT to use, new @p sparent is added to it.
 * @param[in,out] diff Validation diff.
 * @return LY_ERR value.
 */
LY_ERR lyd_validate_new(struct lyd_node **first, const struct lysc_node *sparent, const struct lys_module *mod,
        uint32_t val_opts, uint32_t int_opts, struct ly_ht *getnext_ht, struct lyd_node **diff);

/**
 * @brief Validate the whole data subtree.
 *
 * @param[in] root Subtree root.
 * @param[in] ext Extension instance whose data to validate.
 * @param[in,out] node_when Set for nodes with when conditions.
 * @param[in,out] node_types Set for unres node types.
 * @param[in,out] meta_types Set for unres metadata types.
 * @param[in,out] ext_val Set for parsed extension data to validate.
 * @param[in] val_opts Validation options.
 * @param[in] int_opts Internal parser options.
 * @param[in,out] getnext_ht Getnext HT to use.
 * @param[in,out] diff Validation diff.
 * @return LY_ERR value.
 */
LY_ERR lyd_validate_tree(struct lyd_node *root, const struct lysc_ext_instance *ext, struct ly_set *node_when,
        struct ly_set *node_types, struct ly_set *meta_types, struct ly_set *ext_val, uint32_t val_opts,
        uint32_t int_opts, struct ly_ht *getnext_ht, struct lyd_node **diff);

/**
 * @brief Validate data tree created by an extension instance by storing it in unres.
 *
 * @param[in] node Node with ::LYD_EXT flag whose subtree needs to be validated by an ext instance callback.
 * @param[in] ext Extension instance with the validation callback. If not set, is found first.
 * @param[in,out] ext_val Set with data to validate.
 * @return LY_ERR value.
 */
LY_ERR lyd_validate_tree_ext(struct lyd_node *node, const struct lysc_ext_instance *ext, struct ly_set *ext_val);

/**
 * @brief Validate data node with an extension instance, if any, by storing it in unres.
 *
 * @param[in] node Node to check for an extension instance with a validate callback.
 * @param[in,out] ext_val Set with data to validate.
 * @return LY_ERR value.
 */
LY_ERR lyd_validate_node_ext(struct lyd_node *node, struct ly_set *ext_val);

/**
 * @brief Validate must conditions of a data node.
 *
 * @param[in] node Node to validate.
 * @param[in] val_opts Validation options.
 * @param[in] int_opts Internal parser options.
 * @param[in] xpath_opts Additional XPath options to use.
 * @param[in] incr Incremental validation state, NULL to evaluate every condition.
 * @return LY_ERR value.
 */
LY_ERR lyd_validate_must(const struct lyd_node *node, uint32_t val_opts, uint32_t int_opts, uint32_t xpath_opts,
        const struct lyd_val_incr *incr);

/**
 * @brief Perform all remaining validation tasks, the data tree must be final when calling this function.
 *
 * @param[in] first First sibling.
 * @param[in] parent Data parent.
 * @param[in] sparent Schema parent of the siblings, NULL for top-level siblings.
 * @param[in] mod Module of the siblings, NULL for nested siblings.
 * @param[in] ext Extension instance to use, if relevant.
 * @param[in] val_opts Validation options (@ref datavalidationoptions).
 * @param[in] int_opts Internal parser options.
 * @param[in] must_xp_opts Additional XPath options to use for evaluating "must".
 * @param[in,out] getnext_ht Getnext HT to use.
 * @param[in] scope Scope of the incremental validation, NULL to validate everything.
 * @return LY_ERR value.
 */
LY_ERR lyd_validate_final_r(struct lyd_node *first, const struct lyd_node *parent, const struct lysc_node *sparent,
        const struct lys_module *mod, const struct lysc_ext_instance *ext, uint32_t val_opts, uint32_t int_opts,
        uint32_t must_xp_opts, struct ly_ht *getnext_ht, const struct lyd_val_scope *scope);

/**
 * @brief Validate a data tree.
 *
 * @param[in,out] tree Data tree to validate, nodes may be autodeleted.
 * @param[in] module Module whose data (and schema restrictions) to validate, NULL for all modules.
 * @param[in] ctx libyang context.
 * @param[in] val_opts Validation options, see @ref datavalidationoptions.
 * @param[in] validate_subtree Whether subtree was already validated (as part of data parsing) or not (separate validation).
 * @param[in] node_when_p Set of nodes with when conditions, if NULL a local set is used.
 * @param[in] node_types_p Set of unres node types, if NULL a local set is used.
 * @param[in] meta_types_p Set of unres metadata types, if NULL a local set is used.
 * @param[in] ext_val_p Set of unres extension data to validate, if NULL a local set is used.
 * @param[out] diff Generated validation diff, not generated if NULL.
 * @return LY_ERR value.
 */
LY_ERR lyd_validate(struct lyd_node **tree, const struct lys_module *module, const struct ly_ctx *ctx, uint32_t val_opts,
        ly_bool validate_subtree, struct ly_set *node_when_p, struct ly_set *node_types_p, struct ly_set *meta_types_p,
        struct ly_set *ext_val_p, struct lyd_node **diff);

#endif /* LY_VALIDATION_H_ */
