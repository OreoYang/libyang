/**
 * @file validation_deps.c
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

#define _GNU_SOURCE

#include "validation_deps.h"

#include <pthread.h>
#include <stdlib.h>
#include <string.h>

#include "ly_common.h"
#include "set.h"
#include "tree_schema.h"
#include "xpath.h"

/**
 * @brief Functions whose result depends only on the node sets of their arguments, which are analysed separately.
 *
 * Anything not listed here makes the whole expression unanalysable.
 */
static const char *const lyd_val_dep_pure_funcs[] = {
    "bit-is-set", "boolean", "ceiling", "concat", "contains", "count", "derived-from", "derived-from-or-self",
    "enum-value", "false", "floor", "lang", "last", "local-name", "name", "namespace-uri", "normalize-space",
    "not", "number", "position", "re-match", "round", "starts-with", "string", "string-length", "substring",
    "substring-after", "substring-before", "sum", "translate", "true", NULL
};

/**
 * @brief Axes that only ever reach a bounded, statically known set of schema nodes.
 *
 * The upward axes are included because walking up from the context node follows a single instance chain;
 * the downward and sibling axes are not, they behave like '//'.
 */
static const char *const lyd_val_dep_simple_axes[] = {
    "ancestor", "ancestor-or-self", "attribute", "child", "parent", "self", NULL
};

/**
 * @brief Functions whose result can go from true to false when nodes appear, so an expression using them
 * cannot be assumed unaffected by creations.
 */
static const char *const lyd_val_dep_antitone_funcs[] = {
    "count", "last", "not", "position", "string-length", "sum",
    /* these turn a node-set into the value of its first node, so a node that appears in front changes the result */
    "bit-is-set", "ceiling", "concat", "contains", "enum-value", "floor", "lang", "local-name", "name",
    "namespace-uri", "normalize-space", "number", "re-match", "round", "starts-with", "string", "substring",
    "substring-after", "substring-before", "translate", NULL
};

const char *
lyd_val_dep_class_str(enum lyd_val_dep_class cls)
{
    switch (cls) {
    case LYD_VAL_DEP_LOCAL:
        return "local";
    case LYD_VAL_DEP_LIST_SCOPE:
        return "list-scope";
    case LYD_VAL_DEP_BOUNDED:
        return "bounded";
    case LYD_VAL_DEP_UNBOUNDED:
        return "unbounded";
    }
    return "unbounded";
}

const char *
lyd_val_dep_kind_str(enum lyd_val_dep_kind kind)
{
    switch (kind) {
    case LYD_VAL_DEP_WHEN:
        return "when";
    case LYD_VAL_DEP_MUST:
        return "must";
    case LYD_VAL_DEP_LEAFREF:
        return "leafref";
    case LYD_VAL_DEP_UNIQUE:
        return "unique";
    }
    return "?";
}

/**
 * @brief Compare a token against a NULL-terminated list of names.
 */
static ly_bool
lyd_val_dep_tok_in(const struct lyxp_expr *expr, uint32_t tok, const char *const *names)
{
    const char *str = expr->expr + expr->tok_pos[tok];
    uint32_t len = expr->tok_len[tok];
    uint32_t i;

    for (i = 0; names[i]; ++i) {
        if ((strlen(names[i]) == len) && !strncmp(names[i], str, len)) {
            return 1;
        }
    }
    return 0;
}

static ly_bool
lyd_val_dep_tok_is(const struct lyxp_expr *expr, uint32_t tok, const char *name)
{
    const char *str = expr->expr + expr->tok_pos[tok];
    uint32_t len = expr->tok_len[tok];

    return (strlen(name) == len) && !strncmp(name, str, len);
}

/**
 * @brief Whether a token starts a new path expression, so a following '/' means an absolute path.
 */
static ly_bool
lyd_val_dep_path_start(const struct lyxp_expr *expr, uint32_t tok)
{
    if (!tok) {
        return 1;
    }

    switch (expr->tokens[tok - 1]) {
    case LYXP_TOKEN_PAR1:
    case LYXP_TOKEN_BRACK1:
    case LYXP_TOKEN_COMMA:
    case LYXP_TOKEN_OPER_LOG:
    case LYXP_TOKEN_OPER_EQUAL:
    case LYXP_TOKEN_OPER_NEQUAL:
    case LYXP_TOKEN_OPER_COMP:
    case LYXP_TOKEN_OPER_MATH:
    case LYXP_TOKEN_OPER_UNI:
        return 1;
    default:
        return 0;
    }
}

/**
 * @brief Static shape of an expression, learnt from its token stream alone.
 */
struct lyd_val_dep_shape {
    ly_bool blocked;        /**< contains a construct that cannot be reduced to a finite set of nodes */
    ly_bool abs_path;       /**< contains an absolute location path */
    ly_bool current;        /**< calls current() */
    ly_bool deref;          /**< calls deref() */
    ly_bool antitone;       /**< contains negation or node counting, so appearing nodes can violate it */
    ly_bool predicates;     /**< contains at least one predicate */
};

/**
 * @brief Whether an absolute location path starts anywhere in a token range.
 */
static ly_bool
lyd_val_dep_span_has_abs(const struct lyxp_expr *expr, uint32_t from, uint32_t to)
{
    uint32_t i;

    for (i = from; (i < to) && (i < expr->used); ++i) {
        if ((expr->tokens[i] == LYXP_TOKEN_OPER_PATH) && lyd_val_dep_path_start(expr, i)) {
            return 1;
        }
    }
    return 0;
}

/**
 * @brief Index just past the argument list of a function call starting at @p tok.
 */
static uint32_t
lyd_val_dep_call_end(const struct lyxp_expr *expr, uint32_t tok)
{
    uint32_t i, depth = 0;

    for (i = tok + 1; i < expr->used; ++i) {
        if (expr->tokens[i] == LYXP_TOKEN_PAR1) {
            ++depth;
        } else if (expr->tokens[i] == LYXP_TOKEN_PAR2) {
            if (--depth == 0) {
                return i;
            }
        }
    }
    return expr->used;
}

/**
 * @brief Token range of the boolean operand around @p tok, delimited by 'and'/'or', brackets and commas.
 */
static void
lyd_val_dep_operand_span(const struct lyxp_expr *expr, uint32_t tok, uint32_t *from, uint32_t *to)
{
    int32_t depth = 0;
    uint32_t i;

    *from = 0;
    for (i = tok; i > 0; --i) {
        switch (expr->tokens[i - 1]) {
        case LYXP_TOKEN_PAR2:
        case LYXP_TOKEN_BRACK2:
            ++depth;
            break;
        case LYXP_TOKEN_PAR1:
        case LYXP_TOKEN_BRACK1:
            if (!depth) {
                *from = i;
                goto forward;
            }
            --depth;
            break;
        case LYXP_TOKEN_COMMA:
        case LYXP_TOKEN_OPER_LOG:
            if (!depth) {
                *from = i;
                goto forward;
            }
            break;
        default:
            break;
        }
    }

forward:
    depth = 0;
    *to = expr->used;
    for (i = tok + 1; i < expr->used; ++i) {
        switch (expr->tokens[i]) {
        case LYXP_TOKEN_PAR1:
        case LYXP_TOKEN_BRACK1:
            ++depth;
            break;
        case LYXP_TOKEN_PAR2:
        case LYXP_TOKEN_BRACK2:
            if (!depth) {
                *to = i;
                return;
            }
            --depth;
            break;
        case LYXP_TOKEN_COMMA:
        case LYXP_TOKEN_OPER_LOG:
            if (!depth) {
                *to = i;
                return;
            }
            break;
        default:
            break;
        }
    }
}

static void
lyd_val_dep_shape_scan(const struct lyxp_expr *expr, struct lyd_val_dep_shape *shape)
{
    uint32_t i;
    const char *str;
    uint32_t len;

    memset(shape, 0, sizeof *shape);

    for (i = 0; i < expr->used; ++i) {
        switch (expr->tokens[i]) {
        case LYXP_TOKEN_OPER_RPATH:
        case LYXP_TOKEN_NODETYPE:
        case LYXP_TOKEN_VARREF:
            /* '//', node()/text() and variables all reach an unbounded set of nodes */
            shape->blocked = 1;
            return;
        case LYXP_TOKEN_AXISNAME:
            if (!lyd_val_dep_tok_in(expr, i, lyd_val_dep_simple_axes)) {
                shape->blocked = 1;
                return;
            }
            break;
        case LYXP_TOKEN_NAMETEST:
            str = expr->expr + expr->tok_pos[i];
            len = expr->tok_len[i];
            if (str[len - 1] == '*') {
                /* '*' or 'pfx:*' */
                shape->blocked = 1;
                return;
            }
            break;
        case LYXP_TOKEN_FUNCNAME:
            if (lyd_val_dep_tok_is(expr, i, "current")) {
                shape->current = 1;
            } else if (lyd_val_dep_tok_is(expr, i, "deref")) {
                shape->deref = 1;
                shape->antitone = 1;
            } else if (!lyd_val_dep_tok_in(expr, i, lyd_val_dep_pure_funcs)) {
                shape->blocked = 1;
                return;
            }
            if (lyd_val_dep_tok_in(expr, i, lyd_val_dep_antitone_funcs) &&
                    lyd_val_dep_span_has_abs(expr, i, lyd_val_dep_call_end(expr, i))) {
                /* negating or counting something reachable only from the data root; nodes appearing
                 * elsewhere in the tree can flip the result */
                shape->antitone = 1;
            }
            break;
        case LYXP_TOKEN_OPER_MATH: {
            uint32_t from, to;

            /* arithmetic turns a node-set into the number of its first node, like number() */
            lyd_val_dep_operand_span(expr, i, &from, &to);
            if (lyd_val_dep_span_has_abs(expr, from, to)) {
                shape->antitone = 1;
            }
            break;
        }
        case LYXP_TOKEN_OPER_NEQUAL: {
            uint32_t from, to;

            lyd_val_dep_operand_span(expr, i, &from, &to);
            if (lyd_val_dep_span_has_abs(expr, from, to)) {
                shape->antitone = 1;
            }
            break;
        }
        case LYXP_TOKEN_BRACK1:
            shape->predicates = 1;
            break;
        case LYXP_TOKEN_OPER_PATH:
            if (lyd_val_dep_path_start(expr, i)) {
                shape->abs_path = 1;
            }
            break;
        default:
            break;
        }
    }
}

/**
 * @brief Depth of a schema node in the data tree, 1 for top-level nodes.
 */
static uint32_t
lyd_val_dep_depth(const struct lysc_node *snode)
{
    uint32_t depth = 0;

    while (snode) {
        ++depth;
        snode = lysc_data_parent(snode);
    }
    return depth;
}

static ly_bool
lyd_val_dep_is_ancestor(const struct lysc_node *anc, const struct lysc_node *snode)
{
    while (snode) {
        if (snode == anc) {
            return 1;
        }
        snode = lysc_data_parent(snode);
    }
    return 0;
}

/**
 * @brief Lowest common data ancestor of two schema nodes, NULL if they only meet at the tree root.
 */
static const struct lysc_node *
lyd_val_dep_lca(const struct lysc_node *n1, const struct lysc_node *n2)
{
    uint32_t d1 = lyd_val_dep_depth(n1), d2 = lyd_val_dep_depth(n2);

    while (d1 > d2) {
        n1 = lysc_data_parent(n1);
        --d1;
    }
    while (d2 > d1) {
        n2 = lysc_data_parent(n2);
        --d2;
    }
    while (n1 != n2) {
        n1 = lysc_data_parent(n1);
        n2 = lysc_data_parent(n2);
    }
    return n1;
}

/**
 * @brief Whether reaching @p snode from @p lca passes through a list or leaf-list, meaning the step
 * yields a whole set of instances instead of at most one.
 */
static ly_bool
lyd_val_dep_crosses_list(const struct lysc_node *lca, const struct lysc_node *snode)
{
    while (snode && (snode != lca)) {
        if (snode->nodetype & (LYS_LIST | LYS_LEAFLIST)) {
            return 1;
        }
        snode = lysc_data_parent(snode);
    }
    return 0;
}

/**
 * @brief Whether every predicate in the expression selects instances by a list key.
 *
 * Only key predicates make a target instance immune to creations: a new list instance always carries a key
 * value that no existing referrer can already be pointing at.
 */
static ly_bool
lyd_val_dep_preds_are_keys(const struct lyxp_expr *expr, const struct ly_set *atoms)
{
    const char *name;
    uint32_t i, j, len;
    ly_bool matched;

    for (i = 0; i + 1 < expr->used; ++i) {
        if (expr->tokens[i] != LYXP_TOKEN_BRACK1) {
            continue;
        }
        if (expr->tokens[i + 1] != LYXP_TOKEN_NAMETEST) {
            /* positional or otherwise non-key predicate */
            return 0;
        }

        /* drop the prefix, atoms are matched by their local name */
        name = expr->expr + expr->tok_pos[i + 1];
        len = expr->tok_len[i + 1];
        for (j = 0; j < len; ++j) {
            if (name[j] == ':') {
                name += j + 1;
                len -= j + 1;
                break;
            }
        }

        matched = 0;
        for (j = 0; j < atoms->count; ++j) {
            const struct lysc_node *atom = atoms->snodes[j];

            if (!atom || (strlen(atom->name) != len) || strncmp(atom->name, name, len)) {
                continue;
            }
            if (!(atom->flags & LYS_KEY)) {
                return 0;
            }
            matched = 1;
        }
        if (!matched) {
            return 0;
        }
    }

    return 1;
}

/**
 * @brief Local name of a NameTest token.
 */
static const char *
lyd_val_dep_nametest_local(const struct lyxp_expr *expr, uint32_t tok, uint32_t *len)
{
    const char *name = expr->expr + expr->tok_pos[tok];
    uint32_t i;

    *len = expr->tok_len[tok];
    for (i = 0; i < *len; ++i) {
        if (name[i] == ':') {
            *len -= i + 1;
            return name + i + 1;
        }
    }
    return name;
}

/**
 * @brief Whether an expression counts nothing but the instances holding the same @p snode value as the instance
 * it is evaluated on.
 *
 * Accepted shape is exactly "count(<path>[<snode> = current()]) <cmp> <number>", where the path is a plain
 * location path whose only predicate is its last step, and where every node the expression reads lies on the
 * ancestor chain of @p snode. Together that leaves the value of the validated instance as the expression's only
 * input besides the tree, so the result can only change when an instance of @p snode holding that value appears
 * or disappears.
 */
static ly_bool
lyd_val_dep_value_keyed_shape(const struct lyxp_expr *expr, const struct lysc_node *snode, const struct ly_set *atoms)
{
    uint32_t end, brack1, i, len;
    const char *name;
    ly_bool self = 0;

    if (!expr || !atoms || !(snode->nodetype & LYD_NODE_TERM)) {
        return 0;
    }

    /* count( ... ) <cmp> <number> and nothing else */
    if ((expr->used < 2) || (expr->tokens[0] != LYXP_TOKEN_FUNCNAME) || !lyd_val_dep_tok_is(expr, 0, "count") ||
            (expr->tokens[1] != LYXP_TOKEN_PAR1)) {
        return 0;
    }
    end = lyd_val_dep_call_end(expr, 0);
    if ((end < 9) || (end + 3 != expr->used) || (expr->tokens[end] != LYXP_TOKEN_PAR2) ||
            (expr->tokens[end + 1] != LYXP_TOKEN_OPER_COMP) || (expr->tokens[end + 2] != LYXP_TOKEN_NUMBER)) {
        return 0;
    }

    /* the single predicate is the last step of the path: [<name> = current()] */
    brack1 = end - 7;
    if ((expr->tokens[brack1] != LYXP_TOKEN_BRACK1) || (expr->tokens[brack1 + 1] != LYXP_TOKEN_NAMETEST) ||
            (expr->tokens[brack1 + 2] != LYXP_TOKEN_OPER_EQUAL) ||
            (expr->tokens[brack1 + 3] != LYXP_TOKEN_FUNCNAME) || !lyd_val_dep_tok_is(expr, brack1 + 3, "current") ||
            (expr->tokens[brack1 + 4] != LYXP_TOKEN_PAR1) || (expr->tokens[brack1 + 5] != LYXP_TOKEN_PAR2) ||
            (expr->tokens[brack1 + 6] != LYXP_TOKEN_BRACK2)) {
        return 0;
    }

    /* everything before it is a plain location path, so there is no other predicate and no other function */
    for (i = 2; i < brack1; ++i) {
        if ((expr->tokens[i] != LYXP_TOKEN_OPER_PATH) && (expr->tokens[i] != LYXP_TOKEN_NAMETEST)) {
            return 0;
        }
    }

    /* the predicate compares the constrained node itself */
    name = lyd_val_dep_nametest_local(expr, brack1 + 1, &len);
    if ((strlen(snode->name) != len) || strncmp(snode->name, name, len)) {
        return 0;
    }

    /* the expression reads only the constrained node and its ancestors, so its node set is selected by nothing
     * but the compared value */
    for (i = 0; i < atoms->count; ++i) {
        if (!atoms->snodes[i]) {
            continue;
        }
        if (!lyd_val_dep_is_ancestor(atoms->snodes[i], snode)) {
            return 0;
        }
        if (atoms->snodes[i] == snode) {
            self = 1;
        }
    }

    return self;
}

enum lyd_val_dep_class
lyd_val_dep_classify_expr(const struct lysc_node *ctx_node, const struct lys_module *cur_mod,
        const struct lyxp_expr *expr, const struct lysc_prefix *prefixes, struct ly_set **atoms,
        ly_bool *creation_safe, const struct lysc_node **unit)
{
    struct lyd_val_dep_shape shape;
    struct ly_set *set = NULL;
    const struct lysc_node *region, *lca, *iter, *atom;
    ly_bool crosses_list = 0;
    uint32_t i;

    if (atoms) {
        *atoms = NULL;
    }
    if (creation_safe) {
        *creation_safe = 0;
    }
    if (unit) {
        *unit = NULL;
    }
    if (!expr) {
        return LYD_VAL_DEP_UNBOUNDED;
    }

    lyd_val_dep_shape_scan(expr, &shape);

    /* the atoms are needed even for expressions we cannot classify, the caller uses them to decide whether
     * an edit could have changed the result at all */
    if (lys_find_expr_atoms(ctx_node, cur_mod, expr, prefixes, LYS_FIND_XP_SCHEMA, &set)) {
        ly_set_free(set, NULL);
        return LYD_VAL_DEP_UNBOUNDED;
    }
    if (atoms) {
        *atoms = set;
    }

    if (shape.blocked) {
        goto unbounded;
    }
    if (shape.abs_path || shape.deref) {
        /* leaves the context instance; only usable if the target instance is picked by a key predicate */
        goto cross_instance;
    }
    if (!ctx_node) {
        /* evaluated from the data root, every step is cross-instance */
        goto cross_instance;
    }

    region = ctx_node;
    for (i = 0; i < set->count; ++i) {
        atom = set->snodes[i];
        if (!atom) {
            continue;
        }

        lca = lyd_val_dep_lca(atom, ctx_node);
        if (!lca) {
            /* the expression walks above the top-level node it started from */
            goto cross_instance;
        }
        if (!lyd_val_dep_is_ancestor(atom, ctx_node) && lyd_val_dep_crosses_list(lca, atom)) {
            crosses_list = 1;
        }
        region = lyd_val_dep_lca(region, lca);
        if (!region) {
            goto cross_instance;
        }
    }

    /* the deepest list instance that contains the whole region is what confines this constraint */
    for (iter = region; iter; iter = lysc_data_parent(iter)) {
        if (iter->nodetype == LYS_LIST) {
            break;
        }
    }
    if (!iter) {
        /* no list confines the region; that is only safe if the context node itself is not inside a list,
         * otherwise the expression spans every sibling instance */
        for (atom = ctx_node; atom; atom = lysc_data_parent(atom)) {
            if (atom->nodetype == LYS_LIST) {
                goto cross_instance;
            }
        }
        /* confined to the top-level instance only */
    }
    if (unit) {
        *unit = iter;
    }

    return crosses_list ? LYD_VAL_DEP_LIST_SCOPE : LYD_VAL_DEP_LOCAL;

cross_instance:
    if (shape.blocked) {
        goto unbounded;
    }
    if (!shape.current && !shape.deref) {
        goto unbounded;
    }
    if (creation_safe && !shape.antitone && shape.predicates && lyd_val_dep_preds_are_keys(expr, set)) {
        *creation_safe = 1;
    }
    return LYD_VAL_DEP_BOUNDED;

unbounded:
    return LYD_VAL_DEP_UNBOUNDED;
}

/**
 * @brief Turn an atom set into a NULL-terminated array owned by the index.
 */
static LY_ERR
lyd_val_dep_atoms_store(struct ly_set *set, const struct lysc_node ***atoms_p)
{
    const struct lysc_node **atoms;
    uint32_t i, count = 0;

    atoms = calloc(set ? set->count + 1 : 1, sizeof *atoms);
    if (!atoms) {
        return LY_EMEM;
    }
    for (i = 0; set && (i < set->count); ++i) {
        if (set->snodes[i]) {
            atoms[count++] = set->snodes[i];
        }
    }
    atoms[count] = NULL;
    *atoms_p = atoms;
    return LY_SUCCESS;
}

static LY_ERR
lyd_val_dep_add(struct lyd_val_dep_index *index, const struct lysc_node *snode, enum lyd_val_dep_kind kind,
        enum lyd_val_dep_class cls, ly_bool creation_safe, const struct lysc_node *unit, const char *expr,
        struct ly_set *atom_set)
{
    struct lyd_val_constraint *c, *mem;
    uint32_t *nl, i;

    mem = realloc(index->constraints, (index->constraint_count + 1) * sizeof *index->constraints);
    if (!mem) {
        return LY_EMEM;
    }
    index->constraints = mem;

    c = &index->constraints[index->constraint_count];
    memset(c, 0, sizeof *c);
    c->snode = snode;
    c->kind = kind;
    c->cls = cls;
    c->creation_safe = creation_safe;
    c->unit = unit;
    c->expr = expr;
    LY_CHECK_RET(lyd_val_dep_atoms_store(atom_set, &c->atoms));

    if ((cls == LYD_VAL_DEP_BOUNDED) || (cls == LYD_VAL_DEP_UNBOUNDED)) {
        nl = realloc(index->nonlocal, (index->nonlocal_count + 1) * sizeof *index->nonlocal);
        if (!nl) {
            return LY_EMEM;
        }
        index->nonlocal = nl;
        index->nonlocal[index->nonlocal_count++] = index->constraint_count;
    } else if (!unit) {
        for (i = 0; c->atoms[i]; ++i) {
            LY_CHECK_RET(ly_set_add(&index->toplevel_atoms, (void *)c->atoms[i], 0, NULL));
        }
    }

    ++index->class_count[cls];
    ++index->constraint_count;
    return LY_SUCCESS;
}

/**
 * @brief Mark the constraint added last as value-keyed.
 */
static LY_ERR
lyd_val_dep_value_keyed_mark(struct lyd_val_dep_index *index, const struct lyxp_expr *cond)
{
    uint32_t *vk;

    vk = realloc(index->value_keyed, (index->value_keyed_count + 1) * sizeof *index->value_keyed);
    if (!vk) {
        return LY_EMEM;
    }
    index->value_keyed = vk;
    index->value_keyed[index->value_keyed_count++] = index->constraint_count - 1;

    index->constraints[index->constraint_count - 1].cond = cond;
    index->constraints[index->constraint_count - 1].value_keyed = 1;
    return LY_SUCCESS;
}

ly_bool
lyd_val_deps_value_keyed(const struct lyd_val_dep_index *index, const struct lysc_node *snode,
        const struct lyxp_expr *cond)
{
    const struct lyd_val_constraint *c;
    uint32_t i;

    for (i = 0; i < index->value_keyed_count; ++i) {
        c = &index->constraints[index->value_keyed[i]];
        if ((c->snode == snode) && (c->cond == cond)) {
            return 1;
        }
    }
    return 0;
}

/**
 * @brief Classify every leafref inside a (possibly union) type, and flag the module for instance-identifiers.
 */
static LY_ERR
lyd_val_dep_add_leafrefs(struct lyd_val_dep_index *index, const struct lysc_node *snode, const struct lysc_type *type)
{
    const struct lysc_type_leafref *lref;
    const struct lysc_type_union *uni;
    struct ly_set *atom_set = NULL;
    const struct lysc_node *unit;
    enum lyd_val_dep_class cls;
    LY_ARRAY_COUNT_TYPE u;
    LY_ERR rc;

    switch (type->basetype) {
    case LY_TYPE_LEAFREF:
        lref = (const struct lysc_type_leafref *)type;
        if (!lref->require_instance) {
            /* nothing is checked against the data tree */
            return LY_SUCCESS;
        }
        cls = lyd_val_dep_classify_expr(snode, snode->module, lref->path, lref->prefixes, &atom_set, NULL, &unit);

        /* a require-instance leafref only asks whether some node in the target set carries this value, and
         * creating data can only add to that set, so no creation can invalidate an existing leafref */
        rc = lyd_val_dep_add(index, snode, LYD_VAL_DEP_LEAFREF, cls, atom_set ? 1 : 0, unit,
                lref->path ? lref->path->expr : "", atom_set);
        ly_set_free(atom_set, NULL);
        return rc;
    case LY_TYPE_INST:
        if (((const struct lysc_type_instanceid *)type)->require_instance && (snode->flags & LYS_CONFIG_W)) {
            index->unanalysable = 1;
        }
        return LY_SUCCESS;
    case LY_TYPE_UNION:
        uni = (const struct lysc_type_union *)type;
        LY_ARRAY_FOR(uni->types, u) {
            LY_CHECK_RET(lyd_val_dep_add_leafrefs(index, snode, uni->types[u]));
        }
        return LY_SUCCESS;
    default:
        return LY_SUCCESS;
    }
}

ly_bool
lyd_val_deps_is_implicit(const struct lysc_node *snode)
{
    switch (snode->nodetype) {
    case LYS_LEAF:
        return ((const struct lysc_node_leaf *)snode)->dflt ? 1 : 0;
    case LYS_LEAFLIST:
        return ((const struct lysc_node_leaflist *)snode)->dflts ? 1 : 0;
    case LYS_CONTAINER:
        return (snode->flags & LYS_PRESENCE) ? 0 : 1;
    default:
        return 0;
    }
}

static LY_ERR
lyd_val_dep_add_node(struct lyd_val_dep_index *index, const struct lysc_node *snode)
{
    struct lysc_when **whens;
    struct lysc_must *musts;
    struct ly_set *atom_set = NULL;
    const struct lysc_node *unit;
    enum lyd_val_dep_class cls;
    ly_bool creation_safe;
    LY_ARRAY_COUNT_TYPE u;
    LY_ERR rc = LY_SUCCESS;

    whens = lysc_node_when(snode);
    if (whens && lyd_val_deps_is_implicit(snode)) {
        LY_CHECK_RET(ly_set_add(&index->dflt_when, (void *)snode, 0, NULL));
    }
    LY_ARRAY_FOR(whens, u) {
        cls = lyd_val_dep_classify_expr(whens[u]->context, snode->module, whens[u]->cond, whens[u]->prefixes,
                &atom_set, &creation_safe, &unit);
        rc = lyd_val_dep_add(index, snode, LYD_VAL_DEP_WHEN, cls, creation_safe, unit, whens[u]->cond->expr, atom_set);
        ly_set_free(atom_set, NULL);
        LY_CHECK_RET(rc);
    }

    musts = lysc_node_musts(snode);
    LY_ARRAY_FOR(musts, u) {
        cls = lyd_val_dep_classify_expr(snode, snode->module, musts[u].cond, musts[u].prefixes,
                &atom_set, &creation_safe, &unit);
        rc = lyd_val_dep_add(index, snode, LYD_VAL_DEP_MUST, cls, creation_safe, unit, musts[u].cond->expr, atom_set);

        /* an implicit default appears without the edit describing it, so its value could not be recognised as
         * touched and the constraint has to keep being evaluated on every instance */
        if (!rc && (cls == LYD_VAL_DEP_BOUNDED) && !lyd_val_deps_is_implicit(snode) &&
                lyd_val_dep_value_keyed_shape(musts[u].cond, snode, atom_set)) {
            rc = lyd_val_dep_value_keyed_mark(index, musts[u].cond);
        }
        ly_set_free(atom_set, NULL);
        LY_CHECK_RET(rc);
    }

    if (snode->nodetype & LYD_NODE_TERM) {
        LY_CHECK_RET(lyd_val_dep_add_leafrefs(index, snode, ((const struct lysc_node_leaf *)snode)->type));
    }

    if (snode->nodetype == LYS_LIST) {
        const struct lysc_node_list *slist = (const struct lysc_node_list *)snode;

        /* a unique spans the instances of one list under one parent, so it is confined by the first list above
         * that parent; the scoped final pass runs the sibling checks of every parent it descends through, so a
         * unique is always rechecked without needing any atoms of its own */
        for (unit = lysc_data_parent(snode); unit; unit = lysc_data_parent(unit)) {
            if (unit->nodetype == LYS_LIST) {
                break;
            }
        }
        LY_ARRAY_FOR(slist->uniques, u) {
            LY_CHECK_RET(lyd_val_dep_add(index, snode, LYD_VAL_DEP_UNIQUE, LYD_VAL_DEP_LIST_SCOPE, 1, unit,
                    "unique", NULL));
        }
    }

    return LY_SUCCESS;
}

static void
lyd_val_dep_index_free(struct lyd_val_dep_index *index)
{
    uint32_t i;

    if (!index) {
        return;
    }
    for (i = 0; i < index->constraint_count; ++i) {
        free((void *)index->constraints[i].atoms);
    }
    free(index->constraints);
    free(index->nonlocal);
    free(index->value_keyed);
    ly_set_erase(&index->toplevel_atoms, NULL);
    ly_set_erase(&index->dflt_when, NULL);
    free(index);
}

static LY_ERR
lyd_val_dep_index_build(const struct lys_module *mod, struct lyd_val_dep_index **index_p)
{
    struct lyd_val_dep_index *index;
    const struct lysc_node *snode, *root;
    LY_ERR rc = LY_SUCCESS;

    index = calloc(1, sizeof *index);
    LY_CHECK_ERR_RET(!index, LOGMEM(mod->ctx), LY_EMEM);
    index->mod = mod;
    index->change_count = ly_ctx_get_change_count(mod->ctx);

    if (!mod->compiled) {
        goto cleanup;
    }

    LY_LIST_FOR(mod->compiled->data, root) {
        const struct lysc_node *elem;

        LYSC_TREE_DFS_BEGIN(root, elem) {
            rc = lyd_val_dep_add_node(index, elem);
            LY_CHECK_GOTO(rc, cleanup);
            LYSC_TREE_DFS_END(root, elem);
        }
    }

    /* RPC/action/notification data are validated separately, but their constraints still belong to the module */
    LY_LIST_FOR((const struct lysc_node *)mod->compiled->rpcs, snode) {
        rc = lyd_val_dep_add_node(index, snode);
        LY_CHECK_GOTO(rc, cleanup);
    }
    LY_LIST_FOR((const struct lysc_node *)mod->compiled->notifs, snode) {
        rc = lyd_val_dep_add_node(index, snode);
        LY_CHECK_GOTO(rc, cleanup);
    }

cleanup:
    if (rc) {
        lyd_val_dep_index_free(index);
        return rc;
    }
    *index_p = index;
    return LY_SUCCESS;
}

LY_ERR
lyd_val_deps_get(const struct lys_module *mod, const struct lyd_val_dep_index **index)
{
    struct ly_ctx *ctx = mod->ctx;
    struct lyd_val_dep_index *built = NULL, **mem;
    uint32_t i;
    LY_ERR rc = LY_SUCCESS;

    pthread_mutex_lock(&ctx->val_deps_lock);

    for (i = 0; i < ctx->val_deps_count; ++i) {
        if (ctx->val_deps[i]->mod != mod) {
            continue;
        }

        if (ctx->val_deps[i]->change_count == ly_ctx_get_change_count(ctx)) {
            *index = ctx->val_deps[i];
            goto cleanup;
        }

        /* the schema changed after the index was built, it may miss constraints added to this module or constraints
         * reading nodes that changed; the index is only used during one validation call and the schema must not
         * change while data are being validated, so no one can still hold the old one */
        rc = lyd_val_dep_index_build(mod, &built);
        LY_CHECK_GOTO(rc, cleanup);
        lyd_val_dep_index_free(ctx->val_deps[i]);
        ctx->val_deps[i] = built;
        *index = built;
        goto cleanup;
    }

    rc = lyd_val_dep_index_build(mod, &built);
    LY_CHECK_GOTO(rc, cleanup);

    mem = realloc(ctx->val_deps, (ctx->val_deps_count + 1) * sizeof *ctx->val_deps);
    if (!mem) {
        lyd_val_dep_index_free(built);
        rc = LY_EMEM;
        goto cleanup;
    }
    ctx->val_deps = mem;
    ctx->val_deps[ctx->val_deps_count++] = built;
    *index = built;

cleanup:
    pthread_mutex_unlock(&ctx->val_deps_lock);
    return rc;
}

void
lyd_val_deps_ctx_free(struct ly_ctx *ctx)
{
    uint32_t i;

    for (i = 0; i < ctx->val_deps_count; ++i) {
        lyd_val_dep_index_free(ctx->val_deps[i]);
    }
    free(ctx->val_deps);
    ctx->val_deps = NULL;
    ctx->val_deps_count = 0;
}
