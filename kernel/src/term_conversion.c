/* Comparison by syntax: equality up to bound names and the interval algebra,
 * with nothing reduced or unfolded, and cumulativity built on it. This is the
 * comparison the instructions use. Interval normal forms remain De Morgan
 * expressions; endpoint tests are face formulas. An unbound name must never
 * be identified with a binder on the other side. */
#include "term_internal.h"

typedef struct alpha_binding {
    uint32_t left, right;
    uint64_t scope;
    bool identity;
    size_t previous;
    /* Every name this binding and the ones before it rename, one bit per
     * name modulo 64, as cc_node's masks: a symbol, or a dimension. */
    uint64_t left_mask, right_mask;
} alpha_binding;

/* Bindings live in the comparison frames. Scope links are indices, so
 * growing the frame array never leaves a pointer into its old allocation. */
typedef struct {
    cc_term a, b;
    size_t terms, dims, inner_dims;
    cc_node left, right;
    alpha_binding binding;
    uint64_t term_scope, dimension_scope;
    size_t slot;
    unsigned next;
    bool tubes, waiting, cache;
} alpha_frame;

static const alpha_binding *binding_at(const alpha_frame *frames, size_t index) {
    return index ? &frames[index - 1].binding : NULL;
}

static size_t comparison_slot(uint64_t hash) {
    /* Arena handles and binder names are sequential. Mix their high bits too,
     * rather than letting the power-of-two table discard them outright. */
    hash ^= hash >> 33;
    hash *= UINT64_C(0xff51afd7ed558ccd);
    hash ^= hash >> 33;
    return (size_t)(hash % CC_ALPHA_MEMO_SIZE);
}

static alpha_binding bind(cc_kernel *k, uint32_t left, uint32_t right,
                           const alpha_frame *frames, size_t previous_index) {
    const alpha_binding *previous = binding_at(frames, previous_index);
    uint64_t parent = previous ? previous->scope : 0;
    size_t slot = comparison_slot((parent * UINT64_C(1099511628211) ^ left) *
                                 UINT64_C(1099511628211) ^ right);
    if (!k->alpha_scopes)
        k->alpha_scopes = calloc(CC_ALPHA_MEMO_SIZE, sizeof *k->alpha_scopes);
    cc_alpha_scope *entry = k->alpha_scopes ? &k->alpha_scopes[slot] : NULL;
    uint64_t scope;
    if (entry && entry->scope && entry->parent == parent && entry->left == left && entry->right == right) {
        scope = entry->scope;
    } else {
        if (k->next_alpha_scope == UINT64_MAX)
            ck_fail_as(k, CC_ERROR_RESOURCE, "Alpha-comparison scope counter exhausted.");
        scope = k->next_alpha_scope == UINT64_MAX ? UINT64_MAX : ++k->next_alpha_scope;
        if (entry) *entry = (cc_alpha_scope){left, right, parent, scope};
    }
    return (alpha_binding){left, right, scope,
        left == right && (!previous || previous->identity), previous_index,
        (previous ? previous->left_mask : 0) | UINT64_C(1) << (left % 64),
        (previous ? previous->right_mask : 0) | UINT64_C(1) << (right % 64)};
}

static size_t alpha_slot(cc_term left, cc_term right, uint64_t terms, uint64_t dims) {
    uint64_t hash = (uint64_t)left * UINT64_C(1099511628211);
    hash = (hash ^ right) * UINT64_C(1099511628211);
    hash = (hash ^ terms) * UINT64_C(1099511628211);
    hash = (hash ^ dims) * UINT64_C(1099511628211);
    return comparison_slot(hash);
}

static size_t bound(const alpha_frame *frames, size_t env, uint32_t name, bool right) {
    for (; env; env = binding_at(frames, env)->previous) {
        const alpha_binding *binding = binding_at(frames, env);
        if ((right ? binding->right : binding->left) == name)
            return env;
    }
    return 0;
}

static bool same_name(uint32_t a, uint32_t b, const alpha_frame *frames, size_t env) {
    size_t left = bound(frames, env, a, false);
    size_t right = bound(frames, env, b, true);
    return left || right ? left && left == right : a == b;
}

/* Levels are equal when their normal forms are (G0 §2.9), with each
 * variable bound on the way down named by the binding it resolves to, so
 * that λ (x < ω). U(x) and λ (y < ω). U(y) agree. Free variables keep their
 * symbols; bound ones take keys above every symbol. */
static void bound_keys(cc_level_nf *nf, const alpha_frame *frames, size_t terms, bool right) {
    for (uint32_t i = 0; i < nf->count; ++i) {
        const alpha_binding *binding = binding_at(frames, bound(frames, terms, (uint32_t)nf->terms[i].key, right));
        if (binding)
            nf->terms[i].key = UINT64_C(1) << 63 | binding->scope;
    }
    ck_level_nf_sort(nf);
}

static bool level_alpha(cc_kernel *k, cc_term a, cc_term b, const alpha_frame *frames, size_t terms) {
    if (a == b && a < k->count && k->nodes[a].kind == CC_LCONST)
        return true;
    if (!terms)
        return ck_level_equal(k, a, b);
    cc_level_nf left, right;
    if (!ck_level_normal(k, a, &left))
        return false;
    bool equal = false;
    if (ck_level_normal(k, b, &right)) {
        bound_keys(&left, frames, terms, false);
        bound_keys(&right, frames, terms, true);
        equal = ck_level_nf_equal(&left, &right);
        ck_level_nf_free(&right);
    }
    ck_level_nf_free(&left);
    return equal && !k->error[0];
}

static bool clause_included(cc_clause a, cc_clause b, const alpha_frame *frames, size_t dims) {
    for (unsigned i = 0; i < CC_DIMENSIONS; ++i) {
        uint64_t bit = UINT64_C(1) << i;
        for (unsigned endpoint = 0; endpoint < 2; ++endpoint) {
            if (!((endpoint ? a.positive : a.negative) & bit))
                continue;
            bool found = false;
            for (unsigned j = 0; j < CC_DIMENSIONS; ++j)
                if (((endpoint ? b.positive : b.negative) & (UINT64_C(1) << j)) && same_name(i, j, frames, dims)) {
                    found = true;
                    break;
                }
            if (!found)
                return false;
        }
    }
    return true;
}

static unsigned literals(cc_clause clause) {
    return (unsigned)__builtin_popcountll(clause.positive) + (unsigned)__builtin_popcountll(clause.negative);
}

static bool formula_equal(cc_kernel *k, uint32_t a, uint32_t b, const alpha_frame *frames, size_t dims) {
    /* The same formula, with no dimension binder renamed on the way. */
    if (a == b && !dims)
        return cc_kernel_get_formula(k, a) != NULL;
    const cc_formula *left = cc_kernel_get_formula(k, a);
    const cc_formula *right = cc_kernel_get_formula(k, b);
    if (!left || !right || left->sort != right->sort || left->length != right->length)
        return false;
    for (size_t i = 0; i < left->length; ++i) {
        bool found = false;
        unsigned l = literals(left->clauses[i]);
        /* A binder renaming is bijective. Forward inclusion plus equal
         * literal counts therefore establishes equality of the clauses. */
        for (size_t j = 0; j < right->length; ++j) {
            if (l == literals(right->clauses[j]) && clause_included(left->clauses[i], right->clauses[j], frames, dims)) {
                found = true;
                break;
            }
        }
        if (!found)
            return false;
    }
    return true;
}

/* Scope pruning asks only about names that could occur, retaining exact
 * free-name checks for colliding symbol bits and bound annotations. */
static bool renamed_free(cc_kernel *k, cc_term term, const alpha_frame *frames, size_t env, bool right) {
    const alpha_binding *scope = binding_at(frames, env);
    uint64_t mask = k->nodes[term].symbols;
    if (!(mask & (right ? scope->right_mask : scope->left_mask)))
        return false;
    for (; env && !k->error[0]; env = binding_at(frames, env)->previous) {
        const alpha_binding *binding = binding_at(frames, env);
        uint32_t name = right ? binding->right : binding->left;
        if ((mask & UINT64_C(1) << (name % 64)) && ck_term_free(k, term, name))
            return true;
    }
    return false;
}

static bool renamed_dims_free(cc_kernel *k, cc_term term, const alpha_frame *frames, size_t env, bool right) {
    const alpha_binding *scope = binding_at(frames, env);
    uint64_t renamed = right ? scope->right_mask : scope->left_mask;
    return (k->nodes[term].dims & renamed) && (ck_free_dims(k, term) & renamed);
}

static bool same_key(const cc_alpha_memo *entry, cc_term a, cc_term b, uint64_t terms, uint64_t dims) {
    return entry->left == a && entry->right == b && entry->term_scope == terms && entry->dimension_scope == dims;
}

static void alpha_completed(cc_kernel *k, const alpha_frame *f, bool equal) {
    if (!f->cache || k->error[0]) return;
    if (!k->alpha_memo) {
        k->alpha_memo = calloc(CC_ALPHA_MEMO_SIZE, sizeof *k->alpha_memo);
        if (!k->alpha_memo) {
            ck_fail_as(k, CC_ERROR_RESOURCE, "Alpha-comparison memo allocation failed.");
            return;
        }
    }
    /* A child may have reused the slot. Publish only this completed answer. */
    k->alpha_memo[f->slot] = (cc_alpha_memo){f->a, f->b, f->term_scope, f->dimension_scope,
                                           equal ? CC_FOLDED_EQUAL : CC_FOLDED_DIFFERENT};
}

/* Return true only when children remain. Common cached, identical and leaf
 * comparisons finish before allocating a continuation frame. */
static bool alpha_ready(cc_kernel *k, alpha_frame *f, const alpha_frame *frames, bool *equal) {
    cc_term a = f->a, b = f->b;
    *equal = false;
    if (k->error[0]) return false;
    if (f->tubes) {
        if (!a || !b) { *equal = a == b; return false; }
        f->left = k->nodes[a]; f->right = k->nodes[b];
        return f->left.kind == CC_TUBE && f->right.kind == CC_TUBE &&
               formula_equal(k, f->left.payload, f->right.payload, frames, f->dims);
    }
    if (a && b && a < k->count && b < k->count && (k->nodes[a].depth >= 8 || k->nodes[b].depth >= 8)) {
        const alpha_binding *terms = binding_at(frames, f->terms), *dims = binding_at(frames, f->dims);
        if (terms && !terms->identity && !renamed_free(k, a, frames, f->terms, false) &&
            !renamed_free(k, b, frames, f->terms, true)) f->terms = 0;
        if (dims && !dims->identity && !renamed_dims_free(k, a, frames, f->dims, false) &&
            !renamed_dims_free(k, b, frames, f->dims, true)) f->dims = 0;
        if (k->error[0]) return false;
    }
    const alpha_binding *terms = binding_at(frames, f->terms), *dims = binding_at(frames, f->dims);
    f->term_scope = terms && !terms->identity ? terms->scope : 0;
    f->dimension_scope = dims && !dims->identity ? dims->scope : 0;
    f->slot = alpha_slot(a, b, f->term_scope, f->dimension_scope);
    if (a && b && k->alpha_memo && same_key(&k->alpha_memo[f->slot], a, b, f->term_scope, f->dimension_scope)) {
        uint8_t folded = k->alpha_memo[f->slot].folded;
        if (folded != CC_FOLDED_UNKNOWN) {
            *equal = ck_tick(k) && folded == CC_FOLDED_EQUAL;
            return false;
        }
    }
    f->cache = a && b;
    if (!ck_tick(k)) return false;
    if (!a || !b) { *equal = a == b; return false; }
    if (a == b && (!terms || terms->identity) && (!dims || dims->identity)) {
        *equal = true;
        return false;
    }
    f->left = k->nodes[a]; f->right = k->nodes[b];
    cc_node left = f->left, right = f->right;
    if (left.kind != right.kind) return false;
    if (left.kind == CC_DEFREF || left.kind == CC_LBOUND) {
        *equal = left.payload == right.payload;
        return false;
    }
    if (left.kind == CC_U) {
        *equal = level_alpha(k, left.child[0], right.child[0], frames, f->terms);
        return false;
    }
    if (left.kind == CC_LCONST || left.kind == CC_LSUCC || left.kind == CC_LMAX) {
        *equal = level_alpha(k, a, b, frames, f->terms);
        return false;
    }
    if (left.kind == CC_VAR) {
        *equal = same_name(left.payload, right.payload, frames, f->terms);
        return false;
    }
    if (ck_term_binder(left.kind))
        f->binding = bind(k, left.payload, right.payload, frames, f->terms);
    else if (ck_dim_binder(left.kind))
        f->binding = bind(k, left.payload, right.payload, frames, f->dims);
    if ((left.kind == CC_GLUE_SYSTEM || left.kind == CC_TUBE || left.kind == CC_PAPP) &&
        !formula_equal(k, left.payload, right.payload, frames, f->dims)) return false;
    if ((left.kind == CC_SORT || left.kind == CC_CON || left.kind == CC_ELIM) && left.payload != right.payload)
        return false;
    if (!ck_arity(left.kind)) { *equal = true; return false; }
    return !k->error[0];
}

static bool alpha_push(cc_kernel *k, alpha_frame **frames, size_t *capacity, size_t count,
                       alpha_frame *local, alpha_frame child, bool *equal) {
    if (!alpha_ready(k, &child, *frames, equal)) {
        alpha_completed(k, &child, *equal);
        return false;
    }
    if (count == *capacity) {
        if (*capacity >= 16384)
            return ck_fail_as(k, CC_ERROR_RESOURCE, "Native conversion recursion depth exceeded.");
        size_t next = *capacity * 2;
        alpha_frame *grown = *frames == local ? malloc(next * sizeof *grown)
                                             : realloc(*frames, next * sizeof *grown);
        if (!grown)
            return ck_fail_as(k, CC_ERROR_RESOURCE, "Alpha-comparison stack allocation failed.");
        if (*frames == local) memcpy(grown, local, count * sizeof *grown);
        *frames = grown;
        *capacity = next;
    }
    (*frames)[count] = child;
    return true;
}

static bool alpha_traverse(cc_kernel *k, alpha_frame root) {
    alpha_frame local[32], *frames = local;
    size_t count = 1, capacity = sizeof local / sizeof *local;
    bool equal = false;
    frames[0] = root;
    while (count && !k->error[0]) {
        alpha_frame *f = &frames[count - 1];
        if (f->waiting) {
            if (!equal) goto complete;
            f->waiting = false;
        }
        cc_node left = f->left, right = f->right;
        unsigned arity = f->tubes ? 2 : left.kind == CC_PAPP ? 1 : ck_arity(left.kind);
        if (f->next == arity) { equal = true; goto complete; }
        unsigned i = f->next++;
        if (!f->tubes && left.kind == CC_LAPP && i == 1) {
            equal = level_alpha(k, left.child[1], right.child[1], frames, f->terms);
            goto complete;
        }
        if (!f->tubes && left.kind == CC_SORT && i == 1) {
            cc_term l = left.child[1], r = right.child[1];
            equal = true;
            for (; l && r && !k->error[0]; l = k->nodes[l].child[1], r = k->nodes[r].child[1])
                if (k->nodes[l].kind != CC_LIST || k->nodes[r].kind != CC_LIST ||
                    !level_alpha(k, k->nodes[l].child[0], k->nodes[r].child[0], frames, f->terms)) {
                    equal = false;
                    break;
                }
            equal = equal && !l && !r;
            goto complete;
        }
        alpha_frame child = {.a = left.child[i], .b = right.child[i], .terms = f->terms, .dims = f->dims};
        if (f->tubes) {
            if (i == 0) child.dims = f->inner_dims;
            else { child.tubes = true; child.inner_dims = f->inner_dims; }
        } else if (ck_term_binder(left.kind)) {
            if (i == 1) child.terms = count;
        } else if (ck_dim_binder(left.kind)) {
            if ((i == 0 && left.kind != CC_HCOMP) || (i == 1 && left.kind == CC_PLAM))
                child.dims = count;
            else if (i == 1 && (left.kind == CC_COMP || left.kind == CC_HCOMP)) {
                child.tubes = true;
                child.inner_dims = count;
            }
        }
        f->waiting = true;
        if (alpha_push(k, &frames, &capacity, count, local, child, &equal)) ++count;
        continue;
complete:
        alpha_completed(k, f, equal);
        --count;
    }
    if (frames != local) free(frames);
    return !k->error[0] && equal;
}

static bool alpha(cc_kernel *k, cc_term a, cc_term b) {
    if (!ck_enter(k, "Native conversion recursion depth exceeded."))
        return false;
    alpha_frame root = {.a = a, .b = b};
    bool equal = false;
    if (alpha_ready(k, &root, NULL, &equal)) equal = alpha_traverse(k, root);
    else alpha_completed(k, &root, equal);
    ck_leave(k);
    return !k->error[0] && equal;
}

cc_term cc_kernel_endpoint_term(cc_kernel *k, cc_term term, uint32_t dimension, unsigned endpoint) {
    if (!k || k->error[0] || !term || term >= k->count)
        return 0;
    ck_operation(k, CC_WORK_QUERY);
    if (dimension >= CC_DIMENSIONS || endpoint > 1)
        return ck_fail(k, "An endpoint substitution needs a dimension and 0 or 1."), 0;
    k->recursion = 0;
    return ck_endpoint_term(k, term, dimension, endpoint);
}

cc_term cc_kernel_rename(cc_kernel *k, cc_term term, bool dimension, uint32_t from, uint32_t to) {
    if (!k || k->error[0] || !term || term >= k->count)
        return 0;
    ck_operation(k, CC_WORK_QUERY);
    k->recursion = 0;
    if (!dimension)
        return ck_substitute(k, term, from, ck_var(k, to));
    if (from >= CC_DIMENSIONS || to >= CC_DIMENSIONS)
        return ck_fail(k, "Dimension outside the native range."), 0;
    cc_formula point;
    cc_init(&point, CC_INTERVAL);
    cc_term renamed = ck_formula_result(k, cc_generator(&point, to, true), "Dimension renaming allocation failed.")
        ? ck_dimension_substitute(k, term, from, &point) : 0;
    cc_clear(&point);
    return renamed;
}

/* Syntactic equality up to bound names and interval algebra: nothing is
 * reduced or unfolded. The instruction kernel uses only this. */
bool ck_alpha_equal(cc_kernel *k, cc_term a, cc_term b) {
    return alpha(k, a, b);
}

/* Cumulativity without conversion: universes by level, and Π or Σ with
 * identical domains and cumulative codomains. */
bool ck_syntactic_cumulative(cc_kernel *k, cc_term actual, cc_term expected) {
    for (;;) {
        if (ck_alpha_equal(k, actual, expected))
            return true;
        if (k->error[0] || !actual || !expected)
            return false;
        cc_node left = k->nodes[actual], right = k->nodes[expected];
        if (left.kind == CC_U && right.kind == CC_U)
            return ck_level_leq(k, left.child[0], right.child[0]);
        /* Bounds/domains agree; compare bodies under one fresh variable. */
        if ((left.kind != CC_PI && left.kind != CC_SIGMA && left.kind != CC_LPI) ||
            left.kind != right.kind || !ck_alpha_equal(k, left.child[0], right.child[0]))
            return false;
        cc_term variable = ck_var(k, ck_fresh_symbol(k));
        actual = ck_substitute(k, left.child[1], left.payload, variable);
        expected = ck_substitute(k, right.child[1], right.payload, variable);
    }
}
