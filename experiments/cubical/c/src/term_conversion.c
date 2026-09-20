/* Definitional equality first compares folded syntax, then demanded heads. Interval
 * normal forms remain De Morgan expressions; endpoint tests are face formulas.
 * An unbound name must never be identified with a binder on the other side. */
#include "term_internal.h"

enum comparison_mode { FOLDED, EXPOSE, COMPUTE, CONGRUENCE };

typedef struct alpha_binding {
    uint32_t left, right;
    uint64_t scope;
    const struct alpha_binding *previous;
} alpha_binding;

static alpha_binding bind(cc_kernel *k, uint32_t left, uint32_t right,
                           const alpha_binding *previous) {
    if (k->next_alpha_scope == UINT64_MAX)
        ck_fail(k, "Alpha-comparison scope counter exhausted.");
    return (alpha_binding){left, right, ++k->next_alpha_scope, previous};
}

static size_t alpha_slot(cc_term left, cc_term right, uint64_t terms, uint64_t dims) {
    uint64_t hash = (uint64_t)left * UINT64_C(1099511628211);
    hash = (hash ^ right) * UINT64_C(1099511628211);
    hash = (hash ^ terms) * UINT64_C(1099511628211);
    hash = (hash ^ dims) * UINT64_C(1099511628211);
    return (size_t)(hash % CC_ALPHA_MEMO_SIZE);
}

static const alpha_binding *bound(const alpha_binding *env, uint32_t name, bool right) {
    for (; env; env = env->previous)
        if ((right ? env->right : env->left) == name)
            return env;
    return NULL;
}

static bool same_name(uint32_t a, uint32_t b, const alpha_binding *env) {
    const alpha_binding *left = bound(env, a, false);
    const alpha_binding *right = bound(env, b, true);
    return left || right ? left && left == right : a == b;
}

static bool clause_included(cc_clause a, cc_clause b, const alpha_binding *dims) {
    for (unsigned i = 0; i < CC_DIMENSIONS; ++i) {
        uint64_t bit = UINT64_C(1) << i;
        for (unsigned endpoint = 0; endpoint < 2; ++endpoint) {
            if (!((endpoint ? a.positive : a.negative) & bit))
                continue;
            bool found = false;
            for (unsigned j = 0; j < CC_DIMENSIONS; ++j)
                if (((endpoint ? b.positive : b.negative) & (UINT64_C(1) << j)) && same_name(i, j, dims)) {
                    found = true;
                    break;
                }
            if (!found)
                return false;
        }
    }
    return true;
}

static bool formula_equal(cc_kernel *k, uint32_t a, uint32_t b, const alpha_binding *dims) {
    const cc_formula *left = cc_kernel_get_formula(k, a);
    const cc_formula *right = cc_kernel_get_formula(k, b);
    if (!left || !right || left->sort != right->sort || left->length != right->length)
        return false;
    for (size_t i = 0; i < left->length; ++i) {
        bool found = false;
        /* A binder renaming is bijective. Forward inclusion plus equal
         * literal counts therefore establishes equality of the clauses. */
        for (size_t j = 0; j < right->length; ++j) {
            unsigned l = 0, r = 0;
            for (unsigned d = 0; d < CC_DIMENSIONS; ++d) {
                uint64_t bit = UINT64_C(1) << d;
                l += (left->clauses[i].positive & bit) != 0;
                l += (left->clauses[i].negative & bit) != 0;
                r += (right->clauses[j].positive & bit) != 0;
                r += (right->clauses[j].negative & bit) != 0;
            }
            if (l == r && clause_included(left->clauses[i], right->clauses[j], dims)) {
                found = true;
                break;
            }
        }
        if (!found)
            return false;
    }
    return true;
}

static bool alpha(cc_kernel *, cc_term, cc_term, const alpha_binding *, const alpha_binding *, enum comparison_mode);

static bool tube_alpha(cc_kernel *k, cc_term a, cc_term b, const alpha_binding *terms,
                       const alpha_binding *outer_dims, const alpha_binding *inner_dims, enum comparison_mode mode) {
    if (!a || !b)
        return a == b;
    cc_node left = k->nodes[a], right = k->nodes[b];
    if (left.kind != CC_TUBE || right.kind != CC_TUBE)
        return false;
    return formula_equal(k, left.payload, right.payload, outer_dims) &&
           alpha(k, left.child[0], right.child[0], terms, inner_dims, mode) &&
           tube_alpha(k, left.child[1], right.child[1], terms, outer_dims, inner_dims, mode);
}

static bool alpha_inner(cc_kernel *k, cc_term a, cc_term b, const alpha_binding *terms,
                         const alpha_binding *dims, enum comparison_mode mode) {
    if (!ck_tick(k, false))
        return false;
    if (!a || !b)
        return a == b;
    if (a == b && !terms && !dims)
        return true;
    if (mode != FOLDED && alpha(k, a, b, terms, dims, FOLDED))
        return true;
    if (mode == COMPUTE && alpha(k, a, b, terms, dims, EXPOSE))
        return true;
    if (mode == EXPOSE) {
        /* Delta expansion is separate from evaluation. An alias for a compact
         * numeral can already match its checked expression after one step. */
        cc_node left = k->nodes[a], right = k->nodes[b];
        if (left.kind == CC_DEFREF || right.kind == CC_DEFREF) {
            if (left.kind == CC_DEFREF) {
                if (!left.payload || left.payload >= k->definition_count)
                    return ck_fail(k, "Unknown definition in conversion.");
                a = k->definitions[left.payload].value;
            }
            if (right.kind == CC_DEFREF) {
                if (!right.payload || right.payload >= k->definition_count)
                    return ck_fail(k, "Unknown definition in conversion.");
                b = k->definitions[right.payload].value;
            }
            return alpha(k, a, b, terms, dims, EXPOSE);
        }
    }
    if (mode == EXPOSE) {
        cc_term exposed_a = ck_expose(k, a);
        cc_term exposed_b = ck_expose(k, b);
        if (!exposed_a || !exposed_b)
            return false;
        if (exposed_a != a || exposed_b != b)
            return alpha(k, exposed_a, exposed_b, terms, dims, EXPOSE);
    }
    if (mode == COMPUTE) {
        cc_term old_a, old_b;
        do {
            old_a = a;
            if (k->nodes[a].kind == CC_DEFREF)
                a = k->definitions[k->nodes[a].payload].value;
            else
                a = ck_expose(k, a);
        } while (a && a != old_a && ck_tick(k, false));
        do {
            old_b = b;
            if (k->nodes[b].kind == CC_DEFREF)
                b = k->definitions[k->nodes[b].payload].value;
            else
                b = ck_expose(k, b);
        } while (b && b != old_b && ck_tick(k, false));
        if (!a || !b || k->error[0])
            return false;
        /* Congruence can compare small arguments of a shared computation
         * before evaluating its potentially enormous result. */
        if (alpha(k, a, b, terms, dims, CONGRUENCE))
            return true;
        a = ck_whnf(k, a);
        b = ck_whnf(k, b);
    }
    if (!a || !b)
        return false;
    cc_node left = k->nodes[a], right = k->nodes[b];
    enum comparison_mode children_mode = mode == CONGRUENCE ? COMPUTE : mode;
    if (left.kind != right.kind) {
        if (mode != COMPUTE)
            return false;
        /* Function eta is checked here, without reducing lambda bodies merely
         * to discover their shape during weak-head inspection. */
        if (left.kind == CC_LAM) {
            uint32_t fresh = ck_fresh_symbol(k);
            cc_term applied = ck_make(k, CC_APP, 0, b, ck_var(k, fresh), 0, 0);
            alpha_binding binding = bind(k, left.payload, fresh, terms);
            return alpha(k, left.child[1], applied, &binding, dims, children_mode);
        }
        if (right.kind == CC_LAM) {
            uint32_t fresh = ck_fresh_symbol(k);
            cc_term applied = ck_make(k, CC_APP, 0, a, ck_var(k, fresh), 0, 0);
            alpha_binding binding = bind(k, fresh, right.payload, terms);
            return alpha(k, applied, right.child[1], &binding, dims, children_mode);
        }
        if (left.kind == CC_PLAM || right.kind == CC_PLAM) {
            bool on_left = left.kind == CC_PLAM;
            cc_node line = on_left ? left : right;
            cc_term other = on_left ? b : a;
            uint64_t avoid = ck_free_dims(k, a) | ck_free_dims(k, b);
            for (const alpha_binding *entry = dims; entry; entry = entry->previous)
                avoid |= (UINT64_C(1) << entry->left) | (UINT64_C(1) << entry->right);
            unsigned direction = ck_fresh_dimension(k, avoid);
            if (direction >= CC_DIMENSIONS)
                return false;
            cc_formula_id argument = ck_interval_variable(k, direction);
            cc_formula variable;
            cc_init(&variable, CC_INTERVAL);
            if (cc_copy(&variable, cc_kernel_get_formula(k, argument)) != CC_OK)
                return ck_fail(k, "Path eta dimension allocation failed.");
            cc_term body = ck_dimension_substitute(k, line.child[1], line.payload, &variable);
            cc_clear(&variable);
            cc_term annotation = ck_make(k, CC_PATH, line.payload, line.child[0],
                ck_endpoint_term(k, line.child[1], line.payload, 0),
                ck_endpoint_term(k, line.child[1], line.payload, 1), 0);
            cc_term applied = ck_make(k, CC_PAPP, argument, other, annotation, 0, 0);
            alpha_binding binding = bind(k, direction, direction, dims);
            return on_left ? alpha(k, body, applied, terms, &binding, COMPUTE) :
                             alpha(k, applied, body, terms, &binding, COMPUTE);
        }
        /* Typed surjective pairing: compare a pair with the two projections
         * of the other term. This also handles components that only expose
         * their projection after reduction; it does not normalize unused data. */
        if (left.kind == CC_PAIR) {
            cc_term first = ck_make(k, CC_FST, 0, b, 0, 0, 0);
            cc_term second = ck_make(k, CC_SND, 0, b, 0, 0, 0);
            return alpha(k, left.child[1], first, terms, dims, children_mode) &&
                   alpha(k, left.child[2], second, terms, dims, children_mode);
        }
        if (right.kind == CC_PAIR) {
            cc_term first = ck_make(k, CC_FST, 0, a, 0, 0, 0);
            cc_term second = ck_make(k, CC_SND, 0, a, 0, 0, 0);
            return alpha(k, first, right.child[1], terms, dims, children_mode) &&
                   alpha(k, second, right.child[2], terms, dims, children_mode);
        }
        return false;
    }
    if (left.kind == CC_U || left.kind == CC_DEFREF)
        return left.payload == right.payload;
    if (left.kind == CC_VAR)
        return same_name(left.payload, right.payload, terms);
    if (ck_term_binder(left.kind)) {
        alpha_binding binding = bind(k, left.payload, right.payload, terms);
        return alpha(k, left.child[0], right.child[0], terms, dims, children_mode) &&
               alpha(k, left.child[1], right.child[1], &binding, dims, children_mode);
    }
    if (ck_dim_binder(left.kind)) {
        alpha_binding binding = bind(k, left.payload, right.payload, dims);
        if (!alpha(k, left.child[0], right.child[0], terms, &binding, children_mode))
            return false;
        if (left.kind == CC_PLAM)
            return alpha(k, left.child[1], right.child[1], terms, &binding, children_mode);
        if (left.kind == CC_COMP)
            return tube_alpha(k, left.child[1], right.child[1], terms, dims, &binding, children_mode) &&
                   alpha(k, left.child[2], right.child[2], terms, dims, children_mode);
        return alpha(k, left.child[1], right.child[1], terms, dims, children_mode) &&
               alpha(k, left.child[2], right.child[2], terms, dims, children_mode);
    }
    if ((left.kind == CC_GLUE_SYSTEM || left.kind == CC_TUBE) && !formula_equal(k, left.payload, right.payload, dims))
        return false;
    if (left.kind == CC_PUSH_PATH && !formula_equal(k, left.payload, right.payload, dims))
        return false;
    if (left.kind == CC_PAPP)
        return formula_equal(k, left.payload, right.payload, dims) &&
               alpha(k, left.child[0], right.child[0], terms, dims, children_mode);
    for (unsigned i = 0; i < ck_arity(left.kind); ++i)
        if (!alpha(k, left.child[i], right.child[i], terms, dims, children_mode))
            return false;
    return true;
}

static bool alpha(cc_kernel *k, cc_term a, cc_term b, const alpha_binding *terms,
                   const alpha_binding *dims, enum comparison_mode mode) {
    if (++k->recursion > 512) {
        --k->recursion;
        return ck_fail(k, "Native conversion recursion depth exceeded.");
    }
    uint64_t term_scope = terms ? terms->scope : 0;
    uint64_t dimension_scope = dims ? dims->scope : 0;
    size_t slot = alpha_slot(a, b, term_scope, dimension_scope);
    if (mode == FOLDED && a && b && k->alpha_memo) {
        cc_alpha_memo entry = k->alpha_memo[slot];
        if (entry.left == a && entry.right == b && entry.term_scope == term_scope &&
            entry.dimension_scope == dimension_scope) {
            --k->recursion;
            return ck_tick(k, false) && entry.equal;
        }
    }
    bool equal = alpha_inner(k, a, b, terms, dims, mode);
    if (mode == FOLDED && a && b && !k->error[0]) {
        if (!k->alpha_memo) {
            k->alpha_memo = calloc(CC_ALPHA_MEMO_SIZE, sizeof *k->alpha_memo);
            if (!k->alpha_memo)
                ck_fail(k, "Alpha-comparison memo allocation failed.");
        }
        if (k->alpha_memo)
            k->alpha_memo[slot] = (cc_alpha_memo){a, b, term_scope, dimension_scope, equal};
    }
    --k->recursion;
    return !k->error[0] && equal;
}

bool ck_convertible(cc_kernel *k, cc_term a, cc_term b) {
    /* Prefer the folded checked structure. Equal closed references never
     * need their bodies evaluated, even inside larger matching types. */
    if (alpha(k, a, b, NULL, NULL, FOLDED))
        return true;
    return !k->error[0] && alpha(k, a, b, NULL, NULL, COMPUTE);
}

bool ck_expect(cc_kernel *k, cc_term actual, cc_term expected) {
    if (ck_convertible(k, actual, expected))
        return true;
    actual = ck_whnf(k, actual);
    expected = ck_whnf(k, expected);
    if (actual && expected && k->nodes[actual].kind == CC_U && k->nodes[expected].kind == CC_U &&
        k->nodes[actual].payload <= k->nodes[expected].payload)
        return true;
    return ck_fail(k, "Type mismatch.");
}
