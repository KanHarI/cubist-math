/* Definitional equality compares normal forms modulo alpha-renaming. Interval
 * normal forms remain De Morgan expressions; endpoint tests are face formulas.
 * An unbound name must never be identified with a binder on the other side. */
#include "term_internal.h"

typedef struct alpha_binding {
    uint32_t left, right;
    const struct alpha_binding *previous;
} alpha_binding;

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

static bool alpha(cc_kernel *, cc_term, cc_term, const alpha_binding *, const alpha_binding *);

static bool tube_alpha(cc_kernel *k, cc_term a, cc_term b, const alpha_binding *terms,
                       const alpha_binding *outer_dims, const alpha_binding *inner_dims) {
    if (!a || !b)
        return a == b;
    cc_node left = k->nodes[a], right = k->nodes[b];
    if (left.kind != CC_TUBE || right.kind != CC_TUBE)
        return false;
    return formula_equal(k, left.payload, right.payload, outer_dims) &&
           alpha(k, left.child[0], right.child[0], terms, inner_dims) &&
           tube_alpha(k, left.child[1], right.child[1], terms, outer_dims, inner_dims);
}

static bool alpha(cc_kernel *k, cc_term a, cc_term b, const alpha_binding *terms,
                   const alpha_binding *dims) {
    if (!ck_tick(k, false))
        return false;
    if (!a || !b)
        return a == b;
    if (a == b && !terms && !dims)
        return true;
    a = ck_whnf(k, a);
    b = ck_whnf(k, b);
    if (!a || !b)
        return false;
    cc_node left = k->nodes[a], right = k->nodes[b];
    if (left.kind != right.kind) {
        /* Typed surjective pairing: compare a pair with the two projections
         * of the other term. This also handles components that only expose
         * their projection after reduction; it does not normalize unused data. */
        if (left.kind == CC_PAIR) {
            cc_term first = ck_make(k, CC_FST, 0, b, 0, 0, 0);
            cc_term second = ck_make(k, CC_SND, 0, b, 0, 0, 0);
            return alpha(k, left.child[1], first, terms, dims) &&
                   alpha(k, left.child[2], second, terms, dims);
        }
        if (right.kind == CC_PAIR) {
            cc_term first = ck_make(k, CC_FST, 0, a, 0, 0, 0);
            cc_term second = ck_make(k, CC_SND, 0, a, 0, 0, 0);
            return alpha(k, first, right.child[1], terms, dims) &&
                   alpha(k, second, right.child[2], terms, dims);
        }
        return false;
    }
    if (left.kind == CC_U)
        return left.payload == right.payload;
    if (left.kind == CC_VAR)
        return same_name(left.payload, right.payload, terms);
    if (ck_term_binder(left.kind)) {
        alpha_binding binding = {left.payload, right.payload, terms};
        return alpha(k, left.child[0], right.child[0], terms, dims) &&
               alpha(k, left.child[1], right.child[1], &binding, dims);
    }
    if (ck_dim_binder(left.kind)) {
        alpha_binding binding = {left.payload, right.payload, dims};
        if (!alpha(k, left.child[0], right.child[0], terms, &binding))
            return false;
        if (left.kind == CC_PLAM)
            return alpha(k, left.child[1], right.child[1], terms, &binding);
        if (left.kind == CC_COMP)
            return tube_alpha(k, left.child[1], right.child[1], terms, dims, &binding) &&
                   alpha(k, left.child[2], right.child[2], terms, dims);
        return alpha(k, left.child[1], right.child[1], terms, dims) &&
               alpha(k, left.child[2], right.child[2], terms, dims);
    }
    if ((left.kind == CC_GLUE_SYSTEM || left.kind == CC_TUBE) && !formula_equal(k, left.payload, right.payload, dims))
        return false;
    if (left.kind == CC_PAPP)
        return formula_equal(k, left.payload, right.payload, dims) &&
               alpha(k, left.child[0], right.child[0], terms, dims);
    for (unsigned i = 0; i < ck_arity(left.kind); ++i)
        if (!alpha(k, left.child[i], right.child[i], terms, dims))
            return false;
    return true;
}

bool ck_convertible(cc_kernel *k, cc_term a, cc_term b) {
    a = ck_whnf(k, a);
    b = ck_whnf(k, b);
    return !k->error[0] && alpha(k, a, b, NULL, NULL);
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
