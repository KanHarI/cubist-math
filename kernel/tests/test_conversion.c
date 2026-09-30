/* Conversion-only regression tests use raw syntax deliberately. A successful
 * comparison is not a typing certificate; public checking tests cover that
 * separate gate. In particular, free and bound names must remain distinct. */
#include "term_internal.h"
#include <assert.h>
#include <stdio.h>

static cc_term lambda(cc_kernel *k, uint32_t name, cc_term body) {
    return ck_make(k, CC_LAM, name, ck_make(k, CC_U, 0, ck_make(k, CC_LCONST, 0, 0, 0, 0, 0), 0, 0, 0), body, 0, 0);
}

static void conversion_cache(void) {
    cc_kernel *k = cc_kernel_new();
    assert(k);
    cc_term nat = ck_make(k, CC_U, 0, ck_make(k, CC_LCONST, 0, 0, 0, 0, 0), 0, 0, 0);
    cc_term zero = ck_make(k, CC_UNIT, 0, 0, 0, 0, 0);
    cc_term one = ck_make(k, CC_SUM, 0, ck_make(k, CC_UNIT, 0, 0, 0, 0, 0), zero, 0, 0);
    cc_term x = ck_var(k, 10), y = ck_var(k, 11);
    cc_term beta_x = ck_make(k, CC_APP, 0, lambda(k, 12, ck_var(k, 12)), x, 0, 0);
    assert(ck_convertible(k, beta_x, x));
    uint64_t before = k->reduction_steps;
    assert(ck_convertible(k, beta_x, x));
    assert(k->reduction_steps - before == 1);

    // The cached free comparison is valid under identical binders, but not
    // when one side's x becomes bound and the other's x remains free.
    assert(ck_convertible(k, lambda(k, 10, beta_x), lambda(k, 10, x)));
    assert(!ck_convertible(k, lambda(k, 10, beta_x), lambda(k, 11, x)));
    assert(ck_convertible(k, lambda(k, 10, beta_x), lambda(k, 11, y)));
    assert(!ck_convertible(k, beta_x, y));

    cc_term path = ck_make(k, CC_PATH, 2, nat, zero, zero, 0);
    cc_term at_i = ck_make(k, CC_PAPP, ck_interval_variable(k, 0), ck_var(k, 20), path, 0, 0);
    cc_term beta_i = ck_make(k, CC_APP, 0, lambda(k, 12, ck_var(k, 12)), at_i, 0, 0);
    assert(ck_convertible(k, beta_i, at_i));
    assert(!ck_convertible(k, ck_make(k, CC_PLAM, 0, nat, beta_i, 0, 0),
                            ck_make(k, CC_PLAM, 1, nat, at_i, 0, 0)));

    // A different application can acquire the same numeric handle after
    // rollback. Its old equality must not survive arena reuse.
    cc_term identity = lambda(k, 12, ck_var(k, 12));
    cc_kernel_checkpoint(k);
    cc_term old = ck_make(k, CC_APP, 0, identity, zero, 0, 0);
    assert(old && ck_convertible(k, old, zero));
    cc_kernel_rollback(k);
    cc_term replacement = ck_make(k, CC_APP, 0, identity, one, 0, 0);
    assert(replacement == old);
    assert(!ck_convertible(k, replacement, zero));
    assert(ck_convertible(k, replacement, one));

    // Shared subexpressions may match only after beta reduction. The folded
    // failure cache alone would revisit exponentially many equal branches.
    cc_term left = ck_make(k, CC_APP, 0, identity, zero, 0, 0), right = zero;
    for (unsigned i = 0; i < 24; ++i) {
        left = ck_make(k, CC_PAIR, 0, nat, left, left, 0);
        right = ck_make(k, CC_PAIR, 0, nat, right, right, 0);
    }
    before = k->reduction_steps;
    assert(ck_convertible(k, lambda(k, 10, left), lambda(k, 11, right)));
    assert(k->reduction_steps - before < 2000);

    // Equality reuse never bypasses the typing gate or downward cumulativity.
    cc_term u0 = ck_universe_at(k, 0);
    cc_term u1 = ck_universe_at(k, 1);
    assert(ck_expect(k, u0, u1));
    assert(!ck_convertible(k, u0, u1));
    assert(!ck_expect(k, u1, u0));
    cc_kernel_free(k);
}

/* A scan for free names cut short by the budget answers "not free" without
 * looking. The syntax memo records nothing while an error is set, so the same
 * question with budget enough gets the true answer, and substitution still
 * renames a binder that would capture. */
static void cut_short_scans_are_forgotten(void) {
    cc_kernel *k = cc_kernel_new();
    assert(k);
    cc_term deep = ck_var(k, 7);
    cc_term at_three = ck_make(k, CC_PAPP, ck_interval_variable(k, 3), ck_var(k, 8), 0, 0, 0);
    for (unsigned i = 0; i < 200; ++i) {
        deep = ck_make(k, CC_SUM, 0, ck_make(k, CC_UNIT, 0, 0, 0, 0, 0), deep, 0, 0);
        at_three = ck_make(k, CC_SUM, 0, ck_make(k, CC_UNIT, 0, 0, 0, 0, 0), at_three, 0, 0);
    }
    k->budget = 50;
    assert(!ck_term_free(k, deep, 7) && k->error[0]);
    cc_kernel_clear_error(k);
    k->budget = 50;
    assert(ck_free_dims(k, at_three) == 0 && k->error[0]);
    cc_kernel_clear_error(k);
    k->budget = UINT64_C(1000000);
    assert(ck_term_free(k, deep, 7));
    assert(ck_free_dims(k, at_three) == UINT64_C(1) << 3);
    /* Substituting it under a binder named 7 renames the binder. */
    cc_term binder = ck_make(k, CC_LAM, 7, ck_make(k, CC_U, 0, ck_make(k, CC_LCONST, 0, 0, 0, 0, 0), 0, 0, 0), ck_var(k, 9), 0, 0);
    cc_term substituted = ck_substitute(k, binder, 9, deep);
    assert(substituted && k->nodes[substituted].payload != 7);
    cc_kernel_free(k);
}

/* L(n + 1) = f (λ y. L(n)) (λ z. L(n)) at depth n; R the same with other
 * binder names. R(n) and L(n) are different nodes, alpha-equal, each
 * reached under 2^(40 - n) renamings. The comparison ignores a renaming
 * where neither side has its names free, so 40 levels compare in a few
 * thousand steps, not 2^40: #73's normal-form cache met this as a Convert
 * of two such types running out of budget. The names are chosen so that
 * their bits collide with f's and x's, which only the exact check tells
 * apart. Where a name occurs free, the renaming still decides. */
static cc_term graph(cc_kernel *k, cc_term bottom, uint32_t names, cc_term body_of(cc_kernel *, cc_term, uint32_t)) {
    cc_term unit = ck_make(k, CC_UNIT, 0, 0, 0, 0, 0), f = ck_var(k, 20), t = bottom;
    for (uint32_t n = 0; n < 40; ++n) {
        cc_term first = ck_make(k, CC_LAM, names + 2 * n, unit, body_of(k, t, names + 2 * n), 0, 0);
        cc_term second = ck_make(k, CC_LAM, names + 2 * n + 1, unit, body_of(k, t, names + 2 * n + 1), 0, 0);
        t = ck_make(k, CC_APP, 0, ck_make(k, CC_APP, 0, f, first, 0, 0), second, 0, 0);
    }
    return t;
}
static cc_term unused(cc_kernel *k, cc_term t, uint32_t name) { (void)k; (void)name; return t; }
static cc_term paired(cc_kernel *k, cc_term t, uint32_t name) {
    return ck_make(k, CC_APP, 0, t, ck_var(k, name), 0, 0);
}
static bool equal_within(cc_kernel *k, cc_term a, cc_term b, uint64_t steps) {
    cc_work_counters before, after;
    cc_kernel_work(k, &before);
    ck_operation(k, CC_WORK_QUERY);
    bool equal = ck_alpha_equal(k, a, b);
    assert(!k->error[0]);
    ck_standalone(k);
    cc_kernel_work(k, &after);
    assert(after.query_steps - before.query_steps < steps);
    return equal;
}
static void renamings_share_work(void) {
    cc_kernel *k = cc_kernel_new();
    assert(k);
    cc_term x = ck_var(k, 21);
    cc_term left = graph(k, x, 100, unused), right = graph(k, x, 300, unused);
    assert(left != right && equal_within(k, left, right, 10000));
    /* A difference at the bottom is found as fast. */
    assert(!equal_within(k, left, graph(k, ck_var(k, 22), 500, unused), 10000));
    /* Bodies that mention their binder, as t y: the renaming applies, and a
     * variable bound on one side is not the same name free on the other. */
    cc_term used = graph(k, x, 700, paired);
    assert(equal_within(k, used, graph(k, x, 900, paired), 1000000));
    cc_term unit = ck_make(k, CC_UNIT, 0, 0, 0, 0, 0);
    cc_term bound = ck_make(k, CC_LAM, 1100, unit, ck_make(k, CC_APP, 0, used, ck_var(k, 1100), 0, 0), 0, 0);
    cc_term free_there = ck_make(k, CC_LAM, 1101, unit, ck_make(k, CC_APP, 0, used, ck_var(k, 1100), 0, 0), 0, 0);
    assert(!equal_within(k, bound, free_there, 1000000));
    /* The first review of #77: a formula-bearing node made before its
     * formula exists would keep a mask without the formula's dimensions,
     * and a renaming of them could be dropped. Such a node is refused. */
    uint32_t unregistered = 60000;
    assert(!cc_kernel_get_formula(k, unregistered));
    assert(!cc_kernel_term(k, CC_PAPP, unregistered, x, 0, 0, 0));
    assert(strstr(cc_kernel_error(k), "names no registered formula"));
    cc_kernel_clear_error(k);
    assert(!cc_kernel_term(k, CC_TUBE, unregistered, x, 0, 0, 0));
    cc_kernel_clear_error(k);
    cc_kernel_free(k);
}

int main(void) {
    renamings_share_work();
    conversion_cache();
    cut_short_scans_are_forgotten();
    cc_kernel *k = cc_kernel_new();
    assert(k);
    k->budget = UINT64_C(1000000);
    cc_term nat = ck_make(k, CC_U, 0, ck_make(k, CC_LCONST, 0, 0, 0, 0, 0), 0, 0, 0);
    cc_term zero = ck_make(k, CC_UNIT, 0, 0, 0, 0, 0);
    cc_term x = ck_var(k, 10);
    cc_term y = ck_var(k, 11);
    cc_term identity_x = lambda(k, 10, x);
    cc_term identity_y = lambda(k, 11, y);
    cc_term free_x = lambda(k, 11, x);
    assert(ck_convertible(k, identity_x, identity_y));
    assert(!ck_convertible(k, identity_x, free_x));
    assert(!ck_convertible(k, free_x, identity_x));
    assert(ck_convertible(k, identity_x, identity_y));
    assert(ck_convertible(k, free_x, free_x));
    assert(!ck_convertible(k, lambda(k, 10, lambda(k, 11, x)),
                            lambda(k, 11, lambda(k, 10, x))));
    assert(ck_convertible(k, lambda(k, 10, lambda(k, 10, x)),
                           lambda(k, 11, lambda(k, 11, y))));

    cc_term p = ck_var(k, 12);
    cc_term p_type = ck_make(k, CC_PATH, 2, nat, zero, zero, 0);
    cc_term pi = ck_make(k, CC_PAPP, ck_interval_variable(k, 0), p, p_type, 0, 0);
    cc_term pj = ck_make(k, CC_PAPP, ck_interval_variable(k, 1), p, p_type, 0, 0);
    cc_term line_i = ck_make(k, CC_PLAM, 0, nat, pi, 0, 0);
    cc_term line_j = ck_make(k, CC_PLAM, 1, nat, pj, 0, 0);
    cc_term free_i = ck_make(k, CC_PLAM, 1, nat, pi, 0, 0);
    assert(ck_convertible(k, line_i, line_j));
    assert(!ck_convertible(k, line_i, free_i));
    assert(!ck_convertible(k, free_i, line_i));
    assert(ck_convertible(k, line_i, line_j));
    assert(ck_convertible(k, free_i, free_i));

    /* Homogeneous composition does not bind its type; transport does not
     * bind its face. A composition direction never binds a tube FACE. */
    cc_term hcomp = ck_make(k, CC_HCOMP, 0, pi, 0, zero, 0);
    assert(ck_free_dims(k, hcomp) & UINT64_C(1));
    cc_term side = ck_make(k, CC_TUBE, ck_endpoint_face(k, 0, 0), zero, 0, 0, 0);
    cc_term comp = ck_make(k, CC_COMP, 0, nat, side, zero, 0);
    cc_term trans = ck_make(k, CC_TRANS, 0, pi, side, zero, 0);
    assert(ck_free_dims(k, comp) & UINT64_C(1));
    assert(ck_free_dims(k, trans) & UINT64_C(1));
    cc_formula one;
    cc_init(&one, CC_INTERVAL);
    assert(cc_one(&one) == CC_OK);
    cc_term specialized = ck_dimension_substitute(k, hcomp, 0, &one);
    assert(!(ck_free_dims(k, specialized) & UINT64_C(1)));
    specialized = ck_dimension_substitute(k, comp, 0, &one);
    cc_node tube = k->nodes[k->nodes[specialized].child[1]];
    assert(cc_kernel_get_formula(k, tube.payload)->length == 0);
    cc_clear(&one);

    /* A closed shared sum DAG has 2^24 unfolded branches. Beneath
     * differently named lambdas, its nodes are compared once per scope. */
    cc_term shared = zero;
    for (unsigned i = 0; i < 24; ++i)
        shared = ck_make(k, CC_SUM, 0, shared, shared, 0, 0);
    uint64_t before = k->reduction_steps;
    assert(ck_convertible(k, lambda(k, 10, shared), lambda(k, 11, shared)));
    uint64_t steps = k->reduction_steps - before;
    assert(steps < 1000);
    assert(!k->error[0]);
    printf("Scoped folded DAG comparison: %llu reduction steps.\n", (unsigned long long)steps);
    cc_kernel_free(k);
    return 0;
}
