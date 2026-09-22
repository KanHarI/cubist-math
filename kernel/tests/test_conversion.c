/* Conversion-only regression tests use raw syntax deliberately. A successful
 * comparison is not a typing certificate; public checking tests cover that
 * separate gate. In particular, free and bound names must remain distinct. */
#include "term_internal.h"
#include <assert.h>
#include <stdio.h>

static cc_term lambda(cc_kernel *k, uint32_t name, cc_term body) {
    return ck_make(k, CC_LAM, name, ck_make(k, CC_NAT, 0, 0, 0, 0, 0), body, 0, 0);
}

static void conversion_cache(void) {
    cc_kernel *k = cc_kernel_new();
    assert(k);
    cc_term nat = ck_make(k, CC_NAT, 0, 0, 0, 0, 0);
    cc_term zero = ck_make(k, CC_ZERO, 0, 0, 0, 0, 0);
    cc_term one = ck_make(k, CC_SUCC, 0, zero, 0, 0, 0);
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
    cc_term u0 = ck_make(k, CC_U, 0, 0, 0, 0, 0);
    cc_term u1 = ck_make(k, CC_U, 1, 0, 0, 0, 0);
    assert(ck_expect(k, u0, u1));
    assert(!ck_convertible(k, u0, u1));
    assert(!ck_expect(k, u1, u0));
    cc_kernel_free(k);
}

int main(void) {
    conversion_cache();
    cc_kernel *k = cc_kernel_new();
    assert(k);
    k->budget = UINT64_C(1000000);
    cc_term nat = ck_make(k, CC_NAT, 0, 0, 0, 0, 0);
    cc_term zero = ck_make(k, CC_ZERO, 0, 0, 0, 0, 0);
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

    /* A closed shared arithmetic DAG has 2^24 unfolded branches. Beneath
     * differently named lambdas, its nodes are compared once per scope. */
    cc_term motive = lambda(k, 20, nat);
    cc_term step = lambda(k, 20, lambda(k, 21, ck_var(k, 21)));
    cc_term shared = zero;
    for (unsigned i = 0; i < 24; ++i)
        shared = ck_make(k, CC_NATREC, 0, motive, shared, step, shared);
    uint64_t before = k->reduction_steps;
    assert(ck_convertible(k, lambda(k, 10, shared), lambda(k, 11, shared)));
    uint64_t steps = k->reduction_steps - before;
    assert(steps < 1000);
    assert(!k->error[0]);
    printf("Scoped folded DAG comparison: %llu reduction steps.\n", (unsigned long long)steps);
    cc_kernel_free(k);
    return 0;
}
