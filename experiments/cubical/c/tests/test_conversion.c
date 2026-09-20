/* Conversion-only regression tests use raw syntax deliberately. A successful
 * comparison is not a typing certificate; public checking tests cover that
 * separate gate. In particular, free and bound names must remain distinct. */
#include "term_internal.h"
#include <assert.h>
#include <stdio.h>

static cc_term lambda(cc_kernel *k, uint32_t name, cc_term body) {
    return ck_make(k, CC_LAM, name, ck_make(k, CC_NAT, 0, 0, 0, 0, 0), body, 0, 0);
}

int main(void) {
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
