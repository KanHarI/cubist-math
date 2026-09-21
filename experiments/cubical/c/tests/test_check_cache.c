/* Memoization must preserve rejection under different assumptions, dimensions,
 * shadowing, and rollback. These are proof-boundary tests, not timing tests. */
#include "term_internal.h"
#include <assert.h>
#include <stdio.h>

int main(void) {
    for (unsigned flags = 0; flags < 4; ++flags) {
        cc_kernel *k = cc_kernel_new();
        assert(k);
        cc_kernel_set_optimizations(k, flags);
        cc_term nat = ck_make(k, CC_NAT, 0, 0, 0, 0, 0);
        cc_term unit = ck_make(k, CC_UNIT, 0, 0, 0, 0, 0);
        cc_term x = ck_var(k, 20), p = ck_var(k, 21);
        cc_assumption ctx = {20, nat};
        cc_checked_result result;
        assert(cc_kernel_check(k, x, nat, &ctx, 1, &result));
        assert(cc_kernel_check(k, x, nat, &ctx, 1, &result));
        assert(!cc_kernel_check(k, x, unit, &ctx, 1, &result));
        assert(!result.expression);
        assert(!cc_kernel_check(k, x, nat, NULL, 0, &result));
        ctx.type = unit;
        assert(cc_kernel_check(k, x, unit, &ctx, 1, &result));
        assert(!cc_kernel_check(k, x, nat, &ctx, 1, &result));
        cc_kernel_clear_error(k);

        /* A shadowing lambda must use its own Nat binder, not outer x : Unit. */
        cc_term identity = ck_make(k, CC_LAM, 20, nat, x, 0, 0);
        assert(cc_kernel_check(k, identity, 0, &ctx, 1, &result));
        cc_term body = k->nodes[result.expression].child[1];
        assert(k->nodes[body].payload == k->nodes[result.expression].payload);
        assert(k->nodes[body].payload != 20);

        cc_term zero = ck_make(k, CC_ZERO, 0, 0, 0, 0, 0);
        cc_term path = ck_make(k, CC_PATH, 1, nat, zero, zero, 0);
        cc_assumption path_ctx = {21, path};
        cc_term applied = ck_make(k, CC_PAPP, ck_interval_variable(k, 0), p, 0, 0, 0);
        assert(cc_kernel_check_in_cube(k, applied, nat, &path_ctx, 1, 1, &result));
        assert(!cc_kernel_check_in_cube(k, applied, nat, &path_ctx, 1, 0, &result));
        assert(!result.expression);
        cc_kernel_clear_error(k);

        /* Restricted contexts have independent exact identities. */
        cc_context base = ck_extend(k, 20, nat, NULL);
        cc_context other = ck_extend(k, 20, unit, NULL);
        assert(base.identity != other.identity);
        cc_context collision = ck_extend(k, 20 + CC_CHECK_MEMO_SIZE, nat, NULL);
        assert(collision.identity != base.identity);
        assert(ck_extend(k, 20, nat, NULL).identity != collision.identity);

        cc_kernel_checkpoint(k);
        cc_term temporary = ck_make(k, CC_SUCC, 0, zero, 0, 0, 0);
        assert(cc_kernel_check(k, temporary, nat, NULL, 0, &result));
        cc_kernel_rollback(k);
        cc_term point = ck_make(k, CC_POINT, 0, 0, 0, 0, 0);
        assert(cc_kernel_check(k, point, unit, NULL, 0, &result));
        assert(!cc_kernel_check(k, point, nat, NULL, 0, &result));
        cc_kernel_free(k);
    }
    puts("Syntax and judgement caches preserve contexts, dimensions, shadowing, and rejection in every mode.");
}
