#include "term_internal.h"
#include <assert.h>
#include <stdio.h>

int main(void) {
    cc_kernel *k = cc_kernel_new();
    assert(k);
    cc_kernel_checkpoint(k);
    assert(cc_kernel_commit_checkpoint(k)); /* Empty arena is valid too. */
    cc_term nat = cc_kernel_term(k, CC_NAT, 0, 0, 0, 0, 0);
    cc_term zero = cc_kernel_term(k, CC_ZERO, 0, 0, 0, 0, 0);
    cc_term old = cc_kernel_define(k, 1, zero, nat);
    assert(old);
    cc_kernel_checkpoint(k);
    for (unsigned i = 0; i < 1000; ++i)
        assert(cc_kernel_term(k, CC_SUCC, 0, zero, 0, 0, 0));
    cc_term one = cc_kernel_term(k, CC_SUCC, 0, old, 0, 0, 0);
    cc_term ref = cc_kernel_define(k, 2, one, nat);
    assert(ref && cc_kernel_whnf(k, ref));
    size_t allocated = k->count;
    assert(cc_kernel_commit_checkpoint(k));
    ref = cc_kernel_relocated(k, ref);
    assert(ref && k->count + 900 < allocated);
    cc_checked_result result;
    assert(cc_kernel_check(k, ref, nat, NULL, 0, &result));
    assert(cc_kernel_check(k, old, nat, NULL, 0, &result));
    cc_term unit = cc_kernel_term(k, CC_UNIT, 0, 0, 0, 0, 0);
    assert(!cc_kernel_check(k, ref, unit, NULL, 0, &result));
    assert(!result.expression);
    cc_kernel_clear_error(k);
    cc_kernel_checkpoint(k);
    cc_term rejected = cc_kernel_define(k, 3, ref, nat);
    assert(rejected);
    cc_kernel_rollback(k);
    assert(!cc_kernel_definition(k, rejected, NULL, NULL, NULL));
    assert(cc_kernel_check(k, ref, nat, NULL, 0, &result));
    cc_kernel_free(k);
    puts("Compaction preserves checked definitions; rollback discards new ones.");
}
