/* A rejected check must not prevent a user from constructing a correction. */
#include "cubical_kernel.h"
#include <assert.h>
#include <stdio.h>

int main(void) {
    cc_kernel *kernel = cc_kernel_new();
    assert(kernel);
    cc_term nat = cc_kernel_term(kernel, CC_NAT, 0, 0, 0, 0, 0);
    cc_term unit = cc_kernel_term(kernel, CC_UNIT, 0, 0, 0, 0, 0);
    cc_term zero = cc_kernel_term(kernel, CC_ZERO, 0, 0, 0, 0, 0);
    cc_checked_result result;
    assert(!cc_kernel_check(kernel, zero, unit, NULL, 0, &result));
    assert(result.expression == 0 && result.type == 0);
    assert(cc_kernel_error(kernel)[0]);
    cc_kernel_clear_error(kernel);
    assert(!cc_kernel_error(kernel)[0]);
    cc_term corrected = cc_kernel_term(kernel, CC_SUCC, 0, zero, 0, 0, 0);
    assert(corrected);
    assert(cc_kernel_check(kernel, corrected, nat, NULL, 0, &result));
    assert(result.expression && result.type && !result.normal);
    assert(cc_kernel_normalize(kernel, result.expression));
    cc_kernel_clear_error(NULL);
    cc_kernel_free(kernel);
    puts("Native checked API recovery passed.");
    return 0;
}
