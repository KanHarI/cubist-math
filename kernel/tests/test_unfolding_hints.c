#include "term_internal.h"
#include <assert.h>
#include <stdio.h>

int main(void) {
    cc_kernel *k = cc_kernel_new();
    assert(k);
    cc_term nat = cc_kernel_term(k, CC_NAT, 0, 0, 0, 0, 0);
    cc_term zero = cc_kernel_term(k, CC_ZERO, 0, 0, 0, 0, 0);
    cc_term reference = cc_kernel_define(k, 1, zero, nat);
    assert(reference);
    cc_term repeated[] = {reference, reference};
    assert(cc_kernel_set_unfolding_hints(k, repeated, 2));
    assert(k->unfolding_hint_count == 1);
    uint32_t retained = k->unfolding_hints[0];
    cc_term bad[] = {0, UINT32_MAX, nat};
    for (size_t i = 0; i < 3; ++i) {
        assert(!cc_kernel_set_unfolding_hints(k, &bad[i], 1));
        assert(k->unfolding_hint_count == 1 && k->unfolding_hints[0] == retained);
        cc_kernel_clear_error(k);
    }
    assert(!cc_kernel_set_unfolding_hints(k, NULL, 1));
    assert(cc_kernel_set_unfolding_hints(k, NULL, 0));
    assert(!k->unfolding_hints && !k->unfolding_hint_count);
    cc_kernel_clear_error(k);
    assert(cc_kernel_set_unfolding_hints(k, &reference, 1));
    cc_term one = cc_kernel_term(k, CC_SUCC, 0, zero, 0, 0, 0);
    cc_term line = cc_kernel_term(k, CC_PLAM, 0, nat, reference, 0, 0);
    cc_term false_type = cc_kernel_term(k, CC_PATH, 0, nat, zero, one, 0);
    cc_checked_result result;
    assert(!cc_kernel_check(k, line, false_type, NULL, 0, &result));
    assert(cc_kernel_set_unfolding_hints(k, NULL, 0));
    cc_kernel_free(k);
    puts("Unfolding hints validate checked references and never approve false endpoints.");
}
