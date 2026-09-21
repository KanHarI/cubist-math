/* Head exposure is not a certificate. Raw path-lambda beta is syntactic;
 * neutral path endpoint reduction still needs a checked type annotation. */
#include "term_internal.h"
#include <assert.h>
#include <stdio.h>

int main(void) {
    cc_kernel *k = cc_kernel_new();
    assert(k);
    k->budget = UINT64_C(10000000);
    cc_term universe = ck_make(k, CC_U, 0, 0, 0, 0, 0);
    cc_term nat = ck_make(k, CC_NAT, 0, 0, 0, 0, 0);
    cc_term zero = ck_make(k, CC_ZERO, 0, 0, 0, 0, 0);
    cc_term A = ck_var(k, 10);
    cc_term line = ck_make(k, CC_PLAM, 0, universe, A, 0, 0);
    cc_formula one;
    cc_init(&one, CC_INTERVAL);
    assert(cc_one(&one) == CC_OK);
    cc_formula_id endpoint = cc_kernel_formula(k, &one);
    cc_clear(&one);
    cc_term application = ck_make(k, CC_PAPP, endpoint, line, 0, 0, 0);
    cc_term identity = ck_make(k, CC_LAM, 11, universe, ck_var(k, 11), 0, 0);
    cc_term wrapped = ck_make(k, CC_APP, 0, identity, application, 0, 0);
    assert(cc_kernel_whnf(k, wrapped) == A);
    cc_checked_result checked;
    /* Exposing an unbound variable did not certify its surrounding term. */
    assert(!cc_kernel_check(k, wrapped, universe, NULL, 0, &checked));
    assert(strstr(cc_kernel_error(k), "Unbound term"));
    cc_kernel_clear_error(k);
    cc_assumption context[] = {{10, universe}};
    assert(cc_kernel_check(k, wrapped, universe, context, 1, &checked));

    cc_term path = ck_var(k, 12);
    cc_term neutral = ck_make(k, CC_PAPP, endpoint, path, 0, 0, 0);
    assert(cc_kernel_whnf(k, neutral) == 0);
    assert(strstr(cc_kernel_error(k), "Unchecked path"));
    cc_kernel_clear_error(k);
    cc_term path_type = ck_make(k, CC_PATH, 0, nat, zero, zero, 0);
    cc_assumption path_context[] = {{12, path_type}};
    assert(cc_kernel_check(k, neutral, nat, path_context, 1, &checked));
    cc_term exposed = cc_kernel_whnf(k, checked.expression);
    assert(exposed && k->nodes[exposed].kind == CC_ZERO);
    cc_kernel_free(k);
    puts("Raw path lambda beta remains separate from neutral endpoint certification.");
    return 0;
}
