/* Head exposure is not a certificate. Raw path-lambda beta is syntactic;
 * a neutral path at an endpoint reduces only with its type, which the
 * instructions record in the application. */
#include "term_internal.h"
#include <assert.h>
#include <stdio.h>

int main(void) {
    cc_kernel *k = cc_kernel_new();
    assert(k);
    k->budget = UINT64_C(10000000);
    cc_term universe = ck_universe_at(k, 0);
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
    /* The head is exposed under an unbound name: computing it certifies nothing. */
    assert(cc_kernel_whnf(k, wrapped) == A);

    cc_term path = ck_var(k, 12);
    cc_term neutral = ck_make(k, CC_PAPP, endpoint, path, 0, 0, 0);
    assert(cc_kernel_whnf(k, neutral) == 0);
    assert(strstr(cc_kernel_error(k), "Unchecked path"));
    cc_kernel_clear_error(k);
    /* p : tt = tt in Unit, and p @ 1 as the instructions derive it. */
    cc_judgement_id unit = cc_instr_unit(k), point = cc_instr_point(k);
    cc_judgement_id type = cc_instr_path(k, cc_instr_dimension(k, 0), unit, point, point);
    cc_entry_id p = cc_instr_extend(k, type, 12);
    cc_judgement_info info;
    assert(cc_kernel_judgement(k, cc_instr_path_at(k, cc_instr_variable(k, p), endpoint), &info));
    cc_term exposed = cc_kernel_whnf(k, info.term);
    assert(exposed && k->nodes[exposed].kind == CC_POINT);
    cc_kernel_free(k);
    puts("Raw path lambda beta remains separate from a neutral path's endpoint, which needs its type.");
    return 0;
}
