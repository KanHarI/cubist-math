/* Dimension-slot reuse must preserve lexical binding, context dependencies,
 * and the outer scope of composition faces. Checking is the only certificate. */
#include "term_internal.h"
#include <assert.h>
#include <stdio.h>

int main(void) {
    cc_kernel *k = cc_kernel_new();
    assert(k);
    k->budget = UINT64_C(10000000);
    cc_term universe = ck_make(k, CC_U, 0, 0, 0, 0, 0);
    cc_term nat = ck_make(k, CC_NAT, 0, 0, 0, 0, 0);
    cc_term unit = ck_make(k, CC_UNIT, 0, 0, 0, 0, 0);
    cc_term zero = ck_make(k, CC_ZERO, 0, 0, 0, 0, 0);
    cc_term family_path = ck_make(k, CC_PATH, 2, universe, nat, unit, 0);
    cc_term family = ck_var(k, 10);
    cc_term point = ck_var(k, 11);
    cc_term at_outer = ck_make(k, CC_PAPP, ck_interval_variable(k, 0), family, 0, 0, 0);
    cc_assumption assumptions[] = {{10, family_path}, {11, at_outer}};
    cc_checked_result checked;

    /* The local point has a type depending on outer dimension 0. Rebinding
     * slot 0 does not turn that point into a section of the varying family. */
    cc_term captured = ck_make(k, CC_PLAM, 0, at_outer, point, 0, 0);
    assert(!cc_kernel_check_in_cube(k, captured, 0, assumptions, 2, UINT64_C(1), &checked));
    assert(strstr(cc_kernel_error(k), "Type mismatch"));
    cc_kernel_clear_error(k);

    /* A genuinely constant line at that point retains the outer dependency. */
    cc_term constant = ck_make(k, CC_PLAM, 1, at_outer, point, 0, 0);
    assert(cc_kernel_check_in_cube(k, constant, 0, assumptions, 2, UINT64_C(1), &checked));
    assert(ck_free_dims(k, checked.expression) == UINT64_C(1));

    /* The face uses OUTER slot 0, while the tube body binds slot 0. The
     * checker must rename the latter before restricting by the former. */
    cc_term loop_type = ck_make(k, CC_PATH, 2, nat, zero, zero, 0);
    cc_term loop = ck_var(k, 12);
    cc_term tube_body = ck_make(k, CC_PAPP, ck_interval_variable(k, 0), loop, 0, 0, 0);
    cc_term tube = ck_make(k, CC_TUBE, ck_endpoint_face(k, 0, 0), tube_body, 0, 0, 0);
    cc_term composition = ck_make(k, CC_COMP, 0, nat, tube, zero, 0);
    cc_assumption loop_context[] = {{12, loop_type}};
    assert(cc_kernel_check_in_cube(k, composition, nat, loop_context, 1, UINT64_C(1), &checked));
    assert(k->nodes[checked.expression].payload != 0);
    assert(ck_free_dims(k, checked.expression) == UINT64_C(1));

    /* Pruning never grants a new free coordinate permission. */
    cc_term unbound = ck_make(k, CC_PAPP, ck_interval_variable(k, 5), loop, 0, 0, 0);
    cc_term malformed = ck_make(k, CC_PLAM, 0, nat, unbound, 0, 0);
    assert(!cc_kernel_check(k, malformed, 0, loop_context, 1, &checked));
    assert(strstr(cc_kernel_error(k), "Unbound interval"));
    cc_kernel_clear_error(k);

    /* A full but unused outer cube is harmless: this closed constant line
     * does not consume a sixty-fifth geometric direction. */
    cc_term closed = ck_make(k, CC_PLAM, 0, nat, zero, 0, 0);
    assert(cc_kernel_check_in_cube(k, closed, 0, NULL, 0, UINT64_MAX, &checked));
    assert(ck_free_dims(k, checked.expression) == 0);
    cc_kernel_free(k);
    puts("Dimension liveness preserves context, faces, and binding.");
    return 0;
}
