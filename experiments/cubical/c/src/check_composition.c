#include "term_internal.h"
/* Composition is deliberately rejected until its independent native boundary
 * checker and computations are implemented. No old-kernel fallback exists. */
bool ck_composition(cc_kernel *k, cc_node n, const cc_context *ctx, uint64_t dims,
                    cc_judgement *out) {
    (void)n; (void)ctx; (void)dims; (void)out;
    return ck_fail(k, "Native composition port is not implemented yet.");
}
cc_term ck_reduce_composition(cc_kernel *k, cc_term term) {
    (void)term;
    ck_fail(k, "Unchecked native composition.");
    return 0;
}
