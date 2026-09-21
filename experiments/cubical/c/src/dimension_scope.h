#ifndef CUBICAL_DIMENSION_SCOPE_H
#define CUBICAL_DIMENSION_SCOPE_H
#include "term_internal.h"

/* Interval weakening is admissible: an unused interval assumption can be
 * removed before entering a binder. Local term-variable types are part of the
 * judgement, so their dimensions remain live even when absent from raw syntax.
 * Intersect with the original cube: this can never bind an unbound dimension.
 * ck_free_dims respects the distinct scopes of endpoints, tube faces and bases. */
static inline uint64_t ck_live_dimensions(cc_kernel *k, cc_node term,
                                           const cc_context *ctx, uint64_t dims) {
    cc_term raw = ck_make(k, term.kind, term.payload, term.child[0], term.child[1],
                          term.child[2], term.child[3]);
    uint64_t needed = ck_free_dims(k, raw);
    for (const cc_context *entry = ctx; entry; entry = entry->previous)
        needed |= ck_free_dims(k, entry->type);
    return dims & needed;
}
#endif
