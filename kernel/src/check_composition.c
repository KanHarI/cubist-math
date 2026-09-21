/* Composition checks a partial box in A(i), starting from a0 : A(0).
 * Each face is split into consistent conjunctions of endpoint equations.
 * The tube must equal a0 at i=0 and other tubes on EVERY overlap.
 * Only these restricted, independently checked tube terms are retained. */
#include "dimension_scope.h"

static cc_term rename_tubes(cc_kernel *k, cc_term system, unsigned dim,
                             const cc_formula *replacement) {
    if (!system)
        return 0;
    cc_node tube = k->nodes[system];
    if (tube.kind != CC_TUBE)
        return ck_fail(k, "Malformed composition system."), 0;
    cc_term body = ck_dimension_substitute(k, tube.child[0], dim, replacement);
    cc_term tail = rename_tubes(k, tube.child[1], dim, replacement);
    return ck_make(k, CC_TUBE, tube.payload, body, tail, 0, 0);
}

bool ck_composition(cc_kernel *k, cc_node n, const cc_context *ctx, uint64_t dims,
                      cc_judgement *out) {
    if (n.payload >= CC_DIMENSIONS)
        return ck_fail(k, "Composition dimension outside native range.");
    dims = ck_live_dimensions(k, n, ctx, dims);
    unsigned dim = n.payload;
    if (dims & (UINT64_C(1) << dim)) {
        uint64_t avoid = dims | ck_free_dims(k, n.child[0]) | ck_free_dims(k, n.child[1]);
        unsigned fresh = ck_fresh_dimension(k, avoid);
        cc_formula replacement;
        cc_init(&replacement, CC_INTERVAL);
        if (cc_generator(&replacement, fresh, true) != CC_OK) {
            cc_clear(&replacement);
            return ck_fail(k, "Composition dimension allocation failed.");
        }
        n.child[0] = ck_dimension_substitute(k, n.child[0], dim, &replacement);
        n.child[1] = rename_tubes(k, n.child[1], dim, &replacement);
        cc_clear(&replacement);
        dim = fresh;
    }
    uint64_t inner = dims | (UINT64_C(1) << dim);
    uint32_t level;
    cc_term family, base;
    if (!ck_type(k, n.child[0], ctx, inner, &family, &level))
        return false;
    cc_term start = ck_endpoint_term(k, family, dim, 0);
    if (!ck_check(k, n.child[2], start, ctx, dims, &base))
        return false;
    cc_term reversed = 0;
    for (cc_term cursor = n.child[1]; cursor && !k->error[0];) {
        cc_node tube = k->nodes[cursor];
        if (tube.kind != CC_TUBE)
            return ck_fail(k, "Malformed composition system.");
        cursor = tube.child[1];
        const cc_formula *raw = cc_kernel_get_formula(k, tube.payload);
        if (!raw || raw->sort != CC_FACE)
            return ck_fail(k, "Composition requires face formulas.");
        cc_formula phi;
        cc_init(&phi, CC_FACE);
        if (cc_copy(&phi, raw) != CC_OK)
            return ck_fail(k, "Composition face copy failed.");
        for (size_t i = 0; i < phi.length && !k->error[0]; ++i) {
            cc_clause clause = phi.clauses[i];
            if ((clause.positive | clause.negative) & ~dims) {
                ck_fail(k, "Composition face uses an unbound dimension.");
                break;
            }
            size_t length;
            cc_context *context = ck_restricted_context(k, ctx, clause, &length);
            if (k->error[0]) {
                free(context);
                break;
            }
            cc_term restricted_type = ck_restrict(k, family, clause);
            cc_term restricted_term = ck_restrict(k, tube.child[0], clause);
            cc_term checked;
            bool valid = ck_check(k, restricted_term, restricted_type, context, inner, &checked);
            free(context);
            if (!valid)
                break;
            cc_term initial = ck_endpoint_term(k, checked, dim, 0);
            if (!ck_convertible(k, initial, ck_restrict(k, base, clause))) {
                ck_fail(k, "Composition tube disagrees with its base.");
                break;
            }
            for (cc_term previous = reversed; previous && !k->error[0];) {
                cc_node other = k->nodes[previous];
                const cc_formula *other_face = cc_kernel_get_formula(k, other.payload);
                cc_clause overlap = {clause.positive | other_face->clauses[0].positive,
                                     clause.negative | other_face->clauses[0].negative};
                previous = other.child[1];
                if (overlap.positive & overlap.negative)
                    continue; /* Empty overlap imposes no equation. */
                if (!ck_convertible(k, ck_restrict(k, checked, overlap),
                                       ck_restrict(k, other.child[0], overlap)))
                    ck_fail(k, "Composition tubes disagree on an overlap.");
            }
            cc_formula_id face = ck_clause_formula(k, clause);
            reversed = ck_make(k, CC_TUBE, face, checked, reversed, 0, 0);
        }
        cc_clear(&phi);
    }
    if (k->error[0])
        return false;
    cc_term system = 0;
    while (reversed) {
        cc_node tube = k->nodes[reversed];
        system = ck_make(k, CC_TUBE, tube.payload, tube.child[0], system, 0, 0);
        reversed = tube.child[1];
    }
    out->expression = ck_make(k, CC_COMP, dim, family, system, base, 0);
    out->type = ck_endpoint_term(k, family, dim, 1);
    return !k->error[0];
}
