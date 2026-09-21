/* Glue [phi -> (T,e)] A, with e : Equiv(T,A) checked on each face.
 * Types and equivalence witnesses must agree on overlaps. A Glue element
 * consists of a total a:A and partial t:T whose image e(t) agrees with a.
 * The explicit Glue annotation is retained for projection at a total face. */
#include "term_internal.h"

static bool face_copy(cc_kernel *k, cc_formula_id id, uint64_t dims, cc_formula *out) {
    const cc_formula *raw = cc_kernel_get_formula(k, id);
    if (!raw || raw->sort != CC_FACE)
        return ck_fail(k, "Glue requires a face formula.");
    if (cc_copy(out, raw) != CC_OK)
        return ck_fail(k, "Glue face allocation failed.");
    for (size_t i = 0; i < out->length; ++i)
        if ((out->clauses[i].positive | out->clauses[i].negative) & ~dims)
            return ck_fail(k, "Glue face uses an unbound dimension.");
    return true;
}

static cc_term reverse_system(cc_kernel *k, cc_term reversed, bool types) {
    cc_term result = 0;
    unsigned next = types ? 2 : 1;
    while (reversed && !k->error[0]) {
        cc_node n = k->nodes[reversed];
        reversed = n.child[next];
        n.child[next] = result;
        result = ck_make(k, n.kind, n.payload, n.child[0], n.child[1], n.child[2], 0);
    }
    return result;
}

static bool formation(cc_kernel *k, cc_node n, const cc_context *ctx,
                       uint64_t dims, cc_judgement *out) {
    cc_term base;
    uint32_t level;
    if (!ck_type(k, n.child[0], ctx, dims, &base, &level))
        return false;
    cc_term reversed = 0;
    for (cc_term cursor = n.child[1]; cursor && !k->error[0];) {
        cc_node piece = k->nodes[cursor];
        if (piece.kind != CC_GLUE_SYSTEM)
            return ck_fail(k, "Malformed Glue type system.");
        cursor = piece.child[2];
        cc_formula face;
        cc_init(&face, CC_FACE);
        if (!face_copy(k, piece.payload, dims, &face)) {
            cc_clear(&face);
            return false;
        }
        for (size_t i = 0; i < face.length && !k->error[0]; ++i) {
            cc_clause clause = face.clauses[i];
            size_t length;
            cc_context *context = ck_restricted_context(k, ctx, clause, &length);
            cc_term partial, equivalence;
            uint32_t partial_level;
            bool valid = !k->error[0] && ck_type(k, ck_restrict(k, piece.child[0], clause),
                                               context, dims, &partial, &partial_level);
            if (valid) {
                cc_term target = ck_restrict(k, base, clause);
                cc_term expected = ck_equiv_type(k, partial, target);
                valid = ck_check(k, ck_restrict(k, piece.child[1], clause), expected,
                                 context, dims, &equivalence);
            }
            free(context);
            if (!valid)
                break;
            if (partial_level > level)
                level = partial_level;
            for (cc_term prior = reversed; prior && !k->error[0];) {
                cc_node other = k->nodes[prior];
                const cc_formula *phi = cc_kernel_get_formula(k, other.payload);
                cc_clause overlap = {clause.positive | phi->clauses[0].positive,
                                     clause.negative | phi->clauses[0].negative};
                prior = other.child[2];
                if (overlap.positive & overlap.negative)
                    continue;
                if (!ck_convertible(k, ck_restrict(k, partial, overlap),
                                       ck_restrict(k, other.child[0], overlap)))
                    ck_fail(k, "Glue types disagree on an overlap.");
                if (!ck_convertible(k, ck_restrict(k, equivalence, overlap),
                                       ck_restrict(k, other.child[1], overlap)))
                    ck_fail(k, "Glue equivalences disagree on an overlap.");
            }
            cc_formula_id phi = ck_clause_formula(k, clause);
            reversed = ck_make(k, CC_GLUE_SYSTEM, phi, partial, equivalence, reversed, 0);
        }
        cc_clear(&face);
    }
    out->expression = ck_make(k, CC_GLUE, 0, base, reverse_system(k, reversed, true), 0, 0);
    out->type = ck_make(k, CC_U, level, 0, 0, 0, 0);
    return !k->error[0];
}

static cc_term flatten_values(cc_kernel *k, cc_term system, uint64_t dims) {
    cc_term reversed = 0;
    while (system && !k->error[0]) {
        cc_node piece = k->nodes[system];
        if (piece.kind != CC_TUBE)
            return ck_fail(k, "Malformed partial Glue value."), 0;
        system = piece.child[1];
        cc_formula face;
        cc_init(&face, CC_FACE);
        if (!face_copy(k, piece.payload, dims, &face)) {
            cc_clear(&face);
            return 0;
        }
        for (size_t i = 0; i < face.length; ++i) {
            cc_formula_id clause = ck_clause_formula(k, face.clauses[i]);
            reversed = ck_make(k, CC_TUBE, clause, piece.child[0], reversed, 0, 0);
        }
        cc_clear(&face);
    }
    return reverse_system(k, reversed, false);
}

bool ck_glue(cc_kernel *k, cc_node n, const cc_context *ctx, uint64_t dims,
               cc_judgement *out) {
    if (n.kind == CC_GLUE)
        return formation(k, n, ctx, dims, out);
    cc_term annotation;
    uint32_t level;
    if (!ck_type(k, n.child[0], ctx, dims, &annotation, &level))
        return false;
    cc_node type = k->nodes[annotation];
    if (type.kind != CC_GLUE)
        return ck_fail(k, "Glue term requires an explicit checked Glue type.");
    if (n.kind == CC_UNGLUE) {
        cc_term value;
        if (!ck_check(k, n.child[1], annotation, ctx, dims, &value))
            return false;
        out->expression = ck_make(k, CC_UNGLUE, 0, annotation, value, 0, 0);
        out->type = type.child[0];
        return !k->error[0];
    }
    if (n.kind != CC_GLUE_TERM)
        return ck_fail(k, "Unknown Glue rule.");
    cc_term base;
    if (!ck_check(k, n.child[1], type.child[0], ctx, dims, &base))
        return false;
    cc_term values = flatten_values(k, n.child[2], dims);
    cc_term reversed = 0;
    for (cc_term cursor = type.child[1]; cursor && !k->error[0];) {
        cc_node part = k->nodes[cursor];
        cursor = part.child[2];
        if (!values)
            return ck_fail(k, "Glue value is missing a partial face.");
        cc_node raw = k->nodes[values];
        values = raw.child[1];
        const cc_formula *phi = cc_kernel_get_formula(k, part.payload);
        const cc_formula *supplied = cc_kernel_get_formula(k, raw.payload);
        if (!cc_equal(phi, supplied))
            return ck_fail(k, "Glue value face does not match its type.");
        cc_clause clause = phi->clauses[0];
        size_t length;
        cc_context *context = ck_restricted_context(k, ctx, clause, &length);
        cc_term value;
        bool valid = !k->error[0] && ck_check(k, ck_restrict(k, raw.child[0], clause),
                                            part.child[0], context, dims, &value);
        free(context);
        if (!valid)
            return false;
        cc_term function = ck_make(k, CC_FST, 0, part.child[1], 0, 0, 0);
        cc_term image = ck_make(k, CC_APP, 0, function, value, 0, 0);
        if (!ck_convertible(k, image, ck_restrict(k, base, clause)))
            return ck_fail(k, "Glue value does not agree with its base under the equivalence.");
        for (cc_term prior = reversed; prior && !k->error[0];) {
            cc_node other = k->nodes[prior];
            const cc_formula *face = cc_kernel_get_formula(k, other.payload);
            cc_clause overlap = {clause.positive | face->clauses[0].positive,
                                 clause.negative | face->clauses[0].negative};
            prior = other.child[1];
            if (!(overlap.positive & overlap.negative) &&
                !ck_convertible(k, ck_restrict(k, value, overlap),
                                   ck_restrict(k, other.child[0], overlap)))
                ck_fail(k, "Glue values disagree on an overlap.");
        }
        reversed = ck_make(k, CC_TUBE, part.payload, value, reversed, 0, 0);
    }
    if (values)
        return ck_fail(k, "Glue value supplies extra partial faces.");
    cc_term system = reverse_system(k, reversed, false);
    out->expression = ck_make(k, CC_GLUE_TERM, 0, annotation, base, system, 0);
    out->type = annotation;
    return !k->error[0];
}
