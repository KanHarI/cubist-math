/* Instructions for Glue: the Glue type built one piece at a time, with the
 * equivalences agreeing where pieces overlap, the Glue term, and unglue. The
 * machinery they share is in instructions.c. */
#include "term_internal.h"

/* ---- Glue ---------------------------------------------------------------- */

cc_term cc_kernel_equiv_type(cc_kernel *k, cc_term a, cc_term b) {
    if (!k || !a || !b || a >= k->count || b >= k->count)
        return 0;
    ck_standalone(k);
    return ck_equiv_type(k, a, b);
}

cc_judgement_id cc_instr_glue_base(cc_kernel *k, cc_judgement_id base_id) {
    cc_judgement_id found;
    if (!ck_instr_begin(k, (cc_derivation){.rule = CC_INSTR_GLUE_BASE, .premise = {base_id}}, NULL, 0, &found))
        return found;
    cc_fact a = {0};
    cc_term level = 0;
    if (!ck_instr_premise(k, base_id, CC_FACT_TYPING, &a) || !ck_instr_universe(k, a.type, &level))
        return 0;
    cc_term glue = ck_instr_make(k, CC_GLUE, 0, a.term, 0, 0, 0);
    return glue ? ck_instr_system_fact(k, glue, a.type, a.context, 0) : 0;
}

static cc_term append_piece(cc_kernel *k, cc_term pieces, cc_formula_id face, cc_term type, cc_term equivalence) {
    if (!pieces)
        return ck_instr_make(k, CC_GLUE_SYSTEM, face, type, equivalence, 0, 0);
    cc_node n = k->nodes[pieces];
    cc_term rest = append_piece(k, n.child[2], face, type, equivalence);
    return rest ? ck_instr_make(k, CC_GLUE_SYSTEM, n.payload, n.child[0], n.child[1], rest, 0) : 0;
}

/* A system judgement whose term is of the given kind, with nothing pending. */
static bool open_system(cc_kernel *k, cc_judgement_id id, cc_term_kind kind, cc_fact *s) {
    if (!ck_instr_premise(k, id, CC_FACT_SYSTEM, s))
        return false;
    if (k->nodes[s->term].kind != kind)
        return ck_fail(k, kind == CC_GLUE ? "Not a Glue type under construction." : "Not a Glue term under construction.");
    if (s->pending)
        return ck_fail(k, "The last piece must first be shown to agree with the pieces it overlaps.");
    return true;
}

/* The positions of earlier pieces or tubes, chained through `next`, whose
 * one-clause faces meet a clause. */
static bool overlapping(cc_kernel *k, cc_term cursor, unsigned next, cc_clause clause, uint64_t *out) {
    *out = 0;
    for (uint32_t index = 0; cursor; cursor = k->nodes[cursor].child[next], ++index) {
        const cc_formula *face = cc_kernel_get_formula(k, k->nodes[cursor].payload);
        if (!face->length)
            continue;
        cc_clause other = face->clauses[0];
        if ((clause.positive | other.positive) & (clause.negative | other.negative))
            continue;
        if (index >= 64)
            return ck_fail(k, "A piece may overlap only the first 64 pieces.");
        *out |= UINT64_C(1) << index;
    }
    return true;
}

cc_judgement_id cc_instr_glue_piece(cc_kernel *k, cc_judgement_id system_id, cc_formula_id face,
                                    cc_judgement_id type_id, cc_judgement_id equivalence_id) {
    cc_judgement_id found;
    if (!ck_instr_begin(k, (cc_derivation){.rule = CC_INSTR_GLUE_PIECE, .premise = {system_id, type_id, equivalence_id},
                                  .operand = {face}}, NULL, 0, &found))
        return found;
    cc_fact s = {0}, t = {0}, e = {0};
    cc_term level = 0, own = 0;
    uint32_t dims = 0, context = 0;
    if (!open_system(k, system_id, CC_GLUE, &s) || !ck_instr_premise(k, type_id, CC_FACT_TYPING, &t) ||
        !ck_instr_premise(k, equivalence_id, CC_FACT_TYPING, &e) || !ck_instr_universe(k, s.type, &level) || !ck_instr_universe(k, t.type, &own))
        return 0;
    const cc_formula *phi = cc_kernel_get_formula(k, face);
    if (!phi || phi->sort != CC_FACE || phi->length > 1)
        return ck_fail(k, "A Glue piece's face is one conjunction of endpoint equations, or 0."), 0;
    cc_node glue = k->nodes[s.term];
    uint64_t pending = 0;
    if (phi->length) {
        cc_clause clause = phi->clauses[0];
        uint64_t names = clause.positive | clause.negative;
        if (clause.positive & clause.negative)
            return ck_fail(k, "A Glue piece's face must be consistent."), 0;
        if ((ck_free_dims(k, t.term) | ck_free_dims(k, e.term)) & names)
            return ck_fail(k, "A Glue piece must already be restricted to its face."), 0;
        if (!ck_instr_same(k, e.type, ck_equiv_type(k, t.term, ck_restrict(k, glue.child[0], clause)),
                  "The equivalence is not from the piece's type to the base on the face.") ||
            !overlapping(k, glue.child[1], 2, clause, &pending) || !ck_instr_formula_context(k, phi, &dims))
            return 0;
    }
    if (!ck_instr_merge(k, s.context, t.context, &context) || !ck_instr_merge3(k, context, e.context, dims, &context))
        return 0;
    cc_term pieces = append_piece(k, glue.child[1], face, t.term, e.term);
    cc_term extended = pieces ? ck_instr_make(k, CC_GLUE, 0, glue.child[0], pieces, 0, 0) : 0;
    cc_term sort = ck_universe(k, ck_level_max(k, own, level));
    return extended && sort ? ck_instr_system_fact(k, extended, sort, context, pending) : 0;
}

/* The last piece of a Glue type under construction, and the piece at a position. */
static bool piece_at(cc_kernel *k, cc_term glue, uint32_t position, bool last, cc_node *piece, cc_clause *clause) {
    uint32_t index = 0;
    for (cc_term cursor = k->nodes[glue].child[1]; cursor; cursor = k->nodes[cursor].child[2], ++index) {
        if (last ? k->nodes[cursor].child[2] != 0 : index != position)
            continue;
        *piece = k->nodes[cursor];
        const cc_formula *face = cc_kernel_get_formula(k, piece->payload);
        if (!face || face->length != 1)
            return ck_fail(k, "That piece's face is not one clause.");
        *clause = face->clauses[0];
        return true;
    }
    return ck_fail(k, "The Glue type has no piece at that position.");
}

cc_judgement_id cc_instr_glue_overlap(cc_kernel *k, cc_judgement_id system_id, uint32_t position,
                                      cc_judgement_id types_id, cc_judgement_id equivalences_id) {
    cc_judgement_id found;
    if (!ck_instr_begin(k, (cc_derivation){.rule = CC_INSTR_GLUE_OVERLAP, .premise = {system_id, types_id, equivalences_id},
                                  .operand = {position}}, NULL, 0, &found))
        return found;
    cc_fact s = {0}, t = {0}, e = {0};
    uint32_t context = 0;
    if (!ck_instr_premise(k, system_id, CC_FACT_SYSTEM, &s) || !ck_instr_premise(k, types_id, CC_FACT_EQUALITY, &t) ||
        !ck_instr_premise(k, equivalences_id, CC_FACT_EQUALITY, &e))
        return 0;
    if (k->nodes[s.term].kind != CC_GLUE)
        return ck_fail(k, "Not a Glue type under construction."), 0;
    if (position >= 64 || !(s.pending & (UINT64_C(1) << position)))
        return ck_fail(k, "The last piece does not overlap that piece, or already agrees with it."), 0;
    cc_node mine = {0}, theirs = {0};
    cc_clause a = {0}, b = {0};
    if (!piece_at(k, s.term, 0, true, &mine, &a) || !piece_at(k, s.term, position, false, &theirs, &b))
        return 0;
    cc_clause overlap = {a.positive | b.positive, a.negative | b.negative};
    if (!ck_instr_same(k, t.term, ck_restrict(k, mine.child[0], overlap), "The types' equality does not start at the last piece.") ||
        !ck_instr_same(k, t.other, ck_restrict(k, theirs.child[0], overlap), "The types' equality does not end at the other piece.") ||
        !ck_instr_same(k, e.term, ck_restrict(k, mine.child[1], overlap), "The equivalences' equality does not start at the last piece.") ||
        !ck_instr_same(k, e.other, ck_restrict(k, theirs.child[1], overlap), "The equivalences' equality does not end at the other piece.") ||
        !ck_instr_merge3(k, s.context, t.context, e.context, &context))
        return 0;
    return ck_instr_system_fact(k, s.term, s.type, context, s.pending & ~(UINT64_C(1) << position));
}

cc_judgement_id cc_instr_glue(cc_kernel *k, cc_judgement_id system_id) {
    cc_judgement_id found;
    if (!ck_instr_begin(k, (cc_derivation){.rule = CC_INSTR_GLUE, .premise = {system_id}}, NULL, 0, &found))
        return found;
    cc_fact s = {0};
    if (!open_system(k, system_id, CC_GLUE, &s))
        return 0;
    return ck_instr_typing(k, s.term, s.type, s.context);
}

cc_judgement_id cc_instr_glue_term_base(cc_kernel *k, cc_judgement_id type_id, cc_judgement_id base_id) {
    cc_judgement_id found;
    if (!ck_instr_begin(k, (cc_derivation){.rule = CC_INSTR_GLUE_TERM_BASE, .premise = {type_id, base_id}}, NULL, 0, &found))
        return found;
    cc_fact g = {0}, a = {0};
    cc_term level = 0;
    uint32_t context = 0;
    if (!ck_instr_premise(k, type_id, CC_FACT_TYPING, &g) || !ck_instr_premise(k, base_id, CC_FACT_TYPING, &a) ||
        !ck_instr_universe(k, g.type, &level))
        return 0;
    cc_node glue = k->nodes[g.term];
    if (glue.kind != CC_GLUE)
        return ck_fail(k, "A Glue term needs a Glue type."), 0;
    if (!ck_instr_same(k, a.type, glue.child[0], "The base is not in the Glue type's base.") ||
        !ck_instr_merge(k, g.context, a.context, &context))
        return 0;
    cc_term term = ck_instr_make(k, CC_GLUE_TERM, 0, g.term, a.term, 0, 0);
    return term ? ck_instr_system_fact(k, term, g.term, context, 0) : 0;
}

cc_judgement_id cc_instr_glue_term_piece(cc_kernel *k, cc_judgement_id system_id, cc_judgement_id value_id,
                                         cc_judgement_id image_id) {
    cc_judgement_id found;
    if (!ck_instr_begin(k, (cc_derivation){.rule = CC_INSTR_GLUE_TERM_PIECE, .premise = {system_id, value_id, image_id}},
               NULL, 0, &found))
        return found;
    cc_fact s = {0}, v = {0}, e = {0};
    uint32_t dims = 0, context = 0;
    if (!open_system(k, system_id, CC_GLUE_TERM, &s) || !ck_instr_premise(k, value_id, CC_FACT_TYPING, &v))
        return 0;
    cc_node term = k->nodes[s.term], glue = k->nodes[term.child[0]];
    /* The piece of the type this value is for: the next one, in order. */
    cc_term piece = glue.child[1];
    for (cc_term cursor = term.child[2]; cursor && piece; cursor = k->nodes[cursor].child[1])
        piece = k->nodes[piece].child[2];
    if (!piece)
        return ck_fail(k, "The Glue term has a value for every piece of its type."), 0;
    cc_node part = k->nodes[piece];
    const cc_formula *phi = cc_kernel_get_formula(k, part.payload);
    uint64_t pending = 0;
    if (phi->length) {
        cc_clause clause = phi->clauses[0];
        if (!ck_instr_premise(k, image_id, CC_FACT_EQUALITY, &e))
            return 0;
        if (ck_free_dims(k, v.term) & (clause.positive | clause.negative))
            return ck_fail(k, "A Glue term's value must already be restricted to its face."), 0;
        cc_term image = ck_instr_app(k, ck_instr_make(k, CC_FST, 0, part.child[1], 0, 0, 0), v.term);
        if (!ck_instr_same(k, v.type, part.child[0], "The value is not in the piece's type.") ||
            !ck_instr_same(k, e.term, image, "The equality does not start at the value's image.") ||
            !ck_instr_same(k, e.other, ck_restrict(k, term.child[1], clause), "The equality does not end at the base on the face.") ||
            !overlapping(k, term.child[2], 1, clause, &pending) || !ck_instr_formula_context(k, phi, &dims) ||
            !ck_instr_merge(k, s.context, e.context, &context))
            return 0;
    } else {
        if (image_id)
            return ck_fail(k, "A value on the face 0 takes no equality."), 0;
        context = s.context;
    }
    if (!ck_instr_merge3(k, context, v.context, dims, &context))
        return 0;
    cc_term tubes = ck_instr_append_tube(k, term.child[2], part.payload, v.term);
    cc_term extended = tubes ? ck_instr_make(k, CC_GLUE_TERM, 0, term.child[0], term.child[1], tubes, 0) : 0;
    return extended ? ck_instr_system_fact(k, extended, s.type, context, pending) : 0;
}

cc_judgement_id cc_instr_glue_term(cc_kernel *k, cc_judgement_id system_id) {
    cc_judgement_id found;
    if (!ck_instr_begin(k, (cc_derivation){.rule = CC_INSTR_GLUE_TERM, .premise = {system_id}}, NULL, 0, &found))
        return found;
    cc_fact s = {0};
    if (!open_system(k, system_id, CC_GLUE_TERM, &s))
        return 0;
    cc_node term = k->nodes[s.term];
    cc_term piece = k->nodes[term.child[0]].child[1], tube = term.child[2];
    for (; piece && tube; piece = k->nodes[piece].child[2], tube = k->nodes[tube].child[1]) {}
    if (piece || tube)
        return ck_fail(k, "The Glue term has a value for every piece of its type."), 0;
    return ck_instr_typing(k, s.term, s.type, s.context);
}

cc_judgement_id cc_instr_unglue(cc_kernel *k, cc_judgement_id value_id) {
    cc_judgement_id found;
    if (!ck_instr_begin(k, (cc_derivation){.rule = CC_INSTR_UNGLUE, .premise = {value_id}}, NULL, 0, &found))
        return found;
    cc_fact v = {0};
    if (!ck_instr_premise(k, value_id, CC_FACT_TYPING, &v))
        return 0;
    cc_node glue = k->nodes[v.type];
    if (glue.kind != CC_GLUE)
        return ck_fail(k, "Only an element of a Glue type is unglued."), 0;
    return ck_instr_typing(k, ck_instr_make(k, CC_UNGLUE, 0, v.type, v.term, 0, 0), glue.child[0], v.context);
}
