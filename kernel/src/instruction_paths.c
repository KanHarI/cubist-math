/* Instructions for paths, composition and transport: Path formation, path
 * abstraction and application at an interval formula, endpoints, and
 * composition built one tube at a time, with HComp and Trans for declared
 * higher sorts. The machinery they share is in instructions.c. */
#include "term_internal.h"

/* ---- Paths -------------------------------------------------------------- */

cc_judgement_id cc_instr_path(cc_kernel *k, cc_entry_id dimension, cc_judgement_id family_id,
                              cc_judgement_id left_id, cc_judgement_id right_id) {
    cc_judgement_id found;
    if (!ck_instr_begin(k, (cc_derivation){.rule = CC_INSTR_PATH, .premise = {family_id, left_id, right_id}, .entry = dimension}, NULL, 0, &found))
        return found;
    cc_entry i = {0};
    cc_fact a = {0}, l = {0}, r = {0};
    cc_term level = 0;
    uint32_t context = 0;
    if (!ck_instr_entry(k, dimension, true, &i) || !ck_instr_premise(k, family_id, CC_FACT_TYPING, &a) ||
        !ck_instr_premise(k, left_id, CC_FACT_TYPING, &l) || !ck_instr_premise(k, right_id, CC_FACT_TYPING, &r) ||
        !ck_instr_universe(k, a.type, &level) ||
        !ck_instr_same(k, l.type, ck_endpoint_term(k, a.term, i.symbol, 0), "The left endpoint has the wrong type.") ||
        !ck_instr_same(k, r.type, ck_endpoint_term(k, a.term, i.symbol, 1), "The right endpoint has the wrong type.") ||
        !ck_instr_bind(k, a.context, dimension, &context) || !ck_instr_merge3(k, context, l.context, r.context, &context))
        return 0;
    return ck_instr_typing(k, ck_instr_make(k, CC_PATH, i.symbol, a.term, l.term, r.term, 0), a.type, context);
}

cc_judgement_id cc_instr_path_lambda(cc_kernel *k, cc_entry_id dimension, cc_judgement_id body_id) {
    cc_judgement_id found;
    if (!ck_instr_begin(k, (cc_derivation){.rule = CC_INSTR_PATH_LAMBDA, .premise = {body_id}, .entry = dimension}, NULL, 0, &found))
        return found;
    cc_entry i = {0};
    cc_fact b = {0};
    uint32_t context = 0;
    if (!ck_instr_entry(k, dimension, true, &i) || !ck_instr_premise(k, body_id, CC_FACT_TYPING, &b) ||
        !ck_instr_bind(k, b.context, dimension, &context))
        return 0;
    cc_term type = ck_instr_make(k, CC_PATH, i.symbol, b.type, ck_endpoint_term(k, b.term, i.symbol, 0),
                        ck_endpoint_term(k, b.term, i.symbol, 1), 0);
    return ck_instr_typing(k, ck_instr_make(k, CC_PLAM, i.symbol, b.type, b.term, 0, 0), type, context);
}

cc_judgement_id cc_instr_path_apply(cc_kernel *k, cc_judgement_id path_id, cc_entry_id dimension, unsigned endpoint) {
    cc_judgement_id found;
    if (!ck_instr_begin(k, (cc_derivation){.rule = CC_INSTR_PATH_APPLY, .premise = {path_id}, .entry = dimension, .operand = {endpoint}}, NULL, 0, &found))
        return found;
    cc_fact p = {0};
    cc_entry i = {0};
    uint32_t context = 0;
    if (!ck_instr_premise(k, path_id, CC_FACT_TYPING, &p) || (dimension && !ck_instr_entry(k, dimension, true, &i)))
        return 0;
    cc_node type = k->nodes[p.type];
    if (type.kind != CC_PATH)
        return ck_fail(k, "Only a term of a path type can be applied to a dimension."), 0;
    if (!dimension && endpoint > 1)
        return ck_fail(k, "A path applies at a dimension, 0 or 1."), 0;
    cc_formula point;
    cc_init(&point, CC_INTERVAL);
    cc_status status = dimension ? cc_generator(&point, i.symbol, true) : endpoint ? cc_one(&point) : CC_OK;
    cc_formula_id argument = status == CC_OK ? ck_formula(k, &point) : 0;
    cc_term result = argument ? ck_dimension_substitute(k, type.child[0], type.payload, &point) : 0;
    cc_clear(&point);
    if (status != CC_OK)
        return ck_fail(k, "Interval allocation failed."), 0;
    if (!result || !ck_instr_merge(k, p.context, dimension ? i.scope : 0, &context))
        return 0;
    return ck_instr_typing(k, ck_instr_make(k, CC_PAPP, argument, p.term, p.type, 0, 0), result, context);
}

cc_judgement_id cc_instr_endpoint(cc_kernel *k, cc_judgement_id id, cc_entry_id dimension, unsigned endpoint) {
    cc_judgement_id found;
    if (!ck_instr_begin(k, (cc_derivation){.rule = CC_INSTR_ENDPOINT, .premise = {id}, .entry = dimension, .operand = {endpoint}},
               NULL, 0, &found))
        return found;
    cc_fact t = {0};
    cc_entry i = {0};
    uint32_t context = 0;
    if (!ck_instr_premise(k, id, CC_FACT_TYPING, &t) || !ck_instr_entry(k, dimension, true, &i))
        return 0;
    if (endpoint > 1)
        return ck_fail(k, "An endpoint is 0 or 1."), 0;
    if (!ck_instr_discharge(k, t.context, &dimension, 1, &context))
        return 0;
    return ck_instr_typing(k, ck_endpoint_term(k, t.term, i.symbol, endpoint), ck_endpoint_term(k, t.type, i.symbol, endpoint), context);
}

/* The context of the dimensions an interval or face formula names. */
bool ck_instr_formula_context(cc_kernel *k, const cc_formula *f, uint32_t *out) {
    uint64_t names = 0;
    for (size_t i = 0; i < f->length; ++i) names |= f->clauses[i].positive | f->clauses[i].negative;
    *out = 0;
    for (unsigned dim = 0; dim < CC_DIMENSIONS && !k->error[0]; ++dim)
        if (names & (UINT64_C(1) << dim)) {
            cc_entry_id entry = ck_instr_dimension_entry(k, dim);
            if (!entry || !ck_instr_merge(k, *out, k->entries[entry].scope, out)) return false;
        }
    return !k->error[0];
}

cc_judgement_id cc_instr_path_at(cc_kernel *k, cc_judgement_id path_id, cc_formula_id interval) {
    cc_judgement_id found;
    if (!ck_instr_begin(k, (cc_derivation){.rule = CC_INSTR_PATH_AT, .premise = {path_id}, .operand = {interval}}, NULL, 0, &found))
        return found;
    cc_fact p = {0};
    uint32_t dims = 0, context = 0;
    if (!ck_instr_premise(k, path_id, CC_FACT_TYPING, &p))
        return 0;
    cc_node type = k->nodes[p.type];
    if (type.kind != CC_PATH)
        return ck_fail(k, "Only a term of a path type can be applied to an interval formula."), 0;
    const cc_formula *point = cc_kernel_get_formula(k, interval);
    if (!point || point->sort != CC_INTERVAL)
        return ck_fail(k, "A path applies at an interval formula."), 0;
    if (!ck_instr_formula_context(k, point, &dims) || !ck_instr_merge(k, p.context, dims, &context))
        return 0;
    return ck_instr_typing(k, ck_instr_make(k, CC_PAPP, interval, p.term, p.type, 0, 0),
                  ck_dimension_substitute(k, type.child[0], type.payload, point), context);
}

cc_judgement_id cc_instr_system(cc_kernel *k, cc_entry_id dimension, cc_judgement_id family_id, cc_judgement_id base_id) {
    cc_judgement_id found;
    if (!ck_instr_begin(k, (cc_derivation){.rule = CC_INSTR_SYSTEM, .premise = {family_id, base_id}, .entry = dimension}, NULL, 0, &found))
        return found;
    cc_entry i = {0};
    cc_fact a = {0}, b = {0};
    cc_term level = 0;
    uint32_t context = 0;
    if (!ck_instr_entry(k, dimension, true, &i) || !ck_instr_premise(k, family_id, CC_FACT_TYPING, &a) ||
        !ck_instr_premise(k, base_id, CC_FACT_TYPING, &b) || !ck_instr_universe(k, a.type, &level) ||
        !ck_instr_same(k, b.type, ck_endpoint_term(k, a.term, i.symbol, 0), "The base is not in the family at 0.") ||
        !ck_instr_merge(k, a.context, b.context, &context))
        return 0;
    if (ck_free_dims(k, b.term) & (UINT64_C(1) << i.symbol))
        return ck_fail(k, "The base of a composition may not use its dimension."), 0;
    cc_term comp = ck_instr_make(k, CC_COMP, i.symbol, a.term, 0, b.term, 0);
    return comp ? ck_instr_publish(k, CC_FACT_SYSTEM, comp, 0, ck_endpoint_term(k, a.term, i.symbol, 1), context) : 0;
}

cc_term ck_instr_append_tube(cc_kernel *k, cc_term tubes, cc_formula_id face, cc_term tube) {
    if (!tubes)
        return ck_instr_make(k, CC_TUBE, face, tube, 0, 0, 0);
    cc_node n = k->nodes[tubes];
    cc_term rest = ck_instr_append_tube(k, n.child[1], face, tube);
    return rest ? ck_instr_make(k, CC_TUBE, n.payload, n.child[0], rest, 0, 0) : 0;
}

/* Where a system's tubes hang: a composition's second child, a Glue term's
 * third. Zero for a term that is not a system of tubes. */
static unsigned tube_slot(cc_kernel *k, cc_term system) {
    cc_term_kind kind = k->nodes[system].kind;
    return kind == CC_COMP ? 1 : kind == CC_GLUE_TERM ? 2 : 0;
}

/* The last tube of a system, its clause, and the tube at a position. */
static bool tube_at(cc_kernel *k, cc_term comp, uint32_t position, cc_term *term, cc_clause *clause, bool last) {
    uint32_t index = 0;
    for (cc_term cursor = k->nodes[comp].child[tube_slot(k, comp)]; cursor; cursor = k->nodes[cursor].child[1], ++index) {
        if (last ? k->nodes[cursor].child[1] != 0 : index != position)
            continue;
        const cc_formula *face = cc_kernel_get_formula(k, k->nodes[cursor].payload);
        if (!face || face->length != 1)
            return ck_fail(k, "That tube's face is not one clause.");
        *term = k->nodes[cursor].child[0];
        *clause = face->clauses[0];
        return true;
    }
    return ck_fail(k, "The system has no tube at that position.");
}

cc_judgement_id ck_instr_system_fact(cc_kernel *k, cc_term comp, cc_term type, uint32_t context, uint64_t pending) {
    cc_judgement_id id = ck_instr_publish(k, CC_FACT_SYSTEM, comp, 0, type, context);
    if (id)
        k->facts[id].pending = pending;
    return id;
}

cc_judgement_id cc_instr_system_tube(cc_kernel *k, cc_judgement_id system_id, cc_formula_id face,
                                     cc_judgement_id tube_id, cc_judgement_id adjacency_id) {
    cc_judgement_id found;
    if (!ck_instr_begin(k, (cc_derivation){.rule = CC_INSTR_SYSTEM_TUBE, .premise = {system_id, tube_id, adjacency_id},
                                  .operand = {face}}, NULL, 0, &found))
        return found;
    cc_fact s = {0}, u = {0}, e = {0};
    uint32_t dims = 0, context = 0;
    if (!ck_instr_premise(k, system_id, CC_FACT_SYSTEM, &s) || !ck_instr_premise(k, tube_id, CC_FACT_TYPING, &u))
        return 0;
    if (s.pending)
        return ck_fail(k, "The last tube must first be shown to agree with the tubes it overlaps."), 0;
    cc_node comp = k->nodes[s.term];
    if (comp.kind != CC_COMP)
        return ck_fail(k, "Not a composition system."), 0;
    unsigned dim = comp.payload;
    const cc_formula *phi = cc_kernel_get_formula(k, face);
    if (!phi || phi->sort != CC_FACE || phi->length > 1)
        return ck_fail(k, "A tube's face is one conjunction of endpoint equations, or 0."), 0;
    if (!phi->length) {
        /* On the face 0 nothing is required of the tube: it is never used. */
        if (adjacency_id)
            return ck_fail(k, "A tube on the face 0 takes no equality."), 0;
        cc_term tubes = ck_instr_merge(k, s.context, u.context, &context) ? ck_instr_append_tube(k, comp.child[1], face, u.term) : 0;
        cc_term extended = tubes ? ck_instr_make(k, CC_COMP, dim, comp.child[0], tubes, comp.child[2], 0) : 0;
        return extended ? ck_instr_system_fact(k, extended, s.type, context, 0) : 0;
    }
    if (!ck_instr_premise(k, adjacency_id, CC_FACT_EQUALITY, &e))
        return 0;
    cc_clause clause = phi->clauses[0];
    uint64_t names = clause.positive | clause.negative;
    if (clause.positive & clause.negative)
        return ck_fail(k, "A tube's face must be consistent."), 0;
    if (names & (UINT64_C(1) << dim))
        return ck_fail(k, "A tube's face may not use the composition's dimension."), 0;
    if (ck_free_dims(k, u.term) & names)
        return ck_fail(k, "A tube must already be restricted to its face."), 0;
    /* Every earlier tube whose face meets this one's must agree with it on
     * the overlap: SystemOverlap, once for each. */
    uint64_t pending = 0;
    uint32_t index = 0;
    for (cc_term cursor = comp.child[1]; cursor; cursor = k->nodes[cursor].child[1], ++index) {
        const cc_formula *other_face = cc_kernel_get_formula(k, k->nodes[cursor].payload);
        if (!other_face->length)
            continue;
        cc_clause other = other_face->clauses[0];
        if ((clause.positive | other.positive) & (clause.negative | other.negative))
            continue;
        if (index >= 64)
            return ck_fail(k, "A tube may overlap only the first 64 tubes of a system."), 0;
        pending |= UINT64_C(1) << index;
    }
    if (!ck_instr_same(k, u.type, ck_restrict(k, comp.child[0], clause), "The tube is not in the family on its face.") ||
        !ck_instr_same(k, e.term, ck_endpoint_term(k, u.term, dim, 0), "The equality does not start at the tube at 0.") ||
        !ck_instr_same(k, e.other, ck_restrict(k, comp.child[2], clause), "The equality does not end at the base on the face.") ||
        !ck_instr_formula_context(k, phi, &dims) || !ck_instr_merge(k, s.context, u.context, &context) ||
        !ck_instr_merge3(k, context, e.context, dims, &context))
        return 0;
    cc_term tubes = ck_instr_append_tube(k, comp.child[1], face, u.term);
    cc_term extended = tubes ? ck_instr_make(k, CC_COMP, dim, comp.child[0], tubes, comp.child[2], 0) : 0;
    return extended ? ck_instr_system_fact(k, extended, s.type, context, pending) : 0;
}

/* The last tube u and the tube v at a position agree where their faces meet:
 * an equality u ≡ v, both restricted to the overlap. */
cc_judgement_id cc_instr_system_overlap(cc_kernel *k, cc_judgement_id system_id, uint32_t position,
                                        cc_judgement_id agreement_id) {
    cc_judgement_id found;
    if (!ck_instr_begin(k, (cc_derivation){.rule = CC_INSTR_SYSTEM_OVERLAP, .premise = {system_id, agreement_id},
                                  .operand = {position}}, NULL, 0, &found))
        return found;
    cc_fact s = {0}, e = {0};
    uint32_t context = 0;
    if (!ck_instr_premise(k, system_id, CC_FACT_SYSTEM, &s) || !ck_instr_premise(k, agreement_id, CC_FACT_EQUALITY, &e))
        return 0;
    if (!tube_slot(k, s.term))
        return ck_fail(k, "Not a system of tubes."), 0;
    if (position >= 64 || !(s.pending & (UINT64_C(1) << position)))
        return ck_fail(k, "The last tube does not overlap that tube, or already agrees with it."), 0;
    cc_term last = 0, other = 0;
    cc_clause mine = {0}, theirs = {0};
    if (!tube_at(k, s.term, 0, &last, &mine, true) || !tube_at(k, s.term, position, &other, &theirs, false))
        return 0;
    cc_clause overlap = {mine.positive | theirs.positive, mine.negative | theirs.negative};
    if (!ck_instr_same(k, e.term, ck_restrict(k, last, overlap), "The equality does not start at the last tube on the overlap.") ||
        !ck_instr_same(k, e.other, ck_restrict(k, other, overlap), "The equality does not end at the other tube on the overlap.") ||
        !ck_instr_merge(k, s.context, e.context, &context))
        return 0;
    return ck_instr_system_fact(k, s.term, s.type, context, s.pending & ~(UINT64_C(1) << position));
}

cc_judgement_id cc_instr_comp(cc_kernel *k, cc_judgement_id system_id) {
    cc_judgement_id found;
    if (!ck_instr_begin(k, (cc_derivation){.rule = CC_INSTR_COMP, .premise = {system_id}}, NULL, 0, &found))
        return found;
    cc_fact s = {0};
    uint32_t context = 0;
    if (!ck_instr_premise(k, system_id, CC_FACT_SYSTEM, &s))
        return 0;
    if (s.pending)
        return ck_fail(k, "The last tube must first be shown to agree with the tubes it overlaps."), 0;
    if (k->nodes[s.term].kind != CC_COMP)
        return ck_fail(k, "Not a composition system."), 0;
    cc_entry_id dimension = ck_instr_dimension_entry(k, k->nodes[s.term].payload);
    if (!dimension || !ck_instr_discharge(k, s.context, &dimension, 1, &context))
        return 0;
    return ck_instr_typing(k, s.term, s.type, context);
}

/* Formal composition and transport are for declared higher sorts (H1 family
 * F4); a declared data sort has neither, and composes and transports by Comp
 * (Q1, 3.3). */
static bool formal_family(cc_kernel *k, cc_term family, const char *refusal) {
    cc_term head = ck_whnf(k, family);
    if (!head)
        return false;
    if (k->nodes[head].kind == CC_SORT) {
        const cc_signature *s = ck_instance_signature(k, head);
        if (!s || ck_signature_higher(s))
            return s != NULL;
        return ck_fail(k, "A declared data sort has no formal composition or transport: compose it with Comp, "
                          "whose tube φ ↦ u_0 transports (Q1).");
    }
    return k->error[0] ? false : ck_fail(k, refusal);
}

cc_judgement_id cc_instr_hcomp(cc_kernel *k, cc_judgement_id system_id) {
    cc_judgement_id found;
    if (!ck_instr_begin(k, (cc_derivation){.rule = CC_INSTR_HCOMP, .premise = {system_id}}, NULL, 0, &found))
        return found;
    cc_fact s = {0};
    uint32_t context = 0;
    if (!ck_instr_premise(k, system_id, CC_FACT_SYSTEM, &s))
        return 0;
    if (s.pending)
        return ck_fail(k, "The last tube must first be shown to agree with the tubes it overlaps."), 0;
    if (k->nodes[s.term].kind != CC_COMP)
        return ck_fail(k, "Not a composition system."), 0;
    cc_node comp = k->nodes[s.term];
    if (ck_free_dims(k, comp.child[0]) & (UINT64_C(1) << comp.payload))
        return ck_fail(k, "A homogeneous composition's type may not use its dimension."), 0;
    if (!formal_family(k, comp.child[0], "Homogeneous composition is for declared higher sorts."))
        return 0;
    cc_entry_id dimension = ck_instr_dimension_entry(k, comp.payload);
    if (!dimension || !ck_instr_discharge(k, s.context, &dimension, 1, &context))
        return 0;
    return ck_instr_typing(k, ck_instr_make(k, CC_HCOMP, comp.payload, comp.child[0], comp.child[1], comp.child[2], 0), s.type, context);
}

cc_judgement_id cc_instr_trans(cc_kernel *k, cc_judgement_id system_id, cc_formula_id face) {
    cc_judgement_id found;
    if (!ck_instr_begin(k, (cc_derivation){.rule = CC_INSTR_TRANS, .premise = {system_id}, .operand = {face}}, NULL, 0, &found))
        return found;
    cc_fact s = {0};
    uint32_t context = 0, dims = 0;
    if (!ck_instr_premise(k, system_id, CC_FACT_SYSTEM, &s))
        return 0;
    if (s.pending)
        return ck_fail(k, "The last tube must first be shown to agree with the tubes it overlaps."), 0;
    if (k->nodes[s.term].kind != CC_COMP)
        return ck_fail(k, "Not a composition system."), 0;
    const cc_formula *phi = cc_kernel_get_formula(k, face);
    if (!phi || phi->sort != CC_FACE)
        return ck_fail(k, "A transport's face is a face formula."), 0;
    cc_node comp = k->nodes[s.term];
    size_t clause = 0;
    for (cc_term cursor = comp.child[1]; cursor; cursor = k->nodes[cursor].child[1], ++clause) {
        const cc_formula *own = cc_kernel_get_formula(k, k->nodes[cursor].payload);
        if (clause >= phi->length || own->length != 1 || own->clauses[0].positive != phi->clauses[clause].positive ||
            own->clauses[0].negative != phi->clauses[clause].negative)
            return ck_fail(k, "A transport's tubes are its face's clauses, in order."), 0;
        if (!ck_instr_same(k, k->nodes[cursor].child[0], ck_restrict(k, comp.child[2], phi->clauses[clause]),
                  "A transport's tube is its base on the face."))
            return 0;
    }
    if (clause != phi->length)
        return ck_fail(k, "A transport's tubes are its face's clauses, in order."), 0;
    if (!formal_family(k, comp.child[0], "Transport is for families of declared higher sorts."))
        return 0;
    cc_entry_id dimension = ck_instr_dimension_entry(k, comp.payload);
    if (!dimension || !ck_instr_formula_context(k, phi, &dims) || !ck_instr_discharge(k, s.context, &dimension, 1, &context) ||
        !ck_instr_merge(k, context, dims, &context))
        return 0;
    cc_term tube = ck_instr_make(k, CC_TUBE, face, comp.child[2], 0, 0, 0);
    return ck_instr_typing(k, ck_instr_make(k, CC_TRANS, comp.payload, comp.child[0], tube, comp.child[2], 0), s.type, context);
}
