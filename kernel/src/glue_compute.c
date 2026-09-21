/* CCHM sections 6.2 and 7.1. Glue composition is built from ordinary
 * composition, filling and the SUPPLIED contractible-fiber equivalence.
 * There is no special ua rewrite, chosen inverse, or new theorem axiom. */
#include "term_internal.h"

typedef struct {
    cc_formula_id face;
    cc_term type, equivalence, fiber_point;
} glue_pick;

static cc_term app(cc_kernel *k, cc_term f, cc_term x) {
    return ck_make(k, CC_APP, 0, f, x, 0, 0);
}
static cc_term first(cc_kernel *k, cc_term pair) {
    return ck_make(k, CC_FST, 0, pair, 0, 0, 0);
}
static cc_term second(cc_kernel *k, cc_term pair) {
    return ck_make(k, CC_SND, 0, pair, 0, 0, 0);
}
static cc_term project(cc_kernel *k, cc_term glue_type, cc_term value) {
    return ck_make(k, CC_UNGLUE, 0, glue_type, value, 0, 0);
}
static cc_term end(cc_kernel *k, cc_term term, unsigned dim) {
    return ck_endpoint_term(k, term, dim, 1);
}

static cc_term append_type(cc_kernel *k, cc_term system, cc_formula_id face,
                            cc_term type, cc_term equivalence) {
    if (!system)
        return ck_make(k, CC_GLUE_SYSTEM, face, type, equivalence, 0, 0);
    cc_node piece = k->nodes[system];
    cc_term tail = append_type(k, piece.child[2], face, type, equivalence);
    return ck_make(k, CC_GLUE_SYSTEM, piece.payload, piece.child[0], piece.child[1], tail, 0);
}

static bool formula_at_one(cc_kernel *k, cc_formula *out, cc_formula_id id, unsigned dim) {
    const cc_formula *input = cc_kernel_get_formula(k, id);
    cc_formula one;
    cc_init(&one, CC_INTERVAL);
    bool valid = input && input->sort == CC_FACE && cc_one(&one) == CC_OK &&
                 cc_face_substitute(out, input, dim, &one) == CC_OK;
    cc_clear(&one);
    return valid || ck_fail(k, "Glue endpoint face allocation failed.");
}

static cc_term projected_tubes(cc_kernel *k, cc_term system, cc_term type) {
    if (!system)
        return 0;
    cc_node tube = k->nodes[system];
    cc_term value = project(k, type, tube.child[0]);
    cc_term tail = projected_tubes(k, tube.child[1], type);
    return ck_make(k, CC_TUBE, tube.payload, value, tail, 0, 0);
}

/* A function preserves composition up to a path (CCHM lemma 6).
 * j=0 gives composition of the images; j=1 gives the image of composition. */
static cc_term preservation(cc_kernel *k, unsigned dim, cc_term source, cc_term target,
                             cc_term equivalence, cc_term system, cc_term base,
                             uint64_t avoid) {
    unsigned j = ck_fresh_dimension(k, avoid);
    if (j >= CC_DIMENSIONS)
        return 0;
    cc_formula coordinate;
    cc_init(&coordinate, CC_INTERVAL);
    if (cc_generator(&coordinate, dim, true) != CC_OK)
        return ck_fail(k, "Preservation interval allocation failed."), 0;
    cc_term line = ck_fill(k, dim, source, system, base, &coordinate);
    cc_clear(&coordinate);
    cc_term image = app(k, first(k, equivalence), line);
    cc_term walls = 0;
    for (cc_term cursor = system; cursor;) {
        cc_node tube = k->nodes[cursor];
        walls = ck_append_tube(k, walls, tube.payload, image);
        cursor = tube.child[1];
    }
    walls = ck_append_tube(k, walls, ck_endpoint_face(k, j, 1), image);
    cc_term initial = app(k, first(k, ck_endpoint_term(k, equivalence, dim, 0)), base);
    cc_term body = ck_make(k, CC_COMP, dim, target, walls, initial, 0);
    return ck_make(k, CC_PLAM, j, end(k, target, dim), body, 0, 0);
}

static cc_term extend_fiber(cc_kernel *k, cc_term fiber, cc_term proof, cc_term partial,
                             uint64_t avoid) {
    unsigned j = ck_fresh_dimension(k, avoid | ck_free_dims(k, fiber) | ck_free_dims(k, partial));
    if (j >= CC_DIMENSIONS)
        return 0;
    cc_formula_id coordinate = ck_interval_variable(k, j);
    cc_term center = first(k, proof);
    cc_term contraction = second(k, proof);
    cc_term walls = 0;
    for (cc_term cursor = partial; cursor;) {
        cc_node piece = k->nodes[cursor];
        cc_term path = app(k, contraction, piece.child[0]);
        cc_term path_type = ck_make(k, CC_PATH, j, fiber, center, piece.child[0], 0);
        cc_term along = ck_make(k, CC_PAPP, coordinate, path, path_type, 0, 0);
        walls = ck_append_tube(k, walls, piece.payload, along);
        cursor = piece.child[1];
    }
    return ck_make(k, CC_COMP, j, fiber, walls, center, 0);
}

static cc_term partial_fiber_points(cc_kernel *k, unsigned dim, cc_term glue,
                                     cc_term target_piece_type, cc_term target_equivalence,
                                     cc_clause extent, cc_term target, cc_term a1,
                                     cc_term system, cc_term base, uint64_t avoid) {
    cc_node G = k->nodes[glue];
    cc_term fiber = ck_fiber_type(k, target_piece_type, target, first(k, target_equivalence), a1);
    cc_term partial = 0;
    /* delta = forall i. phi. In DNF retain precisely the clauses not using i. */
    for (cc_term cursor = G.child[1]; cursor && !k->error[0];) {
        cc_node piece = k->nodes[cursor];
        cursor = piece.child[2];
        cc_formula delta;
        cc_init(&delta, CC_FACE);
        const cc_formula *phi = cc_kernel_get_formula(k, piece.payload);
        if (cc_face_forall(&delta, dim, phi) != CC_OK) {
            cc_clear(&delta);
            return ck_fail(k, "Glue universal face allocation failed."), 0;
        }
        for (size_t i = 0; i < delta.length && !k->error[0]; ++i) {
            cc_clause overlap = {extent.positive | delta.clauses[i].positive,
                                 extent.negative | delta.clauses[i].negative};
            if (overlap.positive & overlap.negative)
                continue;
            cc_term t1 = ck_make(k, CC_COMP, dim, piece.child[0], system, base, 0);
            cc_term omega = preservation(k, dim, piece.child[0], G.child[0], piece.child[1], system, base, avoid);
            cc_term point = ck_make(k, CC_PAIR, 0, fiber, t1, omega, 0);
            point = ck_restrict(k, point, overlap);
            partial = ck_append_tube(k, partial, ck_clause_formula(k, overlap), point);
        }
        cc_clear(&delta);
    }
    for (cc_term cursor = system; cursor && !k->error[0];) {
        cc_node piece = k->nodes[cursor];
        cursor = piece.child[1];
        cc_formula phi;
        cc_init(&phi, CC_FACE);
        const cc_formula *raw = cc_kernel_get_formula(k, piece.payload);
        if (cc_copy(&phi, raw) != CC_OK) {
            cc_clear(&phi);
            return ck_fail(k, "Glue boundary face allocation failed."), 0;
        }
        for (size_t i = 0; i < phi.length && !k->error[0]; ++i) {
            cc_clause overlap = {extent.positive | phi.clauses[i].positive,
                                 extent.negative | phi.clauses[i].negative};
            if (overlap.positive & overlap.negative)
                continue;
            unsigned j = ck_fresh_dimension(k, avoid);
            cc_term constant = ck_make(k, CC_PLAM, j, target, a1, 0, 0);
            cc_term point = ck_make(k, CC_PAIR, 0, fiber, end(k, piece.child[0], dim), constant, 0);
            point = ck_restrict(k, point, overlap);
            partial = ck_append_tube(k, partial, ck_clause_formula(k, overlap), point);
        }
        cc_clear(&phi);
    }
    cc_term witness = app(k, second(k, target_equivalence), a1);
    return extend_fiber(k, fiber, witness, partial, avoid);
}

cc_term ck_glue_composition(cc_kernel *k, unsigned dim, cc_term glue,
                             cc_term system, cc_term base) {
    cc_node G = k->nodes[glue];
    uint64_t avoid = ck_free_dims(k, glue) | ck_free_dims(k, system) |
                     ck_free_dims(k, base) | (UINT64_C(1) << dim);
    cc_term projected = projected_tubes(k, system, glue);
    cc_term a0 = project(k, ck_endpoint_term(k, glue, dim, 0), base);
    cc_term a1prime = ck_make(k, CC_COMP, dim, G.child[0], projected, a0, 0);
    cc_term A1 = end(k, G.child[0], dim);
    glue_pick *picks = NULL;
    size_t count = 0, capacity = 0;
    for (cc_term cursor = G.child[1]; cursor && !k->error[0];) {
        cc_node piece = k->nodes[cursor];
        cursor = piece.child[2];
        cc_formula face;
        cc_init(&face, CC_FACE);
        if (!formula_at_one(k, &face, piece.payload, dim)) {
            cc_clear(&face);
            break;
        }
        for (size_t i = 0; i < face.length && !k->error[0]; ++i) {
            if (count == capacity) {
                size_t grown_capacity = capacity ? 2 * capacity : 8;
                if (grown_capacity < capacity || grown_capacity > SIZE_MAX / sizeof *picks) {
                    ck_fail(k, "Glue composition allocation overflow.");
                    break;
                }
                glue_pick *grown = realloc(picks, grown_capacity * sizeof *picks);
                if (!grown) {
                    ck_fail(k, "Glue composition allocation failed.");
                    break;
                }
                picks = grown;
                capacity = grown_capacity;
            }
            cc_clause clause = face.clauses[i];
            cc_term type = ck_restrict(k, end(k, piece.child[0], dim), clause);
            cc_term equivalence = ck_restrict(k, end(k, piece.child[1], dim), clause);
            cc_term point = partial_fiber_points(k, dim, glue, type, equivalence, clause,
                                                 A1, a1prime, system, base, avoid);
            picks[count++] = (glue_pick){ck_clause_formula(k, clause), type, equivalence, point};
        }
        cc_clear(&face);
    }
    unsigned j = ck_fresh_dimension(k, avoid);
    cc_formula_id coordinate = ck_interval_variable(k, j);
    cc_term adjusted = 0, partial = 0;
    for (size_t i = 0; i < count && !k->error[0]; ++i) {
        glue_pick pick = picks[i];
        cc_term value = first(k, pick.fiber_point);
        cc_term alpha = second(k, pick.fiber_point);
        cc_term image = app(k, first(k, pick.equivalence), value);
        cc_term path_type = ck_make(k, CC_PATH, j, A1, a1prime, image, 0);
        cc_term along = ck_make(k, CC_PAPP, coordinate, alpha, path_type, 0, 0);
        adjusted = ck_append_tube(k, adjusted, pick.face, along);
        partial = ck_append_tube(k, partial, pick.face, value);
    }
    free(picks);
    for (cc_term cursor = projected; cursor && !k->error[0];) {
        cc_node piece = k->nodes[cursor];
        adjusted = ck_append_tube(k, adjusted, piece.payload, end(k, piece.child[0], dim));
        cursor = piece.child[1];
    }
    cc_term a1 = ck_make(k, CC_COMP, j, A1, adjusted, a1prime, 0);
    return ck_make(k, CC_GLUE_TERM, 0, end(k, glue, dim), a1, partial, 0);
}

/* Transport id_A in Equiv(A,E(i)) constructs the reverse-line equivalence
 * used for composition in U. This is CCHM section 7.1's alternative derivation. */
cc_term ck_universe_composition(cc_kernel *k, unsigned dim, cc_term system, cc_term base) {
    cc_formula variable, reverse;
    cc_init(&variable, CC_INTERVAL);
    cc_init(&reverse, CC_INTERVAL);
    if (cc_generator(&variable, dim, true) != CC_OK || cc_reverse(&reverse, &variable) != CC_OK) {
        cc_clear(&variable);
        cc_clear(&reverse);
        return ck_fail(k, "Universe composition interval allocation failed."), 0;
    }
    cc_term gluing = 0;
    for (cc_term cursor = system; cursor && !k->error[0];) {
        cc_node piece = k->nodes[cursor];
        cursor = piece.child[1];
        cc_term endpoint = end(k, piece.child[0], dim);
        cc_term backwards = ck_dimension_substitute(k, piece.child[0], dim, &reverse);
        cc_term equivalences = ck_equiv_type(k, endpoint, backwards);
        cc_term identity = ck_identity_equiv(k, endpoint);
        cc_term proof = ck_make(k, CC_COMP, dim, equivalences, 0, identity, 0);
        gluing = append_type(k, gluing, piece.payload, endpoint, proof);
    }
    cc_clear(&variable);
    cc_clear(&reverse);
    return ck_make(k, CC_GLUE, 0, base, gluing, 0, 0);
}
