/* Composition and transport of declared higher sorts (H1 family F4,
 * specification 3.4 and 3.5), after CHM §§3.2 and 3.3.5. General composition
 * decomposes into transport followed by formal homogeneous composition.
 * Transporting a constructor at dimensions also corrects its boundary: the
 * transport of a boundary piece need not be the piece at the transported
 * arguments. All correction terms are built from checked cubical operations. */
#include "term_internal.h"
#include <string.h>

static cc_term app(cc_kernel *k, cc_term f, cc_term x) {
    return ck_make(k, CC_APP, 0, f, x, 0, 0);
}

static cc_formula_id bottom(cc_kernel *k) {
    cc_formula face;
    cc_init(&face, CC_FACE);
    cc_formula_id result = ck_formula(k, &face);
    cc_clear(&face);
    return result;
}

static cc_formula_id join(cc_kernel *k, cc_formula_id a, cc_formula_id b, cc_sort sort) {
    cc_formula result;
    cc_init(&result, sort);
    const cc_formula *left = cc_kernel_get_formula(k, a);
    const cc_formula *right = cc_kernel_get_formula(k, b);
    if (!left || !right || cc_join(&result, left, right) != CC_OK) {
        cc_clear(&result);
        return ck_fail(k, "HIT join allocation failed."), 0;
    }
    cc_formula_id id = ck_formula(k, &result);
    cc_clear(&result);
    return id;
}

static cc_formula_id reversed(cc_kernel *k, unsigned dim) {
    cc_formula coordinate;
    cc_formula reverse;
    cc_init(&coordinate, CC_INTERVAL);
    cc_init(&reverse, CC_INTERVAL);
    bool valid = cc_generator(&coordinate, dim, true) == CC_OK &&
                 cc_reverse(&reverse, &coordinate) == CC_OK;
    cc_formula_id result = valid ? ck_formula(k, &reverse) : 0;
    cc_clear(&coordinate);
    cc_clear(&reverse);
    if (!valid)
        ck_fail(k, "HIT reversal allocation failed.");
    return result;
}

static cc_formula_id endpoint(cc_kernel *k, cc_formula_id interval, unsigned end) {
    cc_formula face;
    cc_init(&face, CC_FACE);
    const cc_formula *r = cc_kernel_get_formula(k, interval);
    if (!r || cc_endpoint(&face, r, end) != CC_OK) {
        cc_clear(&face);
        return ck_fail(k, "HIT endpoint allocation failed."), 0;
    }
    cc_formula_id result = ck_formula(k, &face);
    cc_clear(&face);
    return result;
}

static cc_term substitute(cc_kernel *k, cc_term term, unsigned dim, cc_formula_id argument) {
    cc_formula copy;
    cc_init(&copy, CC_INTERVAL);
    const cc_formula *r = cc_kernel_get_formula(k, argument);
    if (!r || cc_copy(&copy, r) != CC_OK) {
        cc_clear(&copy);
        return ck_fail(k, "HIT substitution interval allocation failed."), 0;
    }
    cc_term result = ck_dimension_substitute(k, term, dim, &copy);
    cc_clear(&copy);
    return result;
}

static cc_term transport(cc_kernel *k, unsigned dim, cc_term family,
                           cc_formula_id face, cc_term base, bool ordinary) {
    cc_term wall = ck_make(k, CC_TUBE, face, base, 0, 0, 0);
    return ck_make(k, ordinary ? CC_COMP : CC_TRANS, dim, family, wall, base, 0);
}

/* squeeze_i P phi u joins transport(P,u(0)) to u(1), fixed on phi. */
static cc_term squeeze(cc_kernel *k, unsigned dim, cc_term family,
                        cc_formula_id face, cc_term value) {
    uint64_t avoid = ck_free_dims(k, family) | ck_free_dims(k, value) | (UINT64_C(1) << dim);
    const cc_formula *phi = cc_kernel_get_formula(k, face);
    if (!phi)
        return ck_fail(k, "Missing HIT transport face."), 0;
    for (size_t i = 0; i < phi->length; ++i)
        avoid |= phi->clauses[i].positive | phi->clauses[i].negative;
    unsigned fresh = ck_fresh_dimension(k, avoid);
    if (fresh >= CC_DIMENSIONS)
        return 0;
    cc_formula_id i = ck_interval_variable(k, dim);
    cc_formula_id j = ck_interval_variable(k, fresh);
    cc_formula_id along = join(k, i, j, CC_INTERVAL);
    cc_formula_id last = ck_endpoint_face(k, dim, 1);
    cc_formula_id fixed = join(k, face, last, CC_FACE);
    return transport(k, fresh, substitute(k, family, dim, along), fixed, value, false);
}

static cc_term rename_tubes(cc_kernel *k, cc_term system, unsigned dim, cc_formula_id along) {
    if (!system)
        return 0;
    cc_node tube = k->nodes[system];
    cc_term value = substitute(k, tube.child[0], dim, along);
    cc_term tail = rename_tubes(k, tube.child[1], dim, along);
    return ck_make(k, CC_TUBE, tube.payload, value, tail, 0, 0);
}

cc_term ck_higher_composition(cc_kernel *k, unsigned dim, cc_term family,
                              cc_term system, cc_term base) {
    cc_formula_id empty = bottom(k);
    cc_term moved = transport(k, dim, family, empty, base, false);
    cc_term walls = 0;
    for (cc_term cursor = system; cursor;) {
        cc_node tube = k->nodes[cursor];
        cc_term value = squeeze(k, dim, family, empty, tube.child[0]);
        walls = ck_append_tube(k, walls, tube.payload, value);
        cursor = tube.child[1];
    }
    cc_term target = ck_endpoint_term(k, family, dim, 1);
    return ck_make(k, CC_HCOMP, dim, target, walls, moved, 0);
}

cc_term ck_eliminate_hcomp(cc_kernel *k, cc_term eliminator, cc_term composition) {
    cc_node e = k->nodes[eliminator];
    cc_node box = k->nodes[composition];
    uint64_t avoid = ck_free_dims(k, eliminator) | ck_free_dims(k, composition) |
                     (UINT64_C(1) << box.payload);
    unsigned dim = ck_fresh_dimension(k, avoid);
    if (dim >= CC_DIMENSIONS)
        return 0;
    cc_formula_id i = ck_interval_variable(k, dim);
    cc_term system = rename_tubes(k, box.child[1], box.payload, i);
    cc_formula coordinate;
    cc_init(&coordinate, CC_INTERVAL);
    if (cc_generator(&coordinate, dim, true) != CC_OK) {
        cc_clear(&coordinate);
        return ck_fail(k, "HIT elimination filling allocation failed."), 0;
    }
    cc_term fill = ck_fill(k, dim, box.child[0], system, box.child[2], &coordinate);
    cc_clear(&coordinate);
    if (!fill)
        return 0;
    cc_node filled = k->nodes[fill];
    cc_term hfill = ck_make(k, CC_HCOMP, filled.payload, filled.child[0], filled.child[1], filled.child[2], 0);
    cc_term walls = 0;
    for (cc_term cursor = system; cursor;) {
        cc_node tube = k->nodes[cursor];
        walls = ck_append_tube(k, walls, tube.payload, app(k, eliminator, tube.child[0]));
        cursor = tube.child[1];
    }
    cc_term family = app(k, e.child[0], hfill);
    return ck_make(k, CC_COMP, dim, family, walls, app(k, eliminator, box.child[2]), 0);
}

/* Transport commutes with formal composition (3.5, case 3):
 * transp^i A(i) φ (hcomp^j A(0) [ψ ↦ w] w_0) is
 * hcomp^j A(1) [ψ ↦ transp^i A(i) φ w(j)] (transp^i A(i) φ w_0). */
static cc_term transport_hcomp(cc_kernel *k, cc_term term, cc_term family, cc_term value) {
    cc_node n = k->nodes[term], z = k->nodes[value];
    unsigned dim = n.payload;
    cc_formula_id phi = k->nodes[n.child[1]].payload;
    unsigned j = ck_fresh_dimension(k, ck_free_dims(k, term) | (UINT64_C(1) << dim) | (UINT64_C(1) << z.payload));
    if (j >= CC_DIMENSIONS)
        return 0;
    cc_formula_id coordinate = ck_interval_variable(k, j);
    cc_term walls = 0;
    for (cc_term cursor = z.child[1]; cursor;) {
        cc_node tube = k->nodes[cursor];
        cc_term point = substitute(k, tube.child[0], z.payload, coordinate);
        walls = ck_append_tube(k, walls, tube.payload, transport(k, dim, family, phi, point, false));
        cursor = tube.child[1];
    }
    cc_term base = transport(k, dim, family, phi, z.child[2], false);
    return ck_make(k, CC_HCOMP, j, ck_endpoint_term(k, family, dim, 1), walls, base, 0);
}

/* ---- Declared higher sorts (H1 family F4, specification 3.4 and 3.5) ---- */

static cc_formula_id constant(cc_kernel *k, unsigned end) {
    cc_formula point;
    cc_init(&point, CC_INTERVAL);
    cc_formula_id result = (!end || cc_one(&point) == CC_OK) ? ck_formula(k, &point) : 0;
    cc_clear(&point);
    return result ? result : (ck_fail(k, "Interval constant allocation failed."), 0);
}

/* The components Fst(Snd^m(t)) of a tuple in a constructor's telescope. */
static void components(cc_kernel *k, cc_term tuple, uint32_t count, cc_term *out) {
    for (uint32_t m = 0; m < count; ++m) {
        out[m] = ck_make(k, CC_FST, 0, tuple, 0, 0, 0);
        tuple = ck_make(k, CC_SND, 0, tuple, 0, 0, 0);
    }
}

/* A constructor type's result, its arguments substituted. */
static cc_term result_type(cc_kernel *k, cc_term type, const cc_term *arguments, uint32_t count) {
    for (uint32_t m = 0; m < count && type; ++m) {
        cc_node pi = k->nodes[type];
        if (pi.kind != CC_PI)
            return ck_fail(k, "A constructor's type has fewer arguments than its application."), 0;
        type = ck_substitute(k, pi.child[1], pi.payload, arguments[m]);
    }
    return type;
}

/* t @ r_1 … @ r_d, each application annotated with the type of the path it
 * applies (3.2): the path step and Whnf read boundaries there. */
cc_term ck_apply_at(cc_kernel *k, cc_term t, cc_term type, const cc_formula_id *formulas, uint32_t count) {
    for (uint32_t l = 0; l < count && t && type; ++l) {
        cc_node path = k->nodes[type];
        if (path.kind != CC_PATH)
            return ck_fail(k, "A constructor's dimensions are its result type's path layers."), 0;
        cc_term next = substitute(k, path.child[0], path.payload, formulas[l]);
        t = ck_make(k, CC_PAPP, formulas[l], t, type, 0, 0);
        type = next;
    }
    return t;
}

/* transp^i S(as(i)) φ u_0 by the weak head of u_0 (3.5). A point constructor
 * transports its argument telescope; a constructor at dimensions is also
 * corrected on each face of its dimensions by a squeeze of its boundary
 * piece, so that transport commutes with restriction to that face. */
static cc_term sort_transport(cc_kernel *k, cc_term term, cc_term family, cc_term value) {
    cc_node n = k->nodes[term];
    unsigned dim = n.payload;
    cc_formula_id phi = k->nodes[n.child[1]].payload;
    const cc_signature *s = ck_instance_signature(k, family);
    if (!s)
        return 0;
    if (!ck_signature_higher(s)) {
        /* A data sort transports as a composition with the tube φ ↦ u_0 (3.3). */
        cc_term tube = ck_make(k, CC_TUBE, phi, n.child[2], 0, 0, 0);
        return ck_whnf(k, ck_make(k, CC_COMP, dim, family, tube, n.child[2], 0));
    }
    if (k->nodes[value].kind == CC_HCOMP)
        return transport_hcomp(k, term, family, value);
    /* (c_k(θ_0)) @ r_1 … @ r_d: collect the formulas, innermost first. */
    cc_formula_id formulas[CC_CONSTRUCTOR_DIMENSIONS];
    uint32_t depth = 0;
    cc_term head = value;
    while (k->nodes[head].kind == CC_PAPP) {
        if (depth == CC_CONSTRUCTOR_DIMENSIONS)
            return term;
        formulas[depth++] = k->nodes[head].payload;
        head = k->nodes[head].child[0];
    }
    for (uint32_t l = 0; l < depth / 2; ++l) {
        cc_formula_id swap = formulas[l];
        formulas[l] = formulas[depth - 1 - l];
        formulas[depth - 1 - l] = swap;
    }
    uint32_t constructor = 0, count = 0;
    cc_term arguments[CC_CONSTRUCTOR_ARGUMENTS];
    if (!ck_constructor_application(k, head, &constructor, arguments, &count) || constructor >= s->constructor_count)
        return term;
    const cc_constructor *c = &s->constructors[constructor];
    if (count != c->data + c->positions || depth != c->dimensions)
        return term;
    cc_term target = ck_endpoint_term(k, family, dim, 1);
    cc_term type = ck_constructor_type(k, family, constructor);
    cc_term telescope = type ? ck_telescope(k, type, count) : 0;
    if (!telescope)
        return 0;
    cc_term start = ck_tuple(k, ck_endpoint_term(k, telescope, dim, 0), arguments, count);
    cc_term fixed = ck_make(k, CC_TUBE, phi, start, 0, 0, 0);
    cc_term moved = ck_make(k, CC_COMP, dim, telescope, fixed, start, 0);
    cc_term point = ck_apply_components(k, target, constructor, moved, count);
    if (!depth)
        return point;
    /* θ(i), the telescope's transport filler, and v := c_k(as(1))(θ(1)) @ rs. */
    cc_formula along;
    cc_init(&along, CC_INTERVAL);
    if (cc_generator(&along, dim, true) != CC_OK) {
        cc_clear(&along);
        return ck_fail(k, "Transport filling allocation failed."), 0;
    }
    cc_term line = ck_fill(k, dim, telescope, fixed, start, &along);
    cc_clear(&along);
    cc_term moved_arguments[CC_CONSTRUCTOR_ARGUMENTS], line_arguments[CC_CONSTRUCTOR_ARGUMENTS];
    components(k, moved, count, moved_arguments);
    components(k, line, count, line_arguments);
    cc_term target_type = ck_constructor_type(k, target, constructor);
    cc_term v = ck_apply_at(k, point, result_type(k, target_type, moved_arguments, count), formulas, depth);
    cc_term along_point = ck_apply_components(k, family, constructor, line, count);
    cc_term along_type = result_type(k, type, line_arguments, count);
    unsigned h = ck_fresh_dimension(k, ck_free_dims(k, term) | (UINT64_C(1) << dim));
    if (h >= CC_DIMENSIONS || !line || !v)
        return 0;
    cc_formula_id reverse = reversed(k, h);
    cc_term walls = 0;
    for (uint32_t l = 0; l < depth; ++l)
        for (unsigned e = 0; e < 2; ++e) {
            /* b_{l,ε}(i): the boundary piece on r_l = ε, at as(i) and θ(i). */
            cc_formula_id pieces[CC_CONSTRUCTOR_DIMENSIONS];
            memcpy(pieces, formulas, depth * sizeof *pieces);
            pieces[l] = constant(k, e);
            cc_term piece = ck_apply_at(k, along_point, along_type, pieces, depth);
            cc_term correction = piece ? substitute(k, squeeze(k, dim, family, phi, piece), dim, reverse) : 0;
            cc_formula_id face = endpoint(k, formulas[l], e);
            if (!correction || !face)
                return 0;
            walls = ck_append_tube(k, walls, face, correction);
        }
    walls = ck_append_tube(k, walls, phi, value);
    return ck_make(k, CC_HCOMP, h, target, walls, v, 0);
}

cc_term ck_hit_reduce(cc_kernel *k, cc_term term) {
    cc_node n = k->nodes[term];
    cc_term exposed = ck_expose(k, term);
    if (exposed != term)
        return exposed ? ck_whnf(k, exposed) : 0;
    if (n.kind == CC_HCOMP) {
        cc_term system = 0;
        for (cc_term cursor = n.child[1]; cursor;) {
            cc_node tube = k->nodes[cursor];
            const cc_formula *face = cc_kernel_get_formula(k, tube.payload);
            if (!face || face->sort != CC_FACE)
                return ck_fail(k, "Unchecked homogeneous composition face."), 0;
            if (face->length)
                system = ck_append_tube(k, system, tube.payload, tube.child[0]);
            cursor = tube.child[1];
        }
        return system == n.child[1] ? term : ck_make(k, CC_HCOMP, n.payload, n.child[0], system, n.child[2], 0);
    }
    cc_term family = ck_whnf(k, n.child[0]);
    cc_term value = ck_whnf(k, n.child[2]);
    if (!family || !value)
        return 0;
    if (k->nodes[family].kind == CC_SORT)
        return sort_transport(k, term, family, value);
    return ck_fail(k, "Transport computation requires a declared higher sort."), 0;
}
