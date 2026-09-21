/* CHM §§3.2 and 3.3.5. General composition decomposes into transport followed
 * by canonical homogeneous composition. Transporting a pushout BRIDGE also
 * corrects its endpoints: transport(f(c)) need not equal f(transport(c)).
 * All correction terms below are built from checked cubical operations. */
#include "term_internal.h"

static cc_term app(cc_kernel *k, cc_term f, cc_term x) {
    return ck_make(k, CC_APP, 0, f, x, 0, 0);
}

static cc_formula_id bottom(cc_kernel *k) {
    cc_formula face;
    cc_init(&face, CC_FACE);
    cc_formula_id result = cc_kernel_formula(k, &face);
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
    cc_formula_id id = cc_kernel_formula(k, &result);
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
    cc_formula_id result = valid ? cc_kernel_formula(k, &reverse) : 0;
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
    cc_formula_id result = cc_kernel_formula(k, &face);
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

cc_term ck_pushout_composition(cc_kernel *k, unsigned dim, cc_term family,
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

cc_term ck_pushout_eliminate_hcomp(cc_kernel *k, cc_term eliminator, cc_term composition) {
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
    if (k->nodes[family].kind != CC_PUSHOUT)
        return ck_fail(k, "Transport computation currently requires a pushout family."), 0;
    cc_node P = k->nodes[family];
    cc_node z = k->nodes[value];
    unsigned dim = n.payload;
    cc_formula_id phi = k->nodes[n.child[1]].payload;
    cc_term target = ck_endpoint_term(k, family, dim, 1);
    if (z.kind == CC_PUSH_LEFT || z.kind == CC_PUSH_RIGHT) {
        cc_term carrier = P.child[z.kind == CC_PUSH_LEFT ? 1 : 2];
        cc_term point = transport(k, dim, carrier, phi, z.child[1], true);
        return ck_make(k, z.kind, 0, target, point, 0, 0);
    }
    if (z.kind == CC_HCOMP) {
        unsigned j = ck_fresh_dimension(k, ck_free_dims(k, term) |
            (UINT64_C(1) << dim) | (UINT64_C(1) << z.payload));
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
        return ck_make(k, CC_HCOMP, j, target, walls, base, 0);
    }
    if (z.kind != CC_PUSH_PATH)
        return term;
    unsigned h = ck_fresh_dimension(k, ck_free_dims(k, term) | (UINT64_C(1) << dim));
    if (h >= CC_DIMENSIONS)
        return 0;
    cc_formula_id reverse = reversed(k, h);
    cc_formula coordinate;
    cc_init(&coordinate, CC_INTERVAL);
    if (cc_generator(&coordinate, dim, true) != CC_OK) {
        cc_clear(&coordinate);
        return ck_fail(k, "Pushout bridge filling allocation failed."), 0;
    }
    cc_term fixed = ck_make(k, CC_TUBE, phi, z.child[1], 0, 0, 0);
    cc_term label_fill = ck_fill(k, dim, P.child[0], fixed, z.child[1], &coordinate);
    cc_clear(&coordinate);
    cc_term left_map = ck_make(k, CC_FST, 0, P.child[3], 0, 0, 0);
    cc_term right_map = ck_make(k, CC_SND, 0, P.child[3], 0, 0, 0);
    cc_term left = ck_make(k, CC_PUSH_LEFT, 0, family, app(k, left_map, label_fill), 0, 0);
    cc_term right = ck_make(k, CC_PUSH_RIGHT, 0, family, app(k, right_map, label_fill), 0, 0);
    cc_term left_correction = substitute(k, squeeze(k, dim, family, phi, left), dim, reverse);
    cc_term right_correction = substitute(k, squeeze(k, dim, family, phi, right), dim, reverse);
    cc_term label = transport(k, dim, P.child[0], phi, z.child[1], true);
    cc_term bridge = ck_make(k, CC_PUSH_PATH, z.payload, target, label, 0, 0);
    cc_term walls = 0;
    walls = ck_append_tube(k, walls, endpoint(k, z.payload, 0), left_correction);
    walls = ck_append_tube(k, walls, endpoint(k, z.payload, 1), right_correction);
    walls = ck_append_tube(k, walls, phi, value);
    return ck_make(k, CC_HCOMP, h, target, walls, bridge, 0);
}
