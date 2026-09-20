/* Computational composition rules for Nat, Unit, Pi, Sigma and Path.
 * Filling is DERIVED from composition with an extra r=0 wall (CCHM §4.4).
 * No rule treats a neutral tube as a constructor merely because its lid is one. */
#include "term_internal.h"

static cc_term app(cc_kernel *k, cc_term f, cc_term x) {
    return ck_make(k, CC_APP, 0, f, x, 0, 0);
}

cc_term ck_append_tube(cc_kernel *k, cc_term system, cc_formula_id face, cc_term value) {
    if (!system)
        return ck_make(k, CC_TUBE, face, value, 0, 0, 0);
    cc_node tube = k->nodes[system];
    cc_term tail = ck_append_tube(k, tube.child[1], face, value);
    return ck_make(k, CC_TUBE, tube.payload, tube.child[0], tail, 0, 0);
}

static cc_term remove_empty_tubes(cc_kernel *k, cc_term system) {
    if (!system)
        return 0;
    cc_node tube = k->nodes[system];
    const cc_formula *face = cc_kernel_get_formula(k, tube.payload);
    if (!face || face->sort != CC_FACE)
        return ck_fail(k, "Unchecked composition face reached reduction."), 0;
    bool empty = face->length == 0;
    cc_term tail = remove_empty_tubes(k, tube.child[1]);
    if (empty)
        return tail;
    return tail == tube.child[1] ? system : ck_make(k, CC_TUBE, tube.payload, tube.child[0], tail, 0, 0);
}

static cc_term map_tubes(cc_kernel *k, cc_term system, cc_term_kind operation,
                         cc_term argument, cc_term annotation) {
    if (!system)
        return 0;
    cc_node tube = k->nodes[system];
    const cc_formula *face = cc_kernel_get_formula(k, tube.payload);
    if (face && !face->length)
        return map_tubes(k, tube.child[1], operation, argument, annotation);
    cc_term value;
    if (operation == CC_APP)
        value = app(k, tube.child[0], argument);
    else if (operation == CC_PAPP)
        value = ck_make(k, CC_PAPP, argument, tube.child[0], annotation, 0, 0);
    else if (operation == CC_SUCC) {
        cc_term head = ck_whnf(k, tube.child[0]);
        value = head ? k->nodes[head].child[0] : 0;
    } else
        value = ck_make(k, operation, 0, tube.child[0], 0, 0, 0);
    cc_term tail = map_tubes(k, tube.child[1], operation, argument, annotation);
    return ck_make(k, CC_TUBE, tube.payload, value, tail, 0, 0);
}

static cc_term substitute_tubes(cc_kernel *k, cc_term system, unsigned dim,
                                const cc_formula *along) {
    if (!system)
        return 0;
    cc_node tube = k->nodes[system];
    cc_term value = ck_dimension_substitute(k, tube.child[0], dim, along);
    cc_term tail = substitute_tubes(k, tube.child[1], dim, along);
    return ck_make(k, CC_TUBE, tube.payload, value, tail, 0, 0);
}

cc_term ck_fill(cc_kernel *k, unsigned dim, cc_term family, cc_term system,
                    cc_term base, const cc_formula *r) {
    uint64_t avoid = ck_free_dims(k, family) | ck_free_dims(k, system) |
                     ck_free_dims(k, base) | (UINT64_C(1) << dim);
    for (size_t i = 0; i < r->length; ++i)
        avoid |= r->clauses[i].positive | r->clauses[i].negative;
    unsigned direction = ck_fresh_dimension(k, avoid);
    if (direction >= CC_DIMENSIONS)
        return 0;
    cc_formula variable, along, wall;
    cc_init(&variable, CC_INTERVAL);
    cc_init(&along, CC_INTERVAL);
    cc_init(&wall, CC_FACE);
    bool valid = cc_generator(&variable, direction, true) == CC_OK &&
                 cc_meet(&along, r, &variable) == CC_OK &&
                 cc_endpoint(&wall, r, 0) == CC_OK;
    cc_term result = 0;
    if (valid) {
        cc_term moved_family = ck_dimension_substitute(k, family, dim, &along);
        cc_term moved_system = substitute_tubes(k, system, dim, &along);
        cc_formula_id face = cc_kernel_formula(k, &wall);
        moved_system = ck_append_tube(k, moved_system, face, base);
        result = ck_make(k, CC_COMP, direction, moved_family, moved_system, base, 0);
    } else
        ck_fail(k, "Composition filling formula allocation failed.");
    cc_clear(&variable);
    cc_clear(&along);
    cc_clear(&wall);
    return result;
}

static bool all_constructor(cc_kernel *k, cc_term system, cc_term_kind kind) {
    for (cc_term cursor = system; cursor;) {
        cc_node tube = k->nodes[cursor];
        const cc_formula *face = cc_kernel_get_formula(k, tube.payload);
        cursor = tube.child[1];
        if (!face->length)
            continue;
        cc_term head = ck_whnf(k, tube.child[0]);
        if (!head || k->nodes[head].kind != kind)
            return false;
    }
    return true;
}

cc_term ck_reduce_composition(cc_kernel *k, cc_term term) {
    cc_node n = k->nodes[term];
    unsigned dim = n.payload;
    cc_term system = remove_empty_tubes(k, n.child[1]);
    cc_term base = n.child[2];
    if (k->error[0])
        return 0;
    for (cc_term cursor = system; cursor;) {
        cc_node tube = k->nodes[cursor];
        const cc_formula *face = cc_kernel_get_formula(k, tube.payload);
        if (!face || face->sort != CC_FACE)
            return ck_fail(k, "Unchecked composition face reached reduction."), 0;
        if (face->length == 1 && !face->clauses[0].positive && !face->clauses[0].negative)
            return ck_whnf(k, ck_endpoint_term(k, tube.child[0], dim, 1));
        cursor = tube.child[1];
    }
    cc_term family = ck_whnf(k, n.child[0]);
    if (!family)
        return 0;
    cc_node type = k->nodes[family];
    if (type.kind == CC_NAT || type.kind == CC_UNIT) {
        cc_term head = ck_whnf(k, base);
        if (!head)
            return 0;
        cc_node constructor = k->nodes[head];
        bool nat = type.kind == CC_NAT && (constructor.kind == CC_ZERO || constructor.kind == CC_SUCC);
        bool unit = type.kind == CC_UNIT && constructor.kind == CC_POINT;
        if ((nat || unit) && all_constructor(k, system, constructor.kind)) {
            if (constructor.kind != CC_SUCC)
                return head;
            cc_term predecessors = map_tubes(k, system, CC_SUCC, 0, 0);
            cc_term recursive = ck_make(k, CC_COMP, dim, family, predecessors, constructor.child[0], 0);
            return ck_make(k, CC_SUCC, 0, recursive, 0, 0, 0);
        }
    }
    if (type.kind == CC_SUM || type.kind == CC_W) {
        cc_term normalized = family == n.child[0] && system == n.child[1] ? term :
            ck_make(k, CC_COMP, dim, family, system, base, 0);
        return ck_inductive_composition(k, normalized, family, system);
    }
    if (type.kind == CC_GLUE)
        return ck_whnf(k, ck_glue_composition(k, dim, family, system, base));
    if (type.kind == CC_U)
        return ck_whnf(k, ck_universe_composition(k, dim, system, base));
    if (type.kind == CC_SIGMA) {
        cc_term first_system = map_tubes(k, system, CC_FST, 0, 0);
        cc_term first_base = ck_make(k, CC_FST, 0, base, 0, 0, 0);
        cc_formula r;
        cc_init(&r, CC_INTERVAL);
        if (cc_generator(&r, dim, true) != CC_OK)
            return ck_fail(k, "Filling direction allocation failed."), 0;
        cc_term first_line = ck_fill(k, dim, type.child[0], first_system, first_base, &r);
        cc_clear(&r);
        cc_term first = ck_make(k, CC_COMP, dim, type.child[0], first_system, first_base, 0);
        cc_term second_family = ck_substitute(k, type.child[1], type.payload, first_line);
        cc_term second_system = map_tubes(k, system, CC_SND, 0, 0);
        cc_term second_base = ck_make(k, CC_SND, 0, base, 0, 0, 0);
        cc_term second = ck_make(k, CC_COMP, dim, second_family, second_system, second_base, 0);
        cc_term target = ck_endpoint_term(k, family, dim, 1);
        return ck_make(k, CC_PAIR, 0, target, first, second, 0);
    }
    if (type.kind == CC_PI) {
        uint32_t name = ck_fresh_symbol(k);
        cc_term argument = ck_var(k, name);
        cc_formula variable, backwards;
        cc_init(&variable, CC_INTERVAL);
        cc_init(&backwards, CC_INTERVAL);
        if (cc_generator(&variable, dim, true) != CC_OK || cc_reverse(&backwards, &variable) != CC_OK) {
            cc_clear(&variable);
            cc_clear(&backwards);
            return ck_fail(k, "Backward filling direction allocation failed."), 0;
        }
        cc_term backwards_domain = ck_dimension_substitute(k, type.child[0], dim, &backwards);
        cc_term line = ck_fill(k, dim, backwards_domain, 0, argument, &backwards);
        cc_clear(&variable);
        cc_clear(&backwards);
        cc_term body_family = ck_substitute(k, type.child[1], type.payload, line);
        cc_term body_system = map_tubes(k, system, CC_APP, line, 0);
        cc_term body_base = app(k, base, ck_endpoint_term(k, line, dim, 0));
        cc_term body = ck_make(k, CC_COMP, dim, body_family, body_system, body_base, 0);
        cc_term domain = ck_endpoint_term(k, type.child[0], dim, 1);
        return ck_make(k, CC_LAM, name, domain, body, 0, 0);
    }
    if (type.kind == CC_PATH) {
        uint64_t avoid = ck_free_dims(k, term) | (UINT64_C(1) << dim) |
                         (UINT64_C(1) << type.payload);
        unsigned direction = ck_fresh_dimension(k, avoid);
        if (direction >= CC_DIMENSIONS)
            return 0;
        cc_formula variable;
        cc_init(&variable, CC_INTERVAL);
        if (cc_generator(&variable, direction, true) != CC_OK)
            return ck_fail(k, "Path composition direction allocation failed."), 0;
        cc_formula_id arg = cc_kernel_formula(k, &variable);
        cc_term body_family = ck_dimension_substitute(k, type.child[0], type.payload, &variable);
        cc_clear(&variable);
        cc_term body_system = map_tubes(k, system, CC_PAPP, arg, family);
        cc_formula_id left_face = ck_endpoint_face(k, direction, 0);
        body_system = ck_append_tube(k, body_system, left_face, type.child[1]);
        cc_formula_id right_face = ck_endpoint_face(k, direction, 1);
        body_system = ck_append_tube(k, body_system, right_face, type.child[2]);
        cc_term start_type = ck_endpoint_term(k, family, dim, 0);
        cc_term body_base = ck_make(k, CC_PAPP, arg, base, start_type, 0, 0);
        cc_term body = ck_make(k, CC_COMP, dim, body_family, body_system, body_base, 0);
        cc_term end_family = ck_endpoint_term(k, body_family, dim, 1);
        return ck_make(k, CC_PLAM, direction, end_family, body, 0, 0);
    }
    /* A neutral family has a neutral composition. */
    return family == n.child[0] && system == n.child[1] ? term : ck_make(k, CC_COMP, dim, family, system, base, 0);
}
