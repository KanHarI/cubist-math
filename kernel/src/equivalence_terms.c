/* Derived equivalence types, with no new inference rule or axiom.
 * Fiber(f,y) = Sigma x:A. Path B y (f x), using CCHM's orientation.
 * IsContr(F) = Sigma center:F. Pi point:F. Path F center point.
 * Equiv(A,B) = Sigma f:(A -> B). Pi y:B. IsContr(Fiber(f,y)).
 * Each operand must be locally closed: it is put under the type's own binders,
 * which would capture a loose index. Where a part built here goes under
 * another, its variable is a CC_OPENED placeholder from an opener started
 * above the operands, closed before the binder is built (section 3.1 of
 * docs/roadmaps/kernel/locally-nameless-kernel.md): the same operands give
 * the same handle. */
#include "term_internal.h"

static cc_term path(cc_kernel *k, cc_term type, cc_term left, cc_term right) {
    unsigned dim = ck_fresh_dimension(k, ck_free_dims(k, type) |
                                         ck_free_dims(k, left) | ck_free_dims(k, right));
    if (dim >= CC_DIMENSIONS)
        return 0;
    return ck_make(k, CC_PATH, dim, type, left, right, 0);
}

static cc_term bound(cc_kernel *k, uint32_t index) {
    return ck_make(k, CC_BOUND, index, 0, 0, 0, 0);
}

/* A placeholder of an opener's next level. */
static cc_term placeholder(cc_kernel *k, cc_opener *opener, uint32_t *level) {
    return ck_opener_take(k, opener, level) ? ck_make(k, CC_OPENED, *level, 0, 0, 0, 0) : 0;
}

/* Σ (center : F). Π (point : F). Path(F, center, point): under the Π,
 * center is index 1 and point index 0. */
cc_term ck_contractible_type(cc_kernel *k, cc_term type) {
    cc_term contraction = path(k, type, bound(k, 1), bound(k, 0));
    contraction = ck_make(k, CC_PI, 0, type, contraction, 0, 0);
    return ck_make(k, CC_SIGMA, 0, type, contraction, 0, 0);
}

/* Σ (x : A). Path(B, y, f x), x index 0. */
cc_term ck_fiber_type(cc_kernel *k, cc_term a, cc_term b, cc_term f, cc_term y) {
    cc_term image = ck_make(k, CC_APP, 0, f, bound(k, 0), 0, 0);
    cc_term equality = path(k, b, y, image);
    return ck_make(k, CC_SIGMA, 0, a, equality, 0, 0);
}

/* Σ (f : A → B). Π (y : B). IsContr(Fiber(f, y)): the fiber goes under
 * IsContr's binders, so f and y are placeholders while it is built. */
cc_term ck_equiv_type(cc_kernel *k, cc_term a, cc_term b) {
    cc_opener opener = {0};
    uint32_t function = 0, target = 0;
    ck_opener_above(k, &opener, a);
    ck_opener_above(k, &opener, b);
    cc_term f = placeholder(k, &opener, &function), y = f ? placeholder(k, &opener, &target) : 0;
    cc_term function_type = ck_make(k, CC_PI, 0, a, b, 0, 0);
    cc_term fiber = y ? ck_fiber_type(k, a, b, f, y) : 0;
    cc_term contraction = fiber ? ck_contractible_type(k, fiber) : 0;
    contraction = contraction ? ck_close(k, contraction, target) : 0;
    cc_term is_equiv = contraction ? ck_make(k, CC_PI, 0, b, contraction, 0, 0) : 0;
    is_equiv = is_equiv ? ck_close(k, is_equiv, function) : 0;
    return is_equiv ? ck_make(k, CC_SIGMA, 0, function_type, is_equiv, 0, 0) : 0;
}

/* Identity equivalence: each fiber is a path singleton. Contract along p by
 * (p(i), <j> p(i meet j)); Sigma and Path eta check the final endpoint. The
 * target y and the fiber's point are placeholders while the parts under
 * their binders are built. */
cc_term ck_identity_equiv(cc_kernel *k, cc_term type) {
    cc_opener opener = {0};
    uint32_t target_level = 0, point_level = 0;
    ck_opener_above(k, &opener, type);
    cc_term target = placeholder(k, &opener, &target_level);
    cc_term point = target ? placeholder(k, &opener, &point_level) : 0;
    if (!point)
        return 0;
    cc_term identity = ck_make(k, CC_LAM, 0, type, bound(k, 0), 0, 0);
    cc_term fiber = ck_fiber_type(k, type, type, identity, target);
    uint64_t avoid = ck_free_dims(k, type);
    unsigned i = ck_fresh_dimension(k, avoid);
    if (i >= CC_DIMENSIONS)
        return 0;
    unsigned j = ck_fresh_dimension(k, avoid | (UINT64_C(1) << i));
    if (j >= CC_DIMENSIONS)
        return 0;
    cc_term reflexivity = ck_make(k, CC_PLAM, j, type, target, 0, 0);
    cc_term center = ck_make(k, CC_PAIR, 0, fiber, target, reflexivity, 0);
    cc_term preimage = ck_make(k, CC_FST, 0, point, 0, 0, 0);
    cc_term proof = ck_make(k, CC_SND, 0, point, 0, 0, 0);
    cc_term proof_type = path(k, type, target, preimage);
    cc_formula vi, vj, meet;
    cc_init(&vi, CC_INTERVAL);
    cc_init(&vj, CC_INTERVAL);
    cc_init(&meet, CC_INTERVAL);
    cc_status status = cc_generator(&vi, i, true);
    if (status == CC_OK) status = cc_generator(&vj, j, true);
    if (status == CC_OK) status = cc_meet(&meet, &vi, &vj);
    cc_formula_id at_i = 0, at_meet = 0;
    if (ck_formula_result(k, status, "Singleton contraction interval allocation failed.")) {
        at_i = ck_formula(k, &vi);
        at_meet = ck_formula(k, &meet);
    }
    cc_clear(&vi);
    cc_clear(&vj);
    cc_clear(&meet);
    cc_term along = ck_make(k, CC_PAPP, at_i, proof, proof_type, 0, 0);
    cc_term segment = ck_make(k, CC_PAPP, at_meet, proof, proof_type, 0, 0);
    segment = ck_make(k, CC_PLAM, j, type, segment, 0, 0);
    cc_term pair = ck_make(k, CC_PAIR, 0, fiber, along, segment, 0);
    cc_term contraction = ck_make(k, CC_PLAM, i, fiber, pair, 0, 0);
    contraction = contraction ? ck_close(k, contraction, point_level) : 0;
    contraction = contraction ? ck_make(k, CC_LAM, 0, fiber, contraction, 0, 0) : 0;
    cc_term contractible = ck_contractible_type(k, fiber);
    cc_term witness = ck_make(k, CC_PAIR, 0, contractible, center, contraction, 0);
    witness = witness ? ck_close(k, witness, target_level) : 0;
    witness = witness ? ck_make(k, CC_LAM, 0, type, witness, 0, 0) : 0;
    return ck_make(k, CC_PAIR, 0, ck_equiv_type(k, type, type), identity, witness, 0);
}
