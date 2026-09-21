/* Derived equivalence types, with no new inference rule or axiom.
 * Fiber(f,y) = Sigma x:A. Path B y (f x), using CCHM's orientation.
 * IsContr(F) = Sigma center:F. Pi point:F. Path F center point.
 * Equiv(A,B) = Sigma f:(A -> B). Pi y:B. IsContr(Fiber(f,y)). */
#include "term_internal.h"

static cc_term path(cc_kernel *k, cc_term type, cc_term left, cc_term right) {
    unsigned dim = ck_fresh_dimension(k, ck_free_dims(k, type) |
                                         ck_free_dims(k, left) | ck_free_dims(k, right));
    if (dim >= CC_DIMENSIONS)
        return 0;
    return ck_make(k, CC_PATH, dim, type, left, right, 0);
}

cc_term ck_contractible_type(cc_kernel *k, cc_term type) {
    uint32_t center = ck_fresh_symbol(k);
    uint32_t point = ck_fresh_symbol(k);
    cc_term contraction = path(k, type, ck_var(k, center), ck_var(k, point));
    contraction = ck_make(k, CC_PI, point, type, contraction, 0, 0);
    return ck_make(k, CC_SIGMA, center, type, contraction, 0, 0);
}

cc_term ck_fiber_type(cc_kernel *k, cc_term a, cc_term b, cc_term f, cc_term y) {
    uint32_t preimage = ck_fresh_symbol(k);
    cc_term image = ck_make(k, CC_APP, 0, f, ck_var(k, preimage), 0, 0);
    cc_term equality = path(k, b, y, image);
    return ck_make(k, CC_SIGMA, preimage, a, equality, 0, 0);
}

cc_term ck_equiv_type(cc_kernel *k, cc_term a, cc_term b) {
    uint32_t function = ck_fresh_symbol(k);
    uint32_t argument = ck_fresh_symbol(k);
    uint32_t target = ck_fresh_symbol(k);
    cc_term function_type = ck_make(k, CC_PI, argument, a, b, 0, 0);
    cc_term fiber = ck_fiber_type(k, a, b, ck_var(k, function), ck_var(k, target));
    cc_term contraction = ck_contractible_type(k, fiber);
    cc_term is_equiv = ck_make(k, CC_PI, target, b, contraction, 0, 0);
    return ck_make(k, CC_SIGMA, function, function_type, is_equiv, 0, 0);
}

/* Identity equivalence: each fiber is a path singleton. Contract along p by
 * (p(i), <j> p(i meet j)); Sigma and Path eta check the final endpoint. */
cc_term ck_identity_equiv(cc_kernel *k, cc_term type) {
    uint32_t argument_name = ck_fresh_symbol(k);
    uint32_t target_name = ck_fresh_symbol(k);
    uint32_t point_name = ck_fresh_symbol(k);
    cc_term target = ck_var(k, target_name);
    cc_term point = ck_var(k, point_name);
    cc_term identity = ck_make(k, CC_LAM, argument_name, type, ck_var(k, argument_name), 0, 0);
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
    bool valid = cc_generator(&vi, i, true) == CC_OK &&
                 cc_generator(&vj, j, true) == CC_OK && cc_meet(&meet, &vi, &vj) == CC_OK;
    cc_formula_id at_i = 0, at_meet = 0;
    if (valid) {
        at_i = cc_kernel_formula(k, &vi);
        at_meet = cc_kernel_formula(k, &meet);
    } else
        ck_fail(k, "Singleton contraction interval allocation failed.");
    cc_clear(&vi);
    cc_clear(&vj);
    cc_clear(&meet);
    cc_term along = ck_make(k, CC_PAPP, at_i, proof, proof_type, 0, 0);
    cc_term segment = ck_make(k, CC_PAPP, at_meet, proof, proof_type, 0, 0);
    segment = ck_make(k, CC_PLAM, j, type, segment, 0, 0);
    cc_term pair = ck_make(k, CC_PAIR, 0, fiber, along, segment, 0);
    cc_term contraction = ck_make(k, CC_PLAM, i, fiber, pair, 0, 0);
    contraction = ck_make(k, CC_LAM, point_name, fiber, contraction, 0, 0);
    cc_term contractible = ck_contractible_type(k, fiber);
    cc_term witness = ck_make(k, CC_PAIR, 0, contractible, center, contraction, 0);
    witness = ck_make(k, CC_LAM, target_name, type, witness, 0, 0);
    return ck_make(k, CC_PAIR, 0, ck_equiv_type(k, type, type), identity, witness, 0);
}
