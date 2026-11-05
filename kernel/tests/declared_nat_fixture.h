/* Test-only source-shaped declaration of N { zero; succ(n : N); }.
 * Every premise and constructor uses the public H1 instruction API. The
 * kernel keeps no names, so an admitted signature of N's shape is N: no
 * parameters, untruncated, a constant and then one constructor whose one
 * argument is a position, Π (n : s). s, closed over the telescope [s, zero]
 * as Π (Bound 1). Bound 2. */
#ifndef DECLARED_NAT_FIXTURE_H
#define DECLARED_NAT_FIXTURE_H
static inline bool fixture_is_nat(cc_kernel *kernel, uint32_t index) {
    cc_signature_info info;
    cc_constructor_info zero, succ;
    if (!cc_kernel_signature(kernel, index, &info) || !info.admitted || info.modifier != CC_UNTRUNCATED ||
        info.level_count || info.parameter_count || info.constructor_count != 2 ||
        !cc_kernel_signature_constructor(kernel, index, 0, &zero) ||
        !cc_kernel_signature_constructor(kernel, index, 1, &succ) || zero.data || zero.positions ||
        zero.dimensions || succ.data || succ.positions != 1 || succ.dimensions)
        return false;
    cc_term_kind kind;
    uint32_t payload;
    cc_term children[4];
    if (!cc_kernel_node(kernel, succ.type, &kind, NULL, children) || kind != CC_PI)
        return false;
    cc_term domain = children[0], body = children[1];
    return cc_kernel_node(kernel, domain, &kind, &payload, NULL) && kind == CC_BOUND && payload == 1 &&
           cc_kernel_node(kernel, body, &kind, &payload, NULL) && kind == CC_BOUND && payload == 2;
}
static inline cc_judgement_id fixture_nat(cc_kernel *kernel) {
    for (uint32_t index = 1; index < cc_kernel_signature_count(kernel); ++index)
        if (fixture_is_nat(kernel, index))
            return cc_instr_sort_begin(kernel, index);
    cc_term level = cc_kernel_term(kernel, CC_LCONST, 0, 0, 0, 0, 0);
    cc_judgement_id universe = cc_instr_universe(kernel, level);
    cc_entry_id sort = cc_instr_extend(kernel, universe);
    cc_judgement_id sig = cc_instr_signature_begin(kernel, universe, CC_UNTRUNCATED, NULL, 0, sort, 0);
    cc_judgement_id s = cc_instr_variable(kernel, sort);
    cc_entry_id zero = cc_instr_extend(kernel, s);
    sig = cc_instr_signature_constructor(kernel, sig, s, zero);
    cc_entry_id n = cc_instr_extend(kernel, s);
    cc_judgement_id succ_type = cc_instr_pi(kernel, n, s);
    cc_entry_id succ = cc_instr_extend(kernel, succ_type);
    sig = cc_instr_signature_constructor(kernel, sig, succ_type, succ);
    uint32_t index = cc_instr_signature_close(kernel, sig);
    return index ? cc_instr_sort_begin(kernel, index) : 0;
}
static inline cc_judgement_id fixture_zero(cc_kernel *kernel) {
    return cc_instr_construct(kernel, fixture_nat(kernel), 0);
}
static inline cc_judgement_id fixture_succ(cc_kernel *kernel, cc_judgement_id n) {
    return cc_instr_apply(kernel, cc_instr_construct(kernel, fixture_nat(kernel), 1), n);
}
#endif
