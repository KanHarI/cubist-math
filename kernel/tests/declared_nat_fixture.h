/* Test-only source-shaped declaration of N { zero; succ(n : N); }.
 * Every premise and constructor uses the public H1 instruction API. */
#ifndef DECLARED_NAT_FIXTURE_H
#define DECLARED_NAT_FIXTURE_H
static inline cc_judgement_id fixture_nat(cc_kernel *kernel) {
    const uint32_t symbol = 900000;
    cc_signature_info info;
    for (uint32_t index = 1; cc_kernel_signature(kernel, index, &info); ++index)
        if (info.admitted && info.sort_symbol == symbol)
            return cc_instr_sort_begin(kernel, index);
    cc_term level = cc_kernel_term(kernel, CC_LCONST, 0, 0, 0, 0, 0);
    cc_judgement_id universe = cc_instr_universe(kernel, level);
    cc_judgement_id sig = cc_instr_signature_begin(kernel, universe, CC_UNTRUNCATED, symbol, 0);
    cc_entry_id sort = cc_instr_extend(kernel, universe, symbol);
    cc_judgement_id s = cc_instr_variable(kernel, sort);
    sig = cc_instr_signature_constructor(kernel, sig, s, symbol + 1);
    cc_entry_id n = cc_instr_extend(kernel, s, symbol + 3);
    sig = cc_instr_signature_constructor(kernel, sig, cc_instr_pi(kernel, n, s), symbol + 2);
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
