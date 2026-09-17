#include "kernel/internal.h"

typedef struct {
    tt_id v[16];
} proof_tuple;
static tt_id proof_step(tt_engine *e, tt_opcode op, const tt_id *j, size_t nj, tt_id c,
                        const tt_id *f, size_t nf, const char *file, int line) {
    if (e->proof_failed)
        return 0;
    tt_id out = 0;
    tt_status status = tt_apply(e, op, j, nj, c, f, nf, &out);
    if (status != TT_OK) {
        e->proof_failed = true;
        fprintf(stderr, "%s:%d: proof step %s failed (status %d)\n", file, line,
                tt_opcode_metadata(op)->name, status);
        for (size_t i = 0; i < nj; i++)
            tt_print_judgement(e, j[i], stderr);
    }
    return out;
}
static tt_id proof_variable(tt_engine *e, tt_id c) {
    return proof_step(e, TT_Vble, NULL, 0, c, NULL, 0, __FILE__, __LINE__);
}
static proof_tuple proof_type_contexts(tt_engine *e, tt_id u, unsigned n) {
    proof_tuple out = {{0}};
    tt_id previous = 0;
    for (unsigned i = 0; i < n && i < 16; i++) {
        out.v[i] = proof_step(e, TT_CtxExt, &u, 1, 0, &previous, 1, __FILE__, __LINE__);
        previous = out.v[i];
    }
    return out;
}
static proof_tuple proof_variables(tt_engine *e, proof_tuple contexts) {
    proof_tuple out = {{0}};
    for (unsigned i = 0; i < 16 && contexts.v[i]; i++)
        out.v[i] = proof_variable(e, contexts.v[i]);
    return out;
}
#include "proofs_generated.inc"

bool tt_prove_composition(tt_engine *e, tt_id *proposition, tt_id *proof) {
    if (!e || !proposition || !proof)
        return false;
    e->proof_failed = false;
    proof_tuple t = p_test_comp(e);
    *proposition = t.v[0];
    *proof = t.v[1];
    return !e->proof_failed && tt_verify(e, *proposition, *proof);
}
bool tt_prove_product_commutes(tt_engine *e, tt_id *proposition, tt_id *proof) {
    if (!e || !proposition || !proof)
        return false;
    e->proof_failed = false;
    proof_tuple t = p_test_product_commutes(e);
    *proposition = t.v[0];
    *proof = t.v[1];
    return !e->proof_failed && tt_verify(e, *proposition, *proof);
}
static bool add_builtin(tt_engine *e, tt_id id) {
    if (!id || e->proof_failed || id > e->nj || e->judgements[id].set)
        return false;
    if (e->nbuiltin >= 128)
        return false;
    e->builtin[e->nbuiltin++] = id;
    return true;
}
static bool add_tuple(tt_engine *e, proof_tuple t, unsigned n) {
    for (unsigned i = 0; i < n; i++)
        if (!add_builtin(e, t.v[i]))
            return false;
    return true;
}
static bool load_builtins(tt_engine *e, bool full) {
    if (!e || (full && !e->conf.allow_axioms))
        return false;
    if (e->nbuiltin && (!full || e->full_builtins))
        return true;
    e->proof_failed = false;
    e->nbuiltin = 0;
    if (!add_builtin(e, p_define_u0(e)) || !add_builtin(e, p_define_unit(e)) ||
        !add_builtin(e, p_define_singleton(e)) || !add_builtin(e, p_define_void(e)) ||
        !add_tuple(e, p_define_nat(e), 2) || !add_builtin(e, p_define_uuomega(e)))
        return false;
    if (!full)
        return true;
    if (!add_builtin(e, p_define_is_trunc(e)) || !add_builtin(e, p_define_is_set(e)) ||
        !add_tuple(e, p_define_propositional_truncation(e), 4) ||
        !add_builtin(e, p_define_lem(e)) || !add_builtin(e, p_define_aoc(e)) ||
        !add_tuple(e, p_define_pr(e), 2) || !add_tuple(e, p_define_homotopy(e), 14) ||
        !add_builtin(e, p_define_based_path_induction(e)) || !add_tuple(e, p_define_two(e), 6) ||
        !add_builtin(e, p_define_unit_prop_unique(e)) ||
        !add_builtin(e, p_define_pi_void_unique(e)) || !add_tuple(e, p_define_wnat(e), 3) ||
        !add_builtin(e, p_define_not(e)) || !add_builtin(e, p_define_is_decidable(e)) ||
        !add_tuple(e, p_define_eq_ops(e), 5))
        return false;
    e->full_builtins = true;
    return true;
}
bool tt_load_builtins(tt_engine *e, bool full) {
    if (!e)
        return false;
    uint32_t limit = e->conf.max_expression_nodes;
    e->conf.max_expression_nodes = 0;
    bool ok = load_builtins(e, full);
    e->conf.max_expression_nodes = limit;
    return ok;
}
bool tt_run_proof_suite(tt_engine *e, FILE *report) {
    tt_id p, q;
    bool ok = tt_prove_composition(e, &p, &q);
    if (report)
        fprintf(report, "composition: %s\n", ok ? "PASS" : "FAIL");
    if (!ok)
        return false;
    ok = tt_prove_product_commutes(e, &p, &q);
    if (report)
        fprintf(report, "product commutativity (including dependent projections): %s\n",
                ok ? "PASS" : "FAIL");
    if (!ok)
        return false;
    ok = tt_load_builtins(e, true);
    if (report)
        fprintf(report,
                "all upstream builtins (including explicit axioms): %s (%u exported judgements)\n",
                ok ? "PASS" : "FAIL", e->nbuiltin);
    return ok;
}
