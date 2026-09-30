/* The instruction kernel derives add, lt and lt_succ forward, as THTH did:
 * every rule application is an instruction, and every reduction is named
 * and placed. The term checker then accepts what the instructions defined. */
#include "cubical_kernel.h"
#include <assert.h>
#include <stdio.h>
#include <string.h>

static cc_kernel *k;
#include "instruction_fixtures.h"

static uint32_t ok(uint32_t id, const char *what, int line) {
    if (!id) {
        fprintf(stderr, "line %d: %s: %s\n", line, what, cc_kernel_error(k));
        assert(0);
    }
    fixture_judgement(id, what, line);
    return id;
}
#define OK(x) ok((x), #x, __LINE__)
/* The same captured arguments drive the request and its optional snapshot.
 * Arguments (including OK premises) run once even without --fixtures. */
#define REQUEST(operation, fragment, face, entry, operand, ...) refusal_request(#operation, \
    (const cc_judgement_id[]){__VA_ARGS__}, sizeof((const cc_judgement_id[]){__VA_ARGS__}) / sizeof(cc_judgement_id), \
    (face), (entry), (operand), (fragment), __LINE__)
#define REJECT(operation, fragment, face, entry, operand, ...) \
    rejects(REQUEST(operation, fragment, face, entry, operand, __VA_ARGS__), (fragment))
#define REJECT_STEP(fragment, judgement, side, rule) \
    REJECT(step, fragment, 0, 0, ((side) << 16) | (rule), judgement)

static void rejects(uint32_t id, const char *fragment) {
    assert(!id);
    if (!strstr(cc_kernel_error(k), fragment)) {
        fprintf(stderr, "expected \"%s\", got \"%s\"\n", fragment, cc_kernel_error(k));
        assert(0);
    }
    cc_kernel_clear_error(k);
}

static cc_judgement_info info(cc_judgement_id j) { cc_judgement_info result; assert(cc_kernel_judgement(k, j, &result)); return result; }
static cc_term term_of(cc_judgement_id j) { return info(j).term; }
static cc_term other_of(cc_judgement_id j) { return info(j).other; }
static cc_term type_of(cc_judgement_id j) { return info(j).type; }
static size_t context_size(cc_judgement_id j) { size_t n = 0; while (cc_kernel_judgement_context(k, j, n)) ++n; return n; }
static cc_term_kind kind(cc_term t) { cc_term_kind result; assert(cc_kernel_node(k, t, &result, NULL, NULL)); return result; }
static cc_term child(cc_term t, unsigned i) { cc_term children[4]; assert(cc_kernel_node(k, t, NULL, NULL, children)); return children[i]; }
/* The level constant ω·tier + n, as raw syntax. */
static cc_term level(unsigned tier, unsigned n) { return cc_kernel_term(k, CC_LCONST, tier << 16 | n, 0, 0, 0, 0); }

/* Reconstruct the actual native request solely from its recorded operands.
 * No separate hand-written request can drift from the replay snapshot. */
static uint32_t refusal_request(const char *operation, const cc_judgement_id *args, size_t count,
                               cc_formula_id face, cc_entry_id entry, uint32_t operand,
                               const char *fragment, int line) {
    uint32_t symbol = 0;
    if (entry) assert(cc_kernel_entry(k, entry, &symbol, NULL, NULL, NULL));
    uint32_t result = 0;
#define REQUEST_CASE(name, arity, expression) \
    if (strcmp(operation, #name) == 0) { assert(count == (arity)); result = (expression); } else
    REQUEST_CASE(pushout, 4, cc_instr_pushout(k, args[0], args[1], args[2], args[3]))
    REQUEST_CASE(pushLeft, 2, cc_instr_push_point(k, args[0], args[1], false))
    REQUEST_CASE(pushRight, 2, cc_instr_push_point(k, args[0], args[1], true))
    REQUEST_CASE(sup, 3, cc_instr_sup(k, args[0], args[1], args[2]))
    REQUEST_CASE(wElim, 3, cc_instr_w_elim(k, args[0], args[1], args[2]))
    REQUEST_CASE(hcomp, 1, cc_instr_hcomp(k, args[0]))
    REQUEST_CASE(trans, 1, cc_instr_trans(k, args[0], face))
    REQUEST_CASE(iota, 1, cc_instr_step(k, OK(cc_instr_refl(k, args[0])), 1, NULL, 0, CC_STEP_IOTA))
    REQUEST_CASE(replace, 2, cc_instr_replace(k, args[0], 1, (const uint8_t[]){(uint8_t)operand}, 1, args[1]))
    REQUEST_CASE(lambda, 1, cc_instr_lambda(k, entry, args[0]))
    REQUEST_CASE(extend, 1, cc_instr_extend(k, args[0], symbol))
    REQUEST_CASE(level, 1, cc_instr_level(k, symbol))
    REQUEST_CASE(step, 1, cc_instr_step(k, args[0], operand >> 16, NULL, 0, (cc_step_rule)(operand & 65535)))
    REQUEST_CASE(system, 2, cc_instr_system(k, entry, args[0], args[1]))
    REQUEST_CASE(systemTube, 3, cc_instr_system_tube(k, args[0], face, args[1], args[2]))
    REQUEST_CASE(systemOverlap, 2, cc_instr_system_overlap(k, args[0], operand, args[1]))
    REQUEST_CASE(gluePiece, 3, cc_instr_glue_piece(k, args[0], face, args[1], args[2]))
    REQUEST_CASE(comp, 1, cc_instr_comp(k, args[0]))
    REQUEST_CASE(glueBase, 1, cc_instr_glue_base(k, args[0]))
    REQUEST_CASE(glue, 1, cc_instr_glue(k, args[0]))
    REQUEST_CASE(glueTermBase, 2, cc_instr_glue_term_base(k, args[0], args[1]))
    REQUEST_CASE(glueTerm, 1, cc_instr_glue_term(k, args[0]))
    REQUEST_CASE(unglue, 1, cc_instr_unglue(k, args[0]))
    REQUEST_CASE(apply, 2, cc_instr_apply(k, args[0], args[1]))
    REQUEST_CASE(lift, 2, cc_instr_lift(k, args[0], args[1]))
    REQUEST_CASE(define, 1, cc_instr_define(k, operand, args[0]))
    REQUEST_CASE(universeTerm, 1, cc_instr_universe(k, term_of(args[0])))
    REQUEST_CASE(universeEntry, 1, cc_instr_universe(k, cc_kernel_term(k, CC_VAR, symbol, 0, 0, 0, 0)))
    REQUEST_CASE(levelApplyTerm, 2, cc_instr_level_apply(k, args[0], term_of(args[1])))
    REQUEST_CASE(convertible, 2, cc_kernel_convertible(k, term_of(args[0]), term_of(args[1]), 0))
    { fprintf(stderr, "unknown refusal operation %s\n", operation); assert(0); }
#undef REQUEST_CASE
    assert(!result);
    if (strcmp(operation, "convertible") == 0) assert(cc_kernel_error_kind(k) == CC_ERROR_NONE);
    else assert(cc_kernel_error_kind(k) == CC_ERROR_OTHER || cc_kernel_error_kind(k) == CC_ERROR_MISMATCH);
    fixture_refusal(operation, args, count, face, entry, operand, fragment, line);
    return result;
}

/* Contract one redex of side 1 of an equality, at a position. */
#define AT(...) (const uint8_t[]){__VA_ARGS__}, sizeof((uint8_t[]){__VA_ARGS__})
#define STEP(eq, rule, ...) OK(cc_instr_step(k, (eq), 1, __VA_ARGS__, (rule)))
#define ROOT NULL, 0

static cc_term lvar(uint32_t symbol) { return cc_kernel_term(k, CC_VAR, symbol, 0, 0, 0, 0); }
static cc_term lsucc(cc_term level, uint32_t n) { return cc_kernel_term(k, CC_LSUCC, n, level, 0, 0, 0); }
static cc_term lmax(cc_term a, cc_term b) { return cc_kernel_term(k, CC_LMAX, 0, a, b, 0, 0); }
static void level_quantification(void);

static unsigned successors(cc_term t) {
    unsigned count = 0;
    cc_term children[4];
    for (cc_term_kind which; (which = kind(t)) == CC_SUCC; ++count) {
        assert(cc_kernel_node(k, t, NULL, NULL, children));
        t = children[0];
    }
    assert(kind(t) == CC_ZERO);
    return count;
}

int main(int argc, char **argv) {
    if (argc == 3 && strcmp(argv[1], "--fixtures") == 0) {
        fixture_file = fopen(argv[2], "w");
        assert(fixture_file);
    } else assert(argc == 1);
    k = cc_kernel_new();
    assert(k);
    enum { N = 1, M, K, A, B, X, P, H, W = 9, Q = 20 };

    /* add(a, b) := natrec(λx. Nat, a, λp. λh. succ(h), b). The motive's
     * applications are beta-reduced where the rules need a plain Nat. */
    cc_judgement_id nat = OK(cc_instr_nat(k));
    cc_entry_id a = OK(cc_instr_extend(k, nat, A)), b = OK(cc_instr_extend(k, nat, B));
    cc_entry_id x = OK(cc_instr_extend(k, nat, X)), p = OK(cc_instr_extend(k, nat, P));
    cc_judgement_id motive = OK(cc_instr_lambda(k, x, nat));
    cc_judgement_id zero = OK(cc_instr_zero(k));
    cc_judgement_id at_zero = OK(cc_instr_apply(k, motive, zero));
    cc_judgement_id base = OK(cc_instr_convert(k, OK(cc_instr_variable(k, a)),
        OK(cc_instr_symmetry(k, STEP(OK(cc_instr_refl(k, at_zero)), CC_STEP_BETA, ROOT)))));
    cc_judgement_id pv = OK(cc_instr_variable(k, p));
    cc_judgement_id at_p = OK(cc_instr_apply(k, motive, pv));
    cc_entry_id h = OK(cc_instr_extend(k, at_p, H));
    cc_judgement_id hv = OK(cc_instr_convert(k, OK(cc_instr_variable(k, h)), STEP(OK(cc_instr_refl(k, at_p)), CC_STEP_BETA, ROOT)));
    assert(context_size(hv) == 2);
    cc_judgement_id at_succ = OK(cc_instr_apply(k, motive, OK(cc_instr_succ(k, pv))));
    cc_judgement_id next = OK(cc_instr_convert(k, OK(cc_instr_succ(k, hv)),
        OK(cc_instr_symmetry(k, STEP(OK(cc_instr_refl(k, at_succ)), CC_STEP_BETA, ROOT)))));
    cc_judgement_id step = OK(cc_instr_lambda(k, p, OK(cc_instr_lambda(k, h, next))));
    assert(context_size(step) == 0);
    cc_judgement_id bv = OK(cc_instr_variable(k, b));
    cc_judgement_id recursion = OK(cc_instr_nat_elim(k, motive, base, step, bv));
    assert(context_size(recursion) == 2);
    cc_judgement_id sum = OK(cc_instr_convert(k, recursion,
        STEP(OK(cc_instr_refl(k, OK(cc_instr_apply(k, motive, bv)))), CC_STEP_BETA, ROOT)));
    cc_judgement_id add = OK(cc_instr_define(k, 100, OK(cc_instr_lambda(k, a, OK(cc_instr_lambda(k, b, sum))))));

    /* The term checker computes with the instructions' definition. */
    cc_term raw_zero = cc_kernel_term(k, CC_ZERO, 0, 0, 0, 0, 0);
    cc_term two = cc_kernel_term(k, CC_SUCC, 0, cc_kernel_term(k, CC_SUCC, 0, raw_zero, 0, 0, 0), 0, 0, 0);
    cc_term three = cc_kernel_term(k, CC_SUCC, 0, two, 0, 0, 0);
    cc_term five = cc_kernel_term(k, CC_APP, 0, cc_kernel_term(k, CC_APP, 0, term_of(add), two, 0, 0), three, 0, 0);
    cc_checked_result checked;
    assert(cc_kernel_check(k, five, cc_kernel_term(k, CC_NAT, 0, 0, 0, 0, 0), NULL, 0, &checked));
    assert(successors(cc_kernel_normalize(k, checked.expression)) == 5);
    if (fixture_file) fixture_closed_equality(five, term_of(nat), cc_kernel_normalize(k, checked.expression), __LINE__);

    /* lt(n, m) := Σ(k : Nat). succ(add(n, k)) = m. */
    cc_entry_id n = OK(cc_instr_extend(k, nat, N)), m = OK(cc_instr_extend(k, nat, M)), kk = OK(cc_instr_extend(k, nat, K));
    cc_entry_id i = OK(cc_instr_dimension(k, 0));
    cc_judgement_id nv = OK(cc_instr_variable(k, n));
    cc_judgement_id n_plus_k = OK(cc_instr_apply(k, OK(cc_instr_apply(k, add, nv)), OK(cc_instr_variable(k, kk))));
    cc_judgement_id equation = OK(cc_instr_path(k, i, nat, OK(cc_instr_succ(k, n_plus_k)), OK(cc_instr_variable(k, m))));
    assert(context_size(equation) == 3);
    cc_judgement_id lt = OK(cc_instr_define(k, 101,
        OK(cc_instr_lambda(k, n, OK(cc_instr_lambda(k, m, OK(cc_instr_sigma(k, kk, equation))))))));

    /* lt_succ : Π(n : Nat). lt(n, succ(n)) := λn. (0, <i> succ(n)).
     * The goal unfolds by one delta and two betas, highlighted in turn. */
    cc_judgement_id sn = OK(cc_instr_succ(k, nv));
    cc_judgement_id goal = OK(cc_instr_apply(k, OK(cc_instr_apply(k, lt, nv)), sn));
    cc_judgement_id unfolded = OK(cc_instr_refl(k, goal));
    unfolded = STEP(unfolded, CC_STEP_DELTA, AT(0, 0));
    unfolded = STEP(unfolded, CC_STEP_BETA, AT(0));
    unfolded = STEP(unfolded, CC_STEP_BETA, ROOT);
    assert(kind(other_of(unfolded)) == CC_SIGMA);
    cc_judgement_id sigma = OK(cc_instr_side(k, unfolded, 1));
    cc_judgement_id expected = OK(cc_instr_family(k, sigma, zero));
    /* succ(add(n, 0)) computes to succ(n) inside the path type. */
    cc_judgement_id computed = OK(cc_instr_refl(k, expected));
    computed = STEP(computed, CC_STEP_DELTA, AT(1, 0, 0, 0));
    computed = STEP(computed, CC_STEP_BETA, AT(1, 0, 0));
    computed = STEP(computed, CC_STEP_BETA, AT(1, 0));
    computed = STEP(computed, CC_STEP_IOTA, AT(1, 0));
    cc_judgement_id loop = OK(cc_instr_path_lambda(k, i, sn));
    assert(context_size(loop) == 1);
    cc_judgement_id witness = OK(cc_instr_convert(k, loop, OK(cc_instr_symmetry(k, computed))));
    cc_judgement_id proof = OK(cc_instr_pair(k, sigma, zero, witness));
    proof = OK(cc_instr_convert(k, proof, OK(cc_instr_symmetry(k, unfolded))));
    assert(term_of(goal) == type_of(proof));
    cc_judgement_id lt_succ = OK(cc_instr_define(k, 102, OK(cc_instr_lambda(k, n, proof))));
    cc_term value;
    assert(cc_kernel_definition(k, term_of(lt_succ), NULL, &value, NULL));
    assert(cc_kernel_check(k, value, type_of(lt_succ), NULL, 0, &checked));

    /* Replacement under a binder: the goal's entry n is the binder's. */
    cc_judgement_id statement = OK(cc_instr_pi(k, n, goal));
    assert(context_size(statement) == 0);
    cc_judgement_id opened = OK(cc_instr_replace(k, OK(cc_instr_refl(k, statement)), 1, AT(1), unfolded));
    assert(context_size(opened) == 0 && kind(other_of(opened)) == CC_PI);
    cc_term children[4];
    assert(cc_kernel_node(k, other_of(opened), NULL, NULL, children) && kind(children[1]) == CC_SIGMA);
    REJECT(replace, "not the equality's left side", 0, 0, 0, OK(cc_instr_refl(k, statement)), unfolded);

    /* The term checker's definitions are not admitted: Lookup refuses them. */
    cc_term raw_nat = cc_kernel_term(k, CC_NAT, 0, 0, 0, 0, 0);
    cc_term unadmitted = cc_kernel_define(k, 103, cc_kernel_term(k, CC_LAM, W, raw_nat, cc_kernel_term(k, CC_VAR, W, 0, 0, 0, 0), 0, 0), 0);
    assert(unadmitted);
    uint32_t lookup_result = cc_instr_lookup(k, unadmitted);
    fixture_unadmitted(unadmitted, "admitted by Define", __LINE__);
    rejects(lookup_result, "admitted by Define");
    /* A bound name must correspond to an entry of the binder's type. The
     * identity λ(W : Nat). W is admitted inside a checkpoint whose entries
     * the commit drops, so W can then name an entry of another type. */
    cc_kernel_checkpoint(k);
    cc_entry_id bound = OK(cc_instr_extend(k, nat, W));
    cc_judgement_id identity_admitted = OK(cc_instr_define(k, 105, OK(cc_instr_lambda(k, bound, OK(cc_instr_variable(k, bound))))));
    cc_term identity = term_of(identity_admitted);
    assert(cc_kernel_commit_checkpoint(k));
    identity = cc_kernel_relocated(k, identity);
    cc_judgement_id identity_value = STEP(OK(cc_instr_refl(k, OK(cc_instr_lookup(k, identity)))), CC_STEP_DELTA, ROOT);
    cc_entry_id w = OK(cc_instr_extend(k, OK(cc_instr_unit(k)), W));
    REJECT(replace, "different types", 0, 0, 1, identity_value, OK(cc_instr_refl(k, OK(cc_instr_variable(k, w)))));

    /* An entry cannot be discharged while another depends on it. */
    cc_judgement_id loop_type = OK(cc_instr_path(k, i, nat, nv, nv));
    cc_entry_id q = OK(cc_instr_extend(k, loop_type, Q));
    REJECT(lambda, "still depends", 0, n, 0, OK(cc_instr_variable(k, q)));
    REJECT(extend, "already names", 0, n, 0, OK(cc_instr_unit(k)));

    /* Paths compute at a path lambda, and at an endpoint of the annotation. */
    cc_judgement_id end = STEP(OK(cc_instr_refl(k, OK(cc_instr_path_apply(k, loop, 0, 1)))), CC_STEP_PATH, ROOT);
    assert(other_of(end) == term_of(sn));
    cc_judgement_id start = STEP(OK(cc_instr_refl(k, OK(cc_instr_path_apply(k, OK(cc_instr_variable(k, q)), 0, 0)))), CC_STEP_PATH, ROOT);
    assert(other_of(start) == term_of(nv));

    cc_judgement_id numeral = OK(cc_instr_succ(k, OK(cc_instr_succ(k, zero))));
    cc_judgement_id four = OK(cc_instr_apply(k, OK(cc_instr_apply(k, add, numeral)), numeral));

    /* Rewriting a typing judgement in place: its type by a step, as THTH's
     * HighType with a pointed reduction, and its term by a replacement. */
    cc_judgement_id retyped = OK(cc_instr_step(k, proof, 2, AT(0, 0), CC_STEP_DELTA));
    retyped = OK(cc_instr_step(k, retyped, 2, AT(0), CC_STEP_BETA));
    retyped = OK(cc_instr_step(k, retyped, 2, ROOT, CC_STEP_BETA));
    assert(term_of(retyped) == term_of(proof) && type_of(retyped) == other_of(unfolded));
    cc_judgement_id reduced = OK(cc_instr_step(k, OK(cc_instr_refl(k, four)), 0, ROOT, CC_STEP_NORMALIZE));
    assert(successors(term_of(reduced)) == 4 && successors(term_of(OK(cc_instr_step(k, four, 0, ROOT, CC_STEP_NORMALIZE)))) == 4);
    REJECT_STEP("sides", four, 1, CC_STEP_NORMALIZE);
    cc_judgement_id swapped = OK(cc_instr_replace(k, goal, 0, ROOT, unfolded));
    assert(term_of(swapped) == other_of(unfolded) && type_of(swapped) == type_of(goal));

    /* The graph records each derivation once: its rule, premises, entry,
     * operands and highlighted position. Dimension entries are their index. */
    assert(OK(cc_instr_dimension(k, 0)) == i && OK(cc_instr_extend(k, nat, N)) == n);
    assert(OK(cc_instr_apply(k, OK(cc_instr_apply(k, lt, nv)), sn)) == goal && OK(cc_instr_nat(k)) == nat);
    cc_judgement_info derived = info(goal);
    assert(derived.rule == CC_INSTR_APPLY && info(derived.premise[0]).rule == CC_INSTR_APPLY && derived.premise[1] == sn);
    derived = info(computed);
    assert(derived.rule == CC_INSTR_STEP && derived.operand[0] == 1 && derived.operand[1] == CC_STEP_IOTA);
    assert(derived.depth == 2 && derived.position[0] == 1 && derived.position[1] == 0);
    assert(OK(cc_instr_step(k, derived.premise[0], 1, AT(1, 0), CC_STEP_IOTA)) == computed);
    assert(info(opened).rule == CC_INSTR_REPLACE && info(opened).premise[1] == unfolded);
    cc_judgement_id source;
    bool dimension;
    assert(cc_kernel_entry(k, h, NULL, NULL, &dimension, &source) && !dimension && source == at_p);
    assert(cc_kernel_entry(k, i, NULL, NULL, &dimension, &source) && dimension && !source);
    for (cc_judgement_id id = 1; id < cc_kernel_judgement_count(k); ++id)
        for (unsigned slot = 0; slot < 4; ++slot)
            assert(info(id).premise[slot] < id);

    /* An endpoint substitutes into a judgement and discharges the dimension. */
    cc_judgement_id at_one = OK(cc_instr_endpoint(k, OK(cc_instr_path_apply(k, loop, i, 0)), i, 1));
    assert(context_size(at_one) == 1 && kind(term_of(at_one)) == CC_PAPP);
    assert(other_of(STEP(OK(cc_instr_refl(k, at_one)), CC_STEP_PATH, ROOT)) == term_of(sn));

    /* A path at a compound formula, and composition along a second
     * dimension with tubes on the faces i = 0 and i = 1. */
    cc_formula formula;
    cc_init(&formula, CC_INTERVAL);
    assert(cc_generator(&formula, 0, false) == CC_OK);
    cc_formula_id reversed = cc_kernel_formula(k, &formula);
    cc_clear(&formula);
    cc_judgement_id at_reversed = OK(cc_instr_path_at(k, loop, reversed));
    assert(context_size(at_reversed) == 2 && type_of(at_reversed) == type_of(sn));
    cc_formula_id faces[2];
    for (unsigned side = 0; side < 2; ++side) {
        cc_init(&formula, CC_FACE);
        assert(cc_generator(&formula, 0, side == 1) == CC_OK);
        faces[side] = cc_kernel_formula(k, &formula);
        cc_clear(&formula);
    }
    cc_entry_id j2 = OK(cc_instr_dimension(k, 1));
    cc_judgement_id system = OK(cc_instr_system(k, j2, nat, nv));
    cc_judgement_id stay = OK(cc_instr_refl(k, nv));
    for (unsigned side = 0; side < 2; ++side)
        system = OK(cc_instr_system_tube(k, system, faces[side], nv, stay));
    /* A third tube, on the face 1, overlaps both: until an equality shows it
     * agrees with each on the overlap, the system neither grows nor closes. */
    cc_formula_id always, never;
    cc_init(&formula, CC_FACE);
    assert(cc_one(&formula) == CC_OK);
    always = cc_kernel_formula(k, &formula);
    cc_clear(&formula);
    cc_init(&formula, CC_FACE);
    assert(cc_zero(&formula) == CC_OK);
    never = cc_kernel_formula(k, &formula);
    cc_clear(&formula);
    cc_judgement_id overlapping = OK(cc_instr_system_tube(k, system, always, nv, stay));
    REJECT(comp, "agree with the tubes it overlaps", 0, 0, 0, overlapping);
    REJECT(systemTube, "agree with the tubes it overlaps", never, 0, 0, overlapping, OK(cc_instr_unit(k)), 0);
    REJECT(systemOverlap, "does not overlap", 0, 0, 2, overlapping, stay);
    REJECT(systemOverlap, "does not start at the last tube", 0, 0, 0, overlapping, OK(cc_instr_refl(k, OK(cc_instr_variable(k, m)))));
    cc_judgement_id agreed = OK(cc_instr_system_overlap(k, overlapping, 0, stay));
    REJECT(systemOverlap, "already agrees", 0, 0, 0, agreed, stay);
    agreed = OK(cc_instr_system_overlap(k, agreed, 1, stay));
    /* A tube on the face 0 is never used: any typing judgement will do. */
    REJECT(systemTube, "takes no equality", never, 0, 0, agreed, OK(cc_instr_unit(k)), stay);
    agreed = OK(cc_instr_system_tube(k, agreed, never, OK(cc_instr_unit(k)), 0));
    cc_judgement_id full = OK(cc_instr_comp(k, agreed));
    assert(cc_kernel_check_in_cube(k, term_of(full), type_of(full), (cc_assumption[]){{N, type_of(nv)}}, 1, 1, &checked));
    assert(other_of(STEP(OK(cc_instr_refl(k, full)), CC_STEP_FACE, ROOT)) == term_of(nv));
    REJECT_STEP("closed by Comp", system, 0, CC_STEP_NORMALIZE);
    cc_judgement_id composed = OK(cc_instr_comp(k, system));
    assert(kind(term_of(composed)) == CC_COMP && kind(type_of(composed)) == CC_NAT);
    /* The context is n and the face's dimension; the composition's is bound. */
    assert(context_size(composed) == 2);
    cc_assumption assumptions[] = {{N, type_of(nv)}};
    assert(cc_kernel_check_in_cube(k, term_of(composed), type_of(composed), assumptions, 1, 1, &checked));
    REJECT(system, "may not use its dimension", 0, i, 0, nat, OK(cc_instr_path_apply(k, loop, i, 0)));
    /* At i = 1 the face i = 1 holds: a face step gives that tube at the end. */
    REJECT_STEP("face that holds", OK(cc_instr_refl(k, composed)), 1, CC_STEP_FACE);
    cc_judgement_id at_face = OK(cc_instr_endpoint(k, composed, i, 1));
    assert(other_of(STEP(OK(cc_instr_refl(k, at_face)), CC_STEP_FACE, ROOT)) == term_of(nv));

    /* The pushout of Nat ← Unit → Nat along 0 and 0: points, a path between
     * them, and the path at an endpoint computing to a point. */
    cc_judgement_id unit_type = OK(cc_instr_unit(k));
    cc_entry_id u0 = OK(cc_instr_extend(k, unit_type, 30));
    cc_judgement_id constant = OK(cc_instr_lambda(k, u0, zero));
    cc_entry_id f0 = OK(cc_instr_extend(k, OK(cc_instr_pi(k, u0, nat)), 31));
    cc_judgement_id span_type = OK(cc_instr_sigma(k, f0, OK(cc_instr_pi(k, u0, nat))));
    cc_judgement_id maps = OK(cc_instr_pair(k, span_type, constant, constant));
    REJECT(pushout, "maps of a pushout", 0, 0, 0, unit_type, nat, nat, zero);
    cc_judgement_id pushout = OK(cc_instr_pushout(k, unit_type, nat, nat, maps));
    assert(kind(term_of(pushout)) == CC_PUSHOUT && kind(type_of(pushout)) == CC_U);
    cc_judgement_id inl = OK(cc_instr_push_point(k, pushout, zero, false));
    assert(kind(term_of(inl)) == CC_PUSH_LEFT && type_of(inl) == term_of(pushout));
    cc_judgement_id tt = OK(cc_instr_point(k));
    REJECT(pushRight, "wrong type", 0, 0, 0, pushout, tt);
    REJECT(pushLeft, "pushout type", 0, 0, 0, nat, zero);
    cc_init(&formula, CC_INTERVAL);
    assert(cc_generator(&formula, 0, true) == CC_OK);
    cc_formula_id along = cc_kernel_formula(k, &formula);
    cc_clear(&formula);
    cc_judgement_id push = OK(cc_instr_push_path(k, pushout, OK(cc_instr_point(k)), along));
    assert(context_size(push) == 1 && kind(term_of(push)) == CC_PUSH_PATH);
    cc_judgement_id at_start = OK(cc_instr_endpoint(k, push, i, 0));
    assert(kind(other_of(STEP(OK(cc_instr_refl(k, at_start)), CC_STEP_IOTA, ROOT))) == CC_PUSH_LEFT);
    REJECT(iota, "Iota needs", 0, 0, 0, push);
    /* Homogeneous composition, over the pushout; not over Nat. */
    cc_judgement_id box = OK(cc_instr_system(k, j2, pushout, inl));
    box = OK(cc_instr_system_tube(k, box, faces[0], inl, OK(cc_instr_refl(k, inl))));
    cc_judgement_id hcomp = OK(cc_instr_hcomp(k, box));
    assert(kind(term_of(hcomp)) == CC_HCOMP && type_of(hcomp) == term_of(pushout));
    REJECT(hcomp, "pushout types", 0, 0, 0, system);
    /* Transport along a constant family: its tubes are the base on each clause. */
    cc_judgement_id moved = OK(cc_instr_trans(k, box, faces[0]));
    assert(kind(term_of(moved)) == CC_TRANS && type_of(moved) == term_of(pushout));
    REJECT(trans, "clauses, in order", faces[1], 0, 0, box);
    cc_judgement_id still = OK(cc_instr_system_tube(k, OK(cc_instr_system(k, j2, pushout, inl)), always, inl,
                                                     OK(cc_instr_refl(k, inl))));
    cc_judgement_id unmoved = OK(cc_instr_trans(k, still, always));
    assert(other_of(STEP(OK(cc_instr_refl(k, unmoved)), CC_STEP_FACE, ROOT)) == term_of(inl));

    /* Glue over Nat with a piece on the face 0, which is never used: a Glue
     * term of it, and unglue. An equivalence must be one, of the stated type. */
    cc_judgement_id glue_system = OK(cc_instr_glue_base(k, nat));
    REJECT(glueBase, "Expected a type", 0, 0, 0, zero);
    REJECT(gluePiece, "equivalence is not", faces[0], 0, 0, glue_system, unit_type, zero);
    REJECT(glue, "Not a Glue type", 0, 0, 0, OK(cc_instr_system(k, j2, nat, zero)));
    glue_system = OK(cc_instr_glue_piece(k, glue_system, never, unit_type, zero));
    cc_judgement_id glued = OK(cc_instr_glue(k, glue_system));
    assert(kind(term_of(glued)) == CC_GLUE && kind(type_of(glued)) == CC_U);
    REJECT(glueTermBase, "needs a Glue type", 0, 0, 0, nat, zero);
    cc_judgement_id glue_value = OK(cc_instr_glue_term_base(k, glued, zero));
    REJECT(glueTerm, "value for every piece", 0, 0, 0, glue_value);
    glue_value = OK(cc_instr_glue_term_piece(k, glue_value, OK(cc_instr_point(k)), 0));
    cc_judgement_id element = OK(cc_instr_glue_term(k, glue_value));
    assert(kind(term_of(element)) == CC_GLUE_TERM && type_of(element) == term_of(glued));
    assert(cc_kernel_check(k, term_of(element), type_of(element), NULL, 0, &checked));
    assert(type_of(OK(cc_instr_unglue(k, element))) == term_of(nat));
    REJECT(unglue, "Glue type", 0, 0, 0, zero);

    /* The W type of trees with Unit many children at each label: W(x : Unit). Unit.
     * A tree whose children are one tree, and W recursion computing on sup. */
    cc_judgement_id trees = OK(cc_instr_w(k, u0, unit_type));
    assert(kind(term_of(trees)) == CC_W && kind(type_of(trees)) == CC_U);
    assert(kind(term_of(OK(cc_instr_family(k, trees, tt)))) == CC_UNIT);
    cc_entry_id sub = OK(cc_instr_extend(k, trees, 32));
    cc_entry_id slot = OK(cc_instr_extend(k, unit_type, 33));
    cc_judgement_id only = OK(cc_instr_lambda(k, slot, OK(cc_instr_variable(k, sub))));
    REJECT(sup, "label has the wrong type", 0, 0, 0, trees, zero, only);
    REJECT(sup, "W type", 0, 0, 0, nat, tt, only);
    cc_judgement_id node = OK(cc_instr_sup(k, trees, tt, only));
    assert(kind(term_of(node)) == CC_SUP && type_of(node) == term_of(trees));
    /* WRec(λz. Nat, λl. λc. λh. 0, node) : (λz. Nat)(node), and it computes. */
    cc_entry_id z0 = OK(cc_instr_extend(k, trees, 34));
    cc_judgement_id count = OK(cc_instr_lambda(k, z0, nat));
    cc_entry_id l0 = OK(cc_instr_extend(k, unit_type, 35));
    cc_entry_id c0 = OK(cc_instr_extend(k, OK(cc_instr_pi(k, slot, trees)), 36));
    cc_judgement_id child_count = OK(cc_instr_apply(k, count, OK(cc_instr_apply(k, OK(cc_instr_variable(k, c0)),
                                                                                OK(cc_instr_variable(k, slot))))));
    cc_entry_id h0 = OK(cc_instr_extend(k, OK(cc_instr_pi(k, slot, child_count)), 37));
    cc_judgement_id tree_count = OK(cc_instr_apply(k, count, OK(cc_instr_sup(k, trees, OK(cc_instr_variable(k, l0)),
                                                                                 OK(cc_instr_variable(k, c0))))));
    cc_judgement_id counted = OK(cc_instr_convert(k, zero, OK(cc_instr_symmetry(k, STEP(OK(cc_instr_refl(k, tree_count)),
                                                                                       CC_STEP_BETA, ROOT)))));
    cc_judgement_id step_case = OK(cc_instr_lambda(k, l0, OK(cc_instr_lambda(k, c0, OK(cc_instr_lambda(k, h0, counted))))));
    REJECT(wElim, "step has the wrong type", 0, 0, 0, count, zero, node);
    cc_judgement_id recursion_w = OK(cc_instr_w_elim(k, count, step_case, node));
    assert(kind(term_of(recursion_w)) == CC_WREC);
    assert(kind(other_of(STEP(OK(cc_instr_refl(k, recursion_w)), CC_STEP_IOTA, ROOT))) == CC_APP);

    /* Mismatches are reported with both types. */
    cc_term found, wanted;
    assert(!REQUEST(apply, "wrong type", 0, 0, 0, add, OK(cc_instr_variable(k, w))));
    assert(cc_kernel_error_kind(k) == CC_ERROR_MISMATCH && cc_kernel_mismatch(k, &found, &wanted));
    assert(kind(found) == CC_UNIT && kind(wanted) == CC_NAT);
    cc_kernel_clear_error(k);
    REJECT_STEP("Beta needs", OK(cc_instr_refl(k, nv)), 0, CC_STEP_BETA);
    REJECT(define, "closed", 0, 0, 104, nv);

    /* Normalization, eta and cumulativity. */
    assert(successors(other_of(STEP(OK(cc_instr_refl(k, four)), CC_STEP_NORMALIZE, ROOT))) == 4);
    assert(kind(other_of(OK(cc_instr_eta(k, add)))) == CC_LAM);
    assert(kind(other_of(OK(cc_instr_eta(k, loop)))) == CC_PLAM);
    cc_judgement_id lifted = OK(cc_instr_lift(k, nat, OK(cc_instr_universe(k, level(0, 1)))));
    assert(kind(type_of(lifted)) == CC_U);
    REJECT(lift, "not included", 0, 0, 0, zero, OK(cc_instr_universe(k, level(0, 0))));

    /* Universes at levels (G0 §2.5, and acceptance cases L16-L19, L26, L27).
     * A universe's level is its child, in normal form, so universes at equal
     * levels are one term; cumulativity crosses tiers. */
    cc_term one = level(0, 1), omega = level(1, 0);
    cc_term max_one = cc_kernel_term(k, CC_LMAX, 0, one, level(0, 0), 0, 0);
    cc_judgement_id u1 = OK(cc_instr_universe(k, one));
    assert(term_of(OK(cc_instr_universe(k, max_one))) == term_of(u1));
    assert(child(type_of(u1), 0) == level(0, 2));
    cc_judgement_id uu0 = OK(cc_instr_universe(k, omega));
    assert(child(type_of(uu0), 0) == level(1, 1));
    assert(kind(type_of(OK(cc_instr_lift(k, u1, OK(cc_instr_universe(k, level(1, 3))))))) == CC_U);
    OK(cc_instr_lift(k, nat, uu0));
    rejects(cc_instr_lift(k, uu0, OK(cc_instr_universe(k, level(0, 5)))), "not included");
    OK(cc_instr_universe(k, level(0, CC_LEVEL_MAX - 1)));
    rejects(cc_instr_universe(k, level(0, CC_LEVEL_MAX)), "bound");
    OK(cc_instr_universe(k, level(1, CC_LEVEL_MAX - 1)));
    rejects(cc_instr_universe(k, level(1, CC_LEVEL_MAX)), "bound");
    OK(cc_instr_universe(k, level(CC_TIER_MAX, 0)));
    rejects(cc_instr_universe(k, level(CC_TIER_MAX + 1, 0)), "bound");
    rejects(cc_instr_universe(k, cc_kernel_term(k, CC_VAR, 999, 0, 0, 0, 0)), "Unbound level variable");
    REJECT(universeEntry, "A term variable is not a level", 0, a, 0, 0);
    REJECT(universeTerm, "Expected a level", 0, 0, 0, nat);
    rejects(cc_instr_universe(k, cc_kernel_term(k, CC_LBOUND, 1, 0, 0, 0, 0)), "A bound is not a level");
    assert(!cc_kernel_term(k, CC_U, 3, 0, 0, 0, 0));
    rejects(0, "payload must be zero");

    /* The kernel's weak head normal form as a step, and the aids an untrusted
     * search may steer by: conversion as a query, and renaming. */
    cc_judgement_id head = STEP(OK(cc_instr_refl(k, four)), CC_STEP_WHNF, ROOT);
    assert(kind(other_of(head)) == CC_SUCC);
    assert(cc_kernel_convertible(k, term_of(four), other_of(head), 0));
    REJECT(convertible, "", 0, 0, 0, four, zero);
    assert(cc_kernel_rename(k, term_of(nv), false, N, M) == term_of(OK(cc_instr_variable(k, m))));
    /* Entries are found by symbol among many, and dimensions by index. */
    cc_entry_id many[400];
    for (uint32_t s = 0; s < 400; ++s) many[s] = OK(cc_instr_extend(k, nat, 1000 + s));
    for (uint32_t s = 0; s < 400; s += 37) assert(OK(cc_instr_extend(k, nat, 1000 + s)) == many[s]);
    /* The same name at the same type is the same entry, whatever derived the type. */
    cc_judgement_id nat_again = OK(cc_instr_side(k, OK(cc_instr_refl(k, nat)), 1));
    assert(nat_again != nat && OK(cc_instr_extend(k, nat_again, 1000)) == many[0]);
    REJECT(extend, "already names", 0, many[234], 0, OK(cc_instr_unit(k)));
    assert(OK(cc_instr_dimension(k, 1)) == j2);

    /* A rollback drops the judgements made since the checkpoint. */
    cc_kernel_checkpoint(k);
    cc_judgement_id scratch = OK(cc_instr_succ(k, numeral));
    cc_kernel_rollback(k);
    cc_judgement_info unused;
    assert(!cc_kernel_judgement(k, scratch, &unused) && cc_kernel_judgement(k, numeral, &unused));
    /* A truncated judgement's id is issued again, and never confused. */
    cc_judgement_id other = OK(cc_instr_succ(k, four));
    assert(other == scratch && info(other).premise[0] == four);
    cc_judgement_id repeated = OK(cc_instr_succ(k, numeral));
    assert(repeated != other && info(repeated).premise[0] == numeral);
    assert(OK(cc_instr_lookup(k, term_of(lt_succ))));

    cc_kernel_free(k);
    k = cc_kernel_new();
    assert(k);
    level_quantification();
    cc_kernel_free(k);
    puts("instruction tests passed");
    if (fixture_file) {
        int closed = fclose(fixture_file);
        assert(closed == 0);
    }
    return 0;
}

/* Universe-generic definitions: level entries and level quantification
 * (G0 §2.7), with the acceptance cases of §5.2-5.6 named by their IDs. */
static void level_quantification(void) {
    enum { X = 1, Y, Z, A, B, C, T, N, F, G, H, ID = 50, ENDO };
    cc_judgement_id nat = OK(cc_instr_nat(k));
    cc_entry_id x = OK(cc_instr_level(k, X)), y = OK(cc_instr_level(k, Y)), z = OK(cc_instr_level(k, Z));
    assert(OK(cc_instr_level(k, X)) == x);
    uint32_t symbol;
    cc_term bound;
    bool dimension;
    cc_judgement_id source;
    assert(cc_kernel_entry(k, x, &symbol, &bound, &dimension, &source) && symbol == X && !dimension && !source);
    assert(kind(bound) == CC_LBOUND);
    rejects(cc_instr_variable(k, x), "not a term");                                       /* B7 */
    REJECT(extend, "already names", 0, x, 0, nat);
    OK(cc_instr_extend(k, nat, N));
    REJECT(level, "already names", 0, OK(cc_instr_extend(k, nat, N)), 0, 0);
    rejects(cc_instr_universe(k, lvar(99)), "Unbound level variable");                   /* L18 */
    REJECT(universeEntry, "A term variable is not a level", 0, OK(cc_instr_extend(k, nat, N)), 0, 0);
    cc_judgement_id ux = OK(cc_instr_universe(k, lvar(X)));                               /* B9 */
    assert(child(type_of(ux), 0) == lsucc(lvar(X), 1) && context_size(ux) == 1);
    cc_judgement_id uy = OK(cc_instr_universe(k, lvar(Y)));
    cc_judgement_id uomega = OK(cc_instr_universe(k, level(1, 0)));

    /* Generic statements are types (§5.3). */
    cc_entry_id a = OK(cc_instr_extend(k, ux, A));
    cc_judgement_id endo_x = OK(cc_instr_pi(k, a, ux));
    cc_judgement_id endo = OK(cc_instr_level_pi(k, x, endo_x));                           /* G1 */
    assert(kind(term_of(endo)) == CC_LPI && child(type_of(endo), 0) == level(1, 0) && context_size(endo) == 0);
    OK(cc_instr_lift(k, endo, OK(cc_instr_universe(k, level(1, 1)))));
    rejects(cc_instr_lift(k, endo, OK(cc_instr_universe(k, lsucc(lvar(Y), 5)))), "not included"); /* G2 */
    assert(child(type_of(OK(cc_instr_level_pi(k, x, nat))), 0) == level(0, 0));          /* G3 */
    cc_judgement_id g4 = OK(cc_instr_level_pi(k, x, uy));                                 /* G4 */
    assert(child(type_of(g4), 0) == lsucc(lvar(Y), 1) && context_size(g4) == 1);
    cc_judgement_id g5 = OK(cc_instr_level_pi(k, x, OK(cc_instr_pi(k, a, uomega))));      /* G5 */
    assert(child(type_of(g5), 0) == level(1, 1));
    rejects(cc_instr_lift(k, g5, uomega), "not included");
    cc_judgement_id inner = OK(cc_instr_level_pi(k, z, OK(cc_instr_universe(k, lmax(lvar(X), lvar(Z))))));
    assert(child(type_of(OK(cc_instr_level_pi(k, x, inner))), 0) == level(1, 0));       /* G6 */
    cc_judgement_id endo_def = OK(cc_instr_define(k, ENDO, endo));                        /* G10 */
    assert(child(type_of(endo_def), 0) == level(1, 0));
    rejects(cc_instr_level_pi(k, a, ux), "Expected a level entry");
    rejects(cc_instr_pi(k, x, ux), "not a term");
    rejects(cc_instr_level_lambda(k, x, OK(cc_instr_variable(k, a))), "still depends");

    /* Cumulativity (§5.4). */
    OK(cc_instr_lift(k, nat, ux));                                                        /* C1 */
    OK(cc_instr_lift(k, ux, OK(cc_instr_universe(k, lmax(lsucc(lvar(X), 1), lvar(Y))))));  /* C2 */
    rejects(cc_instr_lift(k, ux, ux), "not included");                                    /* C3 */
    rejects(cc_instr_lift(k, ux, OK(cc_instr_universe(k, level(0, 1)))), "not included"); /* C4 */
    cc_judgement_id av = OK(cc_instr_variable(k, a));
    rejects(cc_instr_lift(k, av, OK(cc_instr_universe(k, level(0, 0)))), "not included"); /* C5 */
    cc_entry_id b = OK(cc_instr_extend(k, OK(cc_instr_universe(k, lmax(level(0, 1), lvar(X)))), B));
    cc_entry_id c = OK(cc_instr_extend(k, OK(cc_instr_universe(k, lsucc(lvar(X), 1))), C));
    OK(cc_instr_lift(k, OK(cc_instr_variable(k, b)), OK(cc_instr_universe(k, lsucc(lvar(X), 1)))));    /* C9 */
    rejects(cc_instr_lift(k, OK(cc_instr_variable(k, c)), OK(cc_instr_universe(k, lmax(level(0, 1), lvar(X))))), "not included");
    cc_judgement_id constant_nat = OK(cc_instr_level_lambda(k, x, nat));                  /* C11 */
    OK(cc_instr_lift(k, constant_nat, OK(cc_instr_level_pi(k, x, OK(cc_instr_universe(k, level(0, 1)))))));
    cc_entry_id f = OK(cc_instr_extend(k, OK(cc_instr_level_pi(k, x, ux)), F));           /* C13 */
    OK(cc_instr_lift(k, OK(cc_instr_variable(k, f)), OK(cc_instr_level_pi(k, y, OK(cc_instr_universe(k, lsucc(lvar(Y), 1)))))));
    cc_judgement_id raised = OK(cc_instr_level_pi(k, x, OK(cc_instr_universe(k, lsucc(lvar(X), 1)))));
    cc_entry_id g = OK(cc_instr_extend(k, raised, G));                                    /* C14 */
    rejects(cc_instr_lift(k, OK(cc_instr_variable(k, g)), OK(cc_instr_level_pi(k, y, uy))), "not included");
    OK(cc_instr_lift(k, ux, uomega));                                                     /* C15 */
    OK(cc_instr_lift(k, OK(cc_instr_universe(k, level(0, 5))), uomega));                  /* C16 */
    rejects(cc_instr_lift(k, uomega, OK(cc_instr_universe(k, level(0, 5)))), "not included");
    /* Bound names do not matter: λ (x < ω). U(x) converts along an equality
     * that starts at Π (y < ω). U(y + 1). */
    cc_judgement_id family = OK(cc_instr_level_lambda(k, x, ux));
    OK(cc_instr_convert(k, family, OK(cc_instr_refl(k, OK(cc_instr_level_pi(k, y, OK(cc_instr_universe(k, lsucc(lvar(Y), 1)))))))));

    /* Instantiation and substitution (§5.5), with id := λ (x < ω). λ (A : U(x)). λ (t : A). t. */
    cc_entry_id t = OK(cc_instr_extend(k, av, T));
    cc_judgement_id poly = OK(cc_instr_level_lambda(k, x, OK(cc_instr_lambda(k, a, OK(cc_instr_lambda(k, t, OK(cc_instr_variable(k, t))))))));
    cc_judgement_id id = OK(cc_instr_define(k, ID, poly));                                /* S1 */
    assert(kind(type_of(id)) == CC_LPI);
    cc_judgement_id zero = OK(cc_instr_zero(k));
    cc_judgement_id three = OK(cc_instr_succ(k, OK(cc_instr_succ(k, OK(cc_instr_succ(k, zero))))));
    cc_judgement_id id0 = OK(cc_instr_level_apply(k, id, level(0, 0)));                   /* S2 */
    cc_judgement_id applied = OK(cc_instr_apply(k, OK(cc_instr_apply(k, id0, nat)), three));
    assert(kind(type_of(applied)) == CC_NAT);
    assert(successors(other_of(STEP(OK(cc_instr_refl(k, applied)), CC_STEP_NORMALIZE, ROOT))) == 3);
    cc_judgement_id u0 = OK(cc_instr_universe(k, level(0, 0)));
    cc_judgement_id at_one = OK(cc_instr_apply(k, OK(cc_instr_apply(k, OK(cc_instr_level_apply(k, id, level(0, 1))), u0)), nat));
    assert(type_of(at_one) == term_of(u0));
    assert(kind(other_of(STEP(OK(cc_instr_refl(k, at_one)), CC_STEP_NORMALIZE, ROOT))) == CC_NAT);
    rejects(cc_instr_apply(k, id0, u0), "wrong type");                                    /* S3 */
    cc_judgement_id at_ux = OK(cc_instr_apply(k, OK(cc_instr_level_apply(k, id, lsucc(lvar(X), 1))), ux)); /* S4 */
    assert(kind(type_of(at_ux)) == CC_PI && context_size(at_ux) == 1);
    cc_judgement_id outer = OK(cc_instr_level_lambda(k, x, OK(cc_instr_level_lambda(k, y,
        OK(cc_instr_universe(k, lmax(lvar(X), lvar(Y))))))));                            /* S5 */
    cc_judgement_id at_y0 = OK(cc_instr_level_apply(k, OK(cc_instr_level_apply(k, outer, lvar(Y))), level(0, 0)));
    assert(context_size(at_y0) == 1 && child(type_of(at_y0), 0) == lsucc(lvar(Y), 1));
    cc_judgement_id reduced = STEP(STEP(OK(cc_instr_refl(k, at_y0)), CC_STEP_BETA, AT(0)), CC_STEP_BETA, ROOT);
    assert(other_of(reduced) == term_of(uy) && other_of(reduced) != term_of(u0));
    cc_judgement_id fv = OK(cc_instr_variable(k, f));                                     /* S7 */
    cc_judgement_id expanded = OK(cc_instr_eta(k, fv));
    assert(kind(other_of(expanded)) == CC_LLAM);
    assert(other_of(STEP(expanded, CC_STEP_WHNF, ROOT)) == term_of(fv));
    cc_judgement_id at_two = OK(cc_instr_level_apply(k, family, level(0, 2)));             /* S8 */
    assert(other_of(STEP(OK(cc_instr_refl(k, at_two)), CC_STEP_BETA, ROOT)) == term_of(OK(cc_instr_universe(k, level(0, 2)))));
    cc_judgement_id far = OK(cc_instr_level_lambda(k, x, OK(cc_instr_universe(k, lsucc(lvar(X), 65000)))));
    rejects(cc_instr_level_apply(k, far, level(0, 1000)), "bound");                       /* S9 */
    assert(term_of(OK(cc_instr_level_apply(k, id, lmax(level(0, 0), level(0, 0))))) == term_of(id0)); /* S11 */
    rejects(cc_instr_level_apply(k, id, level(1, 0)), "finite");                          /* S12 */
    rejects(cc_instr_level_apply(k, id, lmax(lvar(X), level(1, 0))), "finite");           /* S13 */
    REJECT(levelApplyTerm, "Expected a level", 0, 0, 0, id, nat);
    REJECT(apply, "Only a term of a Π type", 0, 0, 0, id, nat);
    rejects(cc_instr_level_apply(k, id0, level(0, 0)), "Only a term of a level Π");

    /* Composition at a level Π is pointwise (§2.11, K7):
     * h : Π (x < ω). Nat → Nat ⊢ comp^j (Π (x < ω). Nat → Nat) [i = 0 ↦ h] h. */
    cc_entry_id n = OK(cc_instr_extend(k, nat, N));
    cc_judgement_id generic = OK(cc_instr_level_pi(k, x, OK(cc_instr_pi(k, n, nat))));
    assert(child(type_of(generic), 0) == level(0, 0));
    cc_judgement_id hv = OK(cc_instr_variable(k, OK(cc_instr_extend(k, generic, H))));
    cc_formula face;
    cc_init(&face, CC_FACE);
    assert(cc_generator(&face, 0, false) == CC_OK);
    cc_formula_id i0 = cc_kernel_formula(k, &face);
    cc_clear(&face);
    cc_judgement_id box = OK(cc_instr_system(k, OK(cc_instr_dimension(k, 1)), generic, hv));
    cc_judgement_id composed = OK(cc_instr_comp(k, OK(cc_instr_system_tube(k, box, i0, hv, OK(cc_instr_refl(k, hv))))));
    cc_term pointwise = other_of(STEP(OK(cc_instr_refl(k, composed)), CC_STEP_WHNF, ROOT));
    assert(kind(pointwise) == CC_LLAM && kind(child(pointwise, 1)) == CC_COMP);
    assert(kind(child(child(pointwise, 1), 2)) == CC_LAPP);
}
