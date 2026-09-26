/* The instruction kernel derives add, lt and lt_succ forward, as THTH did:
 * every rule application is an instruction, and every reduction is named
 * and placed. The term checker then accepts what the instructions defined. */
#include "cubical_kernel.h"
#include <assert.h>
#include <stdio.h>
#include <string.h>

static cc_kernel *k;

static uint32_t ok(uint32_t id, const char *what, int line) {
    if (!id) {
        fprintf(stderr, "line %d: %s: %s\n", line, what, cc_kernel_error(k));
        assert(0);
    }
    return id;
}
#define OK(x) ok((x), #x, __LINE__)

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

/* Contract one redex of side 1 of an equality, at a position. */
#define AT(...) (const uint8_t[]){__VA_ARGS__}, sizeof((uint8_t[]){__VA_ARGS__})
#define STEP(eq, rule, ...) OK(cc_instr_step(k, (eq), 1, __VA_ARGS__, (rule)))
#define ROOT NULL, 0

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

int main(void) {
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
    rejects(cc_instr_replace(k, OK(cc_instr_refl(k, statement)), 1, AT(0), unfolded), "not the equality's left side");

    /* The term checker's definitions are not admitted: Lookup refuses them. */
    cc_term raw_nat = cc_kernel_term(k, CC_NAT, 0, 0, 0, 0, 0);
    cc_term unadmitted = cc_kernel_define(k, 103, cc_kernel_term(k, CC_LAM, W, raw_nat, cc_kernel_term(k, CC_VAR, W, 0, 0, 0, 0), 0, 0), 0);
    assert(unadmitted);
    rejects(cc_instr_lookup(k, unadmitted), "admitted by Define");
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
    rejects(cc_instr_replace(k, identity_value, 1, AT(1), OK(cc_instr_refl(k, OK(cc_instr_variable(k, w))))), "different types");

    /* An entry cannot be discharged while another depends on it. */
    cc_judgement_id loop_type = OK(cc_instr_path(k, i, nat, nv, nv));
    cc_entry_id q = OK(cc_instr_extend(k, loop_type, Q));
    rejects(cc_instr_lambda(k, n, OK(cc_instr_variable(k, q))), "still depends");
    rejects(cc_instr_extend(k, OK(cc_instr_unit(k)), N), "already names");

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
    rejects(cc_instr_step(k, four, 1, ROOT, CC_STEP_NORMALIZE), "sides");
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
    rejects(cc_instr_comp(k, overlapping), "agree with the tubes it overlaps");
    rejects(cc_instr_system_tube(k, overlapping, never, OK(cc_instr_unit(k)), 0), "agree with the tubes it overlaps");
    rejects(cc_instr_system_overlap(k, overlapping, 2, stay), "does not overlap");
    rejects(cc_instr_system_overlap(k, overlapping, 0, OK(cc_instr_refl(k, OK(cc_instr_variable(k, m))))),
            "does not start at the last tube");
    cc_judgement_id agreed = OK(cc_instr_system_overlap(k, overlapping, 0, stay));
    rejects(cc_instr_system_overlap(k, agreed, 0, stay), "already agrees");
    agreed = OK(cc_instr_system_overlap(k, agreed, 1, stay));
    /* A tube on the face 0 is never used: any typing judgement will do. */
    rejects(cc_instr_system_tube(k, agreed, never, OK(cc_instr_unit(k)), stay), "takes no equality");
    agreed = OK(cc_instr_system_tube(k, agreed, never, OK(cc_instr_unit(k)), 0));
    cc_judgement_id full = OK(cc_instr_comp(k, agreed));
    assert(cc_kernel_check_in_cube(k, term_of(full), type_of(full), (cc_assumption[]){{N, type_of(nv)}}, 1, 1, &checked));
    assert(other_of(STEP(OK(cc_instr_refl(k, full)), CC_STEP_FACE, ROOT)) == term_of(nv));
    rejects(cc_instr_step(k, system, 0, ROOT, CC_STEP_NORMALIZE), "closed by Comp");
    cc_judgement_id composed = OK(cc_instr_comp(k, system));
    assert(kind(term_of(composed)) == CC_COMP && kind(type_of(composed)) == CC_NAT);
    /* The context is n and the face's dimension; the composition's is bound. */
    assert(context_size(composed) == 2);
    cc_assumption assumptions[] = {{N, type_of(nv)}};
    assert(cc_kernel_check_in_cube(k, term_of(composed), type_of(composed), assumptions, 1, 1, &checked));
    rejects(cc_instr_system(k, i, nat, OK(cc_instr_path_apply(k, loop, i, 0))), "may not use its dimension");
    /* At i = 1 the face i = 1 holds: a face step gives that tube at the end. */
    rejects(cc_instr_step(k, OK(cc_instr_refl(k, composed)), 1, ROOT, CC_STEP_FACE), "face that holds");
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
    rejects(cc_instr_pushout(k, unit_type, nat, nat, zero), "maps of a pushout");
    cc_judgement_id pushout = OK(cc_instr_pushout(k, unit_type, nat, nat, maps));
    assert(kind(term_of(pushout)) == CC_PUSHOUT && kind(type_of(pushout)) == CC_U);
    cc_judgement_id inl = OK(cc_instr_push_point(k, pushout, zero, false));
    assert(kind(term_of(inl)) == CC_PUSH_LEFT && type_of(inl) == term_of(pushout));
    rejects(cc_instr_push_point(k, pushout, OK(cc_instr_point(k)), true), "wrong type");
    rejects(cc_instr_push_point(k, nat, zero, false), "pushout type");
    cc_init(&formula, CC_INTERVAL);
    assert(cc_generator(&formula, 0, true) == CC_OK);
    cc_formula_id along = cc_kernel_formula(k, &formula);
    cc_clear(&formula);
    cc_judgement_id push = OK(cc_instr_push_path(k, pushout, OK(cc_instr_point(k)), along));
    assert(context_size(push) == 1 && kind(term_of(push)) == CC_PUSH_PATH);
    cc_judgement_id at_start = OK(cc_instr_endpoint(k, push, i, 0));
    assert(kind(other_of(STEP(OK(cc_instr_refl(k, at_start)), CC_STEP_IOTA, ROOT))) == CC_PUSH_LEFT);
    rejects(cc_instr_step(k, OK(cc_instr_refl(k, push)), 1, ROOT, CC_STEP_IOTA), "Iota needs");
    /* Homogeneous composition, over the pushout; not over Nat. */
    cc_judgement_id box = OK(cc_instr_system(k, j2, pushout, inl));
    box = OK(cc_instr_system_tube(k, box, faces[0], inl, OK(cc_instr_refl(k, inl))));
    cc_judgement_id hcomp = OK(cc_instr_hcomp(k, box));
    assert(kind(term_of(hcomp)) == CC_HCOMP && type_of(hcomp) == term_of(pushout));
    rejects(cc_instr_hcomp(k, system), "pushout types");
    /* Transport along a constant family: its tubes are the base on each clause. */
    cc_judgement_id moved = OK(cc_instr_trans(k, box, faces[0]));
    assert(kind(term_of(moved)) == CC_TRANS && type_of(moved) == term_of(pushout));
    rejects(cc_instr_trans(k, box, faces[1]), "clauses, in order");
    cc_judgement_id still = OK(cc_instr_system_tube(k, OK(cc_instr_system(k, j2, pushout, inl)), always, inl,
                                                     OK(cc_instr_refl(k, inl))));
    cc_judgement_id unmoved = OK(cc_instr_trans(k, still, always));
    assert(other_of(STEP(OK(cc_instr_refl(k, unmoved)), CC_STEP_FACE, ROOT)) == term_of(inl));

    /* Glue over Nat with a piece on the face 0, which is never used: a Glue
     * term of it, and unglue. An equivalence must be one, of the stated type. */
    cc_judgement_id glue_system = OK(cc_instr_glue_base(k, nat));
    rejects(cc_instr_glue_base(k, zero), "Expected a type");
    rejects(cc_instr_glue_piece(k, glue_system, faces[0], unit_type, zero), "equivalence is not");
    rejects(cc_instr_glue(k, OK(cc_instr_system(k, j2, nat, zero))), "Not a Glue type");
    glue_system = OK(cc_instr_glue_piece(k, glue_system, never, unit_type, zero));
    cc_judgement_id glued = OK(cc_instr_glue(k, glue_system));
    assert(kind(term_of(glued)) == CC_GLUE && kind(type_of(glued)) == CC_U);
    rejects(cc_instr_glue_term_base(k, nat, zero), "needs a Glue type");
    cc_judgement_id glue_value = OK(cc_instr_glue_term_base(k, glued, zero));
    rejects(cc_instr_glue_term(k, glue_value), "value for every piece");
    glue_value = OK(cc_instr_glue_term_piece(k, glue_value, OK(cc_instr_point(k)), 0));
    cc_judgement_id element = OK(cc_instr_glue_term(k, glue_value));
    assert(kind(term_of(element)) == CC_GLUE_TERM && type_of(element) == term_of(glued));
    assert(cc_kernel_check(k, term_of(element), type_of(element), NULL, 0, &checked));
    assert(type_of(OK(cc_instr_unglue(k, element))) == term_of(nat));
    rejects(cc_instr_unglue(k, zero), "Glue type");

    /* The W type of trees with Unit many children at each label: W(x : Unit). Unit.
     * A tree whose children are one tree, and W recursion computing on sup. */
    cc_judgement_id trees = OK(cc_instr_w(k, u0, unit_type));
    assert(kind(term_of(trees)) == CC_W && kind(type_of(trees)) == CC_U);
    cc_judgement_id tt = OK(cc_instr_point(k));
    assert(kind(term_of(OK(cc_instr_family(k, trees, tt)))) == CC_UNIT);
    cc_entry_id sub = OK(cc_instr_extend(k, trees, 32));
    cc_entry_id slot = OK(cc_instr_extend(k, unit_type, 33));
    cc_judgement_id only = OK(cc_instr_lambda(k, slot, OK(cc_instr_variable(k, sub))));
    rejects(cc_instr_sup(k, trees, zero, only), "label has the wrong type");
    rejects(cc_instr_sup(k, nat, tt, only), "W type");
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
    rejects(cc_instr_w_elim(k, count, zero, node), "step has the wrong type");
    cc_judgement_id recursion_w = OK(cc_instr_w_elim(k, count, step_case, node));
    assert(kind(term_of(recursion_w)) == CC_WREC);
    assert(kind(other_of(STEP(OK(cc_instr_refl(k, recursion_w)), CC_STEP_IOTA, ROOT))) == CC_APP);

    /* Mismatches are reported with both types. */
    cc_term found, wanted;
    assert(!cc_instr_apply(k, add, OK(cc_instr_variable(k, w))));
    assert(cc_kernel_error_kind(k) == CC_ERROR_MISMATCH && cc_kernel_mismatch(k, &found, &wanted));
    assert(kind(found) == CC_UNIT && kind(wanted) == CC_NAT);
    cc_kernel_clear_error(k);
    rejects(cc_instr_step(k, OK(cc_instr_refl(k, nv)), 0, ROOT, CC_STEP_BETA), "Beta needs");
    rejects(cc_instr_define(k, 104, nv), "closed");

    /* Normalization, eta and cumulativity. */
    assert(successors(other_of(STEP(OK(cc_instr_refl(k, four)), CC_STEP_NORMALIZE, ROOT))) == 4);
    assert(kind(other_of(OK(cc_instr_eta(k, add)))) == CC_LAM);
    assert(kind(other_of(OK(cc_instr_eta(k, loop)))) == CC_PLAM);
    cc_judgement_id lifted = OK(cc_instr_lift(k, nat, OK(cc_instr_universe(k, 1))));
    assert(kind(type_of(lifted)) == CC_U);
    rejects(cc_instr_lift(k, zero, OK(cc_instr_universe(k, 0))), "not included");

    /* The kernel's weak head normal form as a step, and the aids an untrusted
     * search may steer by: conversion as a query, and renaming. */
    cc_judgement_id head = STEP(OK(cc_instr_refl(k, four)), CC_STEP_WHNF, ROOT);
    assert(kind(other_of(head)) == CC_SUCC);
    assert(cc_kernel_convertible(k, term_of(four), other_of(head), 0));
    assert(!cc_kernel_convertible(k, term_of(four), term_of(zero), 0) && !cc_kernel_error(k)[0]);
    assert(cc_kernel_rename(k, term_of(nv), false, N, M) == term_of(OK(cc_instr_variable(k, m))));
    /* Entries are found by symbol among many, and dimensions by index. */
    cc_entry_id many[400];
    for (uint32_t s = 0; s < 400; ++s) many[s] = OK(cc_instr_extend(k, nat, 1000 + s));
    for (uint32_t s = 0; s < 400; s += 37) assert(OK(cc_instr_extend(k, nat, 1000 + s)) == many[s]);
    /* The same name at the same type is the same entry, whatever derived the type. */
    cc_judgement_id nat_again = OK(cc_instr_side(k, OK(cc_instr_refl(k, nat)), 1));
    assert(nat_again != nat && OK(cc_instr_extend(k, nat_again, 1000)) == many[0]);
    rejects(cc_instr_extend(k, OK(cc_instr_unit(k)), 1234), "already names");
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
    puts("instruction tests passed");
    return 0;
}
