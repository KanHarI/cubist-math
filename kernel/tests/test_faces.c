/* Restrict and face entries (Γ, φ). A partial element on a face φ may use a
 * variable whose type mentions φ's dimensions: Endpoint cannot restrict it,
 * since the variable depends on them, and Restrict types it on φ, in the
 * context with φ's face entry. Only a partial element whose face implies φ
 * discharges the entry; no binder discharges a dimension it needs, and
 * Define refuses it. */
#include "cubical_kernel.h"
#include "term_internal.h"
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
static cc_judgement_id var(cc_entry_id e) { return OK(cc_instr_variable(k, e)); }

/* A face formula: the conjunction of dim = end for each pair, or with
 * `either`, their disjunction. */
static cc_formula_id face(size_t count, const unsigned (*equations)[2], bool either) {
    cc_formula f, g;
    cc_init(&f, CC_FACE);
    cc_init(&g, CC_FACE);
    assert((either ? cc_zero(&f) : cc_one(&f)) == CC_OK);
    for (size_t i = 0; i < count; ++i) {
        assert(cc_generator(&g, equations[i][0], equations[i][1]) == CC_OK);
        assert((either ? cc_join(&f, &f, &g) : cc_meet(&f, &f, &g)) == CC_OK);
    }
    cc_formula_id id = cc_kernel_formula(k, &f);
    cc_clear(&f);
    cc_clear(&g);
    return id;
}

/* The face entries of a judgement's context, as a count, and the last one. */
static size_t faces(cc_judgement_id j, cc_entry_id *last) {
    size_t count = 0;
    for (size_t index = 0;; ++index) {
        cc_entry_id entry = cc_kernel_judgement_context(k, j, index);
        if (!entry)
            return count;
        if (cc_kernel_entry_face(k, entry, NULL)) {
            ++count;
            if (last) *last = entry;
        }
    }
}

static void restricted_tubes(void) {
    k = cc_kernel_new();
    assert(k);
    cc_term l0 = cc_kernel_term(k, CC_LCONST, 0, 0, 0, 0, 0);
    cc_judgement_id u0 = OK(cc_instr_universe(k, l0));
    cc_entry_id a = OK(cc_instr_extend(k, u0, 100));
    cc_entry_id kd = OK(cc_instr_dimension(k, 0)), id = OK(cc_instr_dimension(k, 1)), jd = OK(cc_instr_dimension(k, 2));
    /* p : A = A in U0, and x : p @ k, a type that mentions k. */
    cc_judgement_id loop = OK(cc_instr_path(k, kd, u0, var(a), var(a)));
    cc_entry_id p = OK(cc_instr_extend(k, loop, 101));
    cc_judgement_id at_k = OK(cc_instr_path_apply(k, var(p), kd, 0));
    cc_entry_id x = OK(cc_instr_extend(k, at_k, 102));
    cc_judgement_id xv = var(x);
    cc_formula_id k0 = face(1, (const unsigned[][2]){{0, 0}}, false);

    /* comp^i (p @ k) [k = 0 ↦ x] x. The tube must be in the family on its
     * face, p @ 0; x is at p @ k, and Endpoint cannot restrict it, since x's
     * type needs k. */
    cc_judgement_id system = OK(cc_instr_system(k, id, at_k, xv));
    rejects(cc_instr_system_tube(k, system, k0, xv, OK(cc_instr_refl(k, xv))), "not in the family on its face");
    rejects(cc_instr_endpoint(k, xv, kd, 0), "still depends on the discharged entry");

    /* Restricted to k = 0, x is at p @ 0, in the context with the face entry. */
    cc_judgement_id on_face = OK(cc_instr_restrict(k, xv, k0));
    cc_entry_id assumption = 0;
    assert(info(on_face).term == info(xv).term && faces(on_face, &assumption) == 1);
    cc_clause clause = {0};
    assert(cc_kernel_entry_face(k, assumption, &clause) && clause.positive == 0 && clause.negative == 1);
    /* One face entry per clause. */
    cc_judgement_id again = OK(cc_instr_restrict(k, OK(cc_instr_variable(k, a)), k0));
    cc_entry_id same = 0;
    assert(faces(again, &same) == 1 && same == assumption);

    /* The tube on k = 0 discharges it: the composition holds with no face
     * entry, and binds as any term does. */
    cc_judgement_id tube = OK(cc_instr_system_tube(k, system, k0, on_face, OK(cc_instr_refl(k, on_face))));
    assert(faces(tube, NULL) == 0);
    cc_judgement_id comp = OK(cc_instr_comp(k, tube));
    assert(faces(comp, NULL) == 0 && info(comp).type == info(at_k).term);
    OK(cc_instr_path_lambda(k, kd, OK(cc_instr_lambda(k, x, comp))));

    /* With a tube on j = 0 first, x as it is, the two agree on the overlap
     * j = 0 ∧ k = 0: an equality there, restricted, which SystemOverlap
     * discharges with the tubes' own assumption. */
    cc_formula_id j0 = face(1, (const unsigned[][2]){{2, 0}}, false);
    cc_formula_id j0k0 = face(2, (const unsigned[][2]){{0, 0}, {2, 0}}, false);
    cc_judgement_id first = OK(cc_instr_system_tube(k, system, j0, xv, OK(cc_instr_refl(k, xv))));
    cc_judgement_id second = OK(cc_instr_system_tube(k, first, k0, on_face, OK(cc_instr_refl(k, on_face))));
    rejects(cc_instr_comp(k, second), "shown to agree");
    cc_judgement_id overlap = OK(cc_instr_restrict(k, xv, j0k0));
    cc_judgement_id agreed = OK(cc_instr_system_overlap(k, second, 0, OK(cc_instr_refl(k, overlap))));
    assert(faces(agreed, NULL) == 0 && faces(OK(cc_instr_comp(k, agreed)), NULL) == 0);

    /* A face entry is no variable, and no dimension. */
    rejects(cc_instr_variable(k, assumption), "A face entry is an assumption");
    rejects(cc_instr_path_lambda(k, assumption, xv), "A face entry is an assumption");

    /* While the face entry is there, no binder or endpoint discharges k, and
     * no definition is made: A on k = 0 is no line over k. */
    rejects(cc_instr_path_lambda(k, kd, again), "still depends on the discharged entry");
    rejects(cc_instr_endpoint(k, again, kd, 1), "still depends on the discharged entry");
    cc_judgement_id unit = OK(cc_instr_unit(k));
    OK(cc_instr_define(k, 103, unit));
    rejects(cc_instr_define(k, 104, OK(cc_instr_restrict(k, unit, k0))), "Only a closed judgement");

    /* A tube on a face that does not imply the assumption leaves it: x
     * restricted to k = 0 ∧ j = 1 is at p @ 0 as well, but the composition
     * on k = 0 then holds only where j = 1, and k stays bound to it. */
    cc_formula_id k0j1 = face(2, (const unsigned[][2]){{0, 0}, {2, 1}}, false);
    cc_judgement_id narrower = OK(cc_instr_restrict(k, xv, k0j1));
    cc_judgement_id kept = OK(cc_instr_comp(k, OK(cc_instr_system_tube(k, system, k0, narrower,
        OK(cc_instr_refl(k, narrower))))));
    assert(faces(kept, NULL) == 1);
    rejects(cc_instr_path_lambda(k, kd, OK(cc_instr_lambda(k, x, kept))), "still depends on the discharged entry");
    rejects(cc_instr_path_lambda(k, jd, OK(cc_instr_lambda(k, x, kept))), "still depends on the discharged entry");

    /* The face is one consistent clause with at least one equation. */
    const char *shape = "one consistent conjunction of endpoint equations";
    rejects(cc_instr_restrict(k, xv, face(0, NULL, false)), shape);
    rejects(cc_instr_restrict(k, xv, face(0, NULL, true)), shape);
    rejects(cc_instr_restrict(k, xv, face(2, (const unsigned[][2]){{0, 0}, {2, 1}}, true)), shape);
    cc_formula interval;
    cc_init(&interval, CC_INTERVAL);
    assert(cc_generator(&interval, 0, true) == CC_OK);
    rejects(cc_instr_restrict(k, xv, cc_kernel_formula(k, &interval)), shape);
    cc_clear(&interval);
    cc_kernel_free(k);
}

/* A variable typed only on a face cannot leave it: an entry extended at a
 * restricted type depends on the face entry, so no tube discharges the
 * face while the variable is free. */
static void variables_on_a_face(void) {
    k = cc_kernel_new();
    assert(k);
    cc_term l0 = cc_kernel_term(k, CC_LCONST, 0, 0, 0, 0, 0);
    cc_judgement_id u0 = OK(cc_instr_universe(k, l0));
    cc_entry_id a = OK(cc_instr_extend(k, u0, 100));
    cc_entry_id kd = OK(cc_instr_dimension(k, 0)), id = OK(cc_instr_dimension(k, 1));
    cc_judgement_id loop = OK(cc_instr_path(k, kd, u0, var(a), var(a)));
    cc_entry_id p = OK(cc_instr_extend(k, loop, 101));
    cc_judgement_id at_k = OK(cc_instr_path_apply(k, var(p), kd, 0));
    cc_formula_id k0 = face(1, (const unsigned[][2]){{0, 0}}, false);
    cc_judgement_id at_0 = OK(cc_instr_restrict(k, at_k, k0));
    /* y, w : p @ 0, types that hold only where k = 0, and z : p @ k. */
    cc_entry_id y = OK(cc_instr_extend(k, at_0, 102)), w = OK(cc_instr_extend(k, at_0, 103));
    cc_entry_id z = OK(cc_instr_extend(k, at_k, 104));
    cc_judgement_id yv = var(y), zv = var(z);
    assert(faces(yv, NULL) == 1);
    /* comp^i (p @ k) [k = 0 ↦ (λ w. z)(y)] z: the tube is z on the face, by
     * Beta, but it names y. */
    cc_judgement_id tube = OK(cc_instr_apply(k, OK(cc_instr_lambda(k, w, OK(cc_instr_restrict(k, zv, k0)))), yv));
    cc_judgement_id starts = OK(cc_instr_step(k, OK(cc_instr_refl(k, tube)), 1, NULL, 0, CC_STEP_BETA));
    cc_judgement_id system = OK(cc_instr_system(k, id, at_k, zv));
    rejects(cc_instr_system_tube(k, system, k0, tube, starts), "still depends on the discharged entry");
    /* With z itself as the tube, the same face entry is discharged. */
    cc_judgement_id own = OK(cc_instr_restrict(k, zv, k0));
    assert(faces(OK(cc_instr_system_tube(k, system, k0, own, OK(cc_instr_refl(k, own)))), NULL) == 0);
    cc_kernel_free(k);
}

int main(void) {
    restricted_tubes();
    variables_on_a_face();
    printf("face entries: ok\n");
    return 0;
}
