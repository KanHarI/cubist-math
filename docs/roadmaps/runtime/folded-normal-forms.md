# Folded normal forms: `!!` and `!!!`

Status: decided on 2026-10-23, as decision D1 of the
[rational normalization debugging plan](https://github.com/KanHarI/cubist-math/pull/302).
This note specifies the decision before evaluation changes, as the
[demand marks](evaluation-demand-marks.md) did for theirs. FN1 adds the
kernel query; FN2 makes `!!` compute it and adds `!!!` for the full normal
form.

## The problem

A full normal form unfolds every definition it meets
(`weak`, `kernel/src/term_normalize.c:41-45`). Data is not the problem:
closed data computes to constructors either way. Proofs are. A proof that
stays stuck under a binder, such as the certificate of a rational literal,
`fun p => …quotient_effective(…, p)…`, is unfolded lemma by lemma into the
normal form of every lemma it uses, instantiated at every use. On main:

| Query | Full normal form |
| --- | ---: |
| `prop_type_is_set(U0)` | 68,490,929 ticks, 1,034,925 nodes |
| `integers.additive_` | 73,159,138 ticks, 1,799,676 nodes |
| `rationals.(2/3)` | 70,301,825 ticks, 1,116,794 nodes |
| the small inverse `q_inv(2/3)` | 70,725,782 ticks, 1,149,838 nodes |
| the open inverse `q_inv(…)` | `K344` at 80,182,616 ticks |
| the wide inverse | `K337` at 393,274,446 ticks |

Since the demand marks, `evaluate e;`, printing and patterns compute only
what they show or observe. What still computes a full normal form is
`expecting !!_` and a `!!` part of a pattern
(`web/translator/evaluation.mjs:230-233`), an exact expected value, on both
sides (`web/translator/translate.mjs:396` and `:417`),
`print(evaluate(!!e))` and `witness` (`translate.mjs:467`), and the views
that normalize a declaration on request (`translate.mjs:847`,
`web/cubical-program.mjs:703`, `web/cubical-workbench-session.mjs:142`).
Each prints the proof in full, or fails on its size.

## The folded normal form

The folded normal form of a term is its normal form, except where a
definition stays as it was written:

1. The term asked for is reduced to its weak head, unfolding whatever
   definitions that takes, and its parts are taken in turn.
2. A part is reduced to its weak head as well, remembering the first
   definition, applied or projected, that the reduction passes through.
3. If that head is **data**, the part is computed: a constructor applied, a
   pair, an injection, a point, a glued element, or a variable applied or
   projected. Its parts are taken in turn.
4. Otherwise, if the reduction passed through a definition, the part is
   that definition, applied or projected as written, with its arguments'
   folded normal forms: a function, a path, a type, or an eliminator or
   composition stuck on a variable is not unfolded.
5. A part that reached its head through no definition is taken in turn,
   as in the full normal form. A stuck head, an eliminator or composition
   that does not compute, that its last step rebuilt in place is taken as
   that step's term: the head holds its stuck parts reduced,
   `unitrec(…, abort(…))` where the term had `unitrec(…, stuck(x))`, and the
   term keeps them as written, so they fold. A head the step computed, as a
   transport of a path constructor computes a formal composition, is taken
   as computed.
6. Only eta contracts a whole once its parts are folded; reducing it again
   would unfold what was folded.

Only the reduction's own steps are watched, not those that compute a head
for one of them. `(λ y. f(y))(x)` is `f(x)`, but the head of `λ y. f(y)` is
`f` by eta, so the reduction reaches `f`'s body without passing through
`f(x)`, and nothing is folded there; the result is unfolded, not wrong.

So closed data computes in full, as it always did, and proofs stay named.
`rationals.(2/3)` is
`class((class((unat.(2), unat.(0))), class((unat.(3), unat.(0))), int_succ_nonzero(unat.(2))))`,
and `prop_type_is_set(U0)` is `fun (x, y : Prop(U0)) => retract_has_level(…)`,
its lemmas named, in 100 nodes.

Its properties, which FN1's tests state:

- It is convertible with the term: every step is a reduction, and a folded
  definition is its own unfolding. A check that compares folded normal forms
  by conversion answers as one comparing full ones.
- Closed data is the same as in the full normal form. A constructor's sort
  annotation is a type, and a function in it, such as a quotient's relation,
  stays folded.
- It does not depend on what was computed before: the reduction that finds
  the definition to fold reads no cache, and folding twice gives the same
  term.
- It certifies nothing. Like the full normal form, it is an inspection
  query on a term an instruction derived, and no instruction's acceptance
  depends on it.

## The marks

| Mark | Computes | Kernel query |
| --- | --- | --- |
| `!` | the weak head | `cc_kernel_whnf` |
| `!!` | the folded normal form | `cc_kernel_normalize_folded` (FN1) |
| `!!!` | the full normal form | `cc_kernel_normalize` |

`!!!` is read wherever `!!` is: right after `evaluate`, at the start of a
part of an expected pattern, and in `print(evaluate(!!!e))`. An exact
expected value, `witness`, and the views that normalize on request compute
the folded normal form. Step's `CC_STEP_NORMALIZE`
(`kernel/src/instruction_equality.c:270-271`) and the diagnostic probes keep
the full one: what a Step instruction accepts does not change.

## Measurements

A prototype of FN1's query, on 2026-10-23 with main `41d507a0`'s library,
in the debugging plan's fixtures, each query in a fresh program:

| Query | Full normal form | Folded normal form |
| --- | ---: | ---: |
| `prop_type_is_set(U0)` | 68,490,929 ticks, 1,034,925 nodes | 4,696 ticks, 100 nodes |
| `integers.additive_` | 73,159,138 ticks, 1,799,676 nodes | 45,542 ticks, 1,139 nodes |
| `integers.add_assoc` | 57,719,427 ticks, 1,460,386 nodes | 45,034 ticks, 507 nodes |
| `rationals.(2/3)` | 70,301,825 ticks, 1,116,794 nodes | 43,932 ticks, 936 nodes |
| `bint_mul` | 3,694,818 ticks, 96,657 nodes | 15,332 ticks, 400 nodes |
| the small inverse | 70,725,782 ticks, 1,149,838 nodes | 65,051 ticks, 979 nodes |
| the open inverse | `K344` at 80,182,616 ticks | 173,391 ticks, 981 nodes |
| the wide inverse | `K337` at 393,274,446 ticks | 1,423,460 ticks, 1,103 nodes |

The full normal forms are unchanged by the prototype, tick for tick.

## Decisions

Recommended, and taken unless the user changes them:

1. **Data is what computes.** The heads listed in rule 3. A record of a
   theory, such as `integers`, is a pair, so it is computed into its fields,
   each of which folds.
2. **The term asked for is always unfolded.** `!!` on `integers.add_assoc`
   shows its proof's outermost structure, with the lemmas it applies
   folded, not the name back.
3. **A formal composition is not data.** A definition whose head is a
   composition, even one of a higher inductive type, stays folded; the
   demand marks already show such a part as `<composition>`.
4. **Exact expected values compare folded normal forms by conversion**, as
   they compared full ones. The answer is the same, since both are
   convertible with the terms.
5. **The evaluation baseline's `-normal` workloads move to `!!!_`**, so
   that they keep measuring the full normal form, which the runtime
   roadmap's evaluator gates measure.

## Work

- **FN1. The kernel query.** `cc_kernel_normalize_folded` in
  `kernel/src/term_normalize.c`, sharing the full normalizer's explicit
  stack, with a cache of its own that every checkpoint clears, and its
  bridge export. Native tests: closed data equal to the full normal form, a
  stuck definition folded with its arguments folded, the term asked for
  unfolded, a definition reached through a beta step folded, eta, budget and
  deadline, rollback and commit, and the full normal form unchanged. The
  kernel reference chapter on normalization documents it.
- **FN2. The marks.** `!!` computes the folded normal form; `!!!` is lexed,
  parsed, formatted and linted as `!!` is and computes the full one. Exact
  expected values, `witness` and the normalizing views compute the folded
  normal form. The language reference, the error reference (E485 names
  both), the demand marks note and the runtime roadmap's stage 4 say so.
  The baseline's `-normal` workloads move to `!!!_`, and the corpus test
  covers the constructs whose full normal forms it leaves out under `!!_`.

**Acceptance.** The measurements above, re-measured with FN1 and recorded
in FN2; every contract and Cubist test passing; the evaluation baseline's
counters unchanged for every workload but those whose mark changed; and
#283's binary-rational contracts re-run on top, with its three bare
`expecting _;` lines rebased.
