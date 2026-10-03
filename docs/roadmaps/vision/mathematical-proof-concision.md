# Mathematical proof concision

Status: design direction and proposed acceptance criteria, recorded on
2026-09-28. Archive evidence was inspected on `h1-signatures` at `e7bdae5`;
the implementation baseline is the one reviewed in the
[work-plan audit](../audits/2026-09-28-audit.md). The
[work plan](../work-plan.md) remains the scheduling authority.

## Goal

The eventual formal language should let mathematical code follow the
thinking process and written argument of a mathematician as closely as
possible. Its source should express the mathematical objects, decisions,
hypotheses and inferences at the level at which the argument is understood.
The elaborator should construct the routine proof machinery connecting
those steps.

This is a requirement on the final language design. Implementation order
should support that design; immediate improvements alone do not establish
that the language has reached it.

Formalizers can reasonably be expected to understand and specify that:

- a group has a carrier;
- a subgroup element is mapped into the ambient group;
- integers enter rational or real expressions through selected maps;
- multiplication belongs to a particular structure;
- parameters remain fixed throughout a section.

Those mathematical commitments are welcome. The concern is unnecessary
repetition and manual proof assembly: repeatedly supplying the same
environment, spelling out every congruence and transport, restating an
induction motive, or constructing routine evidence that a proposition is a
proposition.

**Target:** each source step should communicate a meaningful mathematical
move. The source should expose decisions such as a common refinement or an
induction generalization while allowing their routine consequences to be
constructed automatically and checked.

## Evidence from the first library

The archived Galois and contour developments provide acceptance material.
Their length alone does not measure the current language: some proofs
predate capabilities that already shorten them. Each example below
distinguishes that case from remaining work.

### Galois: evaluate a relation at one

In `distinct_embeddings_two_independent` in
[artin_hom_independence.cubist](../../../archive/first-library/artin_hom_independence.cubist),
the `sumZero` block at lines 42–69 takes 28 lines. Its argument is:

> Evaluate the coefficient relation at one, use that both embeddings
> preserve one, and simplify multiplication by one.

The archive constructs this equality with nested `trans`, `sym` and `cong`.
The following four-line replacement uses current syntax:

```text
have sumZero : field_add(L, a, b) = field_zero(L) {
  simpa only [f1, g1, scalar_mul_one_right(L, a), scalar_mul_one_right(L, b)]
    using relation(field_one(K));
}
```

On 2026-09-28 this replacement was checked in memory with `CubicalProgram`
and the archive source resolver. Both declarations in the transformed
module verified, with no gaps. No archive file was changed. This was a
module-checking probe; a separate migration comparison of public types and
assumptions was not run.

The field, embeddings and selected laws remain explicit. This example
requires adoption of existing simplification facilities.

### Galois: existence and induction

In [artin_degree.cubist](../../../archive/first-library/artin_degree.cubist),
lines 88–99 give the substantive argument: take the evaluation basis,
deduce spanning, and obtain finite dimensionality and its bound. Lines
101–116 then assemble `mere_eliminate` and the evidence that its result
type is a proposition. This is repeated logical machinery around a clear
mathematical argument.

The language should support scoped elimination of mere existence and
construct the required propositionhood evidence from checked closure
lemmas. Its witness must remain within the permitted scope. The distinction
between mere existence and computational data remains part of the language.

In
[artin_evaluation_basis.cubist](../../../archive/first-library/artin_evaluation_basis.cubist),
`embedding_evaluation_frame_build` at lines 67–80 repeats a full induction
motive and parameter types; its step helper repeats the induction
hypothesis's signature. The recursive call at line 49 changes another
argument to `succ(m)`. An adequate induction interface must therefore
support explicit generalization and changing arguments. The experimental
H1 recursion fragment, which keeps other arguments fixed, does not yet
cover this pattern.

### Contour integration: additivity

The proof body of `affine_dyadic_integral_add` in
[affine_integral_linearity.cubist](../../../archive/first-library/affine_integral_linearity.cubist),
lines 117–182, takes 66 lines, excluding the theorem's statement and
parameter list. Its main mathematical steps are:

1. Finite contour sums distribute over addition.
2. Convergence of the two sequences gives convergence of their sum.
3. Pointwise equality of the sequences and uniqueness of limits identify
   the result with the integral of the sum.

The source repeatedly supplies the field environment, defines intermediate
sequences and values, and constructs the pointwise equality witness.
The continuity hypotheses and the construction of continuity for the sum
are genuine prerequisites. They must remain accounted for in a shorter
proof.

The related
[affine_integrals.cubist](../../../archive/first-library/affine_integrals.cubist)
defines the integral value and its convergence certificate as projections
of one construction, repeating their common parameters. Shared explicit
contexts and a named interface can remove that repetition. Pair
projections `.1` and `.2` already exist; better use of them is a library
design task.

### Contour integration: a common refinement

In
[complex_refinement_cauchy.cubist](../../../archive/first-library/complex_refinement_cauchy.cubist),
`complex_cauchy_from_refinements` at lines 84–119 argues as follows:

1. Pick the refinement bound for half the tolerance.
2. Compare levels `m` and `n` through the common later level `m + n`.
3. Reverse the second comparison and apply the triangle inequality.
4. Simplify the sum of the two half tolerances.

The source explicitly writes dependent families to transport along
`n + m = m + n` and the half-tolerance identity. Rewriting in hypotheses
and goals should generate those transports. The choice of `m + n`, the
half tolerance, and the resulting bound should remain visible. Preserve
the constructed bound when shortening this proof.

For a simpler calculation,
[contour_sums.cubist](../../../archive/first-library/contour_sums.cubist),
lines 106–126, proves that a constant integrand has zero sum around a
closed contour by the chain
`sum = c * (last - first) = c * (first - first) = 0`.
Existing `calc`, `rw` and `simp` provide much of the needed support.

## Requirements for the eventual language

### 1. Proof blocks compose throughout expressions

Allow the same proof facilities inside induction and match branches, tuple
components, function arguments and local definitions. A short argument
should be expressible at the place where its result is needed.

`have`, `calc`, `simp`, goal-directed application and local witness handling
should share scope, goal reconstruction and diagnostics. Nested use must
preserve dependent variables and cubical face information. Requiring an
extra named helper solely to access a proof facility is avoidable overhead.

### 2. Construct routine arguments from the expected goal

Provide `apply` and `refine`, argument inference from known signatures and
expected conclusions, goal-derived induction, and extensionality using
selected checked lemmas.

Authors must be able to name the variables generalized during induction
and inspect the resulting hypothesis. Parameters determined by a selected
structure or theorem application should not need to be repeated. Decisions
left underdetermined by that information should produce local obligations.

Scoped witness elimination should use the h-level solver to establish its
side conditions. This is useful directly in the proof language, alongside
the more general [computation notation](../computation-notation-roadmap.md).

### 3. Rewrite through mathematical expressions

Support rewriting under binders, in dependent hypotheses and goals, and
through mathematical operators using checked congruence lemmas. Finite
sums, evaluation maps and linear combinations are concrete targets.

An author should be able to say that an embedding is applied to an
equation and simplify using its preservation laws. The elaborator should
assemble the pointwise congruence, extensionality and equality composition.
Dependent rewrites must reconstruct the affected context with explicit
checked transports.

For HoTT, the generated witnesses remain meaningful: use proved
propositionhood or setness where available, and preserve relevant path and
coherence data elsewhere.

### 4. Supply reusable methods for routine reasoning

Provide checked methods for algebraic normalization, elementary
inequalities, finite sums and routine logical consequences. Give library
authors a way to define reusable proof methods for their mathematical
interfaces, with visible remaining goals and bounded work.

The source can then name an algebraic or logical step while the method
constructs its proof. A ring method closes the corresponding algebraic
identity; convergence, continuity and other analytic premises still come
from the mathematical argument.

Automation belongs in the elaborator or checked library constructions.
Its output must pass the instruction kernel, retain its assumptions and
remain inspectable. The scope of a method should be clear from its selected
structure, rules and local context.

### 5. Design interfaces around reusable mathematical laws

Use shared, explicitly selected contexts and named structure fields.
Build interfaces that expose facts such as:

- homomorphisms preserve finite sums;
- linear maps preserve linear combinations;
- limits respect the relevant operations;
- structure equality follows from a supported extensionality principle;
- an integral construction supplies its value, convergence and uniqueness.

Prove general preservation and representation laws once and use them in
theorems. A helper earns its abstraction when it captures a reusable
mathematical fact or a clear subargument. Count the cost of introducing it
when evaluating the concision of a development.

### 6. Keep the mathematical argument readable

Concision should preserve the reason a proof works. The common refinement,
the induction invariant, the selected basis and the decisive theorem
applications should remain identifiable in the source.

Source token counts are useful evidence, but readable calculations and
well-named intermediate claims can justify extra lines. The target is a
compact mathematical argument whose routine implementation is generated.

## Relationship to the existing plan

H1–H3 expand the types and dependent constructions the language can express.
Proof concision also needs its own acceptance criteria across the
elaborator and mathematical interfaces. Kernel milestone completion alone
does not establish that the source can express an argument concisely.

Many of the mechanisms are already planned. Connect them through complete
proof examples and fill the remaining contracts:

| Requirement | Existing work and proposed addition |
| --- | --- |
| Composable proof blocks | Extend the shared goal layer, HoTT A5 / work-plan L1.2r, with an explicit contract for proofs inside arbitrary supported expression positions. |
| Application and argument inference | Ergonomics milestone 5 and L4.1a/b, L4.4; require representative theorem compositions with explicit structure selection. |
| Induction with generalization | Ergonomics milestone 7 and L2.2a; exercise a recursive call whose other argument changes, as in evaluation-frame construction. Indexed and companion motives retain their H2/H3 dependencies. |
| Witness elimination and routine side conditions | HoTT D0a/D1 and the h-level work; connect checked propositionhood evidence to scoped proof-language elimination. |
| Rewriting and extensionality | Build on HoTT A1/A2, B3, E1 and the ergonomics implementation plan. Add explicit contracts for rewriting under binders and through operators such as finite sums: A2 excludes binder bodies, and E1 does not supply general binder rewriting. |
| Shared environments and reusable laws | Theories in ergonomics milestone 6, the language feature proposal, and HoTT F1; require compact use of the resulting interfaces. |
| Domain proof methods | Specify supported algebraic/logical methods and a library extension mechanism; the planned path-algebra normalizers address a different class of goals. |

The [proof ergonomics roadmap](../proof-ergonomics-roadmap.md), its
[implementation plan](../proof-ergonomics-implementation-plan.md), and the
[HoTT automation roadmap](../hott-automation-roadmap.md) remain the homes of
their implementation details. This document proposes a common success
criterion for their eventual result. Focused archive fixtures fit the
current language work; broad mathematical development remains scheduled
by the work plan.

## Acceptance through complete proofs

Maintain a small corpus with a mathematical explanation beside each
formal proof. Begin with these cases:

| Case | What a concise proof must express |
| --- | --- |
| Two-embedding independence | Evaluate the relation at one; derive the cancellation argument; conclude both coefficients vanish. |
| Evaluation-frame construction | State the induction and generalized variables; extend the frame and use the appropriately specialized hypothesis. |
| Artin degree bound | Use an evaluation basis, derive spanning and the dimension bound; discharge propositionhood for witness elimination. |
| Constant closed contour sum | A short calculation using the sum formula, closedness and cancellation. |
| Integral additivity | Establish the required continuity, use finite-sum additivity and convergence, then uniqueness. |
| Cauchy from refinements | Take half the tolerance and the common refinement, then compose the two estimates and retain the bound. |

For each case:

1. **Hold the mathematical task fixed.** Record the statement, hypotheses,
   background results, assumptions, extension markers and computational
   outputs. Compare the English and formal versions under the same
   prerequisites.
2. **Separate costs.** Measure statements and shared setup, proof bodies,
   reusable library support, and helpers introduced specifically for the
   example. Include those helpers in the total.
3. **Check the whole result.** A short fragment is preliminary evidence.
   The complete module and relevant consumers must check; migrations must
   perform the appropriate public-type, dependency and computation checks.
4. **Measure implementation cost.** Record source tokens, checking work,
   generated proof size and failures under fixed budgets. Investigate a
   shorter proof that becomes substantially more expensive or brittle.
5. **Review the argument.** A reader should be able to identify the same
   mathematical steps and selected witnesses in both presentations.

Set numerical targets after establishing comparable full-proof baselines.
The verified 28-to-4-line example establishes a local improvement, not a
reduction factor for the whole Galois development.

The historical
[curated migration experiment](../../tactical/proof-ergonomics-handoff.md#curated-rwcalcsimp-pass-findings-stopped)
also cautions against a single percentage: it recorded about 23% fewer
tokens across 22 complex/analysis modules, and about 3% across 24
field/Galois/linear-algebra modules. That pass stopped unmerged on
2026-09-25, and some rewritten proofs checked more slowly. These are
historical measurements, not current corpus results.

## Changes this calls for

- Make complete mathematical arguments part of language acceptance,
  alongside small feature examples and kernel soundness obligations.
- Treat nested proof blocks, induction generalization and dependent
  rewriting as core language capabilities with shared semantics.
- Require the h-level and structure machinery to remove repeated proof
  obligations in actual source, beyond supplying callable lemmas.
- Plan reusable domain proof methods and mathematical interfaces together
  with the syntax that consumes them.
- Evaluate the eventual language by how clearly and concisely it expresses
  the argument, including the supporting material it requires.
