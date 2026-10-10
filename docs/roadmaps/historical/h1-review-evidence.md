# H1 review evidence: the mathematical items of the release checklist

Historical review record: the mathematical release decisions were completed
on 2026-10-02. The current [H1 specification](../h1-signature-specification.md)
and its linked model, canonicity and critical-pair arguments remain normative.

Status: gathered on 2026-09-29 at `0b775b1`, for work-plan K2.1's review;
K1 with tubes and K6 along `ua` traced since (PR #94), and K10 and K11
(PR #95).
Updated on 2026-09-30 with the [H2 case analysis and critical-pair
draft](h1-critical-pairs.md), including representative joins CP01–CP10
in the kernel. The maintainer approved it on 2026-09-30, after the CP01 and
CP07 regressions were strengthened (PR #103). The same day, the
[model construction](../h1-model.md) and the [canonicity argument](../h1-canonicity.md)
were written out as review drafts for items 1 and 3. Their first review
found three substantive issues, and both drafts were revised the same day.
The second review, on 2026-10-01 at `626138d`, accepted those revisions and
asked for three more repairs; the drafts were revised again (section 1 and
section 3 below), with two corrections to the model's spine rank after it.
The maintainer approved both on 2026-10-02.
This record serves the first three items of the
[H1 specification](../h1-signature-specification.md)'s release checklist, the
mathematical ones:

1. D1, D4 and D5 written out and reviewed (4.2, 4.3);
2. Lemma H2's full case analysis, and the critical-pair check of 3.7;
3. canonicity (4.4) reviewed, relative to the assumed baseline of 4.1.

For each it gives the claim, where its argument stands, what reviews have
found, the tests that exercise the behaviour the argument relies on, and what
a review decision still needs. As the specification's 4.5 says, the tests are
evidence for the specified behaviour, not for these claims. **Items 1, 2
and 3 are approved**, relative to the assumed baseline and premise P1. The checklist's other items are not
mathematical: the acceptance matrix (item 4, approved on 2026-10-02), a pinned run (item 5, [recorded at the release revision](h1-release-evidence.md) on 2026-10-02, and again on 2026-10-03 after the refactors of #120–#132) and the
differential fixtures (item 6, retired as a gate on 2026-10-02).

## Summary

| Item | Argument now | Mechanical evidence | Missing for a decision |
| --- | --- | --- | --- |
| D1, D4, D5: the model | [Construction written out](../h1-model.md), **approved on 2026-10-02**: raw trees, a weight by constructor index, carrier, Kan structure and eliminator; the weight revised after the first review, with telescope filling (M0, M4a) | Admission, boundaries and cube depth: A1–A17, N1–N6, R3, E3, K7 | None: approved on 2026-10-02 |
| Lemma H2 and 3.7's critical pairs | [Rule-by-rule case analysis and overlap table](../h1-critical-pairs.md), **approved on 2026-09-30** | CP01–CP10 representative joins; N3, N4, K4–K9 in part or in substance, E5, V11, V16; randomized K10 and K11 | None: approved on 2026-09-30 |
| Canonicity | [Huber's predicates extended, written out](../h1-canonicity.md), **approved on 2026-10-02**; revised after the first review: value clauses separated from expansion, stability, the revised weight, and C1 under computability hypotheses | Closed computations through declared types: E1, E2, K1, E5, T3, T4 | None: approved on 2026-10-02, with the baseline's canonicity an explicit assumption |

## 1. The model: D1, D4 and D5

**Claim.** Every admitted signature has a model: for fixed parameters and
recorded levels, a presheaf over cubes that contains only reduced forms, with
restriction, Kan structure and an eliminator that commute with restriction
(4.2). D1 is that the construction is uniform in the signature. D4 is its
well-foundedness when positions are paths at higher cubes of every depth, as
the squash of level `n` needs at depth `n + 1`. D5 is the same for
infinitary positions.

**Argument now.** Section 4.2 gives the construction in seven steps. Its
only signature-specific inputs are the constructor order (for restriction),
the cube boundary's typing (for overlapping faces) and positivity (for the
inductive definition). The [model construction](h1-model.md) writes these
steps out for every signature, and 4.3 marks D1, D4 and D5 written out and
approved on 2026-10-02. Before it, 4.3 marked them "Argued", each with an
open obligation to write it out. Consistency is relative to the baseline
model (step 7).

**Reviews so far.** The specification had four reviews before its approval
on 2026-09-27 (its "Revisions after review"). They corrected level erasure,
path abstraction in boundaries, hidden tier bounds and the tier walk's
coverage, and they marked D1, D4, D5 and Lemma H2 as open obligations. None
of them wrote out the construction. D2, D6 and D7 were found valid as
conditional outlines, and D3's local wall calculation was found valid.

The written-out [model](../h1-model.md) had its first review on 2026-09-30.
It found that M4's bound `‖T x‖ ≤ ‖x‖` fails: filling a path position
evaluates its endpoint expressions at moved data, and those trees can
outweigh every original position. The review's `pack`, over a pushout
whose connecting path goes to `loop`, gives a transported position of
weight `ω³ + ω²` above the original bound `ω³ + ω`. The draft was revised
the same day: a constructor now weighs the least multiple of `ω^k` above its
positions (M0), which absorbs everything earlier constructors build in its
block, and M4a fills the telescope with its dependent endpoints before M4
uses it. The canonicity draft's C2 inherited the problem and the fix.

The second review, on 2026-10-01, accepted the block weight and the
telescope filling, and requested changes before discharging the item. The
model's eliminator was defined by rank and typed afterwards, but a clause
needs typed recursive results before it applies, and restriction can raise
rank (its `wrap(edge)` example). Premise P1 left out function β at
positional arguments, and Theorem M did not state it as an assumption. The
draft now constructs `elim`, its typing and its naturality together by `μ`
(M6, with the bounded semantic Lemma H1 as M6a), measures by weight and
spine rank, a pair that restriction does not raise, states P1 as an existence claim with function β
and η and assumes it in Theorem M, and merges M5 into M4's induction with
uniformity and the constancy face.

**Literature, as the specification reads it (4.6).**
- Coquand, Huber and Mörtberg (LICS 2018) construct the cubical-set models
  of the examples, pushouts among them, and describe the
  pattern, without a general schema and its soundness proof.
- Cavallo and Harper (POPL 2019) give a general schema whose boundaries are
  constructor terms, with a computational semantics and canonicity, in
  Cartesian cubical computational type theory. It supports the schema's
  shape without covering the kernel's De Morgan rules.
- Lumsdaine and Shulman (2020) cover a general class, infinitary ones
  included, in model categories, a different setting.
- Kaposi and Kovács (LMCS 2020) give signatures for the whole H family; H1's
  signatures are a subclass.

No cited work covers this combination: De Morgan rules, a general schema,
cube positions of every depth and infinitary positions.

**Behaviour that the argument's premises rest on.** Admission decides
positivity and shape syntactically, as step 4 needs: A1–A17, traced in
`kernel/tests/test_signatures.c`. The cube boundary's typing and the
agreement of overlapping faces, step 3: N1–N4 there, N5 and N6 in source.
Cube positions at depth 8 with arity 64 are admitted within budget: R3.
Squash constructors, which need cube positions: E3 for `prop`, and K7 for a
set truncation's squash.

**Decision.** Approved on 2026-10-02: the [model construction](../h1-model.md)
for the whole schema, with the well-founded definition over cubes at every
depth (D4) and infinitary arities (D5), and the items its section 9 lists
for review, premise P1 among them.

## 2. Stability and confluence: Lemma H2 and section 3.7

**Claims.** Lemma H2: every rule of 3.3–3.7 commutes with substitution of
interval formulas for dimensions, and of level expressions for level
variables. Section 3.7, with 4.5: the generated rules are confluent with the
existing ones.

**Argument now.** The [critical-pair analysis](../h1-critical-pairs.md) writes
out Lemma H2 rule by rule and lists CP01–CP10 with their joins and kernel
tests, relative to baseline substitution and conversion. The maintainer
approved it on 2026-09-30. The rest of this section records the argument as
it stood before the analysis.
The specification's previous argument was that substitution preserves the redex
patterns, which are constructor heads, `hcomp`, transport and path
application. The side conditions that substitution can change, that a
formula is an endpoint and that a face holds, hand over to the boundary and
face rules. The correction walls of 3.5 are built to restrict to the
boundary. No reduction rule reads a level. Its open obligation is the full
case analysis, rule by rule, including 3.5's corrected transport under
substitution of formulas into `rs` and `φ`. Confluence is argued only at a
boundary, where `Iota` and the boundary rule meet: Lemma H1 makes them agree,
proved in outline and found valid as a conditional outline. The full
critical-pair check is open. D3's stability is Lemma H2's.

**Behaviour that exercises instances of the claims.**

| Case | What it checks | Where |
| --- | --- | --- |
| N3 | The torus's square restricted in either order reaches the same corner | Kernel |
| N4 | `loop @ (i ∧ j)` restricted to `j = 0` is `base`: a formula substituted into a constructor | Kernel |
| K4, in substance | `hcomp` whose tube's face holds gives the tube at `1`, in `Susp` | Kernel |
| K5, in substance | Transport of a constructor's argument along a line of types | Kernel |
| K6 | Transport of `merid(a) @ j` along a line of types, and along `ua` of the integers' successor: the hcomp of 3.5, which restricted to either end is the transported pole | Kernel; driver along `ua` |
| K7, in substance | The two-dimensional correction of 3.5, for a set truncation's squash | Kernel |
| K8 | Transport commutes with `hcomp` (3.5, case 3) | Kernel |
| K9, in substance | Composition along a constant line is `hcomp` of the moved base, in `Susp` | Kernel |
| E5 | The eliminator on `hcomp` is composition in the motive | Kernel and driver |
| V11 | A generic definition at `x + 1` leaves the instance unchanged, and `elim` on `point` reduces there | Source |
| V16 | Level substitution into `Trunc(U(x))` at `0`, convertible with its `Beta` reduct | Kernel |
| K10, in substance | For 96 random constructor terms of `Susp`, `Torus` and `Quotient` (its `cls` and `eq`), the path constructors at random formulas over two dimensions, moved along `e @ i`, its reversal or a constant line: at every face, the transport restricted, as it is and as its weak head, is the transport of the term restricted | Kernel |
| K11 | Along the constant lines: at φ = 1 the transport is the term, and where φ is a face, the generated rules' weak head restricted to it is the term there | Kernel |

**The property tests, and what is missing.** K10 and K11 are the specified
property tests for Lemma H2, traced since 2026-09-29 by
`transport_properties` in `kernel/tests/test_signatures.c`. K10 checks
`(transp u)[r_l = ε] ≡ transp(u[r_l = ε])`, where `r_l` is one of the
constructor's dimensions, as `r` in `merid(a) @ r` (2.5; 3.5, case 2), not a
parameter line: transport commutes with restriction to a constructor's face,
which 3.5's correction walls are built to ensure. Its lines are drawn from
three kinds rather than at random, and `Quotient` contributes its `cls` and
`eq` but not its squash, so the matrix traces it in substance. K11 checks
that transport along a constant line at `φ = 1` is the identity. Both are
evidence for the claims' instances, not proof of them. The new draft adds
the critical-pair list and a representative test per pair.

**Decision.** Approved on 2026-09-30: the analysis's completeness and
joins, including the use of Lemma H1 and baseline congruence. The review
first found CP01's and CP07's cited tests weaker than their entries; PR #103
replaced them.

## 3. Canonicity: section 4.4

**Claim.** A term in a context of dimensions only, of a closed data type,
using no assumption, reduces to a canonical value: for a declared data sort,
a saturated constructor; for a higher sort, a constructor at non-endpoint
formulas or an `hcomp` of such. So a closed natural number reached through
any H1 declaration normalizes to a numeral.

**Argument now.** An extension of Huber's computability predicates (Huber,
2019), as G0's 3.5 argues for level quantification. It covers the new
formation, constructors, boundary reduction, the eliminator, transport and
composition, and pushes a data sort's compositions as Huber does for the
natural numbers. The [written-out argument](../h1-canonicity.md) followed on
2026-09-30.

**Reviews so far.** The written-out argument's first review, on 2026-09-30,
found three substantive issues:

1. every clause required every restriction to be computable, so at the
   identity a term's computability was a premise of itself, and the least
   fixed point was empty;
2. C2 used the model's weight, which transport can raise (section 1 above);
3. Lemma C1 concluded computable equality from syntactic joins, while
   Huber's Expansion Lemma needs the reducts to be computable.

The draft was revised the same day. Value clauses are separate from
expansion, as Huber's are for `N`, with face premises like his `Glue`
clause, and stability is Lemma C3. The measure is the revised weight, and
C5 fills the telescope. C1 is stated under computability hypotheses, and
each critical pair's join is shown computable and computably equal inside
the fundamental induction.

The second review, on 2026-10-01, accepted these and found that C6's
semantic H1 eliminated a constructor at an endpoint as a V2 value, though
it is N, whose weight can forget the constructor's arguments (its
`erase(step^N(base)) @ 0`). It also asked for P1's scope, V1 among a higher
sort's values, and a measure that does not assume unique derivations. The
semantic H1 is now Lemma C7, an expression lemma with an explicit bound that
eliminates earlier constructors only at fresh dimensions; Theorem C assumes
P1; and `μ` is the least measure over a term's derivations.

**Its baseline is assumed.** Section 4.1 assumes the consistency and
canonicity of De Morgan CCHM with the kernel's formers: Π, Σ, Path, Glue,
universes, unit, the empty type and sums. Pushouts, which no published
canonicity proof covers, left the baseline on 2026-10-01 (#110): they are an
H1 declaration, which items 1 and 3 cover. The baseline's integrity
also relies on the isolation of instruction acceptance from untrusted
conversion queries, which the audit found broken; I1.2a corrected it on
2026-09-28, and `kernel/tests/test_isolation.c` checks it.

**Behaviour that exercises the claim.**
- E1, and E2 as the specification's trace takes it, in
  `docs/examples/h1/winding.cubist`. `tests/declared-match.test.mjs` checks
  the fixture, checks that none of its definitions uses an assumption, and
  checks two kinds of computation:
  - By `rfl`, the winding numbers of `loop`, `trans(loop, loop)` and
    `sym(loop)` are 1, 2 and −1, and `cong(code, loop)` is `ua(succ)`. The
    checker decides these equations by conversion.
  - Separately, three closed `evaluate` directives compute the winding
    numbers of `loop`, `trans(loop, trans(loop, loop))` and
    `trans(loop, sym(loop))` to the normal forms 1, 3 and 0. The test
    compares those values.
- K1: with no tubes, and with a tube of `succ`, a composition in `N` pushes
  into `succ`.
- E5: the eliminator on `hcomp` computes, as composition in the motive.
- T3 and T4: `computable` accepts a definition using `S1`, and a
  declaration that also uses `LEM` is refused, naming `LEM` only.

Normalization, and with it decidable conversion, is not claimed; the kernel
relies on budgets (4.5). A canonicity fixture is not a proof of canonicity.

**Decision.** Approved on 2026-10-02: the [canonicity argument](../h1-canonicity.md)
for the new cases and the items its section 6 lists for review, with the
baseline's canonicity and premise P1 as explicit assumptions.

## What was added as evidence

This record once listed two additions that would strengthen it without
discharging an obligation. Both were added: the table of 3.7's critical
pairs with a kernel test per pair (CP01–CP10), approved on 2026-09-30, and
the written arguments, the last of them approved on 2026-10-02.
