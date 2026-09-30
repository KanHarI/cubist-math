# H1 review evidence: the mathematical items of the release checklist

Status: gathered on 2026-09-29 at `0b775b1`, for work-plan K2.1's review;
K1 with tubes and K6 along `ua` traced since (PR #94), and K10 and K11
(PR #95).
Updated on 2026-09-30 with the [H2 case analysis and critical-pair
draft](h1-critical-pairs.md), including representative joins CP01–CP10
in the kernel. Its mathematical review remains pending. The same day, the
[model construction](h1-model.md) and the [canonicity argument](h1-canonicity.md)
were written out as review drafts for items 1 and 3; their review is
pending too.
This record serves the first three items of the
[H1 specification](h1-signature-specification.md)'s release checklist, the
mathematical ones:

1. D1, D4 and D5 written out and reviewed (4.2, 4.3);
2. Lemma H2's full case analysis, and the critical-pair check of 3.7;
3. canonicity (4.4) reviewed, relative to the assumed baseline of 4.1.

For each it gives the claim, where its argument stands, what reviews have
found, the tests that exercise the behaviour the argument relies on, and what
a review decision still needs. As the specification's 4.5 says, the tests are
evidence for the specified behaviour, not for these claims. **None of the
three items is discharged.** The checklist's other items are not
mathematical: the acceptance matrix (item 4), a pinned run (item 5) and the
differential fixtures (item 6).

## Summary

| Item | Argument now | Mechanical evidence | Missing for a decision |
| --- | --- | --- | --- |
| D1, D4, D5: the model | [Construction written out](h1-model.md), review draft: raw trees, a weight by constructor index, carrier, Kan structure and eliminator | Admission, boundaries and cube depth: A1–A17, N1–N6, R3, E3, K7 | Review of the draft: premise P1, the weight measure, restriction's functoriality at endpoints and the semantic Lemma H1 |
| Lemma H2 and 3.7's critical pairs | [Rule-by-rule case analysis and overlap table](h1-critical-pairs.md), review draft | CP01–CP10 representative joins; N3, N4, K4–K9 in part or in substance, E5, V11, V16; randomized K10 and K11 | Review of the head classification, baseline premises, use of H1 and joining sequences |
| Canonicity | [Huber's predicates extended, written out](h1-canonicity.md), review draft | Closed computations through declared types: E1, E2, K1, E5, T3, T4 | Review of the draft, which uses item 2's joins; the baseline's canonicity accepted explicitly as an assumption |

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
inductive definition). Section 4.3 marks D1, D4 and D5 "Argued", each with
an open obligation to write it out. Consistency is relative to the baseline
model (step 7).

**Reviews so far.** The specification had four reviews before its approval
on 2026-09-27 (its "Revisions after review"). They corrected level erasure,
path abstraction in boundaries, hidden tier bounds and the tier walk's
coverage, and they marked D1, D4, D5 and Lemma H2 as open obligations. None
of them wrote out the construction. D2, D6 and D7 were found valid as
conditional outlines, and D3's local wall calculation was found valid.

**Literature, as the specification reads it (4.6).**
- Coquand, Huber and Mörtberg (LICS 2018) construct the cubical-set models
  of the examples, the kernel's pushouts among them, and describe the
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

**What a decision needs.** Either the construction written out for the
whole schema, with the well-founded definition over cubes at every depth
(D4) and with infinitary arities (D5); or an explicit decision to accept the
argued status on the literature above. The second could narrow the first
release to what the literature covers, for instance finite arities.

## 2. Stability and confluence: Lemma H2 and section 3.7

**Claims.** Lemma H2: every rule of 3.3–3.7 commutes with substitution of
interval formulas for dimensions, and of level expressions for level
variables. Section 3.7, with 4.5: the generated rules are confluent with the
existing ones.

**Argument now.** The [2026-09-30 draft](h1-critical-pairs.md) writes out
Lemma H2 rule by rule and lists CP01–CP10 with their joins and kernel tests.
It remains a draft, relative to baseline substitution and conversion.
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

**What a decision needs.** Review of the draft's completeness and joins,
including the use of Lemma H1 and baseline congruence. Passing the
representative tests does not record that review decision.

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
natural numbers. It is argued, not written out.

**Its baseline is assumed.** Section 4.1 assumes the consistency and
canonicity of De Morgan CCHM with the kernel's formers. No published
canonicity proof covers the kernel's pushouts. The baseline's integrity
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
- T3 and T4: `computable` accepts the H1 marker, and a declaration that also
  uses `LEM` is refused, naming `LEM` only.

Normalization, and with it decidable conversion, is not claimed; the kernel
relies on budgets (4.5). A canonicity fixture is not a proof of canonicity.

**What a decision needs.** The computability argument written out for the
new cases, and an explicit acceptance of the baseline's canonicity as an
assumption.

## What can be added as evidence

These strengthen the record without discharging an obligation:
- a table of 3.7's critical pairs, each with a kernel test of a
  representative instance;
- drafts of the written arguments, for a reviewer to check: Lemma H2's case
  analysis, the critical pairs, and the canonicity argument's new cases.
