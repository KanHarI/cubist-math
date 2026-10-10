# Frontend generation gap inventory

This is the single current status record for PR #188's frontend findings,
including fixing commits and distinguishing regressions. Status below is
for the FG6 stack at `c1780211`, inherited by PR #212; it does not claim
that the stack has merged into main. Scheduling belongs to the
[work plan](../roadmaps/work-plan.md#frontend-generation-track), and invariants
to the [frontend contracts](../roadmaps/frontend-generation.md#shared-contracts)
and [scope contract](../roadmaps/syntax-hygiene.md).

## Evidence and scope

The reproductions below record the original baseline,
[`00d4ecce`](https://github.com/KanHarI/cubist-math/commit/00d4ecce016f7e18d13eedeced07dc098a2277cb),
compared with main
[`cb525f07`](https://github.com/KanHarI/cubist-math/commit/cb525f07796348d8bc806cd8cda11663a6544f0e).
Their failure descriptions are historical observations, not current status.
G8–G12 came from the [follow-up review](https://github.com/KanHarI/cubist-math/pull/188#issuecomment-6095711362)
and were independently reproduced at both revisions and `9c93220d`.
G11 checks both the wrongly accepted and rejected intended equations;
G9 inspects labels and definition targets. The reviewer's mutation counts,
full-suite results and timings are attributed observations, not a reproduced
run by this documentation cleanup.

FG0 (`ed276a03`) installed the standalone examples as executable contracts in
[frontend-generation.test.mjs](../../tests/frontend-generation.test.mjs).
The original review chronology and earlier baseline comparisons remain in
[the pinned checklist](https://github.com/KanHarI/cubist-math/blob/c65bd1533b5295359c6f1bf62911e96b29dba76e/docs/reports/pr-188-todo.md)
and [the review of `9c93220d`](https://github.com/KanHarI/cubist-math/pull/188#issuecomment-6081397127).
The [remaining shared follow-ups](pr-188-todo.md) link here rather than
repeating reproductions. This is not an exhaustive frontend audit.

## Current status and fixing evidence

Each G row owns its disposition. The named `G1:`–`G6:` and `G8:`–`G12:`
contracts in [frontend-generation.test.mjs](../../tests/frontend-generation.test.mjs)
are active regressions, with the additional distinguishing coverage below.
G7 has an injected failure test rather than an outstanding source reproduction.
The phase reports record evidence at their own revisions.

| ID | Current disposition | Fixing commit and report | Distinguishing regression |
| --- | --- | --- | --- |
| [G1](#g1-declaration-ownership-differs-by-declaration-kind) | Fixed: mixed declaration kinds preserve the original owner | `fe05ea5e`, [FG1](frontend-generation-fg1.md) | Both collision orders and generated namespace reservations in [frontend-publication.test.mjs](../../tests/frontend-publication.test.mjs) |
| [G2](#g2-universe-calculation-ignores-fixed-operation-domains) | Fixed: generated universes include fixed domains | `91b3f5bd`, [FG3](frontend-generation-fg3.md) | Fixed U0/U1, generic domains, inherited operations, dependent indices and genuine lowering refusals in [frontend-universes.test.mjs](../../tests/frontend-universes.test.mjs) |
| [G3](#g3-dependence-on-laws-is-mistaken-for-a-fixed-argument) | Fixed by focused refusal of unsupported transport; the checked base theory remains usable | `908fcd60`, [FG2](frontend-generation-fg2.md) | Hidden law/evidence dependencies and fixed external controls in [frontend-dependencies.test.mjs](../../tests/frontend-dependencies.test.mjs) |
| [G4](#g4-nested-derived-matches-lose-access-to-evidence) | Fixed: nested matches retain checked contextual evidence | `d0abfe5a`, [FG4](frontend-generation-fg4.md) | Imported/renamed inheritance, dependent model evidence and wrong-model refusal in [frontend-evidence.test.mjs](../../tests/frontend-evidence.test.mjs) |
| [G5](#g5-a-local-simplification-changes-the-generated-interface) | Fixed: lint preserves public interfaces | `4bb87c0d`, [FG5](frontend-generation-fg5.md) | Safe lint and destructive-arrow controls with named Hom/Iso and initial/free clients in [frontend-provenance.test.mjs](../../tests/frontend-provenance.test.mjs) |
| [G6](#g6-an-invalid-parent-is-re-expanded-as-a-childs-own-error) | Fixed: failed parents remain dependency errors | `fe05ea5e`, [FG1](frontend-generation-fg1.md) | Imported inheritance chains and recovery in [frontend-publication.test.mjs](../../tests/frontend-publication.test.mjs) |
| [G7](#g7-historical-parent-projection-cascade) | Historical source triggers already passed at the baseline; dependency protection is covered by injection | `fe05ea5e`, [FG1](frontend-generation-fg1.md) | `G7: an injected parent projection failure rolls back its base group and blocks descendants once` in [frontend-publication.test.mjs](../../tests/frontend-publication.test.mjs), including native/frontend rollback |
| [G8](#g8-wildcard-fallback-replaces-an-endpoint-mismatch) | Fixed: optional coherence preserves the primary located mismatch | `d0abfe5a`, [FG4](frontend-generation-fg4.md) | Nonrecursive E606 endpoints/range and zero search calls; charged failed fallback and checked successful coherence in [frontend-evidence.test.mjs](../../tests/frontend-evidence.test.mjs) |
| [G9](#g9-source-aliases-conflate-internal-keys-and-public-labels) | Fixed: freshened binders retain public labels and navigation | `4bb87c0d`, [FG5](frontend-generation-fg5.md) | All four binder/use sites, direct/imported observations and CLI checks in [frontend-provenance.test.mjs](../../tests/frontend-provenance.test.mjs), plus browser navigation |
| [G10](#g10-the-capture-refusal-loses-the-conflicting-source-site) | Fixed: E871 identifies the actual conflict range | `f70699fe`, [FG2](frontend-generation-fg2.md) | G10's nonempty pattern/statement conflict ranges and non-enclosing controls in [frontend-generation.test.mjs](../../tests/frontend-generation.test.mjs) |
| [G11](#g11-derived-bodies-are-transformed-outside-their-parameter-telescope) | Fixed: inlining transforms complete declaration telescopes | `f70699fe`, [FG2](frontend-generation-fg2.md) | Opposite intended/captured equations, grouped dependent parameters and renamed inheritance in [frontend-dependencies.test.mjs](../../tests/frontend-dependencies.test.mjs) |
| [G12](#g12-value-calls-are-subjected-to-a-type-unfolding-restriction) | Fixed: earlier recursive value calls remain checked calls | `f70699fe`, [FG2](frontend-generation-fg2.md) | Computing imported/inherited/generated clients, nonstructural self-call and type-unfolding refusals in [frontend-dependencies.test.mjs](../../tests/frontend-dependencies.test.mjs) |
| B1 | Compatibility decision documented and covered | `ed276a03`, `908fcd60`, [FG2](frontend-generation-fg2.md) | `B1: opened fields precede later globals in ordinary and generated declarations across imports` in [frontend-generation.test.mjs](../../tests/frontend-generation.test.mjs) |
| V1 | Bounded composition/mutation gate implemented; original skipped audit case remains unidentified | `deff52a0`, [FG6](frontend-generation-fg6.md) | Eight CI seeds, 32 audit seeds, thirteen required kills and four classified probes; see [audit limits](#mutation-audit-and-remaining-evidence) |
| P1 | Measurements recorded; attribution of the historical overhead and a regression budget remain open | [FG1–FG6 evidence](README.md#frontend-generation-evidence) | Stamped work/time/arena observations; see [performance](#performance-observations-p1) |
| C1 | Planned capability work; no deriving registration or universal proofs supplied by FG | [L2.6](../roadmaps/core-theories.md#initial-and-free-models-l26) | Requires checked uniqueness, universal equivalence and the capability contract's other obligations |

## Fixed failures that motivate the design

These examples were already fixed at `00d4ecce`. They motivate the
contracts without asserting that an invariant holds for every source.

| Evidence | Observed failure in #188 | Design lesson | Existing protection |
| --- | --- | --- | --- |
| H1: [original expansion](https://github.com/KanHarI/cubist-math/commit/499950e227f332ea288275d6e8677184ea8e8dcb) and [first review](https://github.com/KanHarI/cubist-math/pull/188#discussion_r4211251002) | Removing a law's binders before substituting its body changed `forall c : M. c = c` into an equation about the field `c`. Generated names also collided with source names. | Every transformation needs an explicit binder interface; freshness alone cannot recover a scope already discarded. | Shared scope traversal and substitution; initial-model binder tests. |
| H2: [imported-global review](https://github.com/KanHarI/cubist-math/pull/188#discussion_r4221947053) | A retained field's imported `A` was looked up again in the caller, where it named another type. | Capture declaration identity before moving syntax; distinguish the definition's scope from the request's scope. | Resolved references and import/inheritance tests. |
| H3: [family-index regression](https://github.com/KanHarI/cubist-math/pull/188#discussion_r4222631286) | A fix encoded captured identities as ordinary names; a template printed a private binding key as source and failed with E106. | A representation change must migrate every consumer. Source text is not a serialization format for resolved syntax. | Structural references and AST payloads in template holes. |
| H4: [opened-field review](https://github.com/KanHarI/cubist-math/pull/188#discussion_r4230363214) and [meaning-change example](https://github.com/KanHarI/cubist-math/pull/188#issuecomment-6081397127) | Capture used the storage environment rather than the complete `use` scope. An outer natural `one = zero` replaced a selected monoid's identity; the altered law could still type-check. | Kernel acceptance and preservation of source meaning are separate obligations. Capture must include opened fields and notation. | Selected-scope capture; tests check independently written law boundaries. |
| H5: [review fixes at `00d4ecce`](https://github.com/KanHarI/cubist-math/pull/188#issuecomment-6082304276) | Internal names appeared in messages; generated evidence linked outside the file; law binders captured inlined helper fields; generated recursion depended on source namespace visibility. | Identity, public labels, source provenance, and compiler control state need distinct representations. | Selected diagnostic labels, synthetic-link suppression, helper substitution through law expressions (including inherited helpers), explicit generated self-calls. The later baseline reproductions below cover derived-operation parameters (G11), law reference links (G9) and calls to earlier recursive operations (G12). |

The twelve new behavioral tests that fail at `9c93220d` and pass at
`00d4ecce` include both PR regressions and previously shared failures.
They are not twelve independent defects introduced by the last change.
See [theory-hygiene.test.mjs](../../tests/theory-hygiene.test.mjs),
[theory-resolution.test.mjs](../../tests/theory-resolution.test.mjs), and
[references.test.mjs](../../tests/references.test.mjs).

## Baseline reproductions

Every failure description in G1–G12 below refers to `00d4ecce` and its
comparison revisions. Use the [status table](#current-status-and-fixing-evidence)
for fixes and current regression coverage.

## G1: declaration ownership differs by declaration kind

```cubist
def N : Unit := tt;
inductive N : U0 { c; }
def u : Unit := N;
```

Both declarations of `N` are accepted; the output retains the inductive
entry and `u` fails with E606 (`found U0, expected Unit`). The prototype has
the same problem:

```cubist
import hlevels;
import algebra;
def N : Unit := tt;
initial N : Monoid(U0);
def u : Unit := N;
```

Expected: refuse the second same-module declaration with the duplicate-name
diagnostic before replacing `N`; recovery can still check `u` against the
original definition. This does not forbid legal local shadowing or a local
declaration shadowing an import. The rule must distinguish those cases.

The behavior indicates inconsistent ownership checks across declaration
kinds. Audit the dispatcher and publication paths in
[translate.mjs](../../web/translator/translate.mjs),
[inductive.mjs](../../web/translator/inductive.mjs), and
[initial-models.mjs](../../web/translator/initial-models.mjs). A generator's
local collision list is insufficient as the shared policy.

## G2: universe calculation ignores fixed operation domains

```cubist
import hlevels;
theory T(U < UU0) {
  M : set U;
  op(A : U0, x : A) : M;
}
```

`T.Hom` fails with E606: `found max(U, max(V, U1)), expected max(U, V)`.
Its dependent Hom/Iso declarations then fail with E340. Quantifying over
the fixed operation argument `A : U0` contributes a universe that is absent
from the generated annotation.

Expected: account for the complete generated telescope, including fixed
domains, dependent indices and preservation fields. Generate and check
Hom, identity, composition and supported Iso declarations at the resulting
universe. The issue is in the frontend's universe calculation; raising all
generated declarations to an arbitrary large universe is not the remedy.
Start in [morphisms.mjs](../../web/cubist/morphisms.mjs).

## G3: dependence on laws is mistaken for a fixed argument

```cubist
import hlevels;
theory T(U < UU0) {
  M : set U;
  c : M;
  law l : c = c;
  op(p : l = l) : M;
}
```

`T.Hom` fails with E606: `found A.l = A.l, expected B.l = B.l`, followed
by dependent failures. A domain can vary between models even when it does
not directly mention a carrier name: it can depend on a law, evidence, or
another field that does.

Expected for the first fix: the theory remains a usable checked theory,
but unsupported morphism derivation is recorded explicitly, with a focused
message naming `op`, `p`, and the dependence on `l`. No malformed Hom/Iso
family is published. Supporting this case later requires a specified,
checked transport construction; proof irrelevance alone does not make the
two argument types definitionally equal. Review shape analysis in
[morphisms.mjs](../../web/cubist/morphisms.mjs) alongside the separate
initial/free admissibility analysis.

## G4: nested derived matches lose access to evidence

```cubist
import hlevels;
inductive Bit : set U0 { off; yes; }
inductive Bits : set U0 { nil; cons(b : Bit, rest : Bits); }
theory T(U < UU0) {
  M : set U;
  c : M;
  def value(n : Bits) : M := match n {
    nil => c;
    cons(off, rest) => c;
    cons(yes, rest) => c;
  };
}
```

`T.value` fails with E546: it cannot generate `Bit.squash` because it
cannot find evidence that `m.M` is a set. That evidence is already a
checked field of the model. An inherited copy has the same failure.

Expected: nested clause elaboration receives the applicable checked model
evidence, transformed with its context. The required proof is still
checked against the actual motive and boundaries. This does not authorize
arbitrary missing path clauses, false equalities, or a broader elimination
principle. Audit evidence discovery in
[match.mjs](../../web/translator/match.mjs) and
[hlevel.mjs](../../web/translator/hlevel.mjs), and context reconstruction in
[patterns.mjs](../../web/translator/patterns.mjs).

## G5: a local simplification changes the generated interface

```cubist
import hlevels;
theory T(U < UU0) {
  M : set U;
  op : forall x, y : M. M;
}
def id_(S : T(U0)) := T.Hom.id(S);
initial N : T(U0);
```

The source checks. The linter emits W706 for `x` and `y`, advising arrow
form. After replacing the operation by `op : M -> M -> M`, `id_` fails
with E817 and `N` with E864. The single-binder form also receives W705.

On comparison main, the grouped form already fails its Hom client, so it
cannot demonstrate an interface lost through lint there. The supported
control is `op : forall x : M. M`, without the unavailable `initial`
declaration. It checks, receives W705, and loses Hom support when rewritten
to arrow form. This establishes the shared bug without conflating the
two revisions' support for grouped arguments.

Expected: lint treats an operation's named arguments as part of its
generated interface, even when their names are unused in the result type.
Advice must preserve supported derivations and public calling conventions,
or explain the interface change rather than present it as a simplification.
Start in [lint.mjs](../../web/cubist/lint.mjs); acceptance includes checking
the suggested replacement through actual clients.

## G6: an invalid parent is re-expanded as a child's own error

```cubist
import hlevels;
theory P(U < UU0) {
  M : set U;
  e : M;
  law bad : e = Undefined;
}
theory C(U < UU0) extends P { law again : e = e; }
```

Both `P` and `C` report E343 for `Undefined`. Expected: `P` owns that
error; `C` reports E340 for its dependency on `P`, retaining the root cause
for inspection. Valid declarations independent of `P` remain usable.
Audit the retained theory state and expansion dependencies in
[translator/theories.mjs](../../web/translator/theories.mjs).

## G7: historical parent-projection cascade

Earlier capture failures made `Q.p` fail, then made `Q.Hom.p` report E391
about an undetermined universe rather than the failed dependency. The
recorded numeral, operator-operand and opened-field triggers now check.
They are evidence for the dependency contract, not current reproductions.
This symptom requires a genuine upstream projection failure through controlled
failure injection; a source reproduction must be recorded separately before
calling it a confirmed source defect. The current evidence is in the status table.

## G8: wildcard fallback replaces an endpoint mismatch

```cubist
import hlevels;
inductive T : set U0 { t0; t1; seg : t0 = t1; }
def h(x : T) : T := match x { t0 => t0; _ => t1; };
```

At `00d4ecce`, this reports E546, `Cannot generate seg: T must be a
proposition`, at the scrutinee `x`. Main and `9c93220d` report the useful
E606, `found t1 = t1, expected t0 = t1`, at the body. The program remains
rejected, but the diagnostic now describes an unrequested construction.
The reviewer also observed the error with a `Nat` target and initial-model
law constructors such as `N.one_mul`.

The [fallback in match.mjs](https://github.com/KanHarI/cubist-math/blob/00d4ecce016f7e18d13eedeced07dc098a2277cb/web/translator/match.mjs#L456)
tests every failing implicit path clause, even though its stated purpose
is handling recursive boundaries. `seg` has no recursive positions.
Expected: use that fallback only for constructors with recursive positions;
when an eligible fallback also fails, retain the written body's original
mismatch. Explicit path clauses keep their bodies. Test the error code,
endpoints and source range, plus successful checked coherence; the baseline
test only asks whether a gap is named `bad`.

## G9: source aliases conflate internal keys and public labels

```cubist
import hlevels;
theory T(U < UU0) { M : set U; c : M; op(x, y : M) : M;
  def k(x : M) : M := op(x, c);
  law l(c : M) : k(c) = op(c, c);
}
```

Freshening the law binder to internal `c1` is necessary to preserve meaning.
Its three written uses nevertheless display `c1`, and neither uses nor
binder have a definition target at `00d4ecce`. Both comparison revisions
name all four sites `c` and link them to the written binder (although their
inlining has the earlier semantic bug).

[sourceBinding and the alias filter](https://github.com/KanHarI/cubist-math/blob/00d4ecce016f7e18d13eedeced07dc098a2277cb/web/translator/translate.mjs#L113)
record a public label but match it against an internal environment key.
Expected: retain lookup identity/key, display label and binder origin as
separate information all the way through reference recording. Test every
written site and its definition target, with both original and freshened
names; a passing signature or correctly typed law is insufficient.

## G10: the capture refusal loses the conflicting source site

```cubist
import hlevels; import nat;
theory T(U < UU0) { M : set U; c : M;
  def k(n : Nat) : M := c;
  law l(n : Nat) : (match n return M { zero => c; succ(c) => k(c); }) = c;
}
```

E871 correctly refuses the unsafe capture at `00d4ecce`, but its range is
empty at the start of the law. This is a provenance regression in the new
refusal, not a request to restore the earlier E606 produced by bad inlining.
The [inlining refusal](https://github.com/KanHarI/cubist-math/blob/00d4ecce016f7e18d13eedeced07dc098a2277cb/web/cubist/theories.mjs#L173)
locates the whole transformed type instead of the actual conflict.
Expected: carry the conflicting binder or call's original source range
through substitution. Check a nonempty range covering `c` in `succ(c)` or
the helper use; an unrelated pattern binder must still cause no E871.

## G11: derived bodies are transformed outside their parameter telescope

```cubist
import hlevels;
theory T(U < UU0) { M : set U; c : M; op(x, y : M) : M;
  def k(x : M) : M := op(x, c);
  def kk(c : M) : M := k(c);
}
def captured(S : T(U0), x : S.M) : S.kk(x) = S.op(x, x) := refl(S.op(x, x));
```

This wrongly checks at all three revisions. Replacing its last declaration
with `S.kk(x) = S.op(x, S.c) := refl(S.op(x, S.c))` fails with E606.
The helper's free field has become the caller's parameter. Laws built from
`kk` inherit that changed meaning; kernel acceptance does not detect it.

The [derived-operation builder](https://github.com/KanHarI/cubist-math/blob/00d4ecce016f7e18d13eedeced07dc098a2277cb/web/cubist/theories.mjs#L532)
processes `item.value` without its parameter binders. Scope-aware
substitution cannot protect a scope omitted by its caller. The earlier
fix covers law expressions and inherited helpers under law binders, not
this declaration boundary. The [scope contract](../roadmaps/syntax-hygiene.md)
requires a complete declaration interface.

Expected: transform a complete declaration interface, including grouped and
dependent parameter domains, result type and body. Preserve public parameter
labels while freshening internal binders. Check both equations independently,
helper chains, parameter shadowing, inheritance, and generated model clients.

## G12: value calls are subjected to a type-unfolding restriction

```cubist
import hlevels; import nat;
theory T(U < UU0) { M : set U; c : M; op(x : M) : M;
  def iter(n : Nat) : M := match n {
    zero => c; succ(k) => op(iter(k));
  };
  def twice(n : Nat) : M := op(iter(n));
}
```

All three revisions refuse `twice` with E845, `iter is recursive, and a
field's type cannot unfold it`, and an empty range. The caller is a derived
value, not a field type. The [same inlining pass](https://github.com/KanHarI/cubist-math/blob/00d4ecce016f7e18d13eedeced07dc098a2277cb/web/cubist/theories.mjs#L187)
handles both contexts and applies the type restriction indiscriminately.

Expected: retain a checked call to an earlier recursive derived operation
in a value body, without trying to inline its recursion. Distinguish that
from the current definition's structural self-call and from unsupported
unfolding in field types/laws. Verify `S.twice(zero) = S.op(S.c)` by `rfl`,
inherited and initial-model clients, lexical shadowing, and the still-valid
E845 type restrictions. Any refusal must describe its actual context and
point to a nonempty range at the responsible call.

## Limits and confidence

### Capability boundary (C1)

The construction-and-fold prototype registers no initial/free capability.
The deriving opt-in, uniqueness and universal-property proofs belong to
[L2.6](../roadmaps/core-theories.md#initial-and-free-models-l26). Broader
carrier/family strategies and higher coherences remain in that contract;
frontend preservation checks cannot supply those mathematical proofs.

### Mutation audit and remaining evidence

The reviewer reported 20 mutations at `00d4ecce`: 13 killed, one skipped
and six surviving, plus a separate explicit-head probe. FG2 removed the
redundant initial-model `notationScope` aliases after auditing their
producers and consumers; captured notation is the single source of scope.
[FG2's audit](frontend-generation-fg2.md) records the removal and the
synthetic-provenance distinction that remains testable.

[FG6's historical dispositions](frontend-generation-fg6.md#historical-audit-disposition-and-limitations)
record the exact repeatable probes and their limits. The multi-value
explicit-path probe is distinguished; single-value controls alone did not
reach it. The branch recursion-state update, recursive-call producer guard,
extra IsSet/IsProp freshening and historical `scope.fresh` label preference
have documented defensive/equivalent dispositions, separate from the
thirteen required kills. The alpha-freshening label-loss mutation and the
historical fresh-name preference are different probes.

The original manifest, individual thirteen kills and identity/reason for
the skipped case were not supplied. Recover that evidence before claiming
to reproduce or close the historical audit. The bounded transformation
matrix in [frontend-invariants.test.mjs](../../tests/frontend-invariants.test.mjs)
is preventive coverage, not an exhaustive proof of preservation.

### File-level selection (B1)

File-level `use` applies to ordinary inductives as to definitions. After
`use multiplicative;`, a later same-spelled global does not replace an
opened field in a constructor domain. The normative rule is in the
[scope contract](../roadmaps/syntax-hygiene.md#resolved-syntax-and-closures).
The reviewer found no affected corpus source; that observation alone would
not establish source compatibility.

### Performance observations (P1)

The earlier interleaved algebra probe reported medians of 1.125 s on main,
1.186 s at `68f1bf35`, and 1.183 s at `9c93220d`. The follow-up reviewer
reported seven interleaved checks of `import hlevels; import algebra;`,
with medians of 1.32 s on main and 1.41 s at `00d4ecce` (about 6.8% slower).
These samples support the historical 5–9% observation, not its proposed
cause or a performance budget.

The [FG reports and cited snapshots](README.md#frontend-generation-evidence)
retain subsequent measurements with revisions, workload/build stamps and
unchanged limits. They do not establish that the original overhead was
removed. Attribute the work/memory cost with comparable runs before setting
a budget; do not convert machine-dependent medians into a speedup claim.

### Baseline validation

At `00d4ecce` the full run passed 754/755 with one corpus wall-clock timeout;
its unchanged-limit rerun checked all 3,857 declarations in 21 seconds.
The follow-up reviewer also reported a clean 755/755 run, site build/site
tests, browser tests, lint and diff checks at that head. These historical
runs did not negate the small failing programs reproduced above. Later
validation belongs to each FG report; no implementation tests were rerun
for this documentation-only reconciliation.
