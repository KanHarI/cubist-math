# Frontend generation gaps after PR #188

Recorded on 2026-10-09 at PR #188 commit
[`00d4ecce`](https://github.com/KanHarI/cubist-math/commit/00d4ecce016f7e18d13eedeced07dc098a2277cb).
The comparison main revision is
[`cb525f07`](https://github.com/KanHarI/cubist-math/commit/cb525f07796348d8bc806cd8cda11663a6544f0e).
This inventory accompanies the [frontend generation roadmap](../roadmaps/frontend-generation.md).
It records observed behavior separately from proposed explanations and fixes.
The documentation change is stacked on #188; it implements none of the
remaining fixes. Closing #188's review threads did not close its documented
historical follow-ups. The subsequent [review of this same head](pr-188-review-00d4ecce.md)
adds three regressions and two shared defects, recorded as G8–G12 below.

## Evidence and scope

The standalone Cubist examples below were checked with `CubicalProgram`,
the matching WASM kernel and the library module reader. G5 also runs the
source linter before checking its suggested rewrite. Each example is a
separate program. They are small reproductions, not new regression tests
already installed in CI. FG0 in the roadmap makes them durable tests.

For the follow-up review, G8–G12 were also independently reproduced at
`00d4ecce`, main `cb525f07`, and the earlier #188 head `9c93220d` with the
same kernel. The G11 comparison checks both the wrongly accepted equation
and the rejected intended equation. G9 inspects reference labels and
definition targets, not just acceptance. The reviewer's broader mutation
run, full-suite results and performance measurement are attributed below;
this documentation change does not claim to have repeated them.

The [PR review history](pr-188-todo.md) retains the earlier comparisons.
This document is the current inventory at the pinned revision; it does not
claim an exhaustive audit. Recheck and repin it when the implementation
changes. An item is closed only with the expected behavior and a regression
test, not merely a resolved discussion or a passing corpus run.

## Fixed failures that motivate the design

The inventory below remains pinned to `00d4ecce`. Follow-up implementation
evidence is tracked separately so that the original reproductions retain
their meaning:

| Follow-up | Fixing implementation | Distinguishing regression |
| --- | --- | --- |
| FG0 executable evidence | `ed276a03` | `frontend-generation.test.mjs`: independent expected outcomes, with later-phase debt explicit |
| G1/G6 and injected G7 | `fe05ea5e`, [FG1 report](frontend-generation-fg1.md) | Mixed ownership collisions, dependency failures and native/frontend rollback in `frontend-publication.test.mjs` |
| G3 unsupported law transport | `908fcd60`, [FG2 report](frontend-generation-fg2.md) | Active G3 contract; hidden law/evidence dependencies and fixed external controls in `frontend-dependencies.test.mjs` |
| G10 source range, G11 telescope capture, G12 earlier value calls | `f70699fe`, [FG2 report](frontend-generation-fg2.md) | Active G10–G12 contracts; opposite intended/captured equations, renamed inheritance, computation and focused type-unfolding refusal |
| G2 full generated universes | `91b3f5bd`, [FG3 report](frontend-generation-fg3.md) | Active G2 contract; fixed U0/U1 inputs, generic universes, inherited operations, dependent indices and genuine lowering refusals in `frontend-universes.test.mjs` |
| G4 contextual evidence, G8 wildcard diagnostics | `d0abfe5a`, [FG4 report](frontend-generation-fg4.md) | Active G4/G8 contracts; nested/dependent model evidence, wrong-model refusal, charged failed fallback and checked successful coherence in `frontend-evidence.test.mjs` |
| G5 public lint interfaces, G9 labels/navigation | `4bb87c0d`, [FG5 report](frontend-generation-fg5.md) | Active G5/G9 contracts; direct/imported source observations, named Hom constructors and generated clients, CLI and browser navigation |

All eleven executable gaps are active regressions at FG5. The notation-alias
audit's removal and its provenance distinction are documented in the FG2
report. None of these changes registers the separate C1 deriving capability.

The [FG6 release-gate report](frontend-generation-fg6.md) records composed
transformation tests, exact mutation patches, the newly distinguished
multi-value explicit-path probe and measured validation. The historical
audit's unidentified skipped mutation remains an explicit evidence gap.

These specific examples are fixed at `00d4ecce`. They are evidence for
prevention work, not proof that the surrounding invariant holds everywhere:
G8–G12 demonstrate remaining failures in the same contracts.

| Evidence | Observed failure in #188 | Design lesson | Existing protection |
| --- | --- | --- | --- |
| H1: [original expansion](https://github.com/KanHarI/cubist-math/commit/499950e227f332ea288275d6e8677184ea8e8dcb) and [first review](https://github.com/KanHarI/cubist-math/pull/188#discussion_r4211251002) | Removing a law's binders before substituting its body changed `forall c : M. c = c` into an equation about the field `c`. Generated names also collided with source names. | Every transformation needs an explicit binder interface; freshness alone cannot recover a scope already discarded. | Shared scope traversal and substitution; initial-model binder tests. |
| H2: [imported-global review](https://github.com/KanHarI/cubist-math/pull/188#discussion_r4221947053) | A retained field's imported `A` was looked up again in the caller, where it named another type. | Capture declaration identity before moving syntax; distinguish the definition's scope from the request's scope. | Resolved references and import/inheritance tests. |
| H3: [family-index regression](https://github.com/KanHarI/cubist-math/pull/188#discussion_r4222631286) | A fix encoded captured identities as ordinary names; a template printed a private binding key as source and failed with E106. | A representation change must migrate every consumer. Source text is not a serialization format for resolved syntax. | Structural references and AST payloads in template holes. |
| H4: [opened-field review](https://github.com/KanHarI/cubist-math/pull/188#discussion_r4230363214) and [meaning-change example](https://github.com/KanHarI/cubist-math/pull/188#issuecomment-6081397127) | Capture used the storage environment rather than the complete `use` scope. An outer natural `one = zero` replaced a selected monoid's identity; the altered law could still type-check. | Kernel acceptance and preservation of source meaning are separate obligations. Capture must include opened fields and notation. | Selected-scope capture; tests check independently written law boundaries. |
| H5: [review fixes at `00d4ecce`](https://github.com/KanHarI/cubist-math/pull/188#issuecomment-6082304276) | Internal names appeared in messages; generated evidence linked outside the file; law binders captured inlined helper fields; generated recursion depended on source namespace visibility. | Identity, public labels, source provenance, and compiler control state need distinct representations. | Selected diagnostic labels, synthetic-link suppression, helper substitution through law expressions (including inherited helpers), explicit generated self-calls. Derived-operation parameters (G11), law reference links (G9) and calls to earlier recursive operations (G12) are still open. |

The twelve new behavioral tests that fail at `9c93220d` and pass at
`00d4ecce` include both PR regressions and previously shared failures.
They are not twelve independent defects introduced by the last change.
See [theory-hygiene.test.mjs](../../tests/theory-hygiene.test.mjs),
[theory-resolution.test.mjs](../../tests/theory-resolution.test.mjs), and
[references.test.mjs](../../tests/references.test.mjs).

## Open inventory

Priority here orders the follow-up work, rather than assigning GitHub
severity. G1 and G11 come first because they silently change meaning.
G2 and G4 reject useful programs; G3 needs an honest support boundary.
G5 and G6 affect interface stability and error recovery. G1–G6's bug classes
are shared with the comparison main revision; G1's initial-model variant
is specific to the new prototype. G5 uses a single-binder control on main,
as explained below, rather than claiming its grouped example worked there.

| ID | Status at the pinned revision | Work package | Completion condition |
| --- | --- | --- | --- |
| G1 | Open: mixed declaration kinds silently replace a name | FG1 | Refuse the conflicting declaration before publication and preserve the original binding. |
| G2 | Open: generated Hom universes omit fixed argument domains | FG3 | Infer a sufficient universe from all generated fields and check identity/composition at multiple levels. |
| G3 | Open: law-dependent arguments enter an unsupported Hom expansion | FG2 | Either construct checked transport or refuse the requested derivation before publishing its artifacts. |
| G4 | Open: nested generated matches cannot find carrier evidence | FG4 | Carry checked evidence through nested and dependent scopes without adding assumptions. |
| G5 | Open: unused-binder advice removes generated interfaces | FG5 | Suggested rewrites preserve named-call and derivation behavior, or are suppressed. |
| G6 | Open: failed-parent diagnostics are repeated as fresh child failures | FG1 | Report the child's failed dependency once, with the original cause retained. |
| G7 | Historical symptom; no remaining reproduction in this inventory | FG1, FG6 | Exercise an actual failed parent projection and its dependents; do not reuse a now-passing capture example as a bug. |
| G8 | Open regression in `00d4ecce`: wildcard path failures report unwanted generation | FG4 | Restrict fallback to recursive positions and retain the original mismatch when fallback cannot supply checked coherence. |
| G9 | Open regression in `00d4ecce`: freshened law binders lose public labels and definition links | FG5 | Binder and every use display the written label and resolve to the original binder span. |
| G10 | Open regression in `00d4ecce`: E871 has an empty source range | FG2, FG5 | Report the actual conflicting pattern/statement binding or helper call, with a nonempty source range. |
| G11 | Open, shared with main: a derived parameter captures an inlined helper's field | FG2 | Transform the complete parameter telescope, result type and body; accept the intended equation and reject the captured one. |
| G12 | Open, shared with main: calls to an earlier recursive derived operation are treated as forbidden type unfolding | FG2, FG4, FG5 | Distinguish ordinary value calls, recursive self-calls and type unfolding; retain legitimate refusal codes and source sites. |
| C1 | Planned functionality: deriving registration and universal proofs | L2.4d, L2.6; FG6 is a prerequisite for publication | Follow the existing capability contract and register only checked complete evidence. |
| V1 | Coverage gap: combinations of transformations are not systematically explored | FG0, FG6 throughout implementation | Deterministic generated cases, independent meaning checks, and targeted mutation checks run in CI. |
| P1 | Reviewer measured current algebra slowdown; no established resource budget | FG6 | Record pinned work, time and memory measurements and investigate regressions. |
| B1 | Compatibility change: ordinary inductives now honor file-level `use` | FG0, FG2, FG6 | Document and test resolution precedence consistently across ordinary and generated declarations. |

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
FG1 should test a genuine upstream projection failure through controlled
failure injection; a source reproduction, if found, must be recorded
separately before this is called a confirmed remaining defect.

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
endpoints and source range, plus successful checked coherence; the current
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
this declaration boundary. The [review TODO](pr-188-todo.md) and
[scope contract](../roadmaps/syntax-hygiene.md) are qualified accordingly.

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

**C1 is incomplete planned functionality, not a newly discovered bug.**
The construction-and-fold prototype registers no initial/free capability.
The deriving opt-in, uniqueness and universal-property proofs remain in
[L2.6](../roadmaps/core-theories.md#initial-and-free-models-l26). Broader
carrier/family strategies and higher coherences remain in that contract;
the frontend work must not silently extend the supported mathematical
fragment or advertise those proofs as complete.

**V1 concerns preservation of meaning.** Existing tests include useful
scope invariants and independently stated law types, but no systematic
matrix covers combinations of imports, inheritance, notation, inlining,
dependent binders and generation. H4 demonstrates why merely checking that
both versions are accepted is too weak. FG6 defines the comparison oracle
and transformations rather than promising exhaustive testing.

The follow-up reviewer ran 20 mutations against targeted theory, scope,
match and corpus tests: 13 killed, one skipped and six surviving. Two
survivors remove public labels and expose G9's missing observation checks.
One bypasses `notationScope` aliases: now that lexical capture covers the
comparison operands and numerals, the wrapper built in
[initial-models.mjs](../../web/translator/initial-models.mjs) may be redundant.
FG2/FG6 must either identify a distinguishing source behavior and test it,
or remove the redundant layer after auditing consumers. Survival alone
does not prove that code is dead.

The other three concern the branch recursion-state update, a generated
recursive-call source guard, and unnecessary IsSet/IsProp freshening. The
reviewer considered them equivalent or defensive; record each disposition
with its reasoning rather than counting all survivors as bugs or inventing
tests that mirror implementation. The separate explicit-head guard probe
also survived; top-level explicit path clauses do not reach it. The skipped
mutant remains unassessed. Preserve the controls for explicit path bodies,
bare/partial helpers, non-enclosing patterns, inherited recursion, and
`N.model.iter` while strengthening the tests.

**B1 is a compatibility decision, not a reported corpus failure.** File-level
`use` now applies to ordinary inductives as it already did to definitions.
After `use multiplicative;`, even a later `inductive M` does not change the
opened meaning of `M` in `inductive Box : U0 { box(n : M); }`: the argument
is `multiplicative.M`. The reviewer found no affected corpus source.
FG0/FG2 must document this precedence and test it deliberately, including
changed selections, imports and generated declarations; passing today's
corpus does not establish source compatibility.

**P1 has observations, not an established budget.** The previous interleaved algebra probe
reported medians of 1.125 s on main, 1.186 s at `68f1bf35`, and 1.183 s at
`9c93220d`. The follow-up reviewer reports seven interleaved checks of
`import hlevels; import algebra;`, with medians of 1.32 s on main and
1.41 s at `00d4ecce` (about 6.8% slower). These machine-dependent samples
are consistent with the earlier 5–9% range, not evidence for a particular
cause or permission to adopt that range as a performance budget.

At `00d4ecce` the full run passed 754/755 with one corpus wall-clock
timeout; its unchanged-limit rerun checked all 3,857 declarations in
21 seconds. That evidence, and the passing final 53-test theory run, do
not negate the small failing programs above. The follow-up reviewer also
reports a clean 755/755 run, site build/site tests, browser tests, lint and
diff checks at this same head. The roadmap requires both
compatibility checks and direct semantic evidence for each design change.
