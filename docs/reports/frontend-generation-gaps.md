# Frontend generation gaps after PR #188

Recorded on 2026-10-09 at PR #188 commit
[`00d4ecce`](https://github.com/KanHarI/cubist-math/commit/00d4ecce016f7e18d13eedeced07dc098a2277cb).
The comparison main revision is
[`cb525f07`](https://github.com/KanHarI/cubist-math/commit/cb525f07796348d8bc806cd8cda11663a6544f0e).
This inventory accompanies the [frontend generation roadmap](../roadmaps/frontend-generation.md).
It records observed behavior separately from proposed explanations and fixes.
The documentation change is stacked on #188; it implements none of the
remaining fixes. Closing #188's review threads did not close its documented
historical follow-ups.

## Evidence and scope

The standalone Cubist examples below were checked with `CubicalProgram`,
the matching WASM kernel and the library module reader. G5 also runs the
source linter before checking its suggested rewrite. Each example is a
separate program. They are small reproductions, not new regression tests
already installed in CI. FG0 in the roadmap makes them durable tests.

The [PR review history](pr-188-todo.md) retains the earlier comparisons.
This document is the current inventory at the pinned revision; it does not
claim an exhaustive audit. Recheck and repin it when the implementation
changes. An item is closed only with the expected behavior and a regression
test, not merely a resolved discussion or a passing corpus run.

## Fixed failures that motivate the design

These are evidence for prevention work, not outstanding bugs at `00d4ecce`.

| Evidence | Observed failure in #188 | Design lesson | Existing protection |
| --- | --- | --- | --- |
| H1: [original expansion](https://github.com/KanHarI/cubist-math/commit/499950e227f332ea288275d6e8677184ea8e8dcb) and [first review](https://github.com/KanHarI/cubist-math/pull/188#discussion_r4211251002) | Removing a law's binders before substituting its body changed `forall c : M. c = c` into an equation about the field `c`. Generated names also collided with source names. | Every transformation needs an explicit binder interface; freshness alone cannot recover a scope already discarded. | Shared scope traversal and substitution; initial-model binder tests. |
| H2: [imported-global review](https://github.com/KanHarI/cubist-math/pull/188#discussion_r4221947053) | A retained field's imported `A` was looked up again in the caller, where it named another type. | Capture declaration identity before moving syntax; distinguish the definition's scope from the request's scope. | Resolved references and import/inheritance tests. |
| H3: [family-index regression](https://github.com/KanHarI/cubist-math/pull/188#discussion_r4222631286) | A fix encoded captured identities as ordinary names; a template printed a private binding key as source and failed with E106. | A representation change must migrate every consumer. Source text is not a serialization format for resolved syntax. | Structural references and AST payloads in template holes. |
| H4: [opened-field review](https://github.com/KanHarI/cubist-math/pull/188#discussion_r4230363214) and [meaning-change example](https://github.com/KanHarI/cubist-math/pull/188#issuecomment-6081397127) | Capture used the storage environment rather than the complete `use` scope. An outer natural `one = zero` replaced a selected monoid's identity; the altered law could still type-check. | Kernel acceptance and preservation of source meaning are separate obligations. Capture must include opened fields and notation. | Selected-scope capture; tests check independently written law boundaries. |
| H5: [final review and fixes](https://github.com/KanHarI/cubist-math/pull/188#issuecomment-6082304276) | Internal names appeared in messages; generated evidence linked outside the file; caller binders captured inlined helper fields; generated recursion depended on source namespace visibility. | Identity, public labels, source provenance, and compiler control state need distinct representations. | Public labels, synthetic-link suppression, whole-expression helper substitution, explicit generated recursive calls. |

The twelve new behavioral tests that fail at `9c93220d` and pass at
`00d4ecce` include both PR regressions and previously shared failures.
They are not twelve independent defects introduced by the last change.
See [theory-hygiene.test.mjs](../../tests/theory-hygiene.test.mjs),
[theory-resolution.test.mjs](../../tests/theory-resolution.test.mjs), and
[references.test.mjs](../../tests/references.test.mjs).

## Open inventory

Priority here orders the follow-up work, rather than assigning GitHub
severity. G1 comes first because it silently changes name resolution.
G2 and G4 reject useful programs; G3 needs an honest support boundary.
G5 and G6 affect interface stability and error recovery. These bug classes
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
| C1 | Planned functionality: deriving registration and universal proofs | L2.4d, L2.6; FG6 is a prerequisite for publication | Follow the existing capability contract and register only checked complete evidence. |
| V1 | Coverage gap: combinations of transformations are not systematically explored | FG0, FG6 throughout implementation | Deterministic generated cases, independent meaning checks, and targeted mutation checks run in CI. |
| P1 | Earlier performance observation; no current comparative measurement | FG6 | Record pinned work, time and memory measurements and investigate regressions. |

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

**P1 needs a new measurement.** The previous interleaved algebra probe
reported medians of 1.125 s on main, 1.186 s at `68f1bf35`, and 1.183 s at
`9c93220d`. These are historical machine-dependent observations, not a
measurement of `00d4ecce`, a budget, or evidence for a particular cause.

At `00d4ecce` the full run passed 754/755 with one corpus wall-clock
timeout; its unchanged-limit rerun checked all 3,857 declarations in
21 seconds. That evidence, and the passing final 53-test theory run, do
not negate the small failing programs above. The roadmap requires both
compatibility checks and direct semantic evidence for each design change.
