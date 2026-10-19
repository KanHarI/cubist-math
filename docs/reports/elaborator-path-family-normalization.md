# Elaborator path-family normalization audit

A direct map from `Quotient(U0, Unit, Same)` to `Prop(U0)`, where `Same` is
constantly `Unit`, generated four compositions in its squash clause on main
`ddc2e897`. Its motive contained a family of this shape, also beneath another
path type:

```text
(lambda ignored. Prop(U0))(squash(...) @ i @ j)
```

Syntactic free-dimension analysis counted the ignored argument as dependence
on the coordinate. The h-level elaborator consequently built transports for
a constant family. This is an elaborator defect, independent of the integer
or rational definitions.

## Fix and related sites

`homogeneousPath` in `web/translator/core.mjs` recognizes a constant family
after local term, universe and path beta reduction and pair projection. It
first checks the syntactic case; only a family mentioning its coordinate
needs simplification. Callers use the simplified family when recognition
succeeds. If the coordinate remains, recognition conservatively fails.

H-level construction, equality goals, rewriting/simplification, type-path
transport, dependent action, transport/lift syntax, path reversal,
concatenation and path induction use the same recognition. Reversal,
concatenation and path induction previously used a family outside its binder
without recognizing this case. Operations requiring homogeneous equality
continue to refuse genuinely dependent families; h-level construction retains
its dependent case.

Syntactic free-name analysis remains unchanged for scope allocation and
capture avoidance. Every generated proof is checked by the native kernel
against its original expected type. No judgmental transport regularity,
proof irrelevance, kernel computation rule or library helper is introduced.

The independent elaborator audit exposed related annotation and scope hazards:

- Local reduction preserves unchanged syntax objects and memoizes its outputs.
  Copying checked path applications loses the codec's native annotations.
  Contraction can also create new applications, so `Scope.homogeneousPath`
  derives a changed carrier before callers issue head queries. Simplification
  rule patterns use pure recognition while their parameters are still symbolic;
  their instantiated carriers are derived by `equalityRule`.
- Decoding shares syntax using only the dimensions visible in a node, whereas
  encoding keys by the full supplied dimension context. A decode/encode round
  trip with an unused ambient dimension therefore lost checked path-application
  annotations and could fail with K335. Decoding now also records the original
  context's encoding entry, including on decode-cache hits. Moving a visible
  coordinate still rebuilds the node.
- A decoded path binder can reuse the name of an unused ambient coordinate.
  Automatic clause goals now freshen that binder before opening the family,
  derive the renamed family, and then reduce its head.

Genuinely dependent reversal now reports E482 with an explicit-path-abstraction
suggestion instead of an escaped-dimension failure. Dependent concatenation
uses the existing homogeneous-composition diagnostic. Their documented rejection
fixtures and the error index have been updated.

The audit also found two reduction-control defects:

- `betaReduce` spent its contraction budget after recursively reducing the
  contractum. Newly exposed redexes could recurse with the unspent budget.
  It now spends before that recursion. A finite typed example stops at its
  exact one-contraction residual and finishes with three; self-reproducing
  raw syntax also stops at the bound.
- H-level statement recognition's `headBeta` loop had no work bound. It now
  uses the existing syntax-construction budget for contractions and spine
  traversal, reporting a budget error on exhaustion. Its application spine
  uses append/reverse instead of repeated quadratic prepending. Named
  definitions remain folded.

## Evidence and limits

A manual full-normalization probe of the direct quotient map failed at syntax
depth 512 before the family fix, after 120,911,412 query steps with a total of
10,294,987 arena nodes. With the unnecessary compositions removed, it normalized
in 89,917,089 query steps with a total of 17,010,711 arena nodes. Step counts
are for the query; arena totals include the checked imports. A complete successful
normal form is larger than a failed partial result: these numbers establish
successful normalization, not a memory reduction. The underlying
`prop_type_is_set(U0)` proof alone takes about 80 million query steps and
17 million arena nodes on that main revision.

Routine regressions check the kernel-verified source and absence of the
unnecessary compositions, rather than adding this multi-GB normalization to
the test suite. They also check structural h-level goals, equality goals and
supplied witnesses, reversal/concatenation, path induction, type-path transport,
genuine dependence, and both local reducers. Restoring syntactic-only
recognition fails all five focused regressions; restoring the old beta-budget
accounting fails the exact-budget test.

Additional regressions check constant quotient motives containing both existing
and beta-created path applications, unused dimension contexts and cache hits,
visible-coordinate reassignment, binder freshening, and symbolic simplification
parameters. Restoring the old codec fails both the round-trip and binder tests.
The E482 error-index row was checked in the browser.

Five existing H1 migration-ledger value hashes were refreshed because the generated
`mere_map` and `mere_eliminate` squash clauses no longer transport along
beta-constant families. Each hash includes the proof's checked dependency closure. All public
type pins, readable value renderings and assumption/extension pins are unchanged;
no migration example or library source was edited.

The original generic quotient descent and binary-rational inverse full
normalization remain unresolved. `quotient_induction` is compiled over a
truly dependent motive `B`, so its dependent constructions are justified at
that point, even when a later client instantiates `B` with constant `Prop`.
This patch does not remove them or complete NUM2. Separately skipping eager
path-application annotation normalization was measured and did not resolve
the generic descent failure.

The independent audit also identified repeated copying in `withNativeReferences`
as a further optimization lead. Its suggested global copy-on-write change to
`mapSyntax` is unsuitable: binding display intentionally clones and mutates the
result. A targeted change needs its own validation.

## Implicit-inference follow-up

The audit's unification lead now has a source-level reproduction:

```text
def take_value{{B : U0}}(f : Unit -> B) : B := f(tt);
def function_(u : Unit) : (fun (ignored : Unit) => Unit)(u) := tt;
def inferred := take_value(function_);
```

The solver rejected `B` as mentioning the argument's local `u`, although
the candidate reduces to `Unit`. A named definition `Ignored(u) := Unit`
fails the same way. Supplying `B` explicitly or an expected result type
made these calls pass, concealing the missing reduction in inference.

Only after the ordinary constraints stop making progress, a candidate that
fails its occurs or scope check gets a bounded local reduction. If that still
leaves offending names, a separate inference-only pass exposes native heads
beneath type formers. It retains a head only when it removes those names,
visits shared syntax once per dimension context, and never revisits a decoded
head merely because its object identity changed. Candidate-local dimension
binders use the codec's scope allocation. Final occurs, scope and cumulative
universe checks and kernel checking of inferred arguments remain unchanged.
Fuel, budget, resource and deadline failures propagate instead of becoming
inference refusals.

Waiting until the fallback phase matters: another argument can determine a
named type such as `Alias`, which an eager native head query would unfold.
When only the blocked constraint determines the type, native head reduction
can still unfold its name; provide the implicit argument or expected type
explicitly to retain that name. This remains first-order inference, not a
complete solver for arbitrary definitionally equal candidates.

Regressions cover beta and named-definition cases at the head and beneath a
function type, a candidate's own path binder, preservation of a name supplied
by another argument, a fresh but unhelpful decoded head queried only once,
refusal to choose an ambiguous universe after reduction, and all four
resource-stop kinds. Existing fixtures continue to cover genuine dependence
and the refusal to search for arbitrary inhabitants.

This audit follows the [kernel normalization audit](open-quotient-normalization.md).
Validation and Claude Code Opus 5.5 xhigh review results are recorded in the PR.
