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
depth 512 before the family fix, after 120,911,412 query steps and 10,294,987
arena nodes. With the unnecessary compositions removed, it normalized in
89,917,089 query steps with 17,010,711 arena nodes. A complete successful
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

The original generic quotient descent and binary-rational inverse full
normalization remain unresolved. `quotient_induction` is compiled over a
truly dependent motive `B`, so its dependent constructions are justified at
that point, even when a later client instantiates `B` with constant `Prop`.
This patch does not remove them or complete NUM2. Separately skipping eager
path-application annotation normalization was measured and did not resolve
the generic descent failure.

This audit follows the [kernel normalization audit](open-quotient-normalization.md).
Validation and Claude Code Opus 5.5 xhigh review results are recorded in the PR.
