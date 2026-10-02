# Source-defined Nat, W and pushouts

Nat and W since 2026-09-30, pushouts since 2026-10-01 ([below](#source-defined-pushouts)).

Implemented on 2026-09-30, based on `bfef585`. H1 is enabled by default in
the browser, CLI and source-checking tools. Its mathematical review was
approved and H1 released on 2026-10-02: no experimental option or marker
remains (the specification's 5.7 and 6.4).

## Source and imports

[`nat.cubist`](../../archive/first-library/nat.cubist) contains the ordinary
declaration:

```cubist
inductive Nat : U0 {
  zero;
  succ(n : Nat);
}
```

The module loader imports `nat` as a standard prelude. It uses the same source
reader, import graph, declaration admission and transactions as other modules.
A bundled copy of that source supports readers without a library. There is
no elaborator-created Nat signature. `Nat`, `zero` and `succ` are ordinary
names; local bindings can shadow them. Explicit `import nat;` works too.
Program clients can select `prelude: false` to require explicit imports.

Clicking Nat in a proof opens its declared signature, and View source leads
to `nat.cubist` at the inductive declaration. Declared-type references carry
their source binding, including parameterized and recursive occurrences;
shadowed local names retain their own targets.

Numerals resolve the Nat declaration in scope and apply its registered zero
and successor constructors. The existing `induction` syntax constructs its
generic dependent eliminator. Both produce `Sort`, `Con`, `Elim` and ordinary
applications. Structurally recursive `match` definitions use the same rules.
The rebuilt arithmetic library defines addition with `match` on zero and
successor and a recursive call on the predecessor. The earlier `induction`
spelling continues to work with the imported Nat.

The [language reference](../../web/reference/induction.html) now teaches
ordinary declarations, parameterized constructors, exhaustive matching,
structural functions on Nat and lists, accumulator arguments and dependent
proofs. Checked examples also cover path constructors, generated truncation
clauses and the source W API. The chapter index and introductory function
and declaration chapters link to that guide, the errors chapter catalogues
the new refusals, and the quick reference has entries for `inductive` and
`match`. Excerpts quoted from `nat`, `naturals` and `w` are checked with
their module in the page, so their names open the kernel inspector.

Two spellings changed with the chapter. A path clause is written as the
point it covers, `loop @ i => …`, and `squash(x, y) @ i => …`; the former
`loop i => …` is refused with a message naming the new form. `induction n
return C { … }` no longer needs `as k` when the motive is constant and the
successor clause does not use the predecessor; `mul` and `le` in
`naturals` drop it, and the term display omits it in the same case. The
inner case analysis of `le` is a `match`, which names the predecessor in its
clause, `succ(j)`, instead of `as j`.

A linter, `web/mathscript/lint.mjs`, warns about bindings that are never
used and can be removed: `as` names on `induction` and `match`, `forall`
and `exists` variables, and `let`, `have` and `obtain` statements. Checking
reports its warnings in the CLI, the workspace and the reference pages, and
`npm run lint:cubist` lints files without checking. Required names, such as
parameters, clause arguments and induction hypotheses, are never reported.
The rebuilt library has no warnings; the archive has about 120 and is not
changed. Reference examples state their warnings as `// Warning:` comments,
and the errors chapter catalogues them.

[`w.cubist`](../../archive/first-library/w.cubist) supplies the ordinary type
and a structurally recursive dependent `wrec`. Use `import w;`. The API writes
its universe arguments explicitly:

```cubist
W(U, V, A, B)
wrec(U, V, R, A, B, motive, step, tree)
```

Here `U`, `V` and `R` are finite universes below `UU0`. `sup(a, children)`
infers its instance from an expected type; `typed(T, sup(a, children))`
provides it when needed. Nothing imports `w` now: `BinaryNat`,
`BinaryPositive`, `RadixNat` and `RadixPositive` are declared directly by their
constructors, and their recursion and induction principles are structural
`match` definitions. That removes 21 W-encoding helpers from the corpus.
`binary_induction` no longer needs `paths`, since function extensionality on
W child functions is gone. The display prints binary numbers from the new
constructors. Generic arguments at `UU0` cannot instantiate this
finite-universe declaration. A separate inductive at a fixed higher universe
works and is tested; no primitive W fallback remains.

## Kernel retirement and test boundary

The C formation, introduction, elimination, substitution and computation
cases for primitive Nat and W have been removed, along with their public
instruction functions and WASM dispatch cases. ABI 3 retains their numeric
slots as reserved values. Raw construction and all seven retired opcodes
are refused. The shared H1 rules implement arithmetic, child induction
hypotheses, composition and transport.

Current native suites exercise declared arithmetic and trees, signature
admission, isolation, conversion, levels, budgets and compact shared syntax.
The current driver/term-checker differential generator uses sums of Unit.
Old raw primitive-calculus tests ran against a separate historical oracle,
the kernel at `bfef585cfe09f4b94a658564dff505cd67855368`, until 2026-10-02.
Then that oracle was removed, and the tests of features the current kernel
keeps were moved to it: the translator's tests, now in `tests/translator`, check
raw syntax through the instruction kernel (`kernel-check.mjs`), with sums
and Unit in place of Nat. Tests of Nat, W and pushout primitives, and of
the old line protocol, were removed.

## Source-defined pushouts

Decided and implemented on 2026-10-01. Sums stay native: `A or B` keeps its
kernel primitive at every level. Pushouts become an ordinary declaration, so
the specification's assumed baseline (4.1) no longer contains them.
[`pushout.cubist`](../../archive/first-library/pushout.cubist) declares

```cubist
inductive Pushout(U < UU0, V < UU0, W < UU0, C : U, A : V, B : W, f : C -> A, g : C -> B) : max(
  U, max(V, W)
) {
  inl(a : A);
  inr(b : B);
  push(c : C) : inl(f(c)) = inr(g(c));
}
```

with a structural `pushout_induction`. Use `import pushout;`. As for W, the
universe arguments are explicit, and a pushout over `UU`-tier types needs a
separate fixed-universe declaration. The constructors take their instance
from the expected type. A path constructor applied at a point now reads it
from the point's expected type, so a motive's family can say
`P(push(c) @ i)`; the refusal without one says so.

- **Source.** The builtins `Pushout(C, A, B, f, g)`, `push_left`,
  `push_right`, `push_path` and `pushout_induction` are gone, and the names
  are ordinary. `suspension_types` keeps its API (`Suspension`, `north`,
  `south`, `meridian`, `suspension_induction`), now defined by the
  constructors and a `match`; its importers are unchanged. `cubical_paths`
  and the conversion-law example use `match`, and the meridian computation
  laws still hold by `rfl`.
- **Kernel.** The term checker's pushout rules, the pushout instructions and
  their computation (`check_pushout.c`, `pushout_compute.c`, the pushout
  transport in `hit_composition.c`) are removed. The tags 36–40 and the four
  instruction slots are reserved and refused. The term checker also loses
  its `HComp`/`Trans` rule, which only pushout families satisfied; declared
  higher sorts take them through the instruction kernel. The shared
  decomposition and `hcomp` elimination are renamed
  `ck_higher_composition` and `ck_eliminate_hcomp`.
- **Tests.** A new WASM test transports `push(tt)` along a line of pushouts
  whose left map moves along a meridian: the result types over the moved
  endpoint, its normal form is the corrected `hcomp` of specification 3.5,
  and eliminating it computes by `rfl`. The driver test derives the
  suspension from `sortBegin`, `construct` and `eliminator` judgements. The
  retired tags and opcodes are refused, in C and through WASM.
- **Historical oracle.** The pushout cases of X1, X3 and X6–X8 replay
  against the pinned pre-migration kernel, as W's do. X8's source-level
  pushout call is gone, since source pushouts are declared; its sum call
  remains.

Checks on the implementation tree, 2026-10-01:

- `node tools/test.mjs`: 713 tests passed, zero failures. The corpus has
  3,788 declarations, two more than before: `Pushout` and
  `pushout_induction`.
- `make -C kernel test`, `make sanitize SANITIZERS=undefined` and
  `make lint` passed.
- `node tools/build-site.mjs`, `npm run test:site` and
  `npm run test:browser` passed. In the page worker, every example of the
  cubical, induction and errors chapters and of the quick reference checked
  with its labelled verdict, the pushout excerpt with its module; the
  `pushout`, `suspension_types` and `cubical_paths` library pages show
  checked, no axioms, with no console errors.

## Migration ledger

Both sides of a historical-source comparison now import declared Nat and
therefore carry H1. The truncation ledger's 17 exact type and closed-value
pins have been refreshed for this representation. Their four scopes and
logical assumption deltas are unchanged. An exactly pinned type-valued
definition may change its returned type construction when both versions
already carry H1; ordinary proof changes still require ordinary verification.
Tampered values and changed private dependency closures are refused.

## Validation

Checks on the implementation tree:

- `node tools/test.mjs`: 712 tests passed, zero failures.
- `make -C kernel test`: all 13 native suites passed.
- `make sanitize SANITIZERS=undefined`: all 13 suites passed with fatal UBSan.
- `make lint`: C lint passed.
- `node tools/build-site.mjs`: the static site built successfully.
- `npm run test:browser` and `npm run test:site`: the inspector, workbench,
  static worker/WASM, reference examples and REPL flows passed.
- The cubical, statement, proof-navigation and landing browser scripts passed.
- `node tools/instruction-coverage.mjs --limit-ms=60000
  --report=build/h1-program-types-cost.json`: all 3,786 declarations checked;
  all 3,892 stored definitions re-derived, zero gaps. Nat, W and wrec are
  source declarations, and declaring the binary and radix numbers directly
  removed 21 W-encoding helpers.

Regression cases include ordinary-name shadowing, numeral constructor
resolution, source W child recursion, a fixed higher-universe W declaration,
bound-level renaming during replay, refusal of all retired APIs, and a folded
source Nat value of `2^22` without eagerly expanding it. Pinned CI results are
recorded in the pull request after those checks finish.
