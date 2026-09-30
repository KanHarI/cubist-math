# Source-defined Nat and W

Implemented on 2026-09-30, based on `bfef585`. H1 is enabled by default in
the browser, CLI and source-checking tools. Mathematical release review of
H1 remains pending; changing the default does not discharge its soundness,
critical-pair or canonicity obligations.

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

Numerals resolve the Nat declaration in scope and apply its registered zero
and successor constructors. The existing `induction` syntax constructs its
generic dependent eliminator. Both produce `Sort`, `Con`, `Elim` and ordinary
applications. Structurally recursive `match` definitions use the same rules.

[`w.cubist`](../../archive/first-library/w.cubist) supplies the ordinary type
and a structurally recursive dependent `wrec`. Use `import w;`. The API writes
its universe arguments explicitly:

```cubist
W(U, V, A, B)
wrec(U, V, R, A, B, motive, step, tree)
```

Here `U`, `V` and `R` are finite universes below `UU0`. `sup(a, children)`
infers its instance from an expected type; `typed(T, sup(a, children))`
provides it when needed. The binary and radix corpus modules now use these
ordinary definitions. Generic arguments at `UU0` cannot instantiate this
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
Old raw primitive-calculus tests remain useful as a separate historical
oracle: `tools/legacy-kernel.mjs` builds the exact Git revision
`bfef585cfe09f4b94a658564dff505cd67855368` under `build/reference-kernel`.
That binary is never loaded by production checking or included in the site.
Historical comparisons do not certify the current producer; the current
native, source, corpus and driver tests provide that evidence separately.

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

- `node tools/test.mjs`: 704 tests passed, zero failures.
- `make -C kernel test`: all 13 native suites passed.
- `make sanitize SANITIZERS=undefined`: all 13 suites passed with fatal UBSan.
- `make lint`: C lint passed.
- `node tools/build-site.mjs`: the static site built successfully.
- `npm run test:browser` and `npm run test:site`: the inspector, workbench,
  static worker/WASM, reference examples and REPL flows passed.
- The cubical, statement, proof-navigation and landing browser scripts passed.
- `node tools/instruction-coverage.mjs --limit-ms=60000
  --report=build/h1-program-types-cost.json`: all 3,807 declarations checked;
  all 3,917 stored definitions re-derived, zero gaps. The three extra
  declarations are Nat, W and wrec; earlier primitive declarations supplied
  no source declarations.

Regression cases include ordinary-name shadowing, numeral constructor
resolution, source W child recursion, a fixed higher-universe W declaration,
bound-level renaming during replay, refusal of all retired APIs, and a folded
source Nat value of `2^22` without eagerly expanding it. Pinned CI results are
recorded in the pull request after those checks finish.
