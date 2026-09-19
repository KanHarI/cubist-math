# Interactive proof workbench

The browser and CLI use the **same JavaScript session interpreter and actual C
kernel compiled to WebAssembly**. There is no JavaScript type-checker or simulated
proof engine. Each accepted instruction calls `tt_apply`.

## Start

Requires Node.js 24+ for the CLI/tests, Python 3 for the static server, and
Emscripten 6.0.9 for the WASM build. If Emscripten is already on PATH:

```sh
make wasm
make cli
# In a separate terminal:
make serve
```

Open http://127.0.0.1:8088/ for proof highlights, then browse the MathScript
proofs or open `/workbench.html` for the kernel workbench. Proofs run locally in a Web
Worker; the server only serves static files. A repository-local SDK is also
supported and automatically detected by Make:

```sh
git clone --depth 1 https://github.com/emscripten-core/emsdk.git .tools/emsdk
.tools/emsdk/emsdk install 6.0.9
.tools/emsdk/emsdk activate 6.0.9
make wasm
```

`.tools/`, the generated `web/dist/` files, and browser test artifacts are ignored.
The native engine still builds with `make` without Node, Python, or Emscripten.

## Existing proofs and the prelude library

Both interfaces start with the prelude's full **50 exported judgements**, including
`LEM` and `AOC`. Other library names use `lib_`, for example `lib_Unit`,
`lib_pr1`, `lib_funext`, and `lib_univalence`, to leave ordinary names free for
user programs. Explicit axiom instructions are labelled **AXIOM** in the browser;
this label does not claim that other objects are independent of axioms.

The browser's **Existing proofs & library** selector opens all **24 original
proof-construction routines**, the complete prelude library, the existing
polymorphic identity example, the WNat-to-Nat equivalence, and Euclid’s infinitude of primes: **28 programs**. This includes composition, product
commutativity, both projection implementations, equality operations, homotopy,
truncation, choice, excluded middle, uniqueness results, and every basic type.
The original projection helper is instantiated with U0, as in its caller.
The theorem examples are automatically verified when opened.

`open wnat_equiv` opens the new checked equivalence `WNat ≃ Nat`. Its
`wnat_to_nat_isEquiv` proof inhabits `WNatToNat_isEquiv`, the existing
half-adjoint `isEquiv` definition applied to the conversion function. The
1,910-step replay uses only the existing function-extensionality axiom; it
introduces no choice, excluded-middle, or equivalence axiom. Both maps, both
round trips, and the coherence proof are named inspection targets. See
[the construction notes](../docs/wnat_equivalence.md) for the argument and kernel fixes.

```text
proofs
open comp
check Composition composition
open product_commutes
check ProductCommutes product_commutes
open prelude_library
show LEM
show AOC
preview lem_equality = kernel.DefEqRefl(LEM)
accept
save with_choice.thth.json
```

Opening a bundled program replaces the current proof and adopts its displayed
axiom policy. Save current work first if needed. The complete library begins
with axioms enabled; constructive programs open with axioms disabled. `open unit`
provides a small constructive starting point; `goto 0` then clears its program.

Every original construction step is preserved, including repeated instructions
whose results share an interned ID. Individual proof files show intermediate
objects by default. The combined library initially shows only its 50 exports;
use **Show intermediate steps**, or CLI `list all` and `show NAME`, to inspect
its derivation. Selection, reduction, and additional inference work on those
objects exactly as they do on newly constructed objects.

Portable [JSON replay files and .math source](proofs/) live in `web/proofs/`.
They contain instructions and named operands, not trusted prechecked results.
`make proof-export` regenerates them from the checked C proof programs using
the native inference trace, then constructs the new equivalence through WASM
(C compiler, Python 3, Node.js, and Emscripten required). CI checks
regeneration and replays every JSON and source file through WASM. Coverage is
checked against `docs/proof_sources.json`, and the exporter rejects missing routines.

## CLI: direct selection

```text
math> demo
math> use nested
math> select expr.argument
math> children
math> reduce reduced
PREVIEW (live proof unchanged)
... generated HighExp, High1, BetaReducePointed, UnHigh instructions ...
math> accept
math> undo
math> history
math> goto 3
```

History revision numbers are shown by `history`; use the actual number from your
session. `select expr.1` is the equivalent numeric path. `parent` ascends and
`down argument` or `down 1` descends from the current selection. `select type`
selects the whole type; `select type.codomain` selects a Pi/Sigma codomain.
Readline provides command history and basic tab completion. Commands can also be
piped into the interpreter for reproducible sessions.

## CLI: selection with parentheses

After `demo`, the displayed `nested` expression is:

```text
((λ x0. x0) ((λ x0. x0) ⋆))
```

Copy that exact text, putting one **additional** pair of parentheses around the
inner application:

```text
select expr --paren ((λ x0. x0) (((λ x0. x0) ⋆)))
```

The equivalent unambiguous bracket form is:

```text
select expr --paren ((λ x0. x0) [[((λ x0. x0) ⋆)]])
```

Use `select type --paren ...` for its type. Outer single/double quotes around the
whole command argument are optional. Existing whitespace and mathematical text
must be preserved. These commands select an existing AST occurrence; they do not
parse an edited expression into a new proof. Arbitrary textual changes and spans
that do not correspond to complete subtrees are rejected. If extra parentheses
are ambiguous, use the path or bracket form.

Two identical-looking occurrences are distinct selections even when the kernel
interns them as the same node ID. Selection always uses an occurrence path.

## Browser

The initial example selects the inner application of `nested`. Click **Reduce
here**, inspect the preview and generated instruction log, then **Accept step**.
The mathematical workspace remains unchanged until acceptance. Click another
subexpression or use the path/parenthesis editor under the expression inspector.

**Rewrite within selection** takes a definitional equality witness (for example
`equality` from the demo). The existing `HighSubs` rule substitutes matching
occurrences throughout the selected subtree, not necessarily only its root.
**Reduction pass in selection** is one bottom-up pass, not full normalization.
**Unfold / reduce here** uses the existing definition-enabled pointed reduction.

The operation palette exposes all 67 kernel instructions with judgement operands,
an injected context when required, and optional free-context slots. The source
input also accepts every canonical opcode. Rejected previews show the kernel
status and leave the live proof unchanged. The browser currently reports a
rule-level failure, not a complete dependent-type mismatch explanation.

## Source language and proof files

```text
U = universe.zero()
x = assume(U)
A = var(x)
closed = lambda(U, A; bind: x)
```

One binding per line; no nested instruction calls. Names are immutable ASCII
identifiers. The parser never evaluates JavaScript. `#` and `//` begin comments.
The canonical form is:

```text
result = kernel.PiIntro(U, A; free: [x])
value = kernel.Vble(; context: x)
```

`_` denotes an absent optional context. Friendly names include `pi`, `lambda`,
`apply`, `unit`, `unit.value`, `nat`, `zero`, `succ`, `eq.refl`, `defeq.refl`,
`focus.expr`, `focus.type`, `focus.child(j, 0)`, `focus.parent`, `focus.clear`,
`rewrite.focus`, `reduce.focus`, and `reduce.pass`. `ops` lists all canonical rules.

`assume(A)` chooses a predecessor of the same interned type to create a fresh
context counter. `assume(A; after: x)` or raw `CtxExt` gives exact control instead.
The selected predecessor is recorded in canonical source and exported proof files.
A context and its variable judgement remain separate instructions and categories.

To construct and verify the included polymorphic identity from an empty session:

```text
run examples/identity.math
accept
check Identity identity
save identity.thth.json
```

`preview name = kernel.Operation(...)` previews a single instruction. `source`
prints the accepted instruction program. `save FILE` exports the active branch;
`load FILE` checks every instruction before replacing the session. Browser Open
and Save use the identical JSON format. Exports are replay programs, not trusted
serialized conclusions or raw engine IDs. Branch alternatives are retained in
memory; only the active branch is exported in this version.

The full prelude library starts with axioms enabled. `axioms on/off` or the
browser checkbox changes the policy by replaying the active proof. Turning axioms
off fails atomically if that proof uses an axiom; open a constructive bundled
program to start without them. Ordinary file imports require a matching policy.
To load a saved constructive file from the initial library session, first open
`unit`; for a file using axioms, enable the checkbox or run `axioms on` first.
A failed replay never changes the accepted proof or policy.

## Execution and observability

- Selection is UI state. Acting on it emits explicit focus instructions, the
  transformation, and `UnHigh`. Intermediate focus results are hidden in the
  object list but remain in the exported source and kernel.
- Preview replays the current accepted program in a separate engine, then checks
  candidate instructions. Accept swaps in that checked engine. Failed previews,
  discarded previews, and malformed imports cannot publish into the live engine.
- Each accepted action creates a history revision. Undo and branch checkout use
  deterministic replay. There is no hidden rollback of accepted kernel objects.
- Source occurrences are stored independently of deduplicated judgement IDs.
- `stats` and the browser panel expose calls, cache hits, AST nodes, judgements,
  contexts, and reserved engine allocation. Preview elapsed time includes replay.
- Inspection is bounded to 350 displayed tree occurrences and depth 40. Ellipses
  mark omitted subtrees; truncated placeholders cannot be selected. Large terms
  require more capable lazy inspection in a later version.
- Mathematical printing uses named lambda binders where possible and explicit
  reference notation for unsupported cases. It is an inspector, not an elaborator
  or independently type-checked pretty-printer.

The kernel bridge limits expressions to 16,777,216 tree nodes, context counters
to 16,384, and depth to 256. AST and judgment storage pools double as needed,
without fixed count caps. Allocation failure still rejects the operation.
Sessions allow 4,194,304 instructions and 256 accepted history actions. The WASM
heap starts at 16 MiB and may grow up to the wasm32 ceiling of 4 GiB as allocation
permits. Workbench requests time out after 30 seconds; mathematical checking
has a 300-second budget. Reset example starts a new worker. Save useful work
before large explorations.

This first version supports forward proof construction and replay. Goal-directed
search, structured kernel predicate diagnostics,
lazy deep-tree expansion, and separately compiled proof-program WASM artifacts
are follow-up work. The current WASM artifact contains the C kernel; the shared
interpreter dispatches the named instruction program to it.

## Validation

```sh
make test collision-test lint
make wasm-test
npm ci
npx playwright install chromium
npm run test:browser
```

Tests cover preview isolation, rejection/import atomicity, stale preview tokens,
fresh assumptions, branch replay, source/JSON round trips, explicit axiom policy,
all 67 opcode spellings, identical-node occurrence selection, and the real CLI.
WASM also replays the native reference trace, checking successful expression,
type, and context fingerprints (resource-policy failures, if present, are excluded).
Browser tests exercise clicking/marking, reduction, rewriting, undo, failed
previews, and save/import against the real worker and WASM module.

Click an underlined axiom reference to open its declaration and type, or a
`def` reference to open its defining expression and type. This also works for
hidden intermediate declarations. **Back** returns to the previous expression
and selection. Use **Shift-click** to select the reference instead; keyboard
Enter/Space follows the link, and Shift-Enter/Space selects it. Path and
parentheses selection also remain available.

Large expression views initially show at most 350 nodes and 40 levels. An
ellipsis is a display abbreviation, not a proof hole. Click it or **Show full
expression/type** to render the complete tree (within the kernel's 65,536-node,
256-level bounds). Collapse returns to the abbreviated view. These controls do
not alter the checked term or proof history.

The inspector shows **Verified closed judgement** when the kernel verifies the
current object against a named proposition. Click the proposition to inspect its
type expression. **Inferred by** shows the actual instruction and clickable
premises, including hidden steps. For WNat ≃ Nat, `wnat_to_nat_isEquiv` inhabits
`WNatToNat_isEquiv`, the unfolded specialization of the library's `isEquiv`:
an inverse, two round trips, and the coherence condition.

To inspect recorded Gross–Knuth passes, enable **Show intermediate steps** and
filter for `GrossKnuth`. Open a result, then use its **Inferred by** premise to
inspect the input. The instruction log also records every pass. For WNat's
`isEquiv` type, `p3006_PiElim` is followed by `p3007_BetaReduceGrossKnuth` and
`p3008_BetaReduceGrossKnuth`. To run a new pass, select a subtree and choose
**Reduction pass in selection**; inspect the preview before accepting it.

`open primes` loads the constructive infinitude-of-primes theorem with axioms
disabled. Check it with `check InfinitelyManyPrimes infinitely_many_primes`.
See [the proof and definitions](../docs/infinitely_many_primes.md).
