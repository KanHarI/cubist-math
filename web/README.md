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

Open http://127.0.0.1:8080 for the browser. The page runs proofs locally in a Web
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

Axioms are disabled initially. `axioms on` or the browser checkbox explicitly
enables `Axiom`. An import cannot silently enable axioms; its policy must match
the current session. Turning axioms off replays the current branch and fails
atomically if an axiom instruction is present.

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

The kernel bridge limits expressions to 4096 tree nodes, AST storage to 500,000
nodes, judgements to 100,000, context counters to 256, and depth to 256. Sessions
allow 4096 instructions and 256 accepted history actions. WASM memory is capped
at 256 MiB. The browser terminates its worker after a 30-second request timeout;
Reset example starts a new worker. Save useful work before large explorations.

This first version supports forward proof construction and replay. Goal-directed
search, structured kernel predicate diagnostics, transitive axiom highlighting,
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
