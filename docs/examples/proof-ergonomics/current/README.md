# Checked expansions using today's language

These files use current syntax and existing checked constructions. They are
executable reference expansions for the proposed ergonomics features, not
implementations of those features. All 19 declarations passed the native C/WASM
checker on 2026-09-24 and reported an empty axiom dependency list.

| File | Purpose | Declarations | Source tokens | CLI kernel steps |
| --- | --- | ---: | ---: | ---: |
| [arithmetic.cubist](arithmetic.cubist) | Equality chains, fixed-codomain congruence, reverse rewrite | 3 | 108 | 14,358 |
| [type-transport.cubist](type-transport.cubist) | Forward/inverse transport along type and index paths | 3 | 143 | 14,383 |
| [path-coherence.cubist](path-coherence.cubist) | Higher unit/associativity paths and preservation of loop action | 3 | 234 | 6,031 |
| [dependent-transport.cubist](dependent-transport.cubist) | Fiber change, direct `PathP`, transported `apd`, checked bridge, transport composition | 5 | 468 | 6,258 |
| [pointwise.cubist](pointwise.cubist) | Function paths, dependent sections, evaluation coherence, naturality square | 4 | 464 | 671 |
| [scoped-algebra.cubist](scoped-algebra.cubist) | Explicit structure projections for future scoped notation | 1 | 60 | 210,357 |

Tokens use `tokenize(source).length - 1` from `web/mathscript/parser.mjs`,
excluding comments, whitespace, and EOF. The CLI's “kernel steps” are
`CubicalProgram.check().instructionCount`: accumulated checking steps, including
imports and elaboration queries, **not** the sum of checking and reduction work.
Each CLI invocation checks a fresh program. These small fixtures are semantic
baselines; they do not establish a performance improvement.

Run from the repository root with the existing WASM build:

```sh
node cli/repl.mjs check docs/examples/proof-ergonomics/current/arithmetic.cubist
node cli/repl.mjs check docs/examples/proof-ergonomics/current/type-transport.cubist
node cli/repl.mjs check docs/examples/proof-ergonomics/current/path-coherence.cubist
node cli/repl.mjs check docs/examples/proof-ergonomics/current/dependent-transport.cubist
node cli/repl.mjs check docs/examples/proof-ergonomics/current/pointwise.cubist
node cli/repl.mjs check docs/examples/proof-ergonomics/current/scoped-algebra.cubist
node tools/format-mathscript.mjs --check docs/examples/proof-ergonomics/current/*.cubist
```

Each check exits 0 and prints the declaration and step counts above; the
formatter reports `6 sources checked; 0 need formatting.` Imports resolve
beside the source file first, then in `archive/first-library/`; these examples use bundled
`primes`, `paths`, and `field_vector_spaces`. They introduce no axioms, universe templates, or custom
import overrides. The empty assumption lists were also verified through the
program API (`result.outputs.every(d => d.axioms.length === 0)`); the CLI's
success message alone does not establish that property.

The most useful regression details are the retained witnesses:

- `loop_action_right_unit` simplifies the composite loop to the supplied `p`.
  Its result remains `transport(C, x, x, p, v)`, which is not asserted to be `v`.
- `section_path` is a path in a varying fiber, whereas
  `section_after_transport` compares two terms in the final fiber. A future
  surface notation must distinguish these presentations or insert their proved
  bridge explicitly. `section_via_transport` checks the existing
  `path_from_transport` bridge on that same family.
- `pointwise_evaluation` checks that evaluation recovers the supplied `h(x)`
  by conversion. An implementation that replaces an arbitrary pointwise path
  with reflexivity cannot pass the same generic statement.
- `naturality_square` is a `PathP` whose endpoints are `cong(f, p)` and
  `cong(g, p)` and whose side edges are `H(x)` and `H(y)`. Its nested path
  construction checks all four boundaries without assuming they are constant.
- `field_add_zero` uses the field's selected operations throughout. Its count
  includes the larger algebra import graph; a scoped notation expansion must
  preserve those operation identities and the empty axiom list.

The generic loop examples express preservation for every loop; they are not a
proof that a particular circle loop is nontrivial. A full simplifier release
also needs the existing circle/univalence corpus and negative acceptance tests.
