# Proof ergonomics examples

These accompany the [implementation plan](../../roadmaps/proof-ergonomics-implementation-plan.md).
The current files are explicit expansions. The implemented files use new
arithmetic and cubical syntax and pass native checking. The scoped algebra
file remains a design fixture, excluded from `.cubist` corpus checks.

| Short source | Explicit expansion | Status |
| --- | --- | --- |
| [arithmetic](implemented/arithmetic.cubist) | [arithmetic.cubist](current/arithmetic.cubist) | Native checked: typed `have`, `calc`, `rw`, `simp only`, `simpa only` |
| [cubical](implemented/cubical.cubist) | [pointwise.cubist](current/pointwise.cubist) | Native checked: expected paths, interval application, `ext` |
| [dependent](implemented/dependent.cubist) | [dependent-transport.cubist](current/dependent-transport.cubist), [path-coherence.cubist](current/path-coherence.cubist) | Native checked: direct PathP action and explicit transport bridge |
| [type transport](implemented/type-transport.cubist) | [type-transport.cubist](current/type-transport.cubist) | Native checked: `simpa` and `simp` along paths of types and type-valued families |
| [registered simp](implemented/registered-simp.cubist) | [arithmetic.cubist](current/arithmetic.cubist) | Native checked: default/named sets, simplified hypothesis copy and conditional equality premises |
| [scoped algebra](proposed/scoped-algebra.cubist.proposed) | [scoped-algebra.cubist](current/scoped-algebra.cubist) | Design only: lexical notation packs |

Arithmetic elaborates to checked composition, inversion and congruence witnesses.
Function equality swaps an interval binder and a term binder. The naturality
square uses its expected PathP families. The transport shorthand infers
endpoints while preserving the chosen path. The remaining structure notation
proposal would expand to ordinary field operations on an explicitly chosen field.

The dependent examples deliberately distinguish `section_path` from
`section_after_transport`: the former is a path in varying fibers; the latter
is an equality in the final fiber. Neither is interchangeable with ordinary
`cong` without checking the fiber. `loop_action_right_unit` leaves the supplied
loop in the final transport and needs no `IsSet` assumption.

The type-transport pair makes the new non-equality `simpa` reconstruction
explicit. A path `p : A = B` transports a value between `A` and `B`; an
equality `n + 0 = n` lifts through a fixed-codomain family `P : Nat -> U0`
to a path between `P(n + 0)` and `P(n)`. The simplifier does not turn two
ordinary maps `A -> B` and `B -> A` into a path of types.

## Checks and reproducibility

See the [current examples' verification record](current/README.md) for exact
declaration counts, assumption checks, formatter results and CLI commands.
The baseline check `npm test -- docs/examples/proof-ergonomics/current/*.cubist`
passed: six files, 19 declarations, zero axiom dependencies. The new
`npm test -- docs/examples/proof-ergonomics/implemented/*.cubist` selection
checks 30 declarations, also without axioms.
Focused rejection tests are in `tests/proof-ergonomics.test.mjs`. The complete
roadmap remains in progress.

The selected real-library [snapshot](baseline.json) is separate from these
small examples. Reproduce it with the existing C/WASM build:

```sh
node docs/examples/proof-ergonomics/measure.mjs
```

This overwrites `baseline.json` with source hashes, token/line counts, machine
and revision metadata, one timing observation, aggregate native checking steps
and rewrite work per declaration, the kernel arena snapshot at each final check, and import-graph
status. The arena snapshots include earlier retained terms; they are not
per-declaration memory deltas. The script does not overwrite the site's
benchmark report. Review the JSON diff before retaining a newer baseline. The
snapshot explicitly lists unmeasured quantities; timings are not estimates of
future speedups. Hashes pin the source of inferred theorem statements without
serializing normalized types.
PR 1 must additionally preserve checked signatures and assumption inventories.

The separate [rewrite-work snapshot](rewrite-work.json) measures the paired
explicit and ergonomic arithmetic examples plus registered simplification.
Regenerate it with:

```sh
node docs/examples/proof-ergonomics/rewrite-work.mjs
```

One observation checked 19 example declarations with references disabled.
The explicit `add_zero_twice` uses 35 source tokens and 115 native checking
steps; `add_zero_twice_simp` uses 25 tokens, 309 native checking steps and 13
candidate visits. The shorter source currently costs more checking work in this
small example. `recursive_premise` uses 47 candidate visits and two failed
premise searches; the child `nat_add_zero` rewrites complete its proof. A
separate nested test checks two levels of successful premise reconstruction.
These counts
describe this exact source and import order; the recorded arena values are
cumulative snapshots, not per-declaration allocation deltas.

## Rejection examples and remaining acceptance tests

These illustrate current and future negative cases. The focused test file
covers false equality, wrong occurrences, cycles, unsupported dependent
positions, loop non-erasure, and a malformed naturality square. Other rows
remain test targets for later implementation.

| Future snippet/context | Required result |
| --- | --- |
| `def false_goal : 0 = 1 { simp only []; }` | Residual `0 = 1`, unfinished proof. |
| `calc { x = y by p; _ = z by q; }`, with `q : x = z` and distinct `x,y` | Reject the second step's left endpoint. |
| `rw [p] at lhs occurrence 2;` with one eligible occurrence | Error naming the missing occurrence; no partial statement result. |
| `p : x = y`, `C : A -> U0`, `v : C(x)`; change `v` to type `C(y)` by ordinary congruence | Require explicit transport or report unsupported dependent position. |
| `def collapse(A : U0, x : A, p : x = x) : p = refl(x) { simp only []; }` | Leave the higher equality unsolved; never assume UIP. |
| In the naturality square, replace the body with `path j => path i => H(x) @ j` | Reject the generic right edge and outer endpoints; dimensions are not decorative. |
| `exact path i => ...` without an expected path family | Request an explicit `path(family, body)` or a type annotation. |
| `simp only [p, <- p];` on a nontrivial local equality | Cycle/budget diagnostic, with involved rules; no success via a partial run. |
| Equality `law(a,a) : op(a,a) = a` matched against `op(x,y)` | Require conversion of `x` and `y`; do not assign the same rule parameter twice. |
| A registered lemma with an unproved premise | Keep a witness obligation or reject the rule use; no assumed premise. |

Future inference tests must also distinguish `_` as the previous endpoint in a
`calc` step from `_` as a scoped term hole. A term or dimension from one branch
must not solve a hole in a sibling branch.
