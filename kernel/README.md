# Cubist cubical C kernel

This is the sole trusted checker for Cubist Math. It implements cumulative
universes with universe-generic definitions, dependent functions and pairs,
Unit, Void and sums, declared inductive and higher inductive types (H1) with
their dependent elimination, interval paths, composition and transport, and
Glue. Nat, W, pushouts and suspensions are source declarations, in
`archive/first-library/`. The website and CLI use this code through
WebAssembly (`wasm/cubical_bridge.c`).

## Trust boundary

The kernel is the instruction kernel
([design](../docs/roadmaps/kernel-instructions.md)): each typing rule is an
instruction (`cc_instr_*`, `src/instructions.c`, with declared types in
`src/signatures.c` and `src/eliminators.c`) whose side conditions are
syntactic, and a definition is admitted only by the `Define` instruction.
The computation that instructions call, such as `Step`'s reductions,
composition and transport, is trusted with them.

The queries (`cc_kernel_whnf`, `cc_kernel_normalize`, `cc_kernel_rename`,
`cc_kernel_endpoint_term`) compute on syntax and certify nothing. The
untrusted driver (`web/cubical-instruction-driver.mjs`) uses them to choose
the instructions it issues, and each instruction checks its premises as any
other. Until 2026-10-02 the kernel also held a term checker and a
conversion search, as untrusted elaboration aids; work plan I1.2b removed
them, and the comparison that instructions use is now the only one.

The isolation that work plan I1.2a established still holds, and
`tests/test_isolation.c` checks it: a query made before an instruction does
not change whether it is accepted, weak-head reduction contracts pair and
Glue eta only when their sides are the same syntax, and the `Glue` step
contracts Glue eta when its side conditions agree. The probe that the
[2026-09-28 audit](../docs/roadmaps/audits/2026-09-28-audit.md) used is one
of these regressions.

## Reading the mathematics in the code

| File | Mathematical responsibility |
|---|---|
| `include/cubical.h` | Two distinct sorts of formula, their representation and operation contracts |
| `src/formula.c` | Finite joins of finite meets; absorption and shared storage |
| `src/interval.c` | De Morgan reversal and dimension substitution |
| `src/faces.c` | Endpoint equations, face substitution and entailment |
| `include/cubical_kernel.h` | Opaque arena, raw handles, instructions, judgements and queries |
| `src/term_store.c` | Inert syntax allocation, bounded handles, budgets and errors |
| `src/term_substitution.c` | Capture-avoiding term and dimension substitution |
| `src/syntax_cache.c` | Memoized pure operations on the immutable syntax graph |
| `src/instructions.c` | The instruction kernel: forward rules on a graph of judgements |
| `src/signatures.c`, `src/eliminators.c` | Declared types (H1): admission, instances, constructors, elimination |
| `src/term_conversion.c` | Comparison modulo bound names and the interval algebra; syntactic cumulativity |
| `src/levels.c` | Universe levels: normal forms, equality and order by arithmetic (G0 §2.4) |
| `src/term_normalize.c` | Weak-head computation; separate optional normal forms; eta only by syntax |
| `src/term_expose.c` | One beta, projection or boundary step that keeps its result compact |
| `src/composition_compute.c` | Composition for Unit, Π, Σ and paths; derived filling |
| `src/inductive_composition.c` | Composition at sums and at declared data sorts |
| `src/hit_composition.c` | Composition and transport of declared higher sorts, with boundary correction |
| `src/glue_compute.c` | Glue composition and derived universe composition |
| `src/equivalence_terms.c` | Derived contractible-fiber types and the identity equivalence |
| `src/definitions.c` | The definitions Define admitted |
| `src/queries.c` | Weak heads and normal forms on request; the arena's size |
| `src/checkpoint.c` | Checkpoints, rollback and compaction of the arena |
| `src/deadline.c` | A wall-clock deadline that only rejects work |
| `tests/lattice_cli.c` | Inert test input, separate from the trusted algebra |

A clause is a conjunction of generators, represented by two bitsets. A formula
is a disjunction of clauses. Removing a clause that contains another implements
absorption. `positive` and `negative` have different meanings in the two sorts:

- Interval: `i` and `1-i`; their conjunction is allowed.
- Face: `i=1` and `i=0`; their conjunction is impossible.

The empty list is bottom; the list containing an empty clause is top. Joining
formulas concatenates their clauses and applies absorption. Meeting them takes
every pairwise union of clauses and applies absorption. Comments beside each
operation state the corresponding mathematical rule.

Outputs are assembled in private candidates, then published on success. Inputs
may alias outputs. Allocation failure never establishes an equation. Formula
storage belongs to this trusted component; the C structs are not a certificate
format in which untrusted clients may inject arbitrary memory.

The representation supports 64 distinct dimensions, including dimension 63.
Dimension 64 is rejected, never masked to zero. This is a documented native
implementation restriction, not a restriction of cubical type theory. Dynamic
bitsets or a sparse dimension representation are required before removing it.

A universe carries its level as a child: a level expression over constants
`ω·tier + n` below ω², successors, maxima and variables (G0). Levels are
compared by normal form, so equality and cumulativity are arithmetic, never
search; `CC_LEVEL_MAX` and `CC_TIER_MAX` bound them. Level variables are
bound by instructions (`Level`, `LevelPi`, `LevelLambda`, `LevelApply`), so a
universe-generic definition is one derived term (G0). Cumulative upward
inclusion is not downward resizing. The syntax encoding has an ABI version,
`cc_kernel_abi_version()`; the JavaScript loader refuses a client written for
another.

## Running the checks

From the repository root, run `make test`, `make sanitize`, and `make lint`.
The library's tests in `lib/cubical/tests` check raw syntax through this
kernel's instructions, and `npm test` runs them with the rest. The public
corpus benchmark is `web/benchmark.html`; timing results depend on hardware
and browser.

## Compact computation

### Definitions and demanded heads

`Define` registers a closed judgement and returns a folded `CC_DEFREF`;
`Lookup` recalls it at its type, and `cc_kernel_definition` returns its body
and type. `Step(Delta)` unfolds a reference where a derivation needs it.
`cc_kernel_whnf` exposes the demanded head without strongly normalizing
arguments, which suits the driver's type-shape queries. A raw application of
an explicit path lambda can beta-reduce without a type annotation, since this
is just capture-avoiding substitution. Endpoint computation for a neutral
path needs its Path type, which the instructions record in the application.
So a head query can simplify `(<i> A) @ 1` without treating an unknown
neutral path as having arbitrary endpoints; `tests/test_path_head.c` checks
the distinction.

### Sharing during substitution

Free-name analysis and capture-avoiding substitution memoize exact immutable
syntax keys. This prevents repeated traversal of a shared term as if it were
an exponentially larger tree. The bounded direct-mapped table has 8192 entries;
a hash collision only discards an optimization. It stores no typing judgements
and cannot bypass checking a context or a face restriction. Its allocation is
included in the reported arena memory. Substitution also returns the original
node immediately when the substituted variable or dimension does not occur.

### Sharing during comparison

Comparison memoizes syntax pairs too. Its exact key includes both term
handles and unique identifiers for the complete term-binder and
dimension-binder scopes. Scope identifiers are never reused; they are not
hashes of context names. This preserves the distinction between bound and
free names, including under shadowing. Collisions only replace an older
entry. A renaming is left out of the key, and the comparison, where neither
side has a renamed name free: then the pair compares the same under every
renaming. So a shared graph below differently named binders is compared once
per node, not once per path to it. Each node carries masks of the term
variables and dimensions it mentions, which rule most names out at once; the
rest are looked up exactly, and only for terms at least eight levels deep. An
entry holds the comparison's result, equal or different, and no typing
judgement; `tests/test_comparison.c` checks these properties.
