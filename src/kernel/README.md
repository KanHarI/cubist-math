# Reviewing the type-checking kernel

This directory contains the checked inference implementation and its trusted
support code. Start with `apply.c`, then read the context and rule checks. The
public interface is [`include/thth.h`](../../include/thth.h); private data
structures and helper contracts are in `internal.h`.

| File | Correctness responsibility |
|---|---|
| `apply.c` | Validate requests, dispatch rules, enforce bounds, publish results, roll back failures; `tt_verify` |
| `contexts.c` | Reject escaping context dependencies and compute the conclusion's assumptions |
| `rules.c` | Universes, variables, formation/introduction, functions, definitional equality, rewriting, highlights |
| `eliminators.c` | Dependent elimination and computation for Void, Unit, Sigma, Sum, equality, Nat, and W |
| `ast.c` | Binding, substitution, reduction, universe helpers, and highlight paths |
| `store.c` | Immutable interning, exact equality, arenas, dependency sets, cache invalidation, inspection |
| `metadata.inc` | Generated opcode arities and permitted context-discharge masks |
| `internal.h` | Representation, key layouts, and internal function contracts |

The CLI and proof construction programs live outside this directory.
They submit steps through `tt_apply`. This is an organizational boundary, not
memory isolation: C code including the private header can mutate the engine.
Public callers should include only `thth.h`. A compiler, allocator, and the C
runtime remain part of the implementation's trust assumptions.

## Following one inference

`tt_apply` accepts an opcode, premise judgement IDs, an optional injected context,
and optional contexts to discharge. A successful call returns a checked context
or judgement ID, as specified by the opcode metadata.

1. Validate opcode, argument counts, required pointers, and every handle before
   dereferencing it. Copy premises because AST construction may grow arenas.
2. A cached result is usable only when the complete request key matches. The
   table hash alone never establishes identity. Recheck the expression-size
   limit, which builtin loading can temporarily change.
3. `check_contexts` checks that discharging an assumption cannot leave an
   unpermitted dependency on it in the remaining context. The metadata masks
   apply separately to each premise and each free-context slot.
4. `infer_rule` or `infer_eliminator` checks the rule's premises and constructs
   tentative expression/type nodes. `CtxExt` is handled directly in `apply.c`.
   These helpers do not publish judgements.
5. Enforce expression bounds, compute remaining assumptions, attach provenance,
   and call `save_judgement` (or `save_context` for `CtxExt`). These private
   storage functions assume that their caller has performed the checks.
6. On failure, return ID zero and remove only newly allocated AST nodes.
   Rollback invalidates transformation-cache generations before temporary IDs
   can be reused. Resource failures are not cached as permanent illegal rules.

`REQUIRE` in the rule files returns failure; it is not a debug-only assertion.
`EXPR(i)` and `TYPE(i)` denote the expression and type of premise `i`, starting
at zero. `f[i]` denotes an optional context to discharge in metadata order.
The elimination cases state their premise and context order beside the checks.

For example, `PiElim` requires `f : Pi x:A.B` and `a : A`, then constructs
`f(a) : B[a/x]`. It checks the function's constructor and exact domain/type
identity before instantiating the codomain. Context validity is checked by the
outer publication path, not repeated in this individual rule.

## Representation invariants

* IDs are engine-local arena indexes; zero is absent/error. Element zero is an
  initialized sentinel, including for unused premise slots of nullary rules.
* AST identity includes constructor kind, payload, and every child ID. A 64-bit
  hash locates candidates, then full-key equality resolves collisions. The
  derived size, depth, and occurrence flags are recomputed for new nodes.
* A constructor's arity is fixed by its kind. AST nodes and accepted judgements
  are immutable. Helpers copy nodes before allocations, so `realloc` cannot
  invalidate a live pointer used by a rule.
* Judgement identity includes expression, type, assumptions, highlight path,
  and highlighted side. Proof history retains the first checked derivation.
  Context identity includes type, assumptions, and explicit counter.
* Dependency sets are canonical sorted persistent lists of context IDs. Removing
  a context from a conclusion is governed by the rule's discharge masks.
* Transform-cache keys include substitution mode, input, replacements, depth,
  and rollback generation. Cache collisions replace entries, not proof checks.

Layout-dependent key prefixes have `offsetof` comparisons and compile-time
layout assertions. `make collision-test` forces every interning hash to zero
and exercises equality, growth, rollback, and checked inference.

## Binding and reduction conventions

`CRef`/`UCRef` refer to named contexts. Closing an abstraction replaces them with
`VRef` indices. `transform` performs simultaneous substitution so one replacement
cannot accidentally substitute into another. Its distinct modes are documented
in `internal.h`.

The port preserves upstream's **node-wide binder-depth convention**: the depth
increment applies to every child of Pi, Sigma, W, and the eliminators, rather
than only the children conventionally under a binder. The negative shifts in
eliminator beta substitution are also inherited. Review changes against the
ported dependent proofs; do not assume textbook de Bruijn traversal is equivalent.

`reduce` performs one bottom-up pass over the original tree and reduces each
visited root once. It does not normalize repeatedly until a fixed point. Type
matching uses structural identity; conversion requires explicit rewriting or
reduction inferences.

Nat checks distinguish the induction hypothesis `C(n)` from the successor
branch `C(succ(n))`, correcting an inherited upstream defect. Nat beta preserves
the recursive call's virtual binder levels while lowering the predecessor and
zero branch; W beta and WComp place the recursive child variable under the
new W eliminator's two virtual levels. Tests compare reduction before and after
closing an external context. EqComp also corrects upstream computation behavior.
See [compatibility.md](../../docs/compatibility.md) for details and Rust-oracle
exceptions. This layout and the tests support review; they are not a formal
soundness proof for the research calculus.

## Validation commands

```sh
make lint                         # Every C translation unit, including tests
make test collision-test          # Original proofs, all 67 opcodes, negative cases
python3 tools/check_reference.py   # Exact match to the frozen verified trace
make CC=clang sanitize            # AddressSanitizer + UBSan (Linux)
```

Lint includes the checked-in generated proof programs and opcode metadata through
their translation units, as well as public/private headers. It checks both normal
and forced-collision preprocessor configurations. Existing tests also compare
cached and uncached walks across several seeds. The independent Rust oracle and
its explicit exclusions are described in `docs/compatibility.md`.
