# Cubical experiment: scope, specification, and migration ledger

Branch: `experiment/cubical-hott`, based on `dd3fcc8`. The production kernel and
website remain unchanged. This experiment was explicitly requested on 2026-09-20.

## Chosen calculus

The target is the De Morgan interval calculus of Cohen, Coquand, Huber and
Mörtberg, [Cubical Type Theory](https://arxiv.org/abs/1611.02108), with the
computational higher inductive extensions in
[On Higher Inductive Types in Cubical Type Theory](https://arxiv.org/abs/1802.01170).
The first implementation is an executable, independently checked reference core
in JavaScript. It is deliberately separate from the optimized production C
checker. This makes new trusted rules reviewable before changing the production
certificate format, evaluator, or inspector.

An interval variable is NOT an element of a two-element type. Its De Morgan
algebra has connections and reversal, but `i /\ ~i` is not zero and
`i \/ ~i` is not one. Cofibrations are a DIFFERENT lattice: the faces `i=0`
and `i=1` have empty intersection, but their union is not the whole interval.
Conflating these algebras invalidates the model.

## Phases and acceptance criteria

1. Canonical interval/face algebra, substitution, entailment and exhaustive
   small-expression tests. Inventory every MathScript source and its obligations.
2. Checked dependent functions, pairs, naturals, universes and interval paths;
   checked endpoints, substitution, path beta/eta, computational FunExt.
3. Uniform composition and filling, including dependent families, face systems
   and all overlap checks. Composition through every supported type former.
4. Glue, its composition, a derivation of univalence and executable transport
   examples. Do not add a primitive `ua` axiom or a special-case rewrite and call
   it CCHM univalence.
5. Computational suspension and truncation; the Id/Path bridge. The production
   Id/J computation rule is a migration obligation: cubical Path's J only has
   propositional computation in general. Evaluate cubical identity types before
   promising a source-compatible judgemental translation.
6. Translate all existing declarations, retaining LEM/choice exactly where
   explicitly used, deriving rather than postulating FunExt/univalence, and
   reporting each HIT or universe gap. Replaying the old checker is compatibility
   evidence, never evidence that a declaration has been translated.
7. Compare runtime, peak memory, proof/certificate size and instruction count
   on univalence transport, circle loops, group identity, F4 correspondence and
   quotient groups. JavaScript-reference and native-C timings are not a fair
   implementation-performance comparison and must be labeled accordingly.

## Current state

This is an incomplete experiment, not a cubical replacement kernel. The first
increment implements interval/face normal forms, dependent Pi/Sigma, naturals
with induction, cumulative universes, and dependent Path abstraction/application.
Function extensionality is checked as an interval abstraction, with a computing
pointwise roundtrip, without adding an axiom. The original `basics.proof`
translates completely (identity, duplication, natural-number copying and the
proof that copying two gives two). The current whole-library translation pass
checks **116 of 2,069 declarations** in this fragment; 1,953 remain explicit gaps.
See [the exhaustive results](translation-results.json) and
[the source inventory](migration-inventory.md). Counts are for declarations,
not entire modules, and are not an estimate of the remaining effort. The census
includes 212 MathScript modules and separately lists 28 legacy construction
artifacts, which the cubical translator does not admit as trusted exports.

Composition now checks every tube/base boundary and every overlap of its face
system. Its computation rules cover Nat, Unit, Pi, Sigma and Path. Pi composition
uses backward filling in the domain; Sigma composition fills the first component
before composing the second. Derived Path induction has the expected weak beta
behavior: a test deliberately rejects a source proof depending on the old
judgemental J beta rule for an unknown type. Concrete universe-schema uses are
checked at their supplied level; the schema itself is not counted as a translated
closed declaration. Downward resizing is rejected.

No existing declaration is claimed translated merely because it parses or because
the old kernel checks it. Missing universe composition, Glue or HIT rules are gaps, not
assumptions silently inserted into a new checker.

The production library currently has documented unrelated reference-trace and
proof-export CI failures; see [the Galois handoff](../galois-handoff.md).
Complex analysis and further Galois development remain paused. Migration covers
their existing proofs, not completion of their unfinished mathematical goals.

## Universe policy

Retain explicit cumulative universes U0, U1, ...; do not introduce resizing.
Ascending a universe is distinct from making an arbitrary large type small.
The source's compile-time `Universe` parameter and extra kernel universe
constructors require a specified translation, not erasure. Quotient HITs should
preserve the input universe once their computation and elimination are checked.

## Native C work

The first independently implemented C component is now available under
[`experiments/cubical/c`](../../experiments/cubical/c/README.md): interval and
face normalization, reversal, endpoint equations, substitution and entailment.
It is organized by mathematical responsibility with shared formula storage.
Its native checks and 1,800 C/JavaScript cross-checks pass; the README records
the sanitizer results and limitations. Native type checking, paths and
composition are the next ports; do not confuse this working component with a
complete native cubical kernel. The reference fragment's 116 translated
declarations are not yet checked by C.

## Verification commands

Run `node --test experiments/cubical/tests/*.test.mjs` for the experimental core.
Run `node experiments/cubical/check-library.mjs` to regenerate actual translation
results; every successful declaration is checked again from inert term syntax.
Run `node experiments/cubical/inventory.mjs` for the separate AST-only census.
No experiment command changes the production WASM binary or deploys the site.
