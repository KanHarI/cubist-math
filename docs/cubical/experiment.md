# Cubical experiment: scope, specification, and migration ledger

> Historical design notes. The current project uses only the cubical C kernel;
> see [the project README](../../README.md) and the [CLI guide](../guides/cli.md). Retired implementation paths below describe the earlier design.

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
   small-expression tests. Inventory every Cubist source and its obligations.
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
pointwise roundtrip, without adding an axiom. The original `basics.cubist`
translates completely (identity, duplication, natural-number copying and the
proof that copying two gives two). The current whole-library translation pass
checks **117 of 2,128 declarations** in this fragment; 2,011 remain explicit gaps.
See [the exhaustive results](translation-results.json) and
[the source inventory](migration-inventory.md). Counts are for declarations,
not entire modules, and are not an estimate of the remaining effort. The census
includes 216 Cubist modules and separately lists 28 legacy construction
artifacts, which the cubical translator does not admit as trusted exports.

Composition now checks every tube/base boundary and every overlap of its face
system. Its computation rules cover Nat, Unit, Pi, Sigma and Path. Pi composition
uses backward filling in the domain; Sigma composition fills the first component
before composing the second. Derived Path induction has the expected weak beta
behavior: a test deliberately rejects a source proof depending on the old
judgemental J beta rule for an unknown type. Concrete universe-schema uses are
checked at their supplied level; the schema itself is not counted as a translated
closed declaration. Downward resizing is rejected.

The JavaScript reference now includes Glue formation, introduction, projection,
eta, the CCHM composition algorithm and universe composition. Glue witnesses are
checked as equivalences with contractible fibers. Tests execute transport along
the identity equivalence of Nat; separately generated composition expansions
recheck before reduction, including persistent faces and overlapping tubes.
The required face universal quantifier and Sigma eta are also implemented in C.
These Glue and universe rules now also run in the native checker, with
independent normal-form comparisons and rechecks. The
full theorem that idtoequiv is an equivalence remains to be constructed; a map
from equivalences to universe paths alone is not that theorem.

No existing declaration is claimed translated merely because it parses or the
old kernel checks it. Missing full univalence proofs, inductive composition, HITs and bridge
rules are explicit gaps, never assumptions inserted into the new checker.

The experiment now incorporates production `main` at `1f6cddb`. The previously
reported reference-trace/proof-export failures have been repaired there, and the
main agent reports 236 passing regression tests for the new quotient-descent
and kernel/image batch. Galois development is active again; complex analysis
remains paused. See [the updated Galois handoff](../tactical/galois-handoff.md). Migration
covers existing proofs, not completion of their unfinished mathematical goals.
Generated inventory and translation reports record the source revision.

## Universe policy

Retain explicit cumulative universes U0, U1, ...; do not introduce resizing.
Ascending a universe is distinct from making an arbitrary large type small.
The source's compile-time `Universe` parameter and extra kernel universe
constructors require a specified translation, not erasure. Quotient HITs should
preserve the input universe once their computation and elimination are checked.

## Native C work

The independent native checker under
[`kernel`](../../kernel/README.md) now implements
interval/face algebra, explicit universe levels, Pi/Sigma, Nat/Unit/Void/sums,
general dependent W induction, interval paths and checked composition. Its
files separate inference, substitution, conversion and computation by rule
family. Checking preserves compact syntax; optional normalization is a distinct
inspection operation. Path endpoint annotations are reconstructed internally.

All 79 experiment tests pass, with 38 cases in the native/derived-equivalence
UBSan run and 2,100 seeded
C/JavaScript algebra comparisons. Native tests also pass UBSan; ASan remains
unavailable due to the documented runtime startup deadlock. A compact Nat
computation denoting 4,194,304 checks with 1,329 nodes and 65,536 reserved arena
bytes, without constructing the unary numeral. This does not yet establish
the factorial-through-univalence acceptance test.

Native composition covers Nat, Unit, Pi, Sigma, Path, Glue and universes,
including dependent filling and varying function domains. Constructor composition
for W/sums is now implemented. Computational pushouts now support derived suspension;
propositional truncation, the strict Id bridge, and the remaining source migration are gaps.
The main branch is integrating the WASM API and a native-only source frontend;
its manual binary and radix factorial source proofs now pass the new checker.
Those integration changes are coordinated separately from this kernel branch.
The earlier census of 117 translated declarations is a historical source
inventory, not a claim that the full library has migrated. Neither checker
falls back to the old kernel.

## Verification commands

Run `node --test lib/cubical/tests/*.test.mjs` for the experimental core.
Run `node lib/cubical/check-library.mjs` to regenerate actual translation
results; every successful declaration is checked again from inert term syntax.
Run `node lib/cubical/inventory.mjs` for the separate AST-only census.
No experiment command changes the production WASM binary or deploys the site.

## Derived univalence milestone

`lib/cubical/equivalence.mjs` now builds and independently checks the
CCHM theorem that `unglue` is an equivalence (contractible fibers), uniqueness of
contractibility witnesses, and the total-space formulation of univalence:

```text
forall A : U_l. IsContr(Sigma, X : U_l, Equiv(X, A))
```

The final theorem is closed in the native checker. Its identity-equivalence
helper is registered as an earlier closed checked definition, not an assumption.
The proof uses only existing Glue, composition, Pi, Sigma and interval paths;
it adds no axiom or trusted rule. A reference check validates the same derived
construction using the previously checked helper's type. Tests cover levels
U0 and U2. Checking leaves proof bodies folded; strongly normalizing the entire
univalence witness would duplicate a large amount of proof structure and is
unnecessary for certification.

This proves the canonical contractible-total-space formulation. The explicit
`idtoequiv isEquiv` library API still needs to be derived/connected via the
identity-system equivalence theorem, and the full library/HIT migration and
computational-univalence factorial-transfer acceptance remain separate tasks.
Primary source: [CCHM, section 7.2, theorem 9 and corollary 10](https://arxiv.org/html/1611.02108).

A further nonidentity computation test transports `(succ(0), point)` through
the checked product-swap equivalence `(Nat × Unit) ≃ (Unit × Nat)` and obtains
`(point, succ(0))`. Both independent checkers compute and recheck that output.
The strict-isomorphism helper used for this test is only an inert term builder:
an incorrect inverse fails ordinary type checking.

### Computational pushout checkpoint

The native and reference kernels now implement the CHM pushout rules, including
canonical homogeneous composition, dependent elimination on boxes, and
transport with endpoint correction when span maps or carrier types vary.
Suspension is derived at the library level. See [pushouts.md](pushouts.md) for
the trusted rules, append-only ABI, focused cross-checks, and remaining
source-language and circle migration work.
