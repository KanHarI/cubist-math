# Cubist cubical C kernel

This is the sole trusted checker for Cubist Math. It implements cumulative
universes, dependent functions and pairs, Unit, Void, sums, declared inductive
types and their dependent elimination, interval paths and composition, Glue, and computational pushouts.
Suspension is derived from pushouts. The website and CLI use this code through
WebAssembly; the archived first library's source modules live in
`archive/first-library/*.cubist`.

## Trust boundary

The trusted checker is the instruction kernel
([design](../docs/roadmaps/kernel-instructions.md)): each typing rule is an
instruction (`cc_instr_*`, `src/instructions.c`, with declared types in
`src/signatures.c` and `src/eliminators.c`) whose side conditions are
syntactic, and a definition is admitted only by the `Define` instruction.
The computation that instructions call, such as `Step`'s reductions,
composition and transport, is trusted with them.

The term checker (`cc_kernel_check`, `cc_kernel_define`, the `check_*.c`
files) and the conversion search (`cc_kernel_convertible`) are untrusted
services that tests and an optional search aid use. Their answers are never
evidence for an instruction, and this is enforced (work plan I1.2a):

- the folded comparison that instructions use keeps its own entries in the
  comparison memo, apart from conversion's successes;
- weak-head reduction contracts pair and Glue eta only when their sides are
  the same syntax, and normal forms when the parts' normal forms are; the
  `Glue` step contracts Glue eta when its side conditions agree as weak
  heads, part by part or as normal forms, and reduces nothing else; `Eta`
  expands a term of a Glue type; conversion completes both eta rules
  itself;
- the conversion search refuses to run while an instruction does.

`tests/test_isolation.c` checks each of these, including the probe that the
[2026-09-28 audit](../docs/roadmaps/audits/2026-09-28-audit.md) used to show
an untrusted query changing an instruction's verdict.

## Reading the mathematics in the code

| File | Mathematical responsibility |
|---|---|
| `include/cubical.h` | Two distinct sorts, their representation and operation contracts |
| `src/formula.c` | Finite joins of finite meets; absorption and shared storage |
| `src/interval.c` | De Morgan reversal and dimension substitution |
| `src/faces.c` | Endpoint equations, face substitution and entailment |
| `include/cubical_kernel.h` | Opaque arena, raw handles and checked-result API |
| `src/term_store.c` | Inert syntax allocation and bounded handles |
| `src/term_substitution.c` | Capture-avoiding term and dimension substitution |
| `src/instructions.c` | The instruction kernel: forward rules on a graph of judgements |
| `src/signatures.c`, `src/eliminators.c` | Declared types (H1): admission, instances, constructors, elimination |
| `src/term_conversion.c` | Folded comparison modulo bound names (trusted); the demand-driven conversion search (untrusted) |
| `src/term_normalize.c` | Weak-head computation; separate optional normal forms; eta only by syntax |
| `src/check.c` | The untrusted term checker: checked telescopes, dispatch and result publication |
| `src/check_functions.c` | Pi/Sigma formation, introduction and elimination |
| `src/check_inductives.c` | Unit, Void and sums |
| `src/check_pushout.c` | Pushout span, point and dependent bridge premises |
| `src/pushout_compute.c` | Point/bridge computation of the dependent eliminator |
| `src/check_hit_composition.c` | Homogeneous boxes and constant-face transport premises |
| `src/hit_composition.c` | Pushout composition, elimination on boxes, transport corrections |
| `src/check_paths.c` | Dependent paths and reconstructed endpoint annotations |
| `src/face_context.c` | Shared restriction of checked telescopes and face clauses |
| `src/equivalence_terms.c` | Derived contractible-fiber types and identity equivalence |
| `src/check_glue.c` | Checked gluing equivalences, boundaries and overlap coherence |
| `src/glue_compute.c` | Glue composition and derived universe composition |
| `src/levels.c` | Universe levels: normal forms, equality and order by arithmetic (G0 §2.4) |
| `src/check_composition.c` | Restricted contexts, partial boundaries and all overlaps |
| `src/composition_compute.c` | Derived filling and constructor-specific composition |
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

The first representation supports 64 distinct dimensions, including dimension
63. Dimension 64 is rejected, never masked to zero. This is a documented native
implementation restriction, not a restriction of cubical type theory. Dynamic
bitsets or a sparse dimension representation are required before removing it.
A universe carries its level as a child: a level expression over constants
`ω·tier + n` below ω², successors, maxima and variables (G0). Levels are
compared by normal form, so equality and cumulativity are arithmetic, never
search; `CC_LEVEL_MAX` and `CC_TIER_MAX` bound them. Level variables are
bound by instructions (`Level`, `LevelPi`, `LevelLambda`, `LevelApply`), so a
universe-generic definition is one checked term (G0). The term checker takes
universes at closed finite levels only. Cumulative upward inclusion is not
downward resizing. The syntax
encoding has an ABI version, `cc_kernel_abi_version()`; the JavaScript loader
and `kernel-cli` refuse a client written for another.

## Running the checks

From the repository root, run `make test`, `make sanitize`, and `make lint`.
The JavaScript reference and native protocol tests live in `lib/cubical/tests`.
The public corpus benchmark is `web/benchmark.html`; timing results depend on
hardware and browser. Inspect the current report rather than historical milestones.

## The term checker's API and compact computation

The sections below describe the term checker and the conversion search. Since
the instruction kernel became the trusted checker, elaboration no longer uses
them; they serve tests and the optional conversion oracle, and nothing they
accept is admitted (see [Trust boundary](#trust-boundary)).

`cc_kernel_term` only creates inert syntax. `cc_kernel_check` validates the
ordered assumption telescope, infers the term and checks an optional expected
type. Every path application's endpoint annotation is reconstructed internally;
a caller cannot forge an endpoint computation by supplying that annotation.
On failure the entire result is cleared. There is no old-kernel fallback.
Read-only node access supports an inspector with an external table of names.

Checking returns the checked expression and type without normalizing either.
`cc_kernel_normalize` is a separate explicit inspection operation; it does not
certify an arbitrary raw handle. The test CLI accepts a normalization option.
Conversion exposes only needed heads: beta reduction does not evaluate unused
arguments, and generic tree elimination constructs child induction hypotheses as functions
without traversing every subtree in advance.

### Checked definitions and demanded heads

`cc_kernel_define(kernel, symbol, value, expected_type)` checks a closed body
using only earlier checked definitions and publishes a folded `CC_DEFREF`
(tag 35). Failure publishes no definition. Definitions are transparent for
conversion, and a separate `cc_kernel_definition` query returns their checked
bodies and inferred types. Source opacity is an elaboration/display decision,
not a new assumption. No unchecked external theorem can enter this registry.

Conversion first compares folded syntax modulo binder renaming, including
matching definition references. It unfolds definitions only when that comparison
fails. `cc_kernel_whnf` exposes the demanded head without strongly normalizing
arguments, and is suitable for an elaborator's type-shape queries. Like the
normalization inspector, it accepts raw syntax but never certifies it; final
`cc_kernel_check` must validate all elaborated results. A raw application of an
explicit path lambda can beta-reduce without a type annotation, since this is
just capture-avoiding substitution. Endpoint computation for a neutral path
still requires the Path annotation reconstructed by checking. Thus a head
query can simplify `(<i> A) @ 1` during type elaboration without treating an
unknown neutral path as having arbitrary endpoints. The dedicated
`test-path-head` target checks this distinction and recovery after rejection.

The tests also reject duplicate names, free variables, wrong declared types,
unknown references and equality between distinct definitions.

### Sharing during substitution

Free-name analysis and capture-avoiding substitution memoize exact immutable
syntax keys. This prevents repeated traversal of a shared term as if it were
an exponentially larger tree. The bounded direct-mapped table has 8192 entries;
a hash collision only discards an optimization. It stores no typing judgements
and cannot bypass checking a context or a face restriction. Its allocation is
included in the reported arena memory. Substitution also returns the original
node immediately when the substituted variable/dimension does not occur.

A 24-level shared-DAG regression exercises weak-head inspection. The following
arithmetic counts are historical measurements before source-defined Nat/W. With the source
frontend's independently supplied failing arithmetic fixtures, the default
10-million-step budget now checks binary factorial 7 in 59,153 reduction steps
and the radix fixture in 152,535. Their respective cumulative node counts are
14,681 and 83,238. These are source frontend checkpoints, not yet the final
computational-univalence factorial transfer acceptance test.

### Source-defined Nat and W

`archive/first-library/nat.cubist` and `w.cubist` declare these types through H1.
Their instances, constructors and eliminators use `CC_SORT`, `CC_CON` and
`CC_ELIM`; arithmetic and child induction hypotheses compute through the shared
signature rules. No Nat/W-specific C formation, elimination or composition rule
remains. Their old term and instruction numbers are reserved ABI slots and are
refused by the producer.

Primitive-calculus differential fixtures use the exact historical kernel at
`bfef585cfe09f4b94a658564dff505cd67855368`, built only under
`build/reference-kernel` by `tools/legacy-kernel.mjs`. It is a test oracle outside
the production binary and browser bundle. The current native tests and source
corpus validate the current producer separately.

### Conversion preserves compact endpoints

Conversion tries folded syntax, then definition/beta/projection/boundary exposure,
then congruence of matching constructors before computing their values. For
example, equality of `decode(p @ 1)` and `decode(bits)` first compares the small
arguments. It does not evaluate both resulting unary naturals. A lambda is
already a weak head; its body is not evaluated by a head query. Function,
path, pair and Glue eta are handled explicitly when conversion requires them;
weak heads contract pair and Glue eta only when they hold by syntax, since
instructions trust reduction. Conversion recursion is
guarded at 512 active levels, reporting a failed request rather than relying on
a host stack overflow.

The independent native source fixture for `factorial_ten_from_binary` now checks
with **86,638 cumulative arena nodes / 4,392,448 reported bytes**. Its final check
uses 182 checking and 76,790 reduction steps. The focused regression reproduces
the mechanism using a compact 2^22 value hidden behind path endpoints and an
alias; fewer than 5,000 nodes are permitted. The fixture establishes the existing
Nat equality using translated compatibility proofs; the stronger acceptance
criterion of actual computational-univalence transfer is still outstanding.

The derived-library suite also certifies the closed total-space formulation of
univalence at U0 and U2: `forall A, IsContr(Sigma X, Equiv(X,A))`. See the
[experiment milestone](../docs/cubical/experiment.md#derived-univalence-milestone).
The explicit `idtoequiv isEquiv` API is still a remaining library connection.

### Sharing during folded conversion

Folded alpha-comparison also memoizes syntax pairs. Its exact key includes
both term handles and unique identifiers for the complete term-binder and
dimension-binder scopes. Scope identifiers are never reused; they are not
hashes of context names. This preserves the distinction between bound and free
names, including under shadowing. Collisions only replace an older cache entry.
A renaming is left out of the key, and the comparison, where neither side has
a renamed name free: then the pair compares the same under every renaming.
So a shared graph below differently named binders is compared once per node,
not once per path to it. Each node carries masks of the term variables and
dimensions it mentions, which rule most names out at once; the rest are
looked up exactly, and only for terms at least eight levels deep.
No typing judgement is cached by this table. An entry holds two separate
facts: the folded comparison's result, which only that comparison reads, and
a success of the conversion search, which conversion reuses. Until
2026-09-28 one flag held both, and a conversion query could satisfy a later
instruction's syntactic side condition (work plan I1.2a).

The 8192-entry table adds 256 KiB on the tested native platform, included in
reported arena memory. Comparing a closed arithmetic DAG with 2^24 unfolded
branches beneath differently named lambdas takes 105 comparison/reduction
steps. The source integration fixture for a direct binary-to-base-2-radix
univalence beta proof previously exhausted the unchanged ten-million-operation
budget; it now checks in 480 checking and 1,242,556 reduction steps, with 423,468
arena nodes. The source frontend separately avoids duplicating this concrete
proof by checking a generic beta lemma and applying it to the endpoint.

### Cubical higher inductive structure

See [the pushout rule and ABI notes](../docs/cubical/pushouts.md).
Append-only tags 36–42 cover the pushout and its computational structure;
no suspension-specific tags are needed. The existing open-cube checking API
`cc_kernel_check_in_cube` accepts an explicit dimension bitmask and checks all
telescope types under that cube. The original API keeps its closed-cube
behavior, and checked-definition publication remains closed.
