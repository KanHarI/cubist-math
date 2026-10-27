# H1 truncation migration evidence

Status: implemented on 2026-09-30, and H1 released on 2026-10-02. The
ledger remains a review draft at main `e729c2d5` on 2026-10-17; the CB/RC
merges do not complete the remaining K2.5 archive remedies. On 2026-10-20 the
remaining remedies were dropped: the legacy assumptions are removed with the
archive's retirement, as [Removing the legacy assumptions](#removing-the-legacy-assumptions)
plans. On 2026-10-26 its [steps](#steps) 1–4 were scheduled alongside the
runtime phase, starting with `axiom` definitions. Step 1 is implemented
(2026-10-26): excluded middle and choice are the library's axioms, and the
legacy builtins are labelled `LEM[Truncate]` and `Choice[Truncate]`. Steps 2–4
are not implemented yet, and step 5 waits for the archive's deletion. The
[ledger](h1-truncation-ledger.json) pins 12 checked public changes against
`f4d1961`, rebased from `cc6b50f` on 2026-10-05, and records 5 more of two
comparisons that step 1 retired, with the revision at which they last
passed. Its acceptance permits the listed changes; it does not certify
that the old and new proofs are identical or that all 47 declarations of
specification section 8.4 have been rebuilt.

`library/h1_truncation.cubist` admits the universe-preserving proposition
truncation and proves its proposition evidence, mapping and elimination
into an independent finite universe. Its definitions are computable and
have no logical assumptions. The legacy archive stays isolated and unchanged
until it retires.

| Acceptance case | Checked implementation | Dependencies |
| --- | --- | --- |
| G2 | `small_mere_eliminate`, from a small truncation directly into a proposition in U1 | H1; no assumption |
| G4 | Version 2: exact old/new public-type and value hashes and renderings, hypotheses, assumption lists, explicit LEM/Choice replacements and H1 markers; the same change unlisted, or a changed pin, fails | Both versions must first check; local public/value dependencies must be identical or ledgered within the comparison scope |
| G5 | Rebuilt `EventualClose` truncates its small witness at U0; `CauchySame` remains a relation into U0 | H1; neither predicate has assumptions |
| G6 | `resize_prop` decides a proposition using rebuilt LEM at U1, returning Unit or Void with proposition evidence and maps both ways | `LEM` of `classical_axioms` only (`LEM[h1_truncation.Trunc]` before step 1); set evidence for `StrictlyAbove` is rejected |
| G7 | Rebuilt `no_maximal_strict_successor` uses double-negation elimination at U1 on its large truncated conclusion | Legacy LEM explicitly replaced by `LEM[h1_truncation.Trunc]`, now `classical_axioms`'s `LEM`; the four legacy truncation dependencies removed. Its ledger comparison retired in step 1 |

`cubist-tests/h1_cauchy_quotient.cubist` has 16 declarations: five verify as identical and
eleven have exact ledger changes. Its representative-selection wrappers
still call the archived predicate quotient and retain its legacy truncation
dependencies. Those wrappers are recorded explicitly; this slice rebuilds
the small equivalence relation and its laws, not the quotient foundation.

The Zorn comparison selected `no_maximal_strict_successor` and its five
unchanged local dependencies, until step 1 retired it. The field-logic
comparison includes the unchanged `FieldProp` predicate alongside
`small_mere_eliminate`. Neither
claims to rebuild `zorn_chain_complete`, the tower or all of the other remedy
groups. `tower_induction_large` and `tower_relative_induction` are explicitly
deferred to H2, and group 5 is refused by the implemented ledger validator.

The two slices that build on archive developments, `h1_cauchy_quotient` and
`h1_zorn_step`, live in `cubist-tests/`, since a library module imports only
library modules. The prelude `nat` has since moved from the archive into the
library; the verifier reads its baseline from the old path and places it in
the library, as today's checks do.

## Classical signatures

Until step 1, `LEM(Trunc, U, ...)` and `Choice(Trunc, U, ...)` restated the
two assumptions over an admitted proposition truncation, named by its former,
and reported `LEM[h1_truncation.Trunc]` and `Choice[h1_truncation.Trunc]`.
Step 1 retired that form: `library/classical_axioms.cubist` states
`ExcludedMiddle` and `AxiomOfChoice` over `Trunc` and assumes them as
`def LEM := axiom ExcludedMiddle;` and `def Choice := axiom AxiomOfChoice;`,
listed as `LEM` and `Choice`. They keep their non-computing status. Where
nothing binds `LEM` or `Choice`, the old `LEM(U, ...)` and `Choice(U, ...)`
keep their archived signatures, listed as `LEM[Truncate]` and
`Choice[Truncate]`, and can coexist with the axioms in the same session. A
ledger records a replacement of a legacy builtin by the axiom of its name
explicitly.

`h1_classical.cubist` imports `classical_axioms` and proves generic
double-negation elimination, decidability of propositions and proposition
resizing. Resizing takes explicit
`IsProp(U1, P)` evidence; it cannot extract or resize a witness type merely
from its being a set. For propositions, maps in both directions give an
equivalence because both composites are identified with identities by their
proposition evidence.

## Reproduce the scoped comparisons

H1 is on by default, so the commands need no option for it. Each accepted change is checked
against the ledger; removing `--ledger` rejects it. A selected declaration
scope is printed in the report and does not imply whole-module migration.
All ledger entries for a compared module must be inside that run's scope.
`hypothesesAdded` lists newly spelled parameter names for review; the pinned
public type, rather than that informational list, records their actual types.
The CLI defaults to the ledger's pinned baseline and rejects an explicit
`--base` that names a different revision. Archive imports resolve only within
the archive; a compared root prefers its archived predecessor, then library.
Each type and value pin also hashes the checked meanings of referenced
definitions and admitted signatures, so a folded name cannot hide a changed
dependency even when its public type stays the same.

```sh
node tools/verify-proof-migration.mjs --base f4d1961 --no-dependents --edited-file cubist-tests/h1_cauchy_quotient.cubist --ledger docs/roadmaps/hott/h1-truncation-ledger.json cauchy_quotient
node tools/verify-proof-migration.mjs --base f4d1961 --no-dependents --edited-file docs/examples/h1/migrations/field_logic.cubist --declarations FieldProp,small_mere_eliminate --ledger docs/roadmaps/hott/h1-truncation-ledger.json field_logic
```

Step 1 retired the Zorn and classical comparisons, whose pins it invalidated,
and the ledger's `retired` list keeps their scopes and pinned changes as the
record. Both last passed at main `21f55b55`, checked on 2026-10-26 before the
change; the verifier refuses them, naming that revision. The classical
comparison's edited `h1_classical` now imports the compared
`classical_axioms` and no longer declares the compared definitions, and its
replacements name `LEM[h1_truncation.Trunc]` and `Choice[h1_truncation.Trunc]`,
labels that no longer exist. The Zorn comparison's baseline reads
`h1_classical` at `f4d1961`, whose `double_negation` uses the retired
`LEM(Trunc, U, ...)`, and its replacement names the same labels. To reproduce
either, check out `21f55b55` and run its command there:

```sh
node tools/verify-proof-migration.mjs --base f4d1961 --no-dependents --edited-file cubist-tests/h1_zorn_step.cubist --declarations OrderMaximal,StrictlyAbove,strict_above_point,strict_above_laws,strict_above_is_set,no_maximal_strict_successor --ledger docs/roadmaps/hott/h1-truncation-ledger.json zorn_chain_complete
node tools/verify-proof-migration.mjs --base f4d1961 --no-dependents --edited-file library/h1_classical.cubist --declarations ExcludedMiddle,AxiomOfChoice,excluded_middle_assumed,axiom_of_choice_assumed --ledger docs/roadmaps/hott/h1-truncation-ledger.json classical_axioms
```

The field-logic and Cauchy comparisons were rechecked after step 1, and their
pins hold: neither involves `LEM` or `Choice`, and the four legacy truncation
labels are unchanged.

The pins were refreshed at H1's release on 2026-10-02. Results no longer
carry the `kernel extension: H1` marker, so every change's
`extensionsAdded` and `extensionsRetained` are empty. The signature
fingerprint no longer includes the retired `experimental` flag, so 52 type
and value hashes changed. Every assumption list, type text and value text
is unchanged, which the refresh checked before writing the new hashes.

The pins were refreshed again on 2026-10-05, with the base moved to
`f4d1961`, where `nat` and `naturals` became one module and the archive's
`primes` gave up its copies of their arithmetic. Against `cc6b50f`, whose
`primes` still had its own `add` and order, `cauchy_quotient`'s
declarations that use them differed by which definitions they named,
though no source changed. At the new base both versions use `nat`'s:
`close_tails_compose` is identical again, and four value hashes changed,
the old and new values of `sequence_same_transitive` and
`cauchy_same_equivalence`. Every assumption list, type text and value text
is unchanged, which the refresh checked before writing them.

On 2026-10-19, five `newValue.hash` pins were refreshed after the elaborator
stopped generating transports along beta-constant families in `mere_map` and
`mere_eliminate` squash clauses. The affected proofs are
`sequence_same_symmetric`, `sequence_same_transitive`, `cauchy_same_equivalence`,
`small_mere_eliminate` and `no_maximal_strict_successor`; their hashes include
checked dependency closures. Every other pin, readable value and assumption
list was checked unchanged before writing the hashes. All four migration
comparisons pass; no mathematical source was changed.

`tests/truncation-migration.test.mjs` checks G2 and G5–G7, the ledger file
and its retired comparisons, coexistence of the library's `LEM` with the
archive's `LEM[Truncate]`, and the CLI's refusal of another baseline, of a
retired comparison and of a module without a baseline.
Compared modules require a baseline at the requested Git revision in
`library/` or `archive/first-library/`; an untracked new module cannot supply
its own baseline. `tests/proof-migration.test.mjs` checks listed/unlisted G4 changes,
changed pins, forbidden removals, duplicate entries, failed declarations,
scope escapes, body substitution, explicit assumption replacements,
archive/library collisions and refusal to bypass proof-identity checking.
The rebuilt module's `h1_` prefix keeps it apart from the archive's
`cauchy_quotient` in CLI, REPL and page lookup.

## Removing the legacy assumptions

**Decided on 2026-10-20:** the four legacy truncation assumptions,
`Truncate`, `TruncateIntro`, `TruncateProp` and `TruncateElim`, and the
`LEM(U, …)` and `Choice(U, …)` signatures stated over them, are removed from
the language. The archive's remaining remedies of specification section 8.4
are not pursued: the archive retires ([I0.5](../archive-retirement.md)), and
its uses of the legacy assumptions leave with it. Until then, archive modules
are their only permitted consumers. The library's `Trunc` is the one
truncation, and excluded middle and choice become named definitions using
`axiom` in `library/classical_axioms.cubist`, stated over it. The translator's
`LEM` and `Choice` builtins, with or without a truncation former, go with the
legacy truncation (direction of 2026-10-20).

### Measurement, 2026-10-20

At main `694882af`, with `Truncate`'s type changed to the universe-preserving
`forall A : U. U` in `web/cubical-assumptions.mjs`,
`node tools/audit-cubical.mjs --all` fails 47 of 3,810 archive declarations in
20 modules, and no others: the same 47 as the specification's measurement of
2026-09-27 (8.3). Eight fail directly, by a universe mismatch, and 39 only
through them.

| Root | Module | Fails because |
| --- | --- | --- |
| `small_mere_eliminate` | `field_logic` | `FieldExists(P) : U1` for `P : U1`, where `U0` was expected |
| `predicate_union_upper`, `predicate_union_least` | `predicate_chains` | `PredicateUnion` is `A -> U1`, where `A -> U0` was expected |
| `directed_union_independent` | `independent_unions` | The union is a `U1` predicate on the vectors, where `U0` was expected |
| `tower_induction_large` | `bourbaki_tower` | The large motive's truncation is `A -> U1`, where `TowerLaws` takes `A -> U0` |
| `no_maximal_strict_successor` | `zorn_chain_complete` | `FieldExists(StrictlyAbove(…)) : U1`, where `double_negation` takes `U0` |
| `CauchyQuotient`, `cauchy_same_equivalence` | `cauchy_quotient` | `CauchySame` becomes a relation into `U1`, where the predicate quotient takes `U0` |

| Module | Failing declarations |
| --- | --- |
| `field_logic` | `small_mere_eliminate` |
| `polynomial_root_existence` | `polynomial_root_extension_exists` |
| `finite_splitting_extensions` | `finite_splitting_step`, `finite_splitting_by_degree`, `finite_splitting_extension_exists` |
| `splitting_fields` | `finite_splitting_field_exists` |
| `finitely_generated_algebraic` | `finite_extension_finitely_generated` |
| `kernel_quotient_image` | `image_fiber_class_witness`, `image_to_kernel_quotient`, `kernel_quotient_image_right`, `kernel_quotient_image_left`, `kernel_quotient_image_equiv`, `kernel_quotient_image_equality`, `kernel_quotient_is_set` |
| `group_first_isomorphism` | `group_first_isomorphism` |
| `predicate_chains` | `predicate_union_upper`, `predicate_union_least` |
| `independent_unions` | `directed_union_independent`, `chain_union_independent`, `IndependentUnion`, `independent_union_upper` |
| `independent_order` | `independent_union_least` |
| `bourbaki_tower` | `tower_induction_large`, `tower_relative_induction` |
| `bourbaki_witt` | `tower_separation`, `tower_stable_step`, `tower_stable_sup`, `tower_is_stable`, `tower_is_chain`, `bourbaki_witt` |
| `zorn_chain_complete` | `no_maximal_strict_successor`, `no_strict_successor_function`, `zorn_chain_complete` |
| `vector_basis_existence` | `independent_chain_complete`, `vector_space_has_basis` |
| `cauchy_quotient` | `CauchyQuotient`, `cauchy_same_equivalence`, `cauchy_class_represented`, `cauchy_sequence_representatives` |
| `cauchy_ordered` | `ordered_cauchy_same_equivalence` |
| `bouquet_invariants` | `bouquet_maps_determined_by_letters`, `bouquet_maps_determined_by_generators` |
| `puncture_periods` | `puncture_period_formula`, `puncture_period_same_windings`, `puncture_period_zero_windings` |
| `puncture_period_examples` | `nontrivial_loop_with_zero_period` |
| `complex_periods` | `complex_puncture_period_formula` |

The results these declarations establish (the first isomorphism theorem,
Bourbaki–Witt, Zorn for chain-complete orders, the basis theorem, the
Cauchy quotient, splitting fields, periods on punctured planes) are listed
in the [results catalog](../../library-results.md). The retirement's step R3
decides which the library rebuilds, at the universes they need and without
resizing, before the archive is deleted.

### Consumers outside the archive, 2026-10-20

| Where | Files | Uses |
| --- | --- | --- |
| `library/` | 2 | `classical_axioms` states `ExcludedMiddle` and `AxiomOfChoice` over `Truncate` and checks `LEM(U)`/`Choice(U)` against them; `universe_automorphisms` proves excluded middle at `U0` equivalent to a `Truncate(U1, …)` statement, with `TruncateElim`, `TruncateIntro` and `TruncateProp`. `library/README.md` lists `Truncate` as `classical_axioms`'s dependency |
| `cubist-tests/` | 16 | Direct uses in `program_assumptions`, `inspection_axiom_labels`, `assembly_generic_assumptions`, `universe_generic`, `universe_generic_builtins` (the rejected `LEM(UU0, …)` and accepted `LEM(U1, …)` cases), `inductive_assumptions` (E507 fixtures) and `truncation_rebuilt_classical` (`old` and `both`); the legacy labels in E324/E330 goldens of `computability` and `computability_evaluation`, through the archive's `classical`, and of `inductive_computable`, through the library's `classical_axioms`; assumption parameters in the type renderings of six `*_invalid_*` goldens over archive developments |
| `tests/` | 31 | Exact assumption lists or patterns in the Artin, Galois, dimension, linear-algebra, finite-spanning, algebraic-extensions, polynomial, quotient, universe-generic, library, CLI, REPL, assembly, program, inspection, reduction, benchmark, declaration, contract, migration and browser tests; the E324 goldens of `tests/fixtures/contracts/nonempty_contracts.cubist`; the recorded labels of the three capture-bindings cost baselines |
| Reference | 5 | `assumptions.html`: the truncation section and the statements of `LEM` and `Choice`, 40 mentions; `checking.html`, 2; `errors.html`, the E406 row; `terms.html`, the reserved names; `web/proof.html`, the quick reference's no-axiom text and checked `LEM`/`TruncateIntro` example |
| Guides | 3 | `docs/guides/cubist.md`: the list of library principles, universe examples and obsolete standalone `axiom name(params) : T;` paragraph; `docs/guides/regression-contracts.md`: an `expect_axioms` example; `docs/guides/cli.md`: the claim that a source file cannot add assumptions |
| Implementation | 6 | `web/cubical-assumptions.mjs` (the types), `web/translator/builtins.mjs` (the handlers), `web/cubist/parser.mjs` (reserved names), `web/cubical-notation.mjs` (the `‖A‖` hook), `web/diagnostics.mjs` (E404–E406), `tools/migration-ledger.mjs` (the `LEGACY` set) |

### Axioms as definitions

**Syntax revised on 2026-10-21:** an axiom uses an ordinary named definition,
`def Name := axiom Statement;`. The existing statements in
`library/classical_axioms.cubist` are restated over `Trunc` and reused; no
separate `axiom Name(parameters) : Type;` declaration or `axioms.cubist`
module is needed. Excluded middle and choice are the standard classical
assumptions; `FunExt`, `ua` and `UnivalenceBeta` remain derived and compute.
The planned source is:

```text
import h1_truncation;

def ExcludedMiddle(U < UU0) :=
  forall A : U. ((A -> Void) -> Void) -> Trunc(U, A);

def AxiomOfChoice(U < UU0) :=
  forall A : U. forall B : A -> U.
    IsSet(U, A) -> (forall a : A. IsSet(U, B(a))) ->
    (forall a : A. Trunc(U, B(a))) -> Trunc(U, forall a : A. B(a));

def LEM := axiom ExcludedMiddle;
def Choice := axiom AxiomOfChoice;
```

- `axiom F` takes a type, or a type family with a parameter telescope and a
  type-valued body. It checks that family and universally closes its body
  over the telescope, treating universe and ordinary parameters uniformly.
  It uses the family's body, not the inferred type of the family itself.
  Thus `axiom ExcludedMiddle` introduces one constant of type
  `Pi (U < UU0). Pi (A : U). ((A -> Void) -> Void) -> Trunc(U, A)`.
  A supplied type already has no family parameters to close.
- Initially `axiom F` is the whole right-hand side of a named top-level
  `def`; the enclosing definition supplies its identity. The checker adds
  one context entry of the closed type, as `libraryAssumption` does today.
  Aliases and applications share that entry. The kernel checks proofs
  abstracted over the context and trusts no new rule. Universe arguments
  remain explicit at applications, such as `LEM(U0, A, nn)`.
- An axiom is a non-computing dependency, listed by its name. A
  `computable` declaration that depends on one is refused (E330), `evaluate`
  refuses its terms (E324), a declared type's parameters and constructors
  cannot use one (E507), and inspection shows it as it shows an assumption
  today.
- `library/classical_axioms.cubist` holds the types and the two assumptions
  above, importing `h1_truncation` for `Trunc`. `h1_classical` imports it and
  keeps `double_negation`, `decide_prop` and `resize_prop`; its duplicate
  statement definitions go. Existing assumed-result names can remain as
  aliases, such as `excluded_middle_assumed(U) := LEM(U)`, during migration.
- `axiom` becomes a reserved word. This reverses the 2026-09-25 decision
  (`0961f336`) to remove the unimplemented keyword: the parser regression
  in `tests/declarations.test.mjs` currently accepts `def axiom(n : UNat) := n;`.
  Step 1 changes that case to a reserved-name rejection and adds acceptance
  tests for `def Name := axiom Statement;`. The standalone declaration
  `axiom assumed : UNat;` remains rejected; `opaque` remains an ordinary name.
- Imports are transitive, so `import classical_axioms;` brings `Trunc` into
  scope, and a later import shadows an earlier one's names. Transitivity stays as it is
  for now, by direction of 2026-10-20; changing it is later work and no part
  of this plan.

### Continuum hypotheses: checked statements, planned assumptions

Added on 2026-10-21, with no assumptions:

- `finite_sets.cubist` defines `Fin(n)` over the public binary `Nat` and
  proves setness. `binary.cubist` specializes it to `Binary := Fin(2)`, with
  `False`, `True` and the computable operations `Not`, `And`, `Or`, `Xor`
  and `Nor`. `powersets.cubist` defines `PowerSet(U, A) := A -> Prop(U)`
  in `next(U)` and `DecidablePowerSet(U, A) := A -> Binary` in `U`, and
  proves setness of both. Identifying them would require excluded middle.
- `continuum_hypothesis.cubist` states CH and GCH over full powersets.
  Their intermediate sets live in `next(U)` and their statements in
  `next(next(U))`; no resizing is implicit. GCH's infinitude is an explicit
  mere injection from `Nat`.
- The negative forms exclude strictly intermediate cardinalities. The
  `DecidableContinuumHypothesis` and
  `DecidableGeneralizedContinuumHypothesis` forms give a truncated
  disjunction of equivalences to the interval's endpoints. Here
  "Decidable" means this cardinality dichotomy, not `CH or not CH`.
- Checked conditional proofs give `DecidableGCH -> GCH -> CH` and
  `DecidableGCH -> DecidableCH -> CH`. `CantorContinuumHypothesis` separately
  records the constructive binary-sequence formulation, with
  `Cantor := DecidablePowerSet(U0, Nat)`.

With axiom expressions, implemented in step 1, optional assumptions can reuse
these type families in the same way:

```text
def CH := axiom ContinuumHypothesis;
def DecidableCH := axiom DecidableContinuumHypothesis;
def GCH := axiom GeneralizedContinuumHypothesis;
def DecidableGCH := axiom DecidableGeneralizedContinuumHypothesis;
```

These lines are currently comments in the library, not admitted assumptions.
`cubist-tests/continuum_axioms.cubist` checks that a module importing
`continuum_hypothesis` can assume `CH` and `GCH` so, with the families over
`U < UU0` whose bodies live in `next(next(U))`, and that every result that
uses one lists it; there they are labelled `continuum_axioms::CH` and
`continuum_axioms::GCH`. Admitted in the library, they would be labelled
`CH` and `GCH`, by the label rule below.
The targets `DecidableCH -> LEM` and `DecidableGCH -> Choice` are follow-up
proofs. [Kirst and Rech's HoTT mechanization](https://hott-uf.github.io/2021/HoTTUF_2021_paper_4.pdf)
uses propositional resizing; adapting it must account explicitly for that
requirement at these universe levels. No implication to LEM or choice is
claimed as checked here.

### Steps

Each step lands with its affected source, parser, inspection and assumption
expectations updated together; no step relies on a later step to restore a
passing test suite. The coupled changes within step 1 may be prepared
separately, but its axiom switch, dependent library migration and label
transition land together.

1. **`axiom` expressions and `library/classical_axioms.cubist`.** The parser,
   translator and inspection learn the form; the reference's declarations and
   assumptions chapters document it; `classical_axioms` moves to `Trunc` and
   `h1_classical` imports its types and assumptions. In the same change,
   `universe_automorphisms` is restated over `Trunc(U1, …)`, with
   `mere_eliminate` into `Trunc(U0, A)`, so every consumer of the changed
   `ExcludedMiddle` still checks. The translator's `LEM`/`Choice` handlers
   with a truncation former are retired:
   the former's only job was to tell the rebuilt assumptions from the legacy
   ones, and any admitted proposition truncation could fill it, minting a
   separately labelled copy. The legacy builtins are relabelled
   `LEM[Truncate]` and `Choice[Truncate]` now, before the new axioms receive
   the bare `LEM`/`Choice` labels; mixed archive/library programs must list
   both distinctly from this first step. Update library and archive
   assumption expectations together, including `tests/library.test.mjs`,
   `tests/truncation-migration.test.mjs`, inspection and computability
   goldens, affected baseline labels and checked reference examples, and
   `library/README.md`. The `axiom` parser regression and the reference's
   reserved-name list change here too. Update the no-user-assumptions text
   in `docs/guides/cli.md` and `web/proof.html` to explain axiom expressions
   in definitions, and replace the obsolete standalone-axiom paragraph in
   `docs/guides/cubist.md` with that syntax.
   Handle all of `truncation_rebuilt_classical` in this step, including
   `old` and `both`: its `h1_classical` import now shadows the builtin.
   Retire these cases or replace them with coexistence checks using an
   imported archive proof and a rebuilt proof. Any direct legacy-builtin
   probe must use a separate source without the library axiom imports and
   be placed as an archive source, or retired, before step 4.
   **Ledger transition happens here:** the classical and Zorn comparisons
   pin rebuilt and legacy `LEM`/`Choice` labels and proof dependencies that
   this change invalidates. Retire those affected comparisons with their
   last passing revision recorded, preserving the
   old ledger as evidence; update or retire synthetic former-based tests in
   the same change. Recheck the field-logic and Cauchy comparisons; retain
   them only while their pins remain valid, retiring any affected comparison
   in the same transition rather than postponing it. Ordinary proof
   migration checks remain strict.

   **Done on 2026-10-26.** The parser reads `axiom F` only as the whole
   value of a top-level definition without parameters, declared type or
   section, `def Name := axiom F;`, and refuses it anywhere else (E008).
   `axiomAssumption` (`web/cubical-assumptions.mjs`) reads `F`'s telescope off
   its type, applying `F` to a fresh variable for each universe or ordinary
   parameter, takes the weak head of that application as the body, and
   refuses an `F` that is no type or family of types (E666). The checker
   assumes the closed type under the definition's binding with the
   assumption mark, `module__Name#`: every assumption's name carries the
   mark, which no identifier, declaration identity, generated or kernel
   name holds (`assumptionMark` in `web/translator/names.mjs`), so no
   declaration, binder or generated name can spell, capture or overwrite
   one (`checker.axioms` maps the binding to its assumption); the
   definition's value is that variable, and no kernel definition is
   admitted. An axiom of a library module is labelled by its
   bare name, as `LEM` and `Choice` are, when the module reader read that
   module and every module it imports, transitively, unedited from
   `library/` (`fromLibrary` in `web/module-resolution.mjs`, combined over
   the imports in `CubicalProgram.discover`). A replay of a check keeps the
   provenance it recorded (`ReplayInputs`), and the workbench asks which
   transferred sources are the library's text (`libraryProvenance`). A
   provenance that cannot be read, as when `library/` is unreachable,
   leaves a module the text it is, with qualified labels, and the
   workbench refuses a transfer that does not replay completely, every
   declaration of every module it imports included, as a complete check
   requires (`complete` in `CubicalProgram.check`, which the command line's
   `check` reads too). Any
   other is labelled
   `module::Name`, a module of a library module's name from elsewhere or
   edited, or one that imports such a module, included, and
   `tests/library.test.mjs` keeps the library's axiom names distinct; an
   `expect_axioms` list names assumptions by their
   labels, the legacy builtins as `LEM[Truncate]` and `Choice[Truncate]`.
   A declaration's identity is `module__Name`, so two modules' spellings can
   meet in one, as `a::b__c` and `a__b::c` do: the later declaration is
   refused (E256, `identityClash` in `web/translator/translate.mjs`), whether
   it is a definition, a declared type or constructor, or an axiom, and no
   declaration publishes under another module's identity. The migration
   verifier compares an axiom by its assumed statement; an unchanged one
   stands for the original in its dependents' terms, types and assumption
   lists, renamed only where it occurs free (`mapDefinitions` in
   `tools/proof-migration.mjs`), and a changed one is reported. A historical
   reader reads `axiom` as the source's revision did (`historicalKeywords`
   in `web/cubist/legacy-syntax.mjs`; the verifier reads the revision off
   its parser): a revision with the form reserves the word and reads the
   form, and current sources stay readable as baselines; before it, no
   Cubist revision gave `axiom` any meaning, so every occurrence is a name,
   renamed with its declaration wherever its binding comes from, a selected
   model's member or an import included. A qualified reference,
   `module::name`, follows the renaming of its module, as imports do, and
   of its declaration, for every renamed word, as `provider::left` did not
   on main. A renamed module's file is found through the renaming plan's
   inverse (`historicalModulePaths`), never from a spelling's suffix, so
   `axiom__`, the plan's spelling where a source declares `axiom_`, is
   read from `axiom.cubist`. Every report of a result
   lists every assumption it relies on: the command line's `check`
   (`recover assumes LEM`, and after each print `print typeof at line 4
   assumes LEM`) and `inspect`, every REPL result (a definition, `typeof`, a
   print), the workspace console's results (`let`, `typeof`, a term,
   `inspect`, `witness`, `/goal`, `/locals`, `/prove`, through the local
   hypotheses they use; the console refuses a result that does not say), a
   reference
   example's status and each of its prints, the workspace's declarations
   and inspector, and `expect_axioms`; a result that relies on none is
   reported alone. Every text the program renders shows an assumption by
   its label, never by its kernel name or its axiom's identity: a
   declaration's type, an inspection, an assembly listing and a tooltip
   (`tests/assumption-display.test.mjs` sweeps every surface). Rendering
   reads its names from `displaySymbols`; the program's `symbols` hold its
   declarations alone, and an inspected assumption states its axiom
   through the origin the checker recorded, never through its label.
   `LEM` and `Choice` are no longer
   reserved, so an import or declaration binds them before the builtin
   fallback. The aliases `excluded_middle_assumed` and
   `axiom_of_choice_assumed` were dropped, and `universe_automorphisms`'s two
   directions, assumption-free over `Trunc`, became `computable`. The Zorn and
   classical comparisons retired, last passing at main `21f55b55`; the
   field-logic and Cauchy pins hold. A ledger replacement is now
   `LEM[Truncate]` or `Choice[Truncate]` by the library's axiom of its name.
   Direct legacy-builtin probes remain in two JavaScript tests,
   `tests/test-contracts.test.mjs`'s label check and
   `tests/proof-migration.test.mjs`'s replacement, for step 4 to place in
   archive sources or retire.
2. **Remaining fixtures off the legacy assumptions.**
   Fixtures that test the legacy signatures themselves are restated over
   `Trunc` and the axioms;
   `universe_generic_builtins` imports the library axioms and updates both
   `D4`'s `UU0` rejection and `D4_small`'s accepted `U1` case to their new
   signatures and diagnostics. The entire `truncation_rebuilt_classical`
   transition was completed in step 1. The remaining computability fixtures
   import `h1_classical`, and their source and expected dependencies change
   together. Expectations over archive modules retain the distinct legacy
   labels introduced in step 1 until the archive retires. The ledger tests
   that construct legacy baselines run them as archive sources, or retire
   before confinement. Cost baselines invalidated by either transition are
   regenerated or marked historical in that transition.
3. **Remaining reference and guides.** Complete the documentation migration
   after the signature, label and checked-example updates of step 1. The
   assumptions chapter sends truncation to the cubical chapter's declaration
   (`point`, `squash`, `mere_eliminate`); update the E406 explanation and
   remaining legacy-name documentation. Migrate `web/proof.html`'s checked
   quick-reference example to import `classical_axioms` and use `Trunc`
   and `merely` before step 4 confines its old builtin calls. The guide lists
   `Trunc` and the two library axioms among its principles.
4. **Confinement.** `Truncate`, `TruncateIntro`, `TruncateProp`,
   `TruncateElim` and the builtin `LEM(U, …)` and `Choice(U, …)` are
   accepted only in archive modules, which the module reader distinguishes by
   root (I1.1); elsewhere they are refused with an error that names `Trunc`
   and the library's axioms. The archive's three call sites,
   `classical.double_negation`, `zorn_chain_complete` and `surjections`, keep
   the builtins: importing `classical_axioms` next to the archive's
   `truncation` would shadow its `merely`, `mere_eliminate` and `IsProp`.
   Keep the `LEM[Truncate]` and `Choice[Truncate]` labels established in
   step 1, so mixed programs such as `h1_zorn_step` continue to distinguish
   them from library axioms. Check that the migrated
   `universe_generic_builtins` no longer invokes the legacy builtin;
   dedicated confinement tests cover its rejection outside the archive.
   Retire any remaining ledger comparisons whose exact pins change in this
   same step, recording their last passing revision. The alternative to a
   translator check, a source test over the roots, is weaker: it reports
   after the fact and says nothing to a REPL entry.
5. **Removal, with the archive** ([I0.5](../archive-retirement.md), R5).
   `web/cubical-assumptions.mjs` goes entirely: the four truncation types, the
   legacy `LEM`/`Choice` signatures, their builtins, the notation hook and the
   diagnostics. Any surviving archive-dependent comparisons and coexistence
   checks end here, with their last passing revisions recorded. Comparisons
   invalidated by steps 1 or 4 have already retired in those steps. The ledger
   file, its `assumptionsRemoved` lists and the `LEGACY` set
   stay as the record of the pinned changes.

### Decisions

- **Excluded middle and choice are library axioms, not builtins.** With one
  truncation there is nothing for a truncation former to distinguish, and a
  former that any admitted proposition truncation may fill mints a separately
  labelled copy of the assumption, equivalent but noise. A definition using
  `axiom` in `library/classical_axioms.cubist` states each once. Direction of
  2026-10-20, with the definition syntax revised on 2026-10-21.
- **Where `axiom` is allowed.** **Decided on 2026-10-26** (the user):
  user-supplied axioms are allowed, in any module, file, workspace or REPL,
  and every result must report, alongside it, every axiom it relies on; the
  continuum hypothesis is to be introduced so. Every axiom is a
  listed non-computing dependency, `computable` refuses its dependents, and a
  result that wants a classical hypothesis still takes it as a parameter, as
  `h1_classical`'s statements allow. `classical_axioms` supplies the standard
  LEM and choice assumptions; optional CH/GCH assumptions require explicit
  declarations and reviewed expectation lists. The newly added continuum
  modules currently admit none. The library tests continue checking each
  module's exact assumption list.
- **Labels.** **Decided on 2026-10-26** (the user): every library axiom is
  labelled by its bare name, `LEM` and `Choice` and later `CH`, `GCH` and
  the like, wherever its module and every module it imports are read
  unedited from `library/`; user and
  other non-library axioms display their module-qualified names,
  `module::Name`. This replaced a table of `classical_axioms`'s two names.
  The library's axiom names are distinct, which `tests/library.test.mjs`
  checks; the legacy builtins' labels are reserved words or carry brackets.
  Internal identities include their defining module and declaration,
  aliases retain those identities, and one identity names one declaration.
  In step 1 the legacy builtins are
  relabelled `LEM[Truncate]` and `Choice[Truncate]` for their remaining
  archive life, before any new axiom uses a bare canonical label.
- **Module names.** `h1_truncation` and `h1_classical` keep their prefixes
  while the archive's `truncation` and `classical` exist. Renaming them is one
  migration after R5; the axioms' labels do not depend on it. Open until then.
- **Reserved names.** `axiom` joins the reserved words in step 1.
  The existing parser test accepting it as an ordinary definition name
  changes in that same step; the standalone `axiom Name : Type;` form
  remains unsupported.
  That step also permits ordinary declarations of `LEM` and `Choice`, with
  imported bindings resolved before the legacy builtin fallback. Step 4
  restricts that fallback to archive modules.
  `Truncate`, `TruncateIntro`, `TruncateProp` and `TruncateElim` stay
  reserved through step 4, so that a historical source fails with the
  retirement error rather than an unknown name, and are freed in step 5.
  Open: whether to keep them reserved after.
