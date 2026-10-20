# H1 truncation migration evidence

Status: implemented on 2026-09-30, and H1 released on 2026-10-02. The
ledger remains a review draft at main `e729c2d5` on 2026-10-17; the CB/RC
merges do not complete the remaining K2.5 archive remedies. On 2026-10-20 the
remaining remedies were dropped: the legacy assumptions are removed with the
archive's retirement, as [Removing the legacy assumptions](#removing-the-legacy-assumptions)
plans. The
[ledger](h1-truncation-ledger.json) pins 17 checked public changes against
`f4d1961`, rebased from `cc6b50f` on 2026-10-05. Its acceptance permits the listed changes; it does not certify
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
| G6 | `resize_prop` decides a proposition using rebuilt LEM at U1, returning Unit or Void with proposition evidence and maps both ways | `LEM[h1_truncation.Trunc]` only; set evidence for `StrictlyAbove` is rejected |
| G7 | Rebuilt `no_maximal_strict_successor` uses double-negation elimination at U1 on its large truncated conclusion | Legacy LEM explicitly replaced by `LEM[h1_truncation.Trunc]`; the four legacy truncation dependencies removed |

`cubist-tests/h1_cauchy_quotient.cubist` has 16 declarations: five verify as identical and
eleven have exact ledger changes. Its representative-selection wrappers
still call the archived predicate quotient and retain its legacy truncation
dependencies. Those wrappers are recorded explicitly; this slice rebuilds
the small equivalence relation and its laws, not the quotient foundation.

The Zorn comparison selects `no_maximal_strict_successor` and its five
unchanged local dependencies. The field-logic comparison includes the
unchanged `FieldProp` predicate alongside `small_mere_eliminate`. Neither
claims to rebuild `zorn_chain_complete`, the tower or all of the other remedy
groups. `tower_induction_large` and `tower_relative_induction` are explicitly
deferred to H2, and group 5 is refused by the implemented ledger validator.

The two slices that build on archive developments, `h1_cauchy_quotient` and
`h1_zorn_step`, live in `cubist-tests/`, since a library module imports only
library modules. The prelude `nat` has since moved from the archive into the
library; the verifier reads its baseline from the old path and places it in
the library, as today's checks do.

## Classical signatures

`LEM(Trunc, U, ...)` and `Choice(Trunc, U, ...)` explicitly restate the two
assumptions over the admitted proposition truncation. The former must have
one erased universe parameter, one carrier parameter, an `A -> Trunc(A)`
point and the generated proposition squash. An arbitrary proposition former
is refused. They report `LEM[h1_truncation.Trunc]` and
`Choice[h1_truncation.Trunc]` separately from H1 and retain their
non-computing status. The old `LEM(U, ...)` and `Choice(U, ...)` keep their
archived signatures and can coexist in the same session.
Aliases of one checked truncation share an assumption; different admitted
truncations have different labels. The ledger records a replacement explicitly
and does not describe these new signatures as retained legacy assumptions.

`h1_classical.cubist` proves generic double-negation elimination, decidability
of propositions and proposition resizing. Resizing takes explicit
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
node tools/verify-proof-migration.mjs --base f4d1961 --no-dependents --edited-file cubist-tests/h1_zorn_step.cubist --declarations OrderMaximal,StrictlyAbove,strict_above_point,strict_above_laws,strict_above_is_set,no_maximal_strict_successor --ledger docs/roadmaps/hott/h1-truncation-ledger.json zorn_chain_complete
node tools/verify-proof-migration.mjs --base f4d1961 --no-dependents --edited-file library/h1_classical.cubist --declarations ExcludedMiddle,AxiomOfChoice,excluded_middle_assumed,axiom_of_choice_assumed --ledger docs/roadmaps/hott/h1-truncation-ledger.json classical_axioms
```

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

`tests/truncation-migration.test.mjs` checks G2 and G5–G7, the ledger file,
coexistence with the legacy signatures and rejection of a false truncation
former, and the CLI's pinned baseline for a module stored in `library/`.
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
truncation, and excluded middle and choice become declarations of a new
form, `axiom`, in `library/axioms.cubist`, stated over it. The translator's
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
| `cubist-tests/` | 15 | Direct uses in `program_assumptions`, `inspection_axiom_labels`, `assembly_generic_assumptions`, `universe_generic`, `inductive_assumptions` (E507 fixtures) and `truncation_rebuilt_classical` (`old` and `both`); the legacy labels in E324/E330 goldens of `computability`, `computability_evaluation` and `inductive_computable`, through the archive's `classical`; assumption parameters in the type renderings of six `*_invalid_*` goldens over archive developments |
| `tests/` | 31 | Exact assumption lists or patterns in the Artin, Galois, dimension, linear-algebra, finite-spanning, algebraic-extensions, polynomial, quotient, universe-generic, library, CLI, REPL, assembly, program, inspection, reduction, benchmark, declaration, contract, migration and browser tests; the E324 goldens of `tests/fixtures/contracts/nonempty_contracts.cubist`; the recorded labels of the three capture-bindings cost baselines |
| Reference | 4 | `assumptions.html`: the truncation section and the statements of `LEM` and `Choice`, 40 mentions; `checking.html`, 2; `errors.html`, the E406 row; `terms.html`, the reserved names |
| Guides | 2 | `docs/guides/cubist.md`: the list of library principles and the universe examples; `docs/guides/regression-contracts.md`: an `expect_axioms` example |
| Implementation | 6 | `web/cubical-assumptions.mjs` (the types), `web/translator/builtins.mjs` (the handlers), `web/cubist/parser.mjs` (reserved names), `web/cubical-notation.mjs` (the `‖A‖` hook), `web/diagnostics.mjs` (E404–E406), `tools/migration-ledger.mjs` (the `LEGACY` set) |

### Axioms as declarations

Excluded middle and choice are the only assumptions the language has once
the legacy truncation is gone: `FunExt`, `ua` and `UnivalenceBeta` are
derived and compute. They stop being builtins and become declarations of a
new form, which the library states once:

```text
import h1_truncation;

axiom LEM(U < UU0, A : U, nn : (A -> Void) -> Void) : Trunc(U, A);

axiom Choice(
  U < UU0, A : U, B : A -> U, setA : IsSet(U, A), setFibers : (forall a : A. IsSet(U, B(a))),
  inhabited : (forall a : A. Trunc(U, B(a)))
) :
  Trunc(U, forall a : A. B(a));
```

- An `axiom` has a parameter telescope and a result type, and no body. The
  checker adds one context entry of that type, generic over the telescope's
  universe binders, as `libraryAssumption` builds one today. The kernel
  checks proofs abstracted over the context, as it always has, and trusts no
  new rule. Universe arguments stay explicit.
- An axiom is a non-computing dependency, listed by its name. A
  `computable` declaration that depends on one is refused (E330), `evaluate`
  refuses its terms (E324), a declared type's parameters and constructors
  cannot use one (E507), and inspection shows it as it shows an assumption
  today.
- `library/axioms.cubist` holds the two above and imports `h1_truncation`
  for `Trunc`. `h1_classical` imports `axioms` and keeps the derived results,
  `double_negation`, `decide_prop` and `resize_prop`, and the statements
  `ExcludedMiddle(U)` and `AxiomOfChoice(U)`, with
  `excluded_middle_assumed(U) := LEM(U)`.
- `axiom` becomes a reserved word. No checked source uses it as a name; it
  appears in comments only.
- Imports are transitive, so `import axioms;` brings `Trunc` into scope, and
  a later import shadows an earlier one's names. Transitivity stays as it is
  for now, by direction of 2026-10-20; changing it is later work and no part
  of this plan.

### Steps

1. **`axiom` declarations and `library/axioms.cubist`.** The parser,
   translator and inspection learn the form; the reference's declarations and
   assumptions chapters document it; `h1_classical` moves onto `axioms`. The
   translator's `LEM`/`Choice` handlers with a truncation former are retired:
   the former's only job was to tell the rebuilt assumptions from the legacy
   ones, and any admitted proposition truncation could fill it, minting a
   separately labelled copy.
2. **Library and fixtures off the legacy assumptions.** `classical_axioms`
   is deleted in favour of `h1_classical`, and its ledger comparison becomes
   historical; `universe_automorphisms` is restated over `Trunc(U1, …)`, with
   `mere_eliminate` into `Trunc(U0, A)`. Fixtures that test the legacy
   signatures themselves are restated over `Trunc` and the axioms;
   `truncation_rebuilt_classical` loses its former cases; the computability
   fixtures import `h1_classical`. Test expectations over library programs
   lose their `Truncate` labels. Expectations over archive modules keep the
   legacy labels until the archive retires. The ledger tests that construct
   legacy baselines run them as archive sources, or retire in step 5. The
   cost baselines are regenerated or marked historical.
3. **Reference and guides.** The assumptions chapter presents `LEM` and
   `Choice` as the library's axioms over `Trunc` and sends truncation to the
   cubical chapter's declaration (`point`, `squash`, `mere_eliminate`); the
   E406 row and the reserved names follow; the guide lists `Trunc` and the two
   axioms among the library principles.
4. **Confinement.** `Truncate`, `TruncateIntro`, `TruncateProp`,
   `TruncateElim` and the builtin `LEM(U, …)` and `Choice(U, …)` are
   accepted only in archive modules, which the module reader distinguishes by
   root (I1.1); elsewhere they are refused with an error that names `Trunc`
   and the library's axioms. The archive's three call sites,
   `classical.double_negation`, `zorn_chain_complete` and `surjections`, keep
   the builtins: importing `axioms` next to the archive's `truncation` would
   shadow its `merely`, `mere_eliminate` and `IsProp`. The builtins are
   relabelled `LEM[Truncate]` and `Choice[Truncate]`, so that a program mixing
   archive and library classical results, as `h1_zorn_step` does, lists them
   apart from the axioms. The alternative to a translator check, a source test
   over the roots, is weaker: it reports after the fact and says nothing to a
   REPL entry.
5. **Removal, with the archive** ([I0.5](../archive-retirement.md), R5).
   `web/cubical-assumptions.mjs` goes entirely: the four truncation types, the
   legacy `LEM`/`Choice` signatures, their builtins, the notation hook and the
   diagnostics. The four documented ledger comparisons and
   `truncation_rebuilt_classical`'s coexistence check end here: the removal
   commit records the last revision at which they ran, and this record cites
   it. The ledger file, its `assumptionsRemoved` lists and the `LEGACY` set
   stay as the record of the pinned changes.

### Decisions

- **Excluded middle and choice are library axioms, not builtins.** With one
  truncation there is nothing for a truncation former to distinguish, and a
  former that any admitted proposition truncation may fill mints a separately
  labelled copy of the assumption, equivalent but noise. An `axiom` in
  `library/axioms.cubist` states each once. Direction of 2026-10-20.
- **Where `axiom` is allowed.** Recommended: in any module. Every axiom is a
  listed non-computing dependency, `computable` refuses its dependents, and a
  result that wants a classical hypothesis still takes it as a parameter, as
  `h1_classical`'s statements allow. The library's own rule, that
  `axioms.cubist` is its only module with axioms, is a review rule. Accepting
  `axiom` only under `library/` would be one condition on the module root, if
  wanted later.
- **Labels.** The library's axioms are listed by their bare names, `LEM` and
  `Choice`, as the assumptions are today; an axiom declared elsewhere by its
  module-qualified name. The legacy builtins are relabelled `LEM[Truncate]`
  and `Choice[Truncate]` for their remaining archive life.
- **Module names.** `h1_truncation` and `h1_classical` keep their prefixes
  while the archive's `truncation` and `classical` exist. Renaming them is one
  migration after R5; the axioms' labels do not depend on it. Open until then.
- **Reserved names.** `axiom` joins the reserved words in step 1.
  `Truncate`, `TruncateIntro`, `TruncateProp` and `TruncateElim` stay
  reserved through step 4, so that a historical source fails with the
  retirement error rather than an unknown name, and are freed in step 5.
  Open: whether to keep them reserved after.
