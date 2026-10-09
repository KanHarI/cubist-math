# Frontend generation: design and implementation roadmap

Status: planned on 2026-10-09, on top of PR #188 at
[`00d4ecce`](https://github.com/KanHarI/cubist-math/commit/00d4ecce016f7e18d13eedeced07dc098a2277cb).
The [gap inventory](../reports/frontend-generation-gaps.md) pins current
reproductions and distinguishes remaining defects from fixed review
failures. This document proposes implementation work; it does not mark
those defects fixed. The [work plan](work-plan.md#frontend-generation-track)
records its scheduling dependencies.

Follow-up implementation evidence is maintained in the inventory's
[fixing-commit table](../reports/frontend-generation-gaps.md) and the
[FG6 gate report](../reports/frontend-generation-fg6.md). The planned
contracts below remain the reference; the report records the unresolved
historical skipped-mutation evidence rather than declaring it completed.

The goal is to preserve the meaning and interface of a declaration through
capture, inheritance, substitution, generation and elaboration. The
generator must also refuse unsupported constructions before publishing
invalid artifacts. Kernel checking establishes that generated terms have
their stated types; it does not establish that those types express the
source the user wrote.

## What PR #188 teaches

The H identifiers below refer to the inventory's
[fixed examples](../reports/frontend-generation-gaps.md#fixed-failures-that-motivate-the-design);
the G identifiers are open findings. The [follow-up review at `00d4ecce`](../reports/pr-188-review-00d4ecce.md)
shows that the earlier fixes did not establish the complete contracts.
It supplies G8–G12 and the mutation/compatibility evidence below.

| Evidence from #188 | Prevention requirement | Work |
| --- | --- | --- |
| H1: substitution lost law binders; generated names collided | Describe every binder scope once and reserve declaration ownership consistently. | FG0, FG1, FG2 |
| H2: imported globals changed in the caller | Retained syntax carries resolved dependencies and an explicit open interface. | FG2, FG4, FG6 |
| H3: a private captured key was reparsed as source | Migrate producers and consumers together; builders accept structured payloads, with validation at phase boundaries. | FG2, FG5, FG6 |
| H4: opening a model changed which global a law captured | Capture the complete lexical context; verify intended law types independently of elaboration success. | FG2, FG4, FG6 |
| H5: internal names and generated locations escaped into the UI | Keep identity, public label, origin and compiler control state separate. | FG1, FG4, FG5 |
| G8: an overbroad wildcard fallback replaces an endpoint error with a generation error | Separate fallback eligibility, proof search and diagnostic ownership; unsuccessful speculation preserves the primary error. | FG0, FG4, FG6 |
| G9/G10: freshened law uses lose their links; E871 has an empty range | Preserve lookup keys, display labels and exact source origins through all consumers, including failure paths. | FG0, FG2, FG5, FG6 |
| G11: derived-operation parameters are missing from the inlining scope | Transform complete declaration telescopes; capture avoidance cannot recover a binder omitted at the call site. | FG0, FG2, FG6 |
| G12: a value call to an earlier recursive operation is treated as type unfolding | Classify elaboration purpose and dependency kind explicitly; earlier calls and structural self-calls are different operations. | FG0, FG2, FG4, FG5 |
| G2/G3: invalid Hom declarations emerged late | Analyze dependencies and supported transport before generation; calculate universes from complete generated types. | FG2, FG3 |
| G4/G5: evidence and interfaces were lost by otherwise local transformations | Pass evidence explicitly and make tooling consume declaration semantics. | FG4, FG5 |

#188 already introduces resolved `reference` and structural `member`
syntax, scope-aware substitution, closures, explicit generated recursive
calls, and public-label/source-origin separation. Retain and consolidate
those mechanisms according to [the existing contract](syntax-hygiene.md).
This plan does not require a new kernel rule or a switch to de Bruijn
indices. G9 and G11 show that introducing the representations alone does
not migrate every caller and consumer. The failures occurred while
transforming frontend syntax, before kernel binder representation could
repair the lost meaning.

## Shared contracts

The names below describe required information, not APIs already present or
a commitment to introduce one class for every row. Implement them in the
existing modules first; extract a shared service when its consumers agree.

| Boundary | Information it must retain | Forbidden shortcut |
| --- | --- | --- |
| Declaration ownership | Module, namespace, declaration kind, stable identity, source origin, reservation/check status | Using separate duplicate-name rules for definitions, inductives and generated declarations |
| Retained declaration/expression | Complete parameter telescope and scoped result/body, resolved external dependencies, open binder interface, selected notation, source origin | Resolving a captured occurrence from display spelling, or transforming a body after discarding its binders |
| Generation request | Captured theory record, caller-scoped arguments, parameter interface, requested artifact family, support result | Reading a later theory or `use` selection because its name matches |
| Artifact plan | Declared identities, dependency edges, public labels, origins, checked publication groups, obligations | Inferring dependencies from dotted names or retrying arbitrary failed templates |
| Elaboration context | Term/level/dimension scope, refinements, checked evidence, recursion state, value/type purpose, primary diagnostic, resource accounting | Reconstructing compiler state from source names or replacing a written mismatch with a failed speculative fallback |
| Source reference | Lookup identity/key, written label, binder definition origin, occurrence origin | Comparing a public label with an internal environment key to find the binding |
| Published interface | Checked artifacts, argument labels, supported derivations, diagnostic/provenance metadata | Presenting an unchecked reservation or unsupported capability as a usable declaration |

Raw local names remain valid in nominal syntax. Before retaining an
expression, classify every free occurrence as an explicit interface binder,
a resolved external dependency, or an unresolved occurrence to diagnose at
its original site. The destination must not supply a new interpretation
for an accidentally unclassified occurrence. Unknown syntax kinds must
continue to fail scope traversal visibly.

Generation has explicit steps: reserve names; capture interfaces; analyze
support and dependencies; build an artifact plan; elaborate in a staging
context, including universe inference; check; publish. Dependent artifacts
may use checked predecessors inside the staging context. A syntax-only
planner must not claim to have inferred types or discharged obligations.

## FG0: establish evidence and semantic comparisons

Depends on #188's scope fixes. Start this before the implementation slices
and extend it in every slice. Initial change: a small test-only PR.

- Turn G1–G6 and G8–G12 into durable fixtures with explicit current failures and
  expected outcomes. Prefer a focused test for a complete behavior over
  assertions that merely mirror a helper's implementation.
- Map H1–H5 to existing regressions rather than duplicating them. Add the
  missing mixed declaration-kind, dependent-universe, nested-evidence and
  lint-client cases. G7 requires controlled failure injection or a newly
  demonstrated source case; its old capture examples now pass.
- Define a comparison manifest: public declarations and types, argument
  labels, required checked witnesses, computations, assumptions, and
  expected refusal sites. Include which generated artifacts may exist
  when one requested family is unsupported.
- For meaning checks, write expected law types and client proofs
  independently of the generator. H4's selected identity must be verified
  against the selected model's value, not against another output of the
  same expansion. Alpha comparison alone can share the generator's bug.
- Add a source-observation manifest for G8–G10: diagnostic code and
  endpoints, nonempty original source range, written binder/use labels and
  definition targets. Test every occurrence after freshening. Acceptance
  alone, or merely finding a gap named `bad`, cannot establish these facts.
- For G11, require the intended `op(x, S.c)` equation to check and the
  accidentally captured `op(x, x)` equation to fail in a theory with no
  law identifying them. Cover helper chains and complete grouped/dependent
  telescopes, not only law binders. For G12, include both supported value
  calls and legitimate type-unfolding refusals with their source sites.
- Preserve the follow-up review's passing controls: inherited helpers under
  law binders, bare/partial helper uses, non-enclosing pattern binders,
  inherited recursion, `N.model.iter`, and explicit path bodies. Record
  B1's file-level `use` precedence as an intentional compatibility rule,
  with tests against a later same-spelled global and changed selections.

Exit: each confirmed open G1–G6 and G8–G12 item has a reproducible fixture, an
independent expected outcome, a responsible slice below, and a named
regression that demonstrates the failure. G7 remains a separate test
requirement until a source reproduction or failure-injection test exists.
Land activation of a failing regression with its fix, or explicitly track
it as an expected failure during the harness phase. Expected failures must
be removed when fixed and cannot count toward the slice's completion.
Do not normalize wrong behavior into acceptance snapshots.

## FG1: unify declaration ownership and publication

Depends on FG0. Addresses G1, G6 and the historical G7 symptom. Primary
consumers: `translator/translate.mjs`, `inductive.mjs`, `theories.mjs`,
`initial-models.mjs`, and program inspection/export registration.

1. Give ordinary and generated declarations a shared module-local
   ownership check. Reserve an expansion's generated names before any
   member can overwrite an existing entry. Local binder shadowing,
   shadowing imports, and a model's permitted notation extension remain
   separate operations with explicit policies.
2. Record lifecycle and dependency state independently of environment
   aliases. A duplicate declaration fails without replacing the original
   entry by either a new value or an `Untranslated` marker. A failed
   dependency retains its identity and cause; a child reports that
   dependency rather than re-expanding its invalid syntax.
3. Define atomic publication groups before adding transaction machinery.
   A base theory, its derived operations, its Hom/Iso families, and an
   initial/free construction need explicit required/optional edges.
   A refused Hom family must not erase a valid base theory. A group must
   not advertise a complete generated interface while required members
   are missing. Scope the first implementation to the existing families.
4. Reuse and audit the existing transaction/checkpoint mechanisms. Stage
   environment aliases, kernel registrations, theory records, notation,
   inspection links, and export/cache metadata together for the chosen
   group. Check rollback and invalidation at each boundary; frontend
   staging alone cannot undo already-published kernel state.

Split delivery into the ownership fix, dependency-state handling, and the
publication-group migration. Exit tests cover both orders of mixed-kind
collisions, generated namespace collisions, legal shadowing, failed
members, imports and rechecking after edits. After refusal, the earlier
binding and independent declarations still work, no partial group leaks,
and progress/error reporting is consistent. Replaying exported checked
artifacts gives the same result.

## FG2: describe dependencies and supported generation explicitly

Depends on FG0; uses FG1 for artifact publication. Addresses G3, G10–G12
and B1, and guards H1–H4. Primary consumers: `cubist/theories.mjs`, `morphisms.mjs`,
`scopes.mjs`, `references.mjs`, and `translator/initial-models.mjs`.

1. Retain a field dependency graph over binding identities and its open
   parameter interface. Classify references to carriers, operations,
   laws, h-level evidence and fixed external declarations. Follow
   transitive dependencies through earlier fields and inlined helpers.
   A domain is not fixed merely because no carrier spelling occurs in it.
2. Have each construction strategy consume that graph and report a
   structured support result: supported with explicit mapping/transport
   operations; unsupported with a source-located reason; or supported
   subject to named proof obligations. Sharing dependency facts does not
   make morphism and initial/free admissibility the same predicate.
3. For G3, first produce a focused unsupported-derivation result while
   retaining the checked base theory. Do not emit invalid Hom/Iso
   declarations. Accept law-dependent inputs only in a later slice that
   specifies and checks how they are transported and how maps compose.
4. Validate generation boundaries: structured references stay structured,
   local selections keep their receivers, and template holes are distinct
   from source binders. Audit every AST consumer when adding a node kind,
   including free-variable analysis, substitution, serialization,
   relocation, display, diagnostics and elaboration lowering.
5. Give inlining a complete scoped declaration interface: parameter groups,
   their domains, result type and body. Each group's binders are outside
   its domain and inside subsequent domains/result/body. Preserve public
   labels when freshening locals; describe this once in the shared scope
   traversal, then migrate every transformation caller. Do not fix G11 by
   adding another list of forbidden parameter spellings. Carry the actual
   conflicting binder/occurrence when a fixed pattern or statement capture
   must be refused (G10).
6. Distinguish expansion in a field type/law from elaboration of a derived
   value. Nonrecursive helper expansion, calls to checked earlier derived
   operations, and the current operation's structural self-calls need
   explicit, separate support rules. Preserve an earlier recursive call in
   a value body without recursively unfolding it (G12). This must not
   permit nonstructural self-recursion or silently widen supported types.
7. Audit `notationScope` and the aliases installed by initial-model
   generation against the now-complete lexical captures. Retain the layer
   only with a concrete behavior and distinguishing test; otherwise remove
   it with its redundant plumbing after checking all producers/consumers.
   Do not maintain two implicit sources of notation scope. Preserve B1's
   documented precedence during that consolidation.

Exit: G3 receives the intended refusal without type-error cascades; the
same check catches dependencies hidden behind aliases/helpers. Supported
fixed arguments still work. Imported, inherited and renamed variants have
the same support result after the explicit interface correspondence.
Existing sources that no longer need collision refusals remain accepted.
G11's intended and captured equations have opposite, correct outcomes
through helper chains, inheritance and generated clients. G12's ordinary
value call checks and computes, while actual unsupported unfolding retains
its focused refusal. G10 supplies the original conflict range to FG5.
The notation-alias survivor has a recorded test-or-removal disposition.

## FG3: infer universes from the generated telescope

Depends on FG2's planned types and FG1's staging boundary. Addresses G2.
Primary consumers: `cubist/morphisms.mjs`, universe elaboration, and
checked declaration builders.

Elaborate all proposed map and preservation field types in the appropriate
parameter context, then use the ordinary universe rules to derive a
sufficient level for the whole telescope. Include fixed operation domains,
dependent arguments, family indices and evidence/proof fields. Preserve
the theory's shared-universe constraints and the existing finite/tiered
universe rules. Use the least level the existing solver can justify; do not
replace `max(U, V)` by another hard-coded formula or blanket large level.

Build Hom, identity, composition and supported Iso artifacts from the same
analyzed field telescope. Keep user-facing universe labels independent of
the internally chosen binders. If inference cannot discharge a constraint,
report that obligation before publishing the family.

Exit: G2 checks with identity/composition clients. Include fixed domains
at U0 and U1, generic universe parameters, inherited operations, and
dependent indices. Negative cases must still reject actual universe
lowering. Verify generated public types and assumptions, not just the
absence of E606.

## FG4: carry evidence and compiler state with the context

Depends on FG2's interfaces; uses FG1's checked artifact identities.
Addresses G4, G8 and G12 and protects #188's recursion and capture fixes.
Primary consumers: `translator/elaboration.mjs`, `match.mjs`, `patterns.mjs`,
`hlevel.mjs`, and generated derived-operation builders.

- Make available checked evidence an explicit part of the elaboration
  context. A model contributes its h-level projections as checked terms
  with types and dependency identities. Search may index those terms; an
  index hit is never itself a proof.
- Transport or rebuild this evidence with the same substitutions,
  refinements, generalized parameters, and dimension restrictions as the
  goal. Test that evidence from an old context cannot be reused after a
  model or motive changes. Capturing a closure must not freeze variables
  that belong to the destination's explicit interface.
- Keep structural recursion information in its existing private context,
  not source-name aliases. Nested matches update recursive results and
  evidence consistently. Retain ordinary lexical shadowing for written
  source calls.
- Separate written-body checking from optional coherence construction.
  A failing wildcard is eligible for the recursive-boundary fallback only
  when its constructor has recursive positions. Try it against the actual
  clause type; retain the original mismatch if it cannot construct checked
  coherence. A successful fallback commits its checked term and inspection
  evidence; unsuccessful speculation must not replace the source error or
  publish a generated-obligation view. Keep resource-limit failures distinct
  from ordinary proof-search failure and account for all work attempted.
- Preserve explicit path bodies. Independently requested or omitted
  generated obligations still use their own diagnostics. Failure to find
  evidence must not become a fabricated axiom or a stronger eliminator.
- Use FG2's call classification to elaborate earlier recursive operations
  as checked value calls, without confusing them with the current
  declaration's recursion hypotheses or its type-unfolding restrictions.

Exit: G4 and inherited/imported variants check and compute with no new
assumptions. Tests include nested matches under shadowed model names,
dependent motives and generalized parameters. Wrong-model evidence,
incompatible path endpoints, unsupported elimination and nonstructural
recursive calls remain refused. All attempted elaboration work, including
unsuccessful fallback, is charged once to shared fuel. G8's no-recursion example and
recursive fallback failures retain E606, their actual endpoints and original
body range; successful Unit-valued recursive coherence and initial-model
cases still check. Explicit path clauses remain untouched. G12 computes
through ordinary, inherited and initial-model clients.

## FG5: preserve public interfaces and source provenance

Depends on FG2's field/interface information. Uses FG1 for published
metadata. Addresses G5, G9, G10 and G12's diagnostic, and protects H5.
Primary consumers: the source linter, signature/inspection formatting,
diagnostic builders and link sites.

Define one provenance contract for written nodes, copied written syntax,
and synthetic nodes. Written public labels survive alpha renaming. A
diagnostic uses the label and the appropriate origin; resolution uses
identity. Synthetic artifacts can expose their generated signature through
inspection without claiming tokens or links that the user never wrote.

Audit the full source-alias pipeline: binding registration, freshening,
environment filtering, use-site reference recording, hover formatting and
definition navigation. Store resolution identity/key independently of the
public label; neither may substitute for the other's equality test. Keep
both the occurrence's written span and its binder's definition span. For
G9, all three law uses and the binder must display `c`, link to that written
binder, and reveal no internal `c1`. Inspect these observations directly and
through the browser, alongside the independently checked law meaning.

Refusals use an explicit source origin carried from the transformation that
found the conflict. G10 points at the enclosing pattern/statement binding or
helper call; G12 names a value-call limitation only if that is the actual
unsupported context. Assert diagnostic category and a nonempty range over
the responsible original token. An arbitrary law-start marker is not a
valid replacement for a discarded origin.

Make unused-binder advice aware of theory-field roles and public argument
labels. Initially suppress arrow-form advice where it changes a generated
interface. A future broader simplification must prove preservation through
checked clients: named calls, Hom/Iso operations and initial/free folds.
Merely preserving the standalone function type is insufficient.

Exit: G5's suggested edits either preserve those clients or are not
suggested. Ordinary safe unused-binder advice still appears. Import and
generation tests check source spans, link multiplicity, diagnostic codes,
public argument names, and absence of private binding keys. Public labels
and origin metadata do not participate in semantic identity comparison.

## FG6: make preservation tests and measurements a release gate

Build incrementally from FG0, alongside every slice; the complete gate
depends on FG1–FG5. Addresses V1 and P1. This is preventive infrastructure,
not a claim of a formal proof of the compiler.

Use deterministic, bounded generation of small well-formed theories and
clients. Record the seed and minimize a failing case. Start with the
following transformations and explicit side conditions:

| Transformation | Required invariant |
| --- | --- |
| Rename a bound local, preserving intentional shadowing | Same checked meaning up to the declared binder correspondence; original public API labels are kept where they are part of the interface. |
| Add an unrelated declaration or choose colliding generated-name stems | Existing references and laws retain their identities; valid generated locals are freshened. An actual duplicate public declaration is refused instead. |
| Move a theory to an imported module with an explicit export correspondence | Same public types, laws, assumptions and computations after mapping module identities. |
| Inherit under a different caller `use` selection | Inherited expressions retain the parent's selection; newly written expressions use the child's. |
| Inline a supported helper under nested binders, including a derived declaration's full telescope | Equivalent result and law boundaries; intended equations check and captured equations fail; fixed captures point to their original source site. |
| Freshen a binder while preserving its source interface | Written labels, hover values and every definition target still identify the original binder, with no internal names exposed. |
| Try optional coherence after a wildcard mismatch | Only eligible recursive boundaries are tried; success yields a checked term and failure preserves the primary mismatch and source range. |
| Call an earlier recursive operation from a derived value | The call checks and computes without unfolding recursion into the caller; type restrictions and structural self-call checks remain effective. |
| Apply a proposed lint rewrite | Checked clients and generated capabilities remain available with the same public calling conventions. |

Compose transformations, especially import + inheritance + inlining +
shadowing. Compare more than success: independent expected types/proofs,
binding correspondence, assumption sets, computations, supported artifact
sets, and specified diagnostics. Normalize only within bounded checker
work, account for legitimate generative declaration identities, and avoid
using pretty-printed text or the same generator as the sole oracle.

Add targeted mutations at each contract: discard the lexical `use` scope,
re-resolve a reference's spelling, skip a binder region, omit a universe
contribution, drop evidence during refinement, bypass a name reservation,
publish a failed group, or ignore synthetic provenance. A mutation must
have a named distinguishing test; a surviving mutant calls for analysis,
not an automatically weakened assertion. Keep a small deterministic CI
set and a larger repeatable audit set with explicit resource budgets.

Start with the reviewer's 20-mutation audit (13 killed, one skipped, six
surviving). Kill the two label-removal mutants using G9's observation tests.
Resolve the notation-alias mutant via FG2's distinguishing test or removal.
For each remaining or skipped case, record the changed contract, whether it
is reachable in supported source, a distinguishing test if one exists, and
why an equivalent/defensive mutation is excluded if none exists. Include
the separately reported explicit-head guard probe; preserve the checked
explicit-path controls. A survival count is neither proof of dead code nor
a requirement to manufacture an implementation-shaped test.

Before and after each implementation slice, record revision/build stamps,
workload, limits, kernel queries/instructions, syntax allocation or another
available memory measure, and wall time. Include a small algebra import,
an inheritance chain with captured expressions, and a generated fold.
Do not set a regression budget from one historical timing or silently
increase fuel limits to make a change pass.

Exit: direct regressions, invariant tests, the applicable source/library
and corpus checks, and CLI/browser inspection checks pass at the submitted
commit. Each change has its producer/consumer audit and semantic evidence.
Unexpected corpus timeouts are rerun with unchanged limits and reported;
successful retries do not replace direct tests of known gaps.

## Delivery order and capability boundary

Deliver small changes with explicit behavioral contracts:

1. FG0 fixtures and comparison manifests, including G8–G12 and B1.
2. Fix G11's silent capture with the complete-telescope interface from FG2;
   fix G8–G10 with focused FG4/FG5 contracts and regression tests. These
   corrections can land on #188 and remain evidence for the longer work;
   they do not wait for the publication redesign. Update the inventory's
   status with the fixing commit and distinguishing test when each lands.
3. FG1 ownership, then dependency state and publication groups.
4. Complete FG2 dependency/support analysis and boundary validation,
   including G12's value-call classification and the notation-scope audit.
5. FG3 universes and FG4 contextual evidence; each builds on the shared
   interfaces and can be implemented as separate reviewed slices.
6. FG5 tooling/interface preservation; its focused lint fix can land
   earlier once FG0 provides the checked-client regression.
7. FG6's complete cross-transformation gate, accumulated throughout.

Resolve implementation choices for publication groups and context
ownership in those slices' design reviews. Passing the current examples
alone is insufficient to complete a slice; its exit conditions govern.

The existing [L2.6 contract](core-theories.md#initial-and-free-models-l26)
continues to own C1: opt-in registration, uniqueness, universal equivalence,
extra-law evidence and higher coherences. FG1–FG6 are prerequisites for
publishing new checked deriving capabilities, not replacements for those
mathematical proofs. Declaration-and-fold prototypes remain labeled as
such. No phase resumes paused library work or adds unsupported carriers,
families or elimination principles by implication.
