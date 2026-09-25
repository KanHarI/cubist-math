# HoTT and cubical abstractions and automation in Cubist

Status: A7 delivered on 2026-09-25 (see the
[implementation checkpoint](../tactical/hott-automation-handoff.md)); the other
milestones are planned. Revised after two design reviews on 2026-09-24 and a
restructuring on 2026-09-25. The second review added library-first milestones:
several targets follow from computation the kernel already performs, before
any new tactic. The milestones below are proposed work; existing
implementations are identified as evidence.
This roadmap follows the checked first slice of the [proof ergonomics roadmap](proof-ergonomics-roadmap.md)
and its [implementation plan](proof-ergonomics-implementation-plan.md). It
reorders their remaining dependent, cubical and induction work around paths,
transport and path induction, which dominate the library, and it owns the
shared elaboration infrastructure (A4–A6) that the ergonomics roadmap's
remaining argument inference also needs. See
[changes to the ergonomics plan](#changes-to-the-ergonomics-plan). It covers
language tooling and the library foundations that tooling needs. The
kernel-extension investigation, G, now has its own
[kernel roadmap](cubical-kernel-roadmap.md). It does not resume the paused
mathematical roadmaps.

**Restructured later on 2026-09-25.**
- The first library is to be archived and rebuilt; its notable results are
  recorded in [library-results.md](../library-results.md).
- The kernel roadmap adopted G0 (universe-generic checking) and item H
  (inductive signatures, stages H1–H4), from the
  [higher inductive-inductive type design](higher-inductive-types-design.md).
- The ergonomics roadmap adopted milestones 6–8: theories, inductive
  declarations with pattern matching, and computability as a checked
  property.

Consequences here:
- B0, B2, B5, F3 and A9 are superseded; they keep their labels as pointers.
- A2, A5, D0a, D1 and E2 gain requirements, marked "(H)".
- Targets that name declarations of the first library remain as evidence. For
  the rebuild they become acceptance examples: the rebuilt counterpart must
  get the stated benefit.

The [work plan](work-plan.md) sequences this roadmap with the others.

**Terminology.** "Universe template" below means a universe-generic
definition. Until G0 these are elaborator templates, specialized per
universe. After G0 they are level-generic kernel definitions checked once.
Items that ask for templates ask for the latter in the rebuild.

Read the [proof ergonomics checkpoint](../tactical/proof-ergonomics-handoff.md)
first: it records the supported fragment this roadmap starts from.

## Objective

Make the language and library effective for homotopy type theory: path algebra,
transport, path induction, h-levels, dependent paths and structured equivalences.
The native kernel remains the sole proof authority and paths remain
proof-relevant data. A–F build on the existing kernel. The separate
[kernel roadmap](cubical-kernel-roadmap.md) owns kernel changes: G0, H1–H4 and
the remaining G items.

Breaking source/API changes and abstractions that cannot translate back to the
current core are allowed when their benefit is demonstrated. Preserve explicit
assumption reporting and checked typing, boundaries and universes. Document
intentional changes to public representations and computed witnesses instead
of requiring every redesign to produce a convertible predecessor. Each
migration must identify its consumers and the evidence needed to update them.

`Path` and `PathP` remain the primary equality interface. J is compatible with
cubical type theory and already exists here as derived path induction, with a
propositional computation law. A separate `Id` with judgmental J computation
is the declared identity family of [H2](cubical-kernel-roadmap.md#items), which
supersedes G3. K/UIP for arbitrary types is not part of the design.

The first slice serves first-order equational reasoning well, such as
`simp only [nat_add_zero]` on natural-number arithmetic. It does not yet reach
the path vocabulary. The [evidence](#evidence) at the end of this document
records why, and what cubical type theory offers instead. In summary:

- Path builtins lower to raw `PLam`, `PApp` and `Comp` syntax. The rule matcher
  cannot recognize them, and rewriting descends only through applications.
- The kernel already computes more than the library uses. Eliminators that take
  PathP bridges compute on path constructors by conversion, but the library's
  suspension eliminators take transport equations and prove those laws
  instead. Several laws that the library proves by induction, or that
  this plan first listed as rules, hold by conversion.
- In one measured example, the simplifier's proof costs 2.7 times the kernel
  steps of a direct cubical line.

The milestones therefore start with library changes that use existing
computation, then add tooling for what conversion cannot establish.

## Invariants added to the ergonomics requirements

The ergonomics roadmap's [architecture invariants](proof-ergonomics-roadmap.md#architecture-and-invariants)
and [HoTT and cubical requirements](proof-ergonomics-roadmap.md#hott-and-cubical-requirements)
apply, with explicit migration exceptions for new public representations,
changed witnesses, and G's kernel extensions as described here. In addition:

1. **Deterministic elaboration.** Whether automation succeeds depends only on
   source, imports, elaboration strategy/version and declared fuel, never on
   elapsed time. A wall-clock limit remains a safety net, reported as a distinct
   timeout rather than as a proof failure in regression comparisons.
2. **Folded heads are definitions, not rules.** When a builtin elaborates to a
   named checked definition, the definition's body is the syntax the builtin
   produced before. A1 is a definitional refactor. If any corpus
   declaration changes acceptance, investigate it; do not work around it.
3. **No regularity is assumed for existing paths.** Transport along `refl` or
   a constant family, and path induction at `refl`, need not compute for neutral
   types or motives. Automation uses checked propositional laws when conversion
   does not suffice. The kernel roadmap does not add strict J computation to
   `Path`. The separately declared family `Id` (H2) computes J on `refl`; it is
   a different type, not a change to `Path`.
4. **Transported data is flagged.** The inspector marks any transport that
   automation inserts into a term whose type is not a checked proposition. Such
   a term may no longer compute to a canonical value. Conversion avoids an
   inserted transport; `subst` improves context handling but uses derived
   induction and gives no stronger computation guarantee.
5. **Loops stay loops.** Path induction rejects a path whose endpoints are the
   same variable. The h-level solver proves `IsContr`, `IsProp` and `IsSet`
   statements only from registered checked lemmas and local evidence.
6. **Matching transparency is explicit.** The rule matcher unfolds only
   definitions registered as matching aliases, and never unfolds `opaque def`.
   Kernel conversion is unaffected.
7. **Each tactic documents the path it builds.** The inspector distinguishes
   conversion, a supplied equality witness, congruence, composition and
   transport. Freeze/replay must produce a convertible proof under the same
   elaboration strategy/version. Persistent frozen output must retain the
   checked construction or pin the strategy, rather than merely a rule list.
   A3 may change witnesses across versions; migrations recheck their dependent
   consumers and supply comparison paths where the old witness is required.
8. **Universe and assumption changes are explicit.** D0b may replace the public
   equivalence representation and G may remove truncation assumptions. Record
   these intended differences separately from accidental changes; neither
   cumulativity nor a new HIT silently supplies resizing.
9. **Existing computation comes first.** When kernel conversion establishes a
   law, library interfaces and automation use conversion, recorded as a C1
   entry, rather than a registered equality rule. Eliminators generated for
   declared higher inductive types (H1) take dependent-path clauses, so their
   path computation is judgmental. The pushout eliminator already did this. Replacing a proof by conversion changes its witness; record
   that change as for A3. A statement that `rfl` also proves does not license
   replacing a construction: `close_path` has type `origin = origin`, which
   `rfl` inhabits, but its witness is a nontrivial loop.
10. **Computability is expressible and preserved.** Every closed term that
   checks without truncation or any other assumption must reduce to a canonical
   value by kernel computation. This is a design priority, not only a
   consistency property.
   - **Expressible.** A result that computes can be declared `computable` and
     tested with `evaluate`
     ([ergonomics milestone 8](proof-ergonomics-roadmap.md#8-computability-as-a-checked-property)).
   - **No tactic, library abstraction or elaboration convenience is
     implemented through an assumption schema.**
   - **Derived path induction is acceptable**, as used by B1. It computes on
     closed data, and its computation at `refl` is propositional only for
     open terms (invariant 3).
   - **Migrations and refactorings** must not replace a computing
     construction by one that uses an assumption. The migration verifier
     compares non-computing dependencies.
   - Kernel changes follow the same rule; see the
     [kernel roadmap](cubical-kernel-roadmap.md#governing-requirement-computability-is-expressible-and-preserved).

## Milestones

Milestone letters group work by topic, not delivery order. D0 refers to D0a
and D0b together:

| Slice | Dependencies and purpose |
| --- | --- |
| Library first | E0, D0a and A7's conversion audit need no new tactic and can start now, alongside A5. B0 is superseded by H1; in the rebuild its benefit comes with the declarations. |
| Baseline and shared machinery | A7 first; A5/A6 extract goal, scope and diagnostics; A4 uses the baseline to set hard fuel limits. |
| Path vocabulary and library foundations | A1a–A1c, A2 and A8 use the shared machinery. D0b defines the public equivalence type in the rebuild. |
| First useful automation | B1 follows A5 alone: it needs neither folded heads nor search fuel. B4 also follows A5. D1 uses D0a without waiting for D0b. Basic Σ ext in B3 precedes D2's automatic property-field closure; universe ext follows D0b. These do not wait for C3 or all of E. |
| Induction | `match` (ergonomics milestone 7) uses A5's motive abstraction on H1's generated eliminators. D3's library eliminator uses D0b and D4; its interface is a milestone 7 view, with B1 for `Path`. |
| Path optimization and dependent geometry | A3/C1 change proof construction explicitly; C3 uses their checked reconstruction. C4 needs only A5 and its library soundness lemma. E1 uses A1/A2/A5/E0, with optional C2 cleanup. E2's square library can start independently of C; E3 follows E0/E2/A5 and E4 follows the simplifier witness interface. C2 adds B1's computation law when available. |
| Structure descriptions and transfer | F1 can start after D0, D4, B3 and D1/D2; F4 uses D0a's h-level definitions. Theories (ergonomics milestone 6) supply record syntax; transfer builds on that evidence. |
| Kernel work | The [kernel roadmap](cubical-kernel-roadmap.md) ranks G0, then H1–H3. A–F releases do not wait for them, except the (H)-marked requirements, which the [work plan](work-plan.md) sequences. |

The library-first slice can ship before any tooling. The first tooling release
is A7, A5 and B1, with inspection and tests; the next adds A4, A6, A1/A2 and
B4. A3 is independently gated. D1/D2 and Σ extensionality form the next small
release. Argument inference, `apply` and `refine` retain the ergonomics plan's
scoped-metavariable prerequisites; they need not wait for all of D–F.

### A. Core representation for paths

- [ ] **A1. Folded path vocabulary.** Elaborate `refl`, `sym`, `trans`, `cong`,
  `transport`, `apd_path`, `path_induction` and `based_induction` to
  applications of reserved checked definitions, specialized by the full vector
  of universe levels in use (carrier, codomain and motive as applicable).
  Each definition's body is the syntax the builtin emits today. Deliver it in
  three parts: A1a folds `refl`, `sym`, `trans` and `cong`, with E0's
  dependent reversal and congruence; A1b folds `transport`, `apd_path` and both
  induction forms; A1c adds matching views and aliases.
  - Arithmetic sources such as [primes](../../archive/first-library/primes.cubist) use
    these builtins without importing `paths`. The definitions therefore belong
    to a session prelude with a stable logical operation identity across imports.
    Register specializations lazily through declaration transactions; rollback
    must invalidate their native handles and all dependent caches. A later use
    reinstantiates the same logical identity. Test a failed first use followed
    by a successful use, and different import orders.
  - Kernel conversion unfolds definitions on demand, so equalities such as
    `sym(sym(p)) ≡ p` still hold. Match the logical operation and compatible
    universe arguments, not exact native definition identities: a `U1` lemma
    must still apply to a `U0` carrier through cumulativity. Recheck every
    instantiated rule. `rw`/`simp` reach the path and value arguments of
    `transport` where the one-hole context has a fixed codomain.
  - Folded heads carry carrier, endpoint and universe arguments, as in
    `trans(A, x, y, z, p, q)`. These positions are neither occurrences nor
    congruence targets. Recompute them from the explicit path arguments after
    a rewrite; rewriting inside them is the dependent case that A2 excludes.
  - The builtin `sym` fails on a PathP over a varying family with an internal
    "Unbound cubical dimension" error. A1a folds E0's reversal and congruence
    for PathPs, or reports a normal diagnostic.
  - `paths.based_induction` shadows the builtin of the same name with a
    different body: path induction applied to a Π-motive, rather than the
    builtin's connection `comp`. A1b removes or renames one of them before a
    stable logical identity exists.
  - Reuse the specialization mechanism of the existing `builtin__ua__U<n>`
    definitions (`specializeSchema`), including its transaction behavior.
  - A1c: register the library wrappers `inverse`, `concatenate` and `ap` as
    matching aliases, so that a rule stated with either spelling matches. The
    syntax is to be settled, for example `simp_alias concatenate;`. An
    `opaque def` cannot be an alias. `opaque def` currently behaves exactly as
    `def` ([language reference](../../web/language.html)); invariant 6 gives it
    a matcher-only meaning, which the reference must then document.
    The library side is done: the tier 2 migration (2026-09-25,
    [handoff](../tactical/proof-ergonomics-handoff.md)) replaced all 205 full
    applications of `concatenate`, `append_path`, `inverse` and `ap` with
    `trans`, `sym` and `cong`, keeping public types convertible. Two partial
    applications remain. Aliases now serve only user wrappers and those
    partial applications.
  - During matching only, recognize a constant line as `refl` and
    `path i => p @ i` as `p`. Recognition proposes a candidate; the
    instantiated rule is still checked.
  - Give library lemmas with inferred raw endpoints explicit folded result
    signatures or checked view wrappers. `right_unit`, `transport_constant` and
    `transport_ap` currently construct raw `path`/`comp` terms, so changing
    builtin lowering alone does not expose their patterns. `simp only` cannot
    register the last two at all today: their inferred left sides omit `A`, `x`
    and `y`. Test these lemmas directly, including `U1` rules on `U0` carriers,
    rather than only the explicitly typed `ru` probe.
  - Rejected alternative: matching the raw `Comp` shape of `trans`. That breaks
    under ascription wrappers, renaming and convertible re-encodings, and the
    kernel would still re-check a composition at every use.
  - Hypothesis to measure: checking an application of a checked definition
    costs less than re-checking its inline `Comp`. Compare the corpus's native
    steps, arena use and elapsed time before and after. Compare public types by
    conversion and compare assumption lists.
- [ ] **A2. Rewriting through constructors.** Add congruence for these
  explicitly supported positions when their fixed-codomain contexts check:
  - `succ`, pairs, sum injections, projections and `sup` children;
  - in type goals, `Path` carriers and endpoints, and Π/Σ domains.

  A `Path` family carries a dimension binder; dependent family traversal waits
  for an explicit binder-aware implementation. Generic traversal into Glue,
  HIT boundaries, tubes and binder bodies is outside this slice.
  The existing one-hole check already detects dependency. For example, it
  reports a pair component whose sibling's type depends on it; E1 handles that
  case. Memoize simplification of shared DAG nodes within the same context,
  dimensions, faces, universe specialization, rule environment and unfolding
  policy. Reuse the witness as well as the result. Explicit occurrence selection
  must still distinguish different occurrences of a shared node.
  - (H) With H1, every constructor application is one uniform kernel node, so
    descent through constructors is a single rule. It covers `succ`, pairs,
    injections, `sup` and user constructors alike. The stopped curated
    migration found `rw` blocked at `succ`
    ([findings](../tactical/proof-ergonomics-handoff.md#curated-rwcalcsimp-pass-findings-stopped)).
    Descent into cubical forms (`trans`, `sym`, `along`) and a statement-level
    `with unfolding` are further gaps it found; they remain for A2 and C1.
- [ ] **A3. Congruence lines instead of composition chains.** Use a bottom-up
  traversal with local resimplification of subterms introduced by a rewrite.
  Continue to a fixed point under A4 fuel; one pass alone would miss new redexes
  and change residual goals.
  - Record the rewritten positions, each with its own path, and emit one line
    `path i => C[p1 @ i, ..., pk @ i]` for the whole term. Use `trans` only at
    a node rewritten again after its children changed.
  - Rebuild an equality goal with the single composition checked in the
    [evidence](#what-cubical-type-theory-provides-directly).
    When the residual holds by conversion, its path is a constant line, and no
    separate `refl` composition is emitted.
  - For a type goal, transport the following proof along one line of types
    rather than along a composite path of types. This avoids composition in the
    universe, which the kernel computes through Glue.
  - This deliberately changes the generated path. Do not require conversion to
    the old composition chain. Keep public goal types and assumptions for this
    optimization, recheck dependent consumers, and construct comparison paths
    where a migration needs the old witness. Freeze/replay under the same
    strategy must still yield convertible proofs. Record the strategy/version
    and native steps against the [cost table](#cost-of-the-current-proof-shape).
- [ ] **A4. Deterministic fuel.** In matching, traversal, premise search and
  proof construction, replace elapsed-time checks with counted fuel: traversal
  visits, candidate matches, rewrites, premise attempts, generated DAG nodes
  and native queries. Replace unbounded adapter budget growth with hard declared
  limits per native query and cumulative tactic/declaration work. Count failed
  attempts and retries; define reset and cache accounting so fresh and reused
  sessions have the same logical fuel outcome. Keep wall-clock deadlines only
  as the separately reported safety timeout. Distinguish frontend fuel,
  native-step exhaustion and timeout in diagnostics. Set default fuel from the
  A7 baseline and record it in a test fixture.
  - Interim state (2026-09-25 review): a tactic's time limit now covers only
    its own rule search, not later statements or proof reconstruction, and
    search limits are `SearchLimit`/`SearchTimeout` errors rather than message
    strings. The limits are still elapsed time, so a search close to its limit
    can pass on a fast machine and fail on a slow one; this item remains open.
- [ ] **A5. Goal, scope and proof-construction layer.** Before adding further
  tactics, extract the ergonomics plan's `Goal` and `Transition` interfaces from
  `Translator.blockBody`.
  `rw`, `simp`, `ext`, `induction` and `hlevel` then share reconstruction,
  source spans and inspector records. Keep the continuation model:
  - a tactic that produces several goals takes one block per goal, as `cases`
    already does;
  - a goal whose statement depends on an earlier goal's proof receives that
    proof as a named local.

  Introduce a typed proof-construction plan containing the source and target
  terms/types, selected witness, ordered dependency telescope, term and interval
  context, face restrictions, source spans and construction strategy. Its steps
  distinguish conversion, lemma application, congruence, composition, filling
  and transport. One reconstruction interface emits ordinary checked terms;
  the plan itself grants no proof authority. A2/A3/E1 share this representation
  with Σ extensionality, hypothesis substitution, inspection and persistent
  frozen output. Extract telescope abstraction independently of any tactic so
  registered eliminators and structure descriptions can reuse it.
  - Interim state: [proof-goals.mjs](../../lib/cubical/proof-goals.mjs)
    defines `Goal`, a target at a scope (term and interval context), and
    `Transition`: a goal, the goal that remains, a plan and the search trace.
    Plan steps are composition, transport, congruence, abstraction and lemma
    application; conversion closes a goal with a checked constant path.
    `rw`, `simp`, `simpa`, `ext`, `intro` and `over` rebuild through the
    plan's one interface, and `calc` shares its path composition. Tactics
    share inspector records. Filling steps, face restrictions, source spans in
    the plan, telescope abstraction, and `induction` and `hlevel` as tactics
    remain.
  - Also replace these elaborator mechanisms, found in the 2026-09-25 review:
    - [x] One name supply for every generated binder. About a dozen generators
      share one string namespace with kernel symbols. A generated-name
      collision once captured a variable in a theorem statement; unique
      `Translator.fresh` names and binding assertions were the interim fix.
      Delivered in [names.mjs](../../lib/cubical/names.mjs): each source unit
      (a module, or one template inspection) has one supply, which the
      translator, the rewriting service and checker queries all use. Its names
      never spell an assumption or a kernel symbol, and elaborating the same
      source again repeats them. Stand-alone syntax builders stay hygienic by
      avoiding every name in their inputs.
    - [x] Result values for every speculative query. `findRewrite` already
      returns "no match" as a result; checker queries should report mismatch
      and resource failures as values, so that no control flow depends on the
      kernel's "Type mismatch." message. Delivered: the kernel records a
      `cc_error_kind` with each error (mismatch, budget, deadline, other), the
      JS wrapper throws a `KernelError` carrying it, and a speculative check
      (`attempt`) answers `{ok, term}` or `{ok: false, failure}`. Budget
      retries, conversion queries, rewriting, benchmark categories and the
      migration verifier use these kinds; declaration results record
      `failure` and `template` instead of being classified by their reason.
    - [x] One computation of source link sites. The parser records keyword spans,
      as it now does for each `calc` step's `by`; concrete declarations and
      unelaborated templates use the same sites. Delivered in
      [link-sites.mjs](../../web/mathscript/link-sites.mjs): the parser records
      each proof statement's keyword and each `fun`, `forall` and `exists`
      keyword. The elaborator takes tactic, `calc` step, operator and binder
      sites from there, and template links take the same tactic and `calc` step
      sites. Templates list no expression sites, because some operators, such
      as a face formula's `and`, are never elaborated as terms.
    - [x] An explicit elaboration context passed down, instead of Translator
      fields (`source`, `simpRegistry`, `moduleName`, `onReference`,
      `dimensions`, `rewriteWork`) swapped in and out for templates and freeze
      replays. Delivered in [elaboration.mjs](../../lib/cubical/elaboration.mjs):
      a `SourceUnit` (source, module, rules, inspector sink, freeze policy,
      work counters, names) and an immutable `Scope` (telescope, source names,
      dimensions) are passed down; checker queries take the scope's context,
      dimensions and names explicitly. A template specialization or a freeze
      replay elaborates in a derived unit.
  - (H) `match` elaboration (ergonomics milestone 7) is this layer's first
    large client. It needs:
    - motive abstraction over several scrutinees;
    - generalization of hypotheses that depend on the scrutinee;
    - index generalization for indexed families;
    - companion motives for inductive-inductive types.

    It is therefore a prerequisite of milestone 7's first release.
- [ ] **A6. Diagnostics.** Unfinished `rw`, `simp`, `simpa` and `calc` steps
  print the residual goal (bounded in length), the side that changed and the
  rules that fired. A cycle error names the rules involved. The unresolved-goal
  error already names a blocked premise, an exhausted premise search and
  matches skipped in dependent positions; it does not yet show the goal.
- [x] **A7. HoTT baseline.** Delivered on 2026-09-25: the fixtures and
  `tests/hott-automation.test.mjs`, a
  [HoTT measurement script](../examples/hott-automation/measure.mjs) beside the
  unchanged ergonomics baseline, a canonicity fixture for invariant 10, and the
  conversion audit below. Results are in the
  [implementation checkpoint](../tactical/hott-automation-handoff.md).
  Extend the [measurement script](../examples/proof-ergonomics/measure.mjs)
  with these declarations:
  - `group_laws_prop`, `group_total_laws_path`, `identity_system_retraction`
  - `code_upper`, `upper_transition`
  - `adjoint_triangle`, `cancel_left`, `transport_concat`
  - raw inferred and folded signatures for `right_unit`, `transport_constant`
    and `transport_ap`
  - equivalence construction/transport, `group_hom_ext_at`, `quotient_rec_beta`

  Record tokens, native steps, arena use, public types and assumptions, as the
  current baseline does. Promote the accepted cubical probes to regressions
  now. Keep the two original simplifier probes as expected failures until A1
  and A2 land; the later conversion-rejection probes must remain negative.
  Add the proof-construction review probes, mixed-universe matching, and the
  chained dependency example in E1. Record prelude/specialization costs and
  native query/retry work separately from final checking; compare fresh and
  reused sessions. Preserve the original measurements as historical evidence.

  Promote the [conversion probes](../examples/hott-automation/conversion-laws.cubist)
  to regression tests: each law that holds by conversion stays a checked
  declaration, and each [rejected law](../examples/hott-automation/README.md#rejected-laws)
  becomes an expected failure. The fixture decides the C1/C2 classification
  and detects any change to kernel computation. Then audit the
  library's proofs by induction where the kernel already computes: the
  statements of `path_map_constant` and `path_map_identity` hold by conversion.
  The former `field_sigma_eta` helper has been removed: `field_subtype_ext`
  now builds its pair path directly, relying on judgmental Sigma eta.
  The redundant prime arithmetic wrappers for `sym`,
  `trans`, and `cong` have been removed; their callers use the checked builtins.
  Replace the remaining induction proofs where intended, record each changed
  witness, and recheck its consumers (invariant 9).
  - The audit checked all 27 corpus declarations that use derived path
    induction. `path_map_constant`, `path_map_identity` and
    `field_pair_path_decode` hold by conversion and now use `rfl`, with
    unchanged public types and assumptions; the other 18 equality statements
    need their proofs.
- [ ] **A8. Σ projections with inferred families.** Add projection syntax, for
  example `p.1` and `p.2`, elaborating to the core `First` and `Second` with
  the family read from the checked type of `p`. The library spells projections
  through eight helpers that take the family explicitly, with 1,283 calls
  (`field_snd`, `field_fst`, `sigma_first`, …); each helper converts to the
  corresponding projection. A2's matcher then sees one head per projection.
  Keep the helpers during migration.
- [ ] **A9. Superseded by G0 and ergonomics milestone 5.** G0 removes
  templates. Omitted universe arguments become level arguments, inferred from
  level constraints by milestone 5's argument inference. The inspector still
  shows the inferred levels, and an undetermined level remains an error.

Completion:

- Both rejected probes check with `simp only`.
- Rules stated with `trans`, `sym`, `cong` or `transport` match.
- The existing raw lemmas match through checked folded signatures, across
  cumulative universe specializations.
- The corpus checks with unchanged public types and assumption lists.
- A3's changed witnesses are recorded; dependent consumers and same-strategy
  replay check. No claim of conversion to the old proof is made.
- Simplification outcomes do not depend on machine speed.
- Fuel defaults are set from measurements.
- The conversion fixture's positive laws check by `rfl` and its negative laws
  are rejected. Audit replacements record their changed witnesses.
- Projections convert to the existing helpers.

### B. Goal-derived induction and extensionality

Proposed syntax throughout; the final forms must not conflict with the existing
expression forms such as `induction n as k return C { … }`.

- [ ] **B0. Superseded by H1.** Suspensions, the circle and pushouts become
  declared higher inductive types. Their generated eliminators take
  dependent-path clauses, so point and path computation hold by conversion.
  The archived library's transport-equation eliminators remain evidence for
  why: `suspension_meridian_beta` needed a 31-line cube and
  `suspension_rec_beta` 25 lines. In the rebuild, `code_meridian` holds by
  `rfl` and `code_upper(z)` is a single univalence computation.
- [ ] **B1. Path induction from the goal.** `induction p;` applies to
  `p : a =[A] b` when `b` is a local variable that occurs in neither `A` nor
  `a`. It performs these steps:
  1. compute the transitive dependency closure of `b` and `p`, reverting those
     hypotheses in telescope order through A5;
  2. form the motive
     `fun (y : A) => fun (q : a = y) => forall (reverted…)[y/b, q/p], Goal[y/b, q/p]`;
  3. continue the block with the goal at `a` and `refl(a)`, reintroducing the
     reverted hypotheses under their original names;
  4. emit the builtin `based_induction` construction, whatever definition of
     that name is in scope (A1b), with universes read from the checked types
     (the least level where cumulativity allows several).

  Further forms:
  - If only `a` is a variable, induct on `sym(p)`. Substituting `sym(q)` for
    `p` is sound here because `sym(sym(p))` converts to `p`.
  - `subst p;` is the same transition when the goal only needs `b` replaced.
    It retains the computational behavior of derived `based_induction`.
  - `generalize e as y with q;` first abstracts a non-variable endpoint and
    checks that the abstracted goal is type-correct.

  Each of the following gets its own diagnostic: a loop (both endpoints the same
  variable), an endpoint variable occurring in the other endpoint or the
  carrier, and an interval variable. Provide the propositional computation law
  of `based_induction` at `refl` as a checked lemma. The eliminator does not
  reduce there for neutral motives.
  - Targets: `group_total_laws_path`, `group_total_multiplication_path`,
    `identity_system_retraction`, `decode_encode`. The last should become
    `induction p; rfl;`, since its current base case is `refl(refl(base))`.
- [ ] **B2. Superseded by ergonomics milestone 7.** Goal-derived elimination
  for every declared type is `match`:
  - inferred motives, with explicit `as … return` available;
  - dependent branch goals for sums;
  - index generalization;
  - dependent-path clauses for path constructors.

  It replaces the per-type interfaces planned here for natural numbers, sums,
  pushouts and suspensions.
- [ ] **B3. Type-directed `ext`.** Dispatch on the carrier of an equality goal:
  - dependent functions: the current behavior;
  - Σ and ×: `ext (p : a = a') { … }` proves the first component in the block
    and binds `p`. The remaining goal is
    `PathP(fun (i : Interval) => B(p @ i), b, b')`, or a homogeneous equality
    for ×. The witness is `path i => (p @ i, q @ i)`.
  - universe: asks for `e : Equiv(U, A, B)` and produces `ua(U, A, B, e)`. Here
    `ua` is built from Glue. This case follows D0b's canonical equivalence API;
    its dependencies are reported as usual.
  - equivalences: `ext` on `Equiv` compares the underlying maps through D0b's
    `equiv_eq`.
  - registered structures: `ext_rule Group using lemma;` registers a checked
    lemma from structure data to equality, and `ext` opens its premises. Two
    unrelated maps never qualify.

  Equality of paths remains a nested `path` or an E2 square.
- [ ] **B4. `show` and `suffices`.** `show T;` replaces the goal by a
  convertible type, checked by conversion. `suffices h : T by term;` (or a
  block) proves the goal from `h`, then continues with goal `T`.
  Reconstruction uses only conversion or application.
- [ ] **B5. Superseded by H1 and ergonomics milestone 7.** Generated
  eliminators need no registry, because the kernel signature is the
  description. What remains of B5 is views, which milestone 7 owns: checked
  eliminators used with `match … using`. That includes D3's identity systems,
  quotient-style views and presentations. The truncation and quotient
  registrations are unnecessary, because `Trunc` and `Quotient` are declared
  types with dependent eliminators. The two- and three-class inductions in
  the archived `quotient_operations` become `match` on several values with
  per-argument respect obligations.

Completion:

- The B1 targets shorten without changing public types or assumptions.
- Loops, invalid endpoint variables and dependent hypotheses have focused
  rejection and preservation tests.
- `ext` on Σ produces the single-line witness.

### C. Path algebra and transport

- [ ] **C1. Conversion normalization and equality rules.** Keep two explicit
  kinds of registration/construction. A conversion-normalization entry is
  accepted only when kernel conversion identifies its sides with parameters
  free; it changes syntax without adding a path atom. An equality rule applies
  its supplied checked witness even when the endpoints happen to convert.
  Endpoint convertibility alone never licenses erasing that witness.
  - A witness-preserving optimization may omit a rule application only when
    the witness itself converts to the corresponding reflexivity path.
  - The inspector and frozen output record which kind was selected. Test the
    arbitrary higher-loop `omega` probe and a consumer that depends on it.
  - Candidates, each of which checks by `rfl` in the current kernel
    ([evidence](#what-the-kernel-computes-that-the-library-does-not-use)):
    - `sym(sym(p)) = p`
    - `cong(f, sym(p)) = sym(cong(f, p))`
    - `cong(g, cong(f, p)) = cong(fun x => g(f(x)), p)`
    - `cong(fun x => x, p) = p`
    - `cong(f, refl(x)) = refl(f(x))`
    - `transport(fun a => C(f(a)), x, y, p, v) = transport(C, f(x), f(y), cong(f, p), v)`
    - `transport(fun y => a = y, x, y, p, q) = trans(q, p)`, moved from C2
    - transport in a non-dependent function family `fun t => B(t) -> C(t)`:
      precomposition with the reverse transport, then the forward transport
  - A closed binder subterm in a pattern is compared by conversion.
  - Revalidate conversion entries when their definitions change. Reject an
    entry whose sides do not convert. Do not silently reclassify ordinary
    equality rules based on their endpoints.
- [ ] **C2. Transport rule set.** A named set oriented to move transports
  inward or remove them. State each entry's C1 construction kind explicitly.
  - Members:
    - `transport_refl`, `transport_constant`, `transport_ap`
    - `transport_concat`, `transport_inverse_after`, `transport_after_inverse`
    - transport in Π, Σ and path families where conversion does not suffice,
      for example `transport(fun y => y = a, x, y, p, q) = trans(sym(p), q)`
    - `transport_ua`, from `UnivalenceBeta`
    - the `based_induction` computation law from B1
  - Keep the PathP/transport bridge out of automatic rules in both directions,
    as the ergonomics plan requires.
  - Targets: `code_loop`, `code_upper_inverse`, `code_lower_inverse`. With
    H1's circle, `code_upper` and `code_lower` are already single lemma
    applications.
- [ ] **C3. Path-algebra normalizer.** `path_algebra;` proves `P = Q` for paths
  built from atoms with `refl`, `sym`, `trans` and `cong`.
  - Normalizing a side: flatten composition, remove `refl`, push `sym` and
    `cong` inward, and cancel adjacent inverse pairs whose atoms convert.
  - Success: the two reduced words agree atom by atom. On failure, report both
    normal forms.
  - Proof construction: build each side's normalization path from these
    checked laws or their universe-template forms:
    - `path_associative`, `left_unit`, `right_unit`, `inverse_left`,
      `inverse_right` and `map_concat`;
    - whiskering through A3 lines, and C1 definitional steps;
    - a law for the inverse of a composition, not found by name in the current
      library, to be added.
  - Scope: the free groupoid plus functoriality of `cong`. There is no
    commutation of atoms, no naturality and no Eckmann–Hilton argument. An
    arbitrary loop atom is never identified with `refl` without checked evidence.
  - Targets: `cancel_left`, `append_cancel_inverse`, `append_inverse_cancel`,
    `upper_transition`, and the composition steps of `adjoint_triangle`.
- [ ] **C4. Reflective normalizer for loops at one point.** A variant of C3 for
  loops at a single basepoint, the common case in the fundamental-group files.
  [loop_words](../../archive/first-library/loop_words.cubist) already defines signed
  words, `eval_word` and the cancellation step `word_backtrack_cancels`.
  - Add a tree syntax over atom indices whose evaluation is definitionally the
    quoted path, free reduction to a word, and one checked soundness lemma
    `sound(e) : eval(normalize(e)) = eval(e)`.
  - The tactic quotes both sides, giving convertible atoms the same index, and
    lets the kernel compute both normal forms. When they agree, the certificate
    is `trans(sym(sound(e1)), sound(e2))`.
  - The witness depends on the soundness lemma and the quoted syntax, not on a
    rewrite sequence. Changing the normalizer is a library change, rechecked
    like any other.
  - Paths whose atoms have different endpoints stay with C3.
  - Targets: `integer_loop_successor` in [circle](../../archive/first-library/circle.cubist)
    and the word lemmas in `loop_words`; compare proof size and native steps
    with C3.

Completion:

- The targets shorten and check.
- C4 compares normal forms by kernel computation, and its certificate is one
  application of the soundness lemma.
- `trans(p, q) = trans(q, p)` for arbitrary neutral loops is rejected, with both
  normal forms shown.
- Arbitrary loop atoms and their transport actions are preserved; inverse
  cancellation and transport in constant families use their checked laws.
- The transport set never contains both a rule and its inverse.

### D. Equivalence foundations, h-levels and identity systems

- [ ] **D0a. h-level templates.** Publish universe templates for `IsContr`,
  `IsProp` and `IsSet`, their propositionhood, subtype closure, and closure
  under Π, Σ, products and path types as applicable. Add preservation under
  equivalences and retracts. Existing `U0`/`U1` spellings may be temporary
  migration wrappers. D1 needs only this part of D0.
  - Define the levels once by recursion on `Nat`, with `IsProp` at level zero.
    `IsSet(A)` is then definitionally level one
    ([evidence](#what-the-kernel-computes-that-the-library-does-not-use)), and
    one family of closure lemmas serves every level. `IsProp`, `Proposition`,
    `FieldProp`, `IsSet`, `FieldSet` and `LoopSpaceIsSet` become aliases that
    conversion identifies, rather than names the matcher must register.
    Cubical Agda's `isOfHLevel` uses two base cases to keep `IsContr`
    definitional as well.
  - (H) Milestone 7's automatic clauses consult these definitions. A clause
    for a squash constructor is generated when the target's h-level is proved.
    D0a and D1's first slice therefore precede milestone 7's first release.
- [ ] **D0b. Canonical equivalences.** Make the public equivalence
  representation agree with the native contractible-fiber type:

  ```text
  IsContr(A) = exists center : A, forall x : A, center = x
  Fiber(f, y) = exists x : A, y = f(x)
  Equiv(A, B) = exists f : A -> B, forall y : B, IsContr(Fiber(f, y))
  ```

  These are schematic signatures; explicit universe templates must check all
  carrier and codomain levels. Preserve the native fiber orientation `y = f(x)`.
  This is a deliberate public representation change using existing core syntax.
  - Publish the checked native witness-uniqueness, total-space contraction,
    `idtoequiv`, `ua`, beta, eta and counit constructions from
    [equivalence.mjs](../../lib/cubical/equivalence.mjs) and
    [public-equivalence.mjs](../../lib/cubical/public-equivalence.mjs) as library
    declarations. D3's equivalence instance then uses this same representation.
  - Provide identity, inverse, composition and Π/Σ/product equivalence
    combinators, with checked maps and laws. Keep explicit quasi-inverse data as
    a convenient constructor input; choose fiber centers so extracting the
    inverse of that constructor computes to the supplied inverse map.
  - Migrate the public `IsEquiv`/`Equiv` definitions, `ua` lowering, tuple
    constructors and projections, and `equiv_from_inverse`. Homotopies and
    coherence witnesses may change; identify and recheck their consumers.
    Canonicalizing `Equiv` does not make `idtoequiv(refl)` compute strictly.
  - The existing `Fiber` in [maps](../../archive/first-library/maps.cubist) is
    `exists x : A, f(x) = y`, the opposite orientation, with 83 uses in 19
    files. Choose the surviving name and migrate one orientation, recording
    the changed statements.
  - Publish `is_prop_is_equiv` and `equiv_eq`: equivalences with equal
    underlying maps are equal. `ext` on `Equiv` (B3) and transfer (F2) use
    these rather than the fiber data.
  - Decide how the native constructions built in JavaScript become library
    declarations: a documented builtin, as `ua` already is, or source proofs
    once B1 and E2 exist. Printing their raw terms would repeat the generated
    `comp` text that fills most of
    [equivalence_from_inverse](../../archive/first-library/equivalence_from_inverse.cubist)
    (1,893 lines).
  - Before removing an old representation, record its migration map and
    changed computation/assumption behavior. Proving uniqueness of arbitrary
    public half-adjoint witnesses remains an alternative if the old public
    representation is retained; it is not a prerequisite for the chosen redesign.

- [ ] **D1. h-level solver.** `hlevel;` closes goals of these kinds:
  - `IsContr(T)`, `IsProp(T)`, `IsSet(T)` and the aliases that D0a identifies
    with them by conversion, such as `Proposition`, `FieldProp` and `FieldSet`;
  - `x = y` for `x,y : T` when `IsProp(T)` is proved;
  - `p = q` for `p,q : x = y` when `IsSet(T)` is proved.

  `IsSet(T)` alone never proves equality between arbitrary elements of `T`.
  Contractibility can provide propositionhood, but the solver must construct
  its center and contraction from checked evidence; it does not invent an
  inhabitant. D0a's numeric levels already cover general finite h-levels; the
  solver starts with the three cases that have corpus targets.

  Resolution is directed by the head of the goal and bounded by A4 fuel. It
  tries, in order:
  1. exact local evidence and explicit hints (`hlevel with [setA];`), then
     quantified hints used as checked rules;
  2. registered rules (`hlevel_rule lemma;`) matching the folded type, including
     the implications `IsContr` to `IsProp` to `IsSet`, and `hedberg`, which
     derives `IsSet` from checked decidable equality registered for carriers
     such as `Nat` and `Z`;
  3. unfolding one layer of a definition registered for this purpose, then
     structural rules for Π (via cubical function extensionality), Σ, ×, paths
     in a set, `IsProp`/`IsSet` themselves, `Nat`, `Unit`, `Void` and
     `Truncate` with its currently declared assumptions.

  Define stable priority/identity order for overlapping rules, detect active
  obligation cycles, and count every recursive attempt. A failed rule may try
  the next candidate under the same fuel; the inspector records the chosen
  witnesses. Cache only within the full checked context and rule environment.
  Failure shows the chain to the first undischarged obligation. Also use the
  solver for conditional-rule premises and the target proposition of truncation
  elimination. Use D0a's closure lemmas. Proposed shape for
  `group_laws_prop` (not checked):

  ```text
  def group_laws_prop(A : U0, unit : A, multiply : A -> A -> A,
      p q : GroupLaws(A, unit, multiply)) : p = q {
    have setA = group_set_law(A, unit, multiply, p);
    hlevel with [setA, group_inverse_evidence_prop(A, unit, multiply, p)];
  }
  ```
  - (H) `hlevel;` is also the procedure milestone 7 calls:
    - for automatic clauses, where the target must be a set or a
      proposition;
    - for setness proofs of declared data types, before a squash constructor
      would be added;
    - for deleting reflexive index equations in dependent pattern matching.
- [ ] **D2. Subtype extensionality.** Add a checked lemma: given `B : A -> U`
  whose fibers are propositions and a path `p : a = a'`, any `b : B(a)` and
  `b' : B(a')` are connected by `PathP(fun (i : Interval) => B(p @ i), b, b')`.
  With it, `ext` on a Σ type closes the second component whenever `hlevel`
  proves the fibers are propositions. The standalone lemma can land before B3;
  automatic closure follows B3's basic Σ extensionality. Targets:
  `field_subtype_ext`, `sigma_prop`, and equalities of structure laws.
- [ ] **D3. Identity systems.** [identity_systems](../../archive/first-library/identity_systems.cubist)
  already proves encode/decode round trips from a contraction of
  `IdentityTotal(A, R)` at `U1`.
  - Add the missing eliminator: from the contraction and `d : P(a, r0)`, prove
    `P(b, r)` for every `b` and `r : R(b)`. The proof transports along the
    total-space path and comes with its computation law as a checked lemma.
  - Generalize the development to universe templates. Remove the set-valued
    restriction of `identity_system_equivalence` using the general checked
    inverse constructor from D0b: the existing section/retraction already work
    without that restriction. This bounded foundation work is in scope.
  - `match r using sys` then applies the identity system as a milestone 7
    view, abstracting the goal over `R` in place of the path type. The
    standalone library eliminator need not wait for the language interface.
  - Instances:
    - based paths;
    - group isomorphisms, from `group_isomorphism_total_contractible`;
    - structured sets, from `structure_total_contractible`;
    - equivalences, from the total-space form of univalence. That form is
      checked in `lib/cubical/equivalence.mjs` ([derived univalence milestone](../cubical/experiment.md#derived-univalence-milestone))
      and published at D0b's canonical public representation. Do not assume the
      native contraction already has the old half-adjoint public type.
- [ ] **D4. Total-space contraction combinators.** Identity systems (D3) and
  structure identity (F1) both reduce to showing that a total space is
  contractible. Provide checked combinators for the standard steps:
  - based path spaces are contractible, using the connection `p @ meet(i, j)`;
  - a Σ type with a contractible base and a contractible fiber over its center
    is contractible;
  - reassociation and reordering of Σ components;
  - the singleton given by function extensionality: the maps `g` with
    `forall x, f(x) = g(x)`;
  - the singleton given by univalence: the types `B` with `Equiv(U, A, B)`,
    from D0b;
  - fibers that are propositions, from D0a.
  - Target: `group_isomorphism_total_contractible`, then F1's generated
    contractions.

Completion:

- `PropLevel(1, A)`, or its final name, agrees with `IsSet(A)` by conversion,
  and the closure lemmas check at every level.
- `group_laws_prop` and one equality of structure laws migrate.
- Public `Equiv` and native univalence use the same representation. Mixed-level
  templates, inverse extraction and changed witness consumers check.
- `IsProp` of an arbitrary type is left unsolved.
- `IsSet` is never inferred from a theorem's name.
- `0 = 1` remains unsolved with `IsSet(Nat)` available; equality between two
  parallel Nat paths is solved. Cyclic h-level registrations terminate.
- Truncation elimination into a non-proposition is rejected.
- An identity system without a checked contraction is rejected.
- D4's combinators rebuild `group_isomorphism_total_contractible`.

### E. Dependent rewriting and two-dimensional paths

- [ ] **E0. Dependent path operations.** Library definitions that E1 and E3
  build on:
  - reversal of a PathP over the reversed family, `path i => q @ flip(i)`;
  - dependent congruence, `path i => f(p @ i, q @ i)` for
    `q : PathP(fun (i : Interval) => B(p @ i), u, v)`;
  - composition of PathPs over `trans(p, q)`;
  - `α ◁ q` and `q ▷ β`, which adjust PathP endpoints by paths in the endpoint
    fibers (moved from E2).

  The first two are single lines that already check
  ([evidence](#what-the-kernel-computes-that-the-library-does-not-use)). With
  `◁` and `▷`, `rw` and `simp` can rewrite an endpoint of a PathP goal whose
  family is fixed, then rebuild the original goal by the adjustment.
- [ ] **E1. Rewriting with transport fillers.** This replaces the dependent
  rewriting item of ergonomics milestone 4. For a rule instance `p : t = t'`
  inside a term of fixed type:
  1. select occurrences according to the existing `rw` target/occurrence
     interface, then abstract those positions; if the fixed-codomain context
     checks, the witness is `path i => C[p @ i]`;
  2. otherwise, compute the transitive closure of dependent data in A5's
     telescope. Construct their fillers in dependency order, substituting
     previously constructed lines into each later type. Endpoints at `i = 1`
     become the transported data in the result;
  3. report any remaining failure, such as a dependency under a binder or a
     dimension, with the offending subterm and its type.

  For `v : B(x)` and `w : E(x, v)`, first construct
  `v(i) = fill(fun j => B(p @ j), v, i)`, then
  `w(i) = fill(fun j => E(p @ j, v(j)), w, i)`.
  The family `E(p @ j, v)` is generally ill-typed. Add both the successful
  ordered construction and rejection of the independent-filler attempt as
  regressions. These formulas are schematic; elaboration supplies the types.

  Show selected occurrences and the additional dependent data that must move
  separately in the inspector. If satisfying a dependency would require moving
  another unselected occurrence of `t`, diagnose it instead of silently changing
  the user's selection. A2's memoization must respect that distinction.

  The result contains `transport`, which C2 may simplify; C2 is optional
  cleanup rather than a prerequisite for generating the line. B1's `subst`
  handles endpoint variables through context abstraction, with the same weak
  computation caveat. Otherwise bind a transported hypothesis copy, as
  `simp … at h as h2` already does.
- [ ] **E2. Squares.** Provide a `Square` view of the nested PathP used by the
  naturality example. It names the edges, and the inspector displays edges and
  corners. Start from squares the kernel already provides: for
  `h : forall a, f(a) = g(a)` and `p : x = y`, `path i => h(p @ i)` is the
  naturality square by conversion. Prove the conversion between a square and
  an equation of composites once as a general lemma, and re-derive
  `homotopy_natural` (86 lines of raw `comp`), `map_concat` and
  `transport_concat` (131 lines) through it before any search. Add these
  checked constructions:
  - double composition `p ·· q ·· r` and its filler, with `trans` as the case
    of a constant first edge;
  - horizontal and vertical composition, transposition and reversal, the last
    two being definitional;
  - conversions between a square and an equation of composites, whose round
    trips are not judgmental.

  Write and display cells in the implementation plan's box notation (item 4 of
  its [cubical language changes](proof-ergonomics-implementation-plan.md#cubical-language-changes-worth-prioritizing)).
  The corpus has 248 `face_when(` and 131 `comp(` occurrences, mostly in raw
  terms, and A3 and E2 generate more.

  Expose the kernel's face-restricted conversion as a read-only adapter query.
  It serves boundary display and locating face mismatches, and is an interface
  extension, not a rule. Nested squares consume interval slots (64 in the
  native representation), so measure their use.

  Add a bounded boundary-filling prototype in two stages:
  - search interval reparametrizations of supplied cells using De Morgan
    expressions, starting with squares whose edges come from one path;
  - then search a bounded number of compositions of named cells/fillers.

  Reparametrization search produces larger De Morgan formulas. It depends on
  the interval-certificate plan in the ergonomics roadmap's
  [architecture section](proof-ergonomics-roadmap.md#architecture-and-invariants),
  not on raised lattice limits.

  Every candidate is checked at all required faces and overlaps. Record the
  selected construction and deterministic fuel; failure reports an unsolved
  boundary, not a claim that no filler exists. This is separate from C3's free
  groupoid normalizer. The algorithms in
  [Automating Boundary Filling in Cubical Type Theories](https://lmcs.episciences.org/18519)
  are a research precedent, not an implementation already present here.
  Targets: `homotopy_natural`, `transport_concat`, `map_concat`.
  - (H) The same square view is the language's `cell` syntax for
    two-dimensional constructors and their clauses: the torus surface, and
    squash clauses that are not generated. Its boundary display is the one the
    inspector uses for declarations.
- [ ] **E3. Dependent `calc`.** `calc over C { u =[p] v by α; _ =[q] w by β; }`
  composes PathPs over `trans(p, q)`. Steps over a constant base use E0's `◁`
  and `▷`. Changing to a different but equal base path needs an explicit checked
  square. Targets: suspension and pushout bridge branches, `decoder_meridians`.
- [ ] **E4. Paths as named results.** `normalize [rules] (e)` is a term: the
  checked simplification path from `e` to its simplified form, usable wherever
  a path is data, for example as a transport argument. A lint flags `simp`
  without `only` when its path later reaches a transport, `along`, `over` or a
  PathP family, since a change to the rule set would change that path.
  `only` fixes rule selection, not future elaboration strategies. Persistent
  freezing follows invariant 7 and retains the checked construction or its
  strategy/version. E4 can land with A5's witness interface before all of E.

Completion:

- E0's reversal and congruence check for PathPs, and the builtin `sym` no longer
  fails with an internal error.
- The filler probe is reproduced by `rw`.
- Chained dependencies are filled in order; occurrence selection is preserved
  or rejected with an explanation of the dependency conflict.
- Binder and dimension positions are rejected with the offending subterm.
- Wrong square edges and corner mismatches are rejected.
- `homotopy_natural` shortens with its path construction recorded. If it changes,
  dependent consumers are migrated with the needed checked comparison paths.

### F. Reusable structures, transfer and selected HIT declarations

F1 starts after D0's foundations, D4, B3 and D1/D2; registration of its
identity systems additionally uses D3 and milestone 7's views. F2 uses D0b's canonical `Equiv` API,
including `equiv_eq`, and C2's transport laws. F4 uses D0a's h-level
definitions. Theories
(ergonomics milestone 6) are the record syntax. Kernel extensions are
separate work.

- [ ] **F1. Compositional structure descriptions and SIP.** Implement checked
  descriptions for carrier data, constants, products, function operations and
  proposition-valued extensions. Start with existing Σ encodings; later record
  syntax elaborates through the same descriptions.
  - Distinguish equality of records over a fixed carrier from the structure
    identity principle (SIP), which relates carrier equivalences preserving
    structure to equality of whole structures.
  - Generate preservation predicates and prove the obligations represented by
    `RelationProp`, `RelationIdentity` and `RelationReflects` in
    [structured_sets](../../archive/first-library/structured_sets.cubist). Compose their
    checked proofs to obtain extensionality and, with D4's combinators, the
    total-space contraction. Register the resulting `ext_rule`, h-level rules
    and identity system.
  - Property fields require checked proposition evidence. Unsupported dependent
    fields require an explicit preservation relation and proof; naming a field
    a law does not erase its data. Preserve selected operation maps visibly.
  - Targets: `FieldOps`, `group_hom_ext_at`, `EmbeddingsOver`, and one complete
    group or field structure identity. Measure projection and preservation
    boilerplate as well as proof size and native checking cost.
  - Acceptance: generated obligations and dependencies are inspectable;
    incorrect operation preservation is rejected; a proof-relevant field cannot
    be discarded. A nonidentity carrier equivalence exercises the full SIP.
  - [Cubical Agda's structure descriptions](https://agda.github.io/cubical/Cubical.Structures.Auto.html)
    are a precedent for a supported grammar, not a specification to copy.
  - (H) F1 is the engine behind each theory's generated
    `T.equality : (M = N) ≃ T.Iso(M, N)`
    ([theories](inductive-language-features.md#1-theories-one-declaration-for-structures-initial-models-and-universal-properties)).
    Its descriptions are generated from theory declarations rather than
    written separately.
- [ ] **F2. Maps and equivalences for transfer.** Build a checked library API
  before adding `transfer e;`, reusing D0b's identity, inverse, composition,
  product and Π/Σ combinators and h-level preservation lemmas. Add sums and
  domain-specific maps with their computation and preservation laws.
  - For goal rewriting, construct a checked map `G' -> G`: ordinary function
    domains are contravariant and codomains covariant. Dependent Π/Σ positions
    additionally require a checked map between the corresponding fibers;
    polarity alone does not supply one. Report the missing map as an obligation.
  - Offer direct transfer through these maps and transfer along `ua(e)` with
    C2 cleanup. Document which construction is selected, and prove comparison
    laws where both APIs expose the same operation. Computational data should
    use the supplied maps where possible.
  - Targets: natural/binary equivalences, product swaps, and transport of one
    algebraic operation with its laws. Acceptance includes reduction of closed
    transferred data and rejection of a wrong map or missing preservation law.
    Do not promise judgmental `idtoequiv(refl)` from the representation change.
  - (H) Presentations (milestone 7), which match on one type with an
    equivalent type's constructors, reuse these maps.
- [ ] **F3. Superseded by H1 and ergonomics milestone 7.** Higher inductive
  declarations are native kernel signatures rather than elaborations into
  pushouts. They have generated constructors, eliminators with
  dependent-path clauses, and judgmental computation on points and paths.
  Boundary diagrams display through E2's square view.
- [ ] **F4. Pointed types and loop spaces.** A library API for pointed types,
  pointed maps, loop spaces, the action of pointed maps on loops, and rebasing
  along a path (`rebase_loop` in [homotopy_paths](../../archive/first-library/homotopy_paths.cubist)
  is a start). [fundamental_groups](../../archive/first-library/fundamental_groups.cubist)
  proves the group laws of loops generically, but only at `U1` (G0 makes
  them universe-generic), so
  [circle](../../archive/first-library/circle.cubist) re-proves them at `U0` as
  `loop_group`. The loop files also repeat
  `concatenate(U1, S1, base, base, base, …)` and `append_path(…)`.
  - Targets: `loop_group` through the generic laws, then the bouquet and
    puncture developments.

### G. Kernel extensions (moved)

Kernel work lives in the [kernel roadmap](cubical-kernel-roadmap.md):
- G0, universe-generic checking;
- H1–H4, inductive signatures, which supersede G1 and G3;
- G2's resizing policy;
- G4, optional transport regularity;
- G5, certified interval normalization.

The kernel roadmap ranks them by invariant 10. Items A–F do not wait for
them, except where marked (H).

## Changes to the ergonomics plan

| Ergonomics item | This roadmap |
| --- | --- |
| Milestone 1: goal/reconstruction representation | A5 typed plans and dependency telescopes, before further tactics |
| Milestone 2: resource bounds | A4 frontend and hard native fuel, with limits set from A7 |
| Milestone 2: residual-goal and cycle diagnostics | A6 |
| Milestone 3: general proposition premises | Deferred; h-level premises through D1 |
| Milestone 4: path, transport and structure simp sets | A1 first, then C1–C2, classified by A7's conversion fixture |
| Milestone 4: dependent applications, pairs and hypotheses | A2, E1 and B1's `subst` |
| Milestone 4: cubical constructors | E2 squares and bounded boundary-filling experiments |
| Milestone 5: goal-derived induction | Ergonomics milestone 7 (`match`); B1 remains for `Path` induction |
| Milestone 5: named and implicit arguments, `apply`, `refine` | Retain scoped-metavariable prerequisites; do not wait for all D–F |
| Milestone 5: universe specialization inference | Level-argument inference after G0; A9 superseded |
| Milestone 6: `ext` with selected lemmas | B3 and D2 |
| Milestone 6: records, notation, sections, algebra normalization | Ergonomics milestone 6 (theories) supplies records, notation and sections; A8 projections and F1 identity serve it |
| Implementation plan: box notation (cubical language change 4) | Retained; E2 writes and displays cells with it |
| Library foundations supporting tactics | D0a h-level definitions, D0b canonical equivalences, D3 general identity systems and D4 contraction combinators; B0's eliminators come from H1 |
| Existing-kernel scope | A–F retain it except where marked (H); the [kernel roadmap](cubical-kernel-roadmap.md) owns G0, H1–H4, G2, G4 and G5 |
| Architecture: large interval expressions | [G5](cubical-kernel-roadmap.md#items), certified interval normalization |

Do not broaden generic premise search before A1/A4/A5 and the first D1 slice.
The matcher, resource limits and witness reconstruction must support it first.

## Integration map

| Existing location | Planned work |
| --- | --- |
| [translator](../../lib/cubical/translate.mjs) | Builtin lowering (A1), goal/scope plans (A5), projections (A8), canonical `ua` input (D0b), new statements; `match` and views are ergonomics milestone 7 |
| [proof-rewrite.mjs](../../lib/cubical/proof-rewrite.mjs) | Traversal (A2), congruence lines (A3), alias and view matching (A1), fillers (E1) |
| [path-algebra.mjs](../../lib/cubical/path-algebra.mjs), [paths](../../archive/first-library/paths.cubist), [path_actions](../../archive/first-library/path_actions.cubist) | Prelude bodies, C3 laws, dependent path operations (E0), double composition and squares (E2), missing lemmas |
| [suspension_types](../../archive/first-library/suspension_types.cubist), [suspension](../../archive/first-library/suspension.cubist), [circle](../../archive/first-library/circle.cubist) | Evidence only (archived): replaced by H1 declarations in the rebuild |
| [homotopy_paths](../../archive/first-library/homotopy_paths.cubist), [field_extensionality](../../archive/first-library/field_extensionality.cubist), [primes](../../archive/first-library/primes.cubist) | Conversion audit of proofs by induction (A7) |
| [loop_words](../../archive/first-library/loop_words.cubist) | Reflective loop normalizer (C4) |
| [simp-registry.mjs](../../lib/cubical/simp-registry.mjs) | Aliases, distinct conversion/equality entries, bounded `hlevel_rule` and `ext_rule` registries |
| [sets](../../archive/first-library/sets.cubist), [truncation](../../archive/first-library/truncation.cubist), [bijection_equality](../../archive/first-library/bijection_equality.cubist) | Numeric h-level templates and their aliases (D0a) |
| [equivalence.mjs](../../lib/cubical/equivalence.mjs), [public-equivalence.mjs](../../lib/cubical/public-equivalence.mjs), [paths](../../archive/first-library/paths.cubist), [maps](../../archive/first-library/maps.cubist) | Canonical public equivalences, `Fiber` orientation and checked univalence API (D0b) |
| [identity_systems](../../archive/first-library/identity_systems.cubist) | Eliminator, computation law and universe templates (D3); contraction combinators (D4) |
| [fundamental_groups](../../archive/first-library/fundamental_groups.cubist) | Pointed types and loop spaces (F4) |
| [structured_sets](../../archive/first-library/structured_sets.cubist), [algebraic_fields](../../archive/first-library/algebraic_fields.cubist), [field_embedding_spaces](../../archive/first-library/field_embedding_spaces.cubist) | Compositional descriptions, property fields and derived identity (F1) |
| [quotient_descent](../../archive/first-library/quotient_descent.cubist), [quotient_operations](../../archive/first-library/quotient_operations.cubist) | Evidence only (archived): replaced by the `Quotient` declaration and milestone 7's multi-argument `match` |
| [native elaborator](../../web/cubical-elaborator.mjs), [kernel adapter](../../web/cubical-kernel.mjs) | Fuel accounting (A4), prelude definitions (A1), face-restricted query (E2) |
| [assumption schemas](../../web/cubical-assumptions.mjs), [field_logic](../../archive/first-library/field_logic.cubist), [kernel](../../kernel/README.md) | Replaced by H1's `Trunc` and `Quotient` and G2's resizing policy ([kernel roadmap](cubical-kernel-roadmap.md)) |
| [parser](../../web/mathscript/parser.mjs), [formatter](../../web/mathscript/formatter.mjs) | New statement syntax, projection syntax (A8), spans and roundtrips |
| [measurement script](../examples/proof-ergonomics/measure.mjs) | HoTT baseline (A7) |
| [conversion probes](../examples/hott-automation/conversion-laws.cubist), [rejected laws](../examples/hott-automation/README.md#rejected-laws) | Conversion fixture and expected failures (A7) |
| [runtime build](../../tools/build-cubical-runtime.mjs) | List every new shared module |
| [language reference](../../web/language.html) | Document delivered syntax only |

A–F require no new C kernel rule. The face-restricted query exposes a judgement
the kernel already makes internally when checking composition overlaps; it
needs review as an interface change. G has its own rule specification, native
and reference implementations, universe audit and migration gates.

## Validation

Each milestone includes parser and formatter tests, native acceptance and
rejection tests, and inspector coverage, as in the ergonomics roadmap.
Mandatory cases:

| Feature | Must be rejected or preserved |
| --- | --- |
| A1 folded heads | Public types equal by conversion and identical assumptions for this refactor; `sym(sym(p))` still converts to `p`; no match through `opaque def`; U1 rules match U0 carriers; raw inferred lemma signatures migrated; failed-first-use rollback recovers; carrier/endpoint arguments of folded heads are never rewritten; one `based_induction` identity remains |
| A2, A3 | `succ(n + 0) = succ(n)` accepted; dependent positions identified; newly introduced redexes resimplified; A3 path changes recorded and consumers rechecked; same-strategy freeze/replay yields convertible proofs |
| A4 fuel | CLI/browser and fresh/reused sessions agree on logical fuel outcome; hard native exhaustion is tested independently of frontend exhaustion and wall-clock timeout |
| A5 plans | Context, face and universe data preserved; occurrence selection survives DAG sharing; generated witnesses checked independently |
| A7 conversion fixture | Positive laws check by `rfl` and negative laws stay rejected; audit replacements record changed witnesses; a construction whose statement `rfl` also proves, such as `close_path`, keeps its witness |
| A8 | Projections convert to the existing helpers |
| B1 induction | A loop `p : x = x` rejected; an endpoint occurring in the other endpoint rejected; dependent hypotheses reverted and restored; no computation at `refl` assumed |
| B3 `ext` | Σ second component typed over `p`; the universe case requires an equivalence, not two maps |
| C1 | Invalid conversion entry rejected; an arbitrary `omega : p = p` is retained when applying its equality rule even if endpoints convert; reclassified transport entries hold by conversion |
| C2 | Nontrivial transport action in the circle code family preserved; constant-family cleanup requires its checked law |
| C3 | `trans(p, q) = trans(q, p)` for arbitrary neutral loops rejected with normal forms; an arbitrary loop atom is not erased; inverse cancellation uses checked laws |
| C4 | Normal forms compared by kernel computation; convertible atoms share an index; atoms with other endpoints are left to C3; `trans(p, q) = trans(q, p)` for distinct loop atoms rejected |
| D0a | Numeric levels agree with `IsProp`/`IsSet` by conversion; closure lemmas check at every level; aliases need no matcher registration |
| D0b | Public/native equivalence representations agree; supplied inverse extraction computes; mixed-universe templates check; intentional public type and witness changes audited; `Fiber` orientation migrated with changed statements recorded; `equiv_eq` checked |
| D1 | `IsProp(A)` for arbitrary `A` unsolved; `IsSet(Nat)` cannot close `0 = 1` but closes equality of parallel paths; recursive rule cycles terminate |
| D3 | General identity-system equivalence needs no set-valued restriction; missing contraction rejected; computation law and canonical equivalence instance checked |
| D4 | Each combinator checked independently; `group_isomorphism_total_contractible` rebuilt; a noncontractible base or fiber rejected |
| E0 | PathP reversal and congruence check over varying families; the builtin `sym` gives a normal diagnostic or folds E0's reversal |
| E1 | Ordered fillers handle `v : B(x), w : E(x,v)`; independent ill-typed filler rejected; occurrence conflicts and unsupported binder/dimension positions diagnosed |
| E2–E4 | Wrong edges/corners rejected; square/equation conversions checked; bounded boundary search preserves faces and records witnesses; persistent freeze pins construction/strategy |
| F1 | Incorrect operation preservation rejected; property fields require proposition evidence; nonidentity carrier equivalence exercises derived SIP |
| F2 | Transferred closed data computes; dependent fibers require maps |
| F4 | Generic loop-group laws specialize at `U0` and `U1`; `loop_group` migrates without a local copy |
| Invariant 10 | Closed assumption-free results in [canonicity.cubist](../examples/hott-automation/canonicity.cubist) still reduce to their stated canonical values after each migration; no tactic or convenience introduces an assumption |

Future gates, not claimed results:

```sh
node tools/build-cubical-runtime.mjs
npm test -- tests/proof-ergonomics.test.mjs tests/cubical-program.test.mjs
npm test -- paths circle group_identity group_total_identity identity_systems equivalence_from_inverse
npm test -- suspension_types suspension homotopy_paths loop_words fundamental_groups
npm test -- docs/examples/hott-automation/conversion-laws.cubist
npm test -- structured_sets group_hom_universes field_embedding_spaces quotient_descent quotient_operations
node docs/examples/proof-ergonomics/measure.mjs
npm run test:browser
make lint
npm test
```

The [kernel roadmap](cubical-kernel-roadmap.md#validation) lists the additional
gates for kernel changes. A documentation update alone does not run these
future implementation gates.

For each migration, compare against A7: source tokens, native steps, arena use
and elapsed time. A1 and other definitional refactors compare public statements
by conversion and require identical assumptions. A3 and the A7 audit record
changed witnesses; D0/F/G may change representations or universes
intentionally. For those changes, list old/new public types, migration maps or
comparison paths, actual computation behavior, and removed/retained/new
assumptions. A proved equivalence is not reported as conversion. Recheck
dependent consumers and persistent replay.
When implementation starts, add a tactical handoff recording the supported
fragment, assumptions, commands run and next unfinished item.

## Evidence

### Where the library's proof text goes

Approximate occurrence counts over `archive/first-library/*.cubist`, comments included
(commands in the [measurement record](#measurement-record)):

| Construct | Occurrences |
| --- | --- |
| `trans(`, `cong(`, `sym(` | 1,674; 1,393; 782 |
| `transport(` | 429 |
| Explicit motives: `induction … as … return`, `match … return` | 308; 250 |
| `path_induction(`, `based_induction(` | 23; 9 |
| `FunExt(` | 112 |
| Declarations named `*_prop`, `*_set`, `*_is_set`, `*_are_set` and similar | 136 |
| Uses of generic closure lemmas (`product_prop`, `forall_prop`, `sigma_prop`, their `field_*` copies, `is_set_prop`, `is_prop_prop`) | 175 |
| Library path wrappers `concatenate(`, `inverse(U`, `append_path(`, `ap(U` | 61; 57; 48; 36 |
| Calls of the eight projection helpers that take the Σ family explicitly (`field_snd`, `field_fst`, `sigma_first`, …) | 1,283 |
| Raw cubical syntax `face_when(`, `comp(` | 248; 131 |
| `transport_constant(` corrections | 23 |

Representative proofs:

- `group_laws_prop` ([group_identity](../../archive/first-library/group_identity.cubist)):
  about 60 lines of nested `product_prop` and `forall_prop`.
- `group_total_laws_path` ([group_total_identity](../../archive/first-library/group_total_identity.cubist))
  and `identity_system_retraction` ([identity_systems](../../archive/first-library/identity_systems.cubist)):
  each `path_induction`/`based_induction` motive restates the whole goal.
- `code_upper` and `upper_transition` ([circle](../../archive/first-library/circle.cubist)):
  transport, univalence computation and path re-bracketing written by hand.
- `adjoint_triangle` and `homotopy_natural` ([equivalence_from_inverse](../../archive/first-library/equivalence_from_inverse.cubist)):
  whiskering and naturality; the latter is a large raw `comp` term.
- `cancel_left` and `transport_concat` ([paths](../../archive/first-library/paths.cubist)).
- `suspension_rec_beta` ([suspension](../../archive/first-library/suspension.cubist)) and
  `transport_path_roundtrip` ([suspension_types](../../archive/first-library/suspension_types.cubist)):
  25 and 31 lines proving path computation laws, because the eliminators take
  transport equations rather than PathPs.

### What the current simplifier cannot reach

Both probes are rejected with "simp only left an unresolved equality goal; add
a following proof statement":

```text
import primes;

def under_succ(n : Nat) : succ(n + 0) = succ(n) {
  simp only [nat_add_zero];
}
```

```text
import paths;

def ru(A : U1, x y : A, p : x = y) : trans(p, refl(y)) = p {
  exact right_unit(A, x, y, p);
}

def use_ru(A : U1, x y z : A, p : x = y, q : y = z) :
  trans(trans(p, refl(y)), q) = trans(p, q) {
  simp only [ru];
}
```

Causes, in the current source:

1. `refl`, `sym`, `trans`, `cong`, `transport`, `path_induction` and
   `based_induction` lower directly to `PLam`, `PApp` and `Comp` syntax in
   `Translator.termBody` ([translator](../../lib/cubical/translate.mjs)). The
   quantified-rule matcher, `simplificationRule` in
   [proof-rewrite.mjs](../../lib/cubical/proof-rewrite.mjs), understands only
   variables, definition references, applications, `Succ` and a few constants.
   A rule stated with `trans` therefore never matches, and `rw` cannot reach the
   path argument of any `transport`.
2. `rewriteFirst` descends only through `App` nodes. `Succ`, pairs, injections
   and type formers are opaque to it.
3. Neither error shows the residual goal.

### What cubical type theory provides directly

These three declarations check in the native kernel:

```text
import primes;

// Sigma extensionality: the second component is a PathP over the first.
def sigma_line(A : U0, B : A -> U0, a a2 : A, b : B(a), b2 : B(a2), p : a = a2,
  q : PathP(fun (i : Interval) => B(p @ i), b, b2)) :
  typed(exists x : A, B(x), (a, b)) = typed(exists x : A, B(x), (a2, b2)) {
  exact path i => typed(exists x : A, B(x), (p @ i, q @ i));
}

// Rewriting in a dependent position: the dependent argument follows its
// transport filler. One line, no composition.
def filler_rewrite(B : Nat -> U0, R : U0, f : (forall a : Nat, B(a) -> R), n : Nat,
  v : B(n + 0)) :
  f(n + 0, v) = f(n, transport(B, n + 0, n, nat_add_zero(n), v)) {
  exact path i => f(nat_add_zero(n) @ i,
    fill(fun (j : Interval) => B(nat_add_zero(n) @ j), v, i));
}

// Several positions rewritten at once.
def multi_hole(g : Nat -> Nat -> Nat, n m : Nat) : g(n + 0, m + 0) = g(n, m) {
  exact path i => g(nat_add_zero(n) @ i, nat_add_zero(m) @ i);
}
```

A second file checks three further constructions:

- `l = r` rebuilt from `pl : l = l2`, `pr : r = r2` and `s : l2 = r2` using a
  single `comp` with walls `at(pl, flip(j))` at `i = 0` and `at(pr, flip(j))`
  at `i = 1` over the base `at(s, i)`;
- `trans(p, q)` equal by `refl` to that composition with the constant first
  edge `refl(x)`;
- `sym(sym(p)) = p` proved by `refl(p)`.

The library also proves some path laws by `refl`: `map_inverse` and
`inverse_twice` in [path_actions](../../archive/first-library/path_actions.cubist), and
`transport_ap` in [paths](../../archive/first-library/paths.cubist).

### What the kernel computes that the library does not use

These probes, from the second review, check in the native kernel. The checked
file [conversion-laws.cubist](../examples/hott-automation/conversion-laws.cubist)
collects them, and its [README](../examples/hott-automation/README.md) maps each
declaration to a milestone and gives the rejected laws as a checkable source
block.

**Path constructors compute through PathP bridges.** With the bridge supplied
directly, suspension recursion computes on meridians by conversion:

```text
import suspension;

def bridge_rec(A : U0, B : U1, n : B, s : B, h : A -> (n = s), x : Suspension(A)) =
  pushout_induction(
    fun (p : Suspension(A)) => B, fun (u : Unit) => n, fun (u : Unit) => s,
    fun (a : A) => h(a), x
  );

def bridge_rec_beta(A : U0, B : U1, n : B, s : B, h : A -> (n = s), a : A) :
  cong(fun (x : Suspension(A)) => bridge_rec(A, B, n, s, h, x), meridian(A, a)) = h(a) {
  rfl;
}
```

The dependent eliminator `bridge_ind`, with bridges
`m(a) : PathP(fun (i : Interval) => C(meridian(A, a) @ i), n, s)`, likewise
proves `apd_path(bridge_ind(…), meridian(A, a)) = m(a)` by `rfl`. The library's
eliminators take transport equations instead, so their path computation laws
need `transport_path_roundtrip` and `suspension_rec_beta`. With the circle's
`code` defined through `bridge_rec` as `bridge_code`, `code_meridian` holds by
`rfl`, `code_upper(z)` is `UnivalenceBeta(U0, Z, Z, successor_equivalence, z)`
and `code_lower(z)` is `transport_constant(U0, Z, Z, Z, refl(Z), z)`.

**Several path and transport laws hold by conversion.** Each law in the first
column checks by `rfl` with its parameters free; each law in the second is
rejected:

| Holds by conversion | Rejected by `rfl` |
| --- | --- |
| `cong(fun v => point, p) = refl(point)`; `cong(fun v => v, p) = p` | `trans(p, refl(y)) = p` |
| `cong(g, cong(f, p)) = cong(fun v => g(f(v)), p)`; `cong(f, refl(x)) = refl(f(x))` | `cong(f, trans(p, q)) = trans(cong(f, p), cong(f, q))` |
| `cong(f, sym(p)) = sym(cong(f, p))`; `sym(sym(p)) = p` | |
| `transport(fun t => a = t, x, y, p, q) = trans(q, p)` | `transport(fun t => t = a, x, y, p, q) = trans(sym(p), q)` |
| `transport(fun t => B(t) -> C(t), x, y, p, f)` equals `fun v => transport(C, x, y, p, f(transport(B, y, x, sym(p), v)))` | `transport(fun t => B, x, x, refl(x), v) = v` for a neutral type `B` |
| `cong(fun k => k(a), FunExt(U0, A, P, f, g, h)) = h(a)`; Σ-η for `field_first` and `field_second` | |
| `path i => h(p @ i)` has type `PathP(fun (i : Interval) => f(p @ i) = g(p @ i), h(x), h(y))` | |

Transport along a constant family still computes on closed values:
`transport(fun t => Nat, x, x, refl(x), 3) = 3` checks by `rfl`.

The library proved several of these laws by induction. Since A7,
`path_map_constant` and `path_map_identity` in
[homotopy_paths](../../archive/first-library/homotopy_paths.cubist), and
`field_pair_path_decode` in [field_products](../../archive/first-library/field_products.cubist),
use conversion instead. The former `field_sigma_eta` pair-induction helper in
[field_extensionality](../../archive/first-library/field_extensionality.cubist) has been
removed; `field_subtype_ext` now uses judgmental Sigma eta directly.
[primes](../../archive/first-library/primes.cubist) used to define `nat_eq_sym`,
`nat_eq_trans` and `nat_congruence` by path induction; the historical arithmetic
measurements in this document include them. The current corpus uses `sym`,
`trans`, and `cong` directly. A statement that `rfl`
also proves does not identify witnesses: `close_path` in
[path_actions](../../archive/first-library/path_actions.cubist) has type
`origin = origin`, which `rfl` inhabits, but its witness is a nontrivial loop.

**Numeric h-levels can agree with the existing definitions by conversion.**
With this definition, `PropLevel(0, A) =[U0] IsProp(A)` and
`PropLevel(1, A) =[U0] IsSet(A)` both check by `rfl`:

```text
import sets;
import truncation;

def PropLevel(n : Nat) = induction n as k return (U0 -> U0) {
    zero => fun (A : U0) => IsProp(A);
    succ previous => fun (A : U0) => forall x : A, forall y : A, previous(x = y);
  };
```

**Dependent path operations are single lines.** For
`q : PathP(fun (i : Interval) => B(p @ i), u, v)`, `path i => q @ flip(i)`
checks against `PathP(fun (i : Interval) => B(p @ flip(i)), v, u)`, and
`path i => f(p @ i, q @ i)` against `f(x, u) = f(y, v)`. The builtin `sym(q)`
fails with "Unbound cubical dimension: d0".

**Two planned transport rules cannot be registered.**
`simp only [transport_constant]` and `simp only [transport_ap]` are rejected
with "A simplification rule parameter is not determined by the matched side":
their inferred left sides are raw `comp` terms that omit `A`, `x` and `y`.

### Cost of the current proof shape

`simplifyEqualityGoal` restarts traversal at the root after every rewrite. It
wraps the whole endpoint in a one-hole context and composes each step with
`trans`, which is a `Comp`. When the residual goal holds by conversion, it also
composes a closing `refl`. The following table is for
`g((n + 0) + 0, (m + 0) + 0) = g(n, m)`, with `g : Nat -> Nat -> Nat`. Each
count is CLI kernel steps minus those of a file containing one trivial
declaration (14,115 steps, mostly from `import primes`).

| Proof | Kernel steps |
| --- | --- |
| `simp only [nat_add_zero]` | 824 |
| `trans` of two `cong` contexts, each around a `trans` chain | 527 |
| One line, with a `trans` chain at each position | 302 |

Kernel steps are deterministic; a second run reproduced every count. This is
one small example, not a general ratio. The
[rewrite-work snapshot](../examples/proof-ergonomics/rewrite-work.json) points
the same way. There, the ergonomic forms of its arithmetic examples use 1.7 to
5.4 times the native checking steps of their explicit counterparts.

### Other findings

- Budgets depend on elapsed time. The frontend polls `performance.now()`
  deadlines, and the kernel deadline in [deadline.c](../../kernel/src/deadline.c)
  reads `CLOCK_MONOTONIC`. Near a budget, the same source can therefore check
  in Node and fail in the browser's WebAssembly build. The numeric limits (64
  rewrites, 512 traversal visits, 8,192 candidates, premise depth two, 64
  premise attempts) were fixed before the measurements that the ergonomics
  plan requires first.
- The ergonomics roadmap's goal/transition layer was not extracted.
  Reconstruction lives in closures inside `Translator.blockBody`.
- The `cases` statement uses a constant motive. Its branch goals do not replace
  the scrutinee by `left(x)` or `right(y)`.
- The kernel has no regularity. Transport along a constant family need not
  compute for a neutral type ([path-algebra.mjs](../../lib/cubical/path-algebra.mjs),
  [kernel overview](../../kernel/README.md)). Consequently, `based_induction`
  at `refl` need not reduce to its base case.
- The kernel adapter's [withGrowingBudget](../../web/cubical-kernel.mjs)
  doubles an exhausted native step budget up to the unsigned 64-bit maximum.
  Frontend fuel alone therefore does not bound native work.
- Public [Equiv](../../archive/first-library/paths.cubist) uses half-adjoint data;
  [native equivalences](../../lib/cubical/equivalence.mjs) use contractible
  fibers. The native total-space univalence theorem cannot simply be published
  at the existing public type: the reverse public roundtrip remains an
  [open obligation](../cubical/public-equivalence.md#validation-and-remaining-obligations).
- [Truncate](../../web/cubical-assumptions.mjs) currently maps every `U_l` to
  `U0`. This includes resizing, used explicitly by
  [small_mere_eliminate](../../archive/first-library/field_logic.cubist). Standard
  computational truncation preserves the input universe; replacing these
  assumptions requires a separate resizing decision in G.
- `paths.based_induction` shadows the builtin of the same name wherever
  `paths` is imported, and the bodies differ: the library applies
  `path_induction` to a Π-motive, while the builtin is a direct connection
  `comp`.
- `opaque def` is accepted syntax with the same checking and unfolding as
  `def` ([language reference](../../web/language.html)).
- The public `Fiber` in [maps](../../archive/first-library/maps.cubist) is
  `exists x : A, f(x) = y`; the native fiber is `y = f(x)`.
- `fundamental_group_laws` in [fundamental_groups](../../archive/first-library/fundamental_groups.cubist)
  is generic but fixed at `U1`; [circle](../../archive/first-library/circle.cubist)
  re-proves the same laws at `U0` as `loop_group`.

### Proof-construction review probes

Native review probes reject `rfl` for `trans(p, refl(y)) = p` at a neutral
carrier, and for a sequential composition of two congruences equated to the
simultaneous line `path i => g(p @ i, q @ i)`. These are candidates for checked
higher paths, not conversion-preserving optimizations.

Convertible endpoints also do not determine a rule's witness. For arbitrary
`omega : p = p`, this declaration checks:

```text
def convertible_rule(A : U0, x y : A, p : x = y, omega : p = p) :
  sym(sym(p)) = p { exact omega; }
```

Its result does not in general convert to `refl(p)`. A7 retains these
distinctions as regressions in
[rejected-probes.cubist.rejected](../examples/hott-automation/rejected-probes.cubist.rejected),
before A3 or C1 changes proof construction.

## Measurement record

The original probes and counts were run on 2026-09-24:

- revision `ff9fc02`, with 21 modified working-tree files not yet committed;
- Node v24.13.0 on an Apple M3 Pro;
- `node cli/repl.mjs check FILE` with default options.

The source excerpts and probe descriptions above record the original evidence;
A7 must preserve complete reproducible fixtures before implementation. The
first design review ran the 43 focused proof-ergonomics tests successfully and
checked native probes for changed path witnesses and ordered dependent fillers.
Those checks validate the starting point, not completion of any milestone.

The second design review, on the same day, reran the original corpus counts,
both simplifier probes and the three declarations under
[What cubical type theory provides directly](#what-cubical-type-theory-provides-directly),
with identical results. It added the probes under
[What the kernel computes that the library does not use](#what-the-kernel-computes-that-the-library-does-not-use)
and the last four rows of the occurrence table. It used the same revision and
command with a larger uncommitted working tree, including kernel changes, and
checked each rejected law in a separate file. The collected
[conversion-laws.cubist](../examples/hott-automation/conversion-laws.cubist)
then checked 25 declarations in 89,080 native checking steps, with no axioms,
through `npm test -- docs/examples/hott-automation/conversion-laws.cubist`. The
[rejected-law block](../examples/hott-automation/README.md#rejected-laws),
checked as one file, rejected all seven declarations with the listed reasons.

The A7 baseline, on 2026-09-25, used revision `7d9893b` with the A7 changes
uncommitted, on Node v22.22.0 and the same Apple M3 Pro. Its measurement
script and
[baseline.json](../examples/hott-automation/baseline.json) record 15
declarations in fresh and reused sessions; the
[implementation checkpoint](../tactical/hott-automation-handoff.md#measurement-baseline)
summarizes them. The original measurements above are kept as historical
evidence.

Corpus counts use `grep -o PATTERN archive/first-library/*.cubist | wc -l` with the
patterns `'\btrans('`, `'\bcong('`, `'\bsym('`, `'\btransport('`,
`'induction [a-z_]* as [a-z_]* return'`, `'match [^{]* return'`,
`'path_induction('`, `'based_induction('` and `'FunExt('`. The h-level
declarations match the suffixes `_prop`, `_set`, `_is_set`, `_are_set`,
`_are_a_set`, `_is_prop`, `_prop_at`, `_set_at` and `_prop_ext` among `def`
names. The closure-lemma count uses `product_prop(`, `forall_prop(`,
`sigma_prop(`, `field_forall_prop(`, `field_and_prop(`, `field_sigma_prop(`,
`is_set_prop(` and `is_prop_prop(`. The second review's rows use
`'\bconcatenate('`, `'\binverse(U'`, `'\bappend_path('`, `'\bap(U'`,
`'\bface_when('`, `'\bcomp('` and `'\btransport_constant('`, and
`'\b\(fst\|snd\|field_fst\|field_snd\|sigma_first\|sigma_second\|field_first\|field_second\)('`
for the projection helpers. The `Fiber` counts use `'\bFiber('`, with
`grep -l` for the number of files.
