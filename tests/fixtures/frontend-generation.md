# Frontend generation cases

These source fixtures and the observer are selectively adopted from #224 at
`1fdc68a5e7da198f2b538dfbaa95e4bad40c97ca`, on the CB0 compiler base
`f0417ee0ee5f824f030069be0e6d1666696de0d1`. Adoption does not implement the
later fixing PRs. Eighteen cases pass; eighteen retain exact known defects
in [frontend-generation-baseline.json](frontend-generation-baseline.json).
These observations were measured at `d70c07ae` (the same production code).

Each case is a Cubist module in [frontend-generation/](frontend-generation/),
headed `// ID (phase): contract.`. Its source comments and extra observations
state the desired behavior independently of the baseline.
[frontend-generation.test.mjs](../frontend-generation.test.mjs) runs every
case against the checkout's fresh WASM build. Imports and observation errors
must pass before known-defect classification. A TODO requires an exact match
to its recorded observation and a difference from its desired behavior. A
changed failure or an unexpected fix fails normally, before marking TODO;
retire the known-defect record when its responsible CB package lands. There
is no automatic baseline rewrite command. `CUBIST_GENERATION_STRICT=1`
requires all desired contracts to pass without TODOs.

Run with `npm test -- tests/frontend-generation.test.mjs`; select a case
with `--test-name-pattern`, for example `\[G12-inherited\]`. The expanded
cases replace the old twelve coarse TODO tests, so the TODO count alone is
not a measure of new defects. The original `00d4ecce` inventory remains
historical evidence, not a runtime pin.

## Desired outcomes

A module states its desired check as
[`tools/inline-errors.mjs`](../../tools/inline-errors.mjs) writes it: an
`// Error:` comment above each declaration that must be refused, giving the
exact message, and nothing above a declaration that must check. Every
client must also check without assumptions.

Before comparison, the runner requires every local checker failure to have
a matching reported error, consuming each error once. Imports, including
unused and transitive imports, must check. An unaccounted failure is an
assertion failure.
[frontend-generation-observer.test.mjs](../frontend-generation-observer.test.mjs)
checks missing modules, missing transitive modules and refused declarations
and directives in unused imports, for a control and G5/G9. It also checks
that a repeated local failure cannot reuse one reported error.

The comment comparison sees local errors and warnings, with their exact
text, at the line of their declaration. It does not see a declaration
with no output, which reports nothing, where in its line a refusal lies, or
the work a check did. So every case also requires each declaration without a
comment to have an output of its own, and
[frontend-generation-cases.mjs](../frontend-generation-cases.mjs) observes a
refusal's range in its line, the links at each use of a name, the names a
case must not publish and work counters, for the cases that need them,
beside their desired values. Lint advice needs no observation of its own: it
is a warning, and a module without a `// Warning:` comment admits none. A
generated declaration is not written, so its output can disappear unseen: a
case names each generated interface its contract needs in a written client.
The cases module's `gaps` lookup gives the provenance and browser tests a
case's source by ID.

The clients and their statements are written by hand, independently of the
generator. A client must also tell the fix from a blanket one: G2's
fixed-domain theory needs U1 either way, so an ordinary theory's Hom must
stay in U0. The desired messages, ranges and links were adopted from #224's fixtures
(the fixing compiler at `1b64229b`), each reviewed against the
[roadmap](../../docs/roadmaps/frontend-generation.md), the authority for
desired behavior. Never take a desired output from a compiler that still has
the defect: that would record wrong behavior as accepted. A reworded message
changes the case's comment, and the new wording needs the same review.

## What each case distinguishes

- **G1** covers both orders of definition/inductive collisions, a
  definition/initial-model collision and a same-kind duplicate. The second
  declaration is refused as a duplicate. The first keeps its own output,
  which the refused one must not replace, and its clients check. Clients of
  the refused constructors (`c`, `N.one`, `N.mul`) are refused with E343,
  while G1-reverse keeps its original constructor. G1-initial publishes no
  `N.model`, `N.fold_map` or `N.fold`.
- **G2** checks Hom/Iso, composition, the fixed-domain operation's
  preservation field (`map_op`) and the Hom's level at U0 and U1. A U0
  model's Hom lives in U1; stating it in U0 is refused with
  `found U1, expected U0`. An ordinary theory's Hom still lives in U0, so a
  hard-coded `max(U, V, U1)` fails.
- **G3** keeps the base theory usable, through its operation and its
  constructor `T.make`, refuses both its Hom and its Iso client with E817
  naming operation `op`, argument `p` and law `l`, and publishes nothing under
  `T.Hom` or `T.Iso`.
- **G4** and **G4-flat** compute nested and flat matches with distinct branch
  results, and refuse a constant-result equation.
- **G5** and **G5-single** use positional operation calls, a Hom identity, a
  named generated-constructor client (`T.Hom.make` with `map :=` and
  `map_op :=`) and an initial model with its `N.model` and `N.fold`; named
  operation calls are separately unsupported (E378).
  The linter must not advise the arrow form on an operation's binders,
  since the rewrite would remove generated interfaces; neither module has a
  `// Warning:` comment, so any advice fails it. Passing controls in
  the runner keep W705 and W706 for ordinary unused binders and check their
  rewrites.
- **G6** keeps the parent's cause (E343 for `Undefined`), and the child
  reports its failed dependency once (E340 naming `P`); an unrelated client
  checks.
- **G8** refuses the wildcard with ordered endpoints
  (`found t1 = t1, expected t0 = t1`) over the wildcard's body `t1`, without
  starting a coherence search at its nonrecursive boundary.
- **G9** freshens a law binder; every written `c` keeps its label, links to
  the binder and spans exactly the label, and `meaning` fixes the law's
  meaning. CB1's lexical-entry observation metadata fulfills this control;
  it now passes without a known-defect exemption.
- **G10** requires the law to check despite a colliding `box(c)` binder
  of type `M`. The intended and captured laws are both well-typed and have
  opposite client verdicts, checked by independent source controls. The
  intended client requires `S.c = S.c` directly from `S.l(x)`; the rejected
  client asks for `x = S.c` directly from that law. This semantic fixture
  compares diagnostic codes, since the mismatch may print an alpha-renamed
  binder. The current E871 refusal is a known observation only.
- **G11** requires the intended `op(x, S.c)` equation to check and the
  captured `op(x, x)` equation to be refused, directly, through a helper
  chain with grouped/dependent parameters, through inheritance and through an
  initial model.
- **G12** computes `twice` at zero, one and two recursive steps, directly,
  through inheritance and through an initial model, and refuses a base-only
  result. The second step distinguishes using the recursive result from
  substituting the base value. **G12-shadowed** keeps a local parameter apart
  from the earlier recursive field. **G12-range** refuses unfolding `iter` in a
  field type with E845, over the written call. **FG6-predecessor-k** and
  **FG6-predecessor-T** keep a recursive call's predecessor after a nested
  match destructs it, whatever the predecessor is named.
- The **controls** must check at CB0: B1's file-level `use` precedence over
  later globals, in one file, across an import and with changed selections;
  inherited, bare and partial helpers under colliding law binders, and their
  ordinary clients; inherited and initial-model recursion; explicit path
  bodies, while wrong explicit path bodies are refused without a coherence
  obligation; and a local recursive name in a field type.

## Migration

Until the declaration pragmas proposed for RC1 exist, these exact messages are
the cases' semantic expectations. The modules stay outside `cubist-tests/`, so
`tools/inline-errors.mjs --write` never rewrites them, and a declaration
without a comment must check. RC1/RC2 can move them into `cubist-tests/` with
pragmas, keeping their IDs and the group prefixes the FG6 mutation gate selects.

## Historical and passing coverage

The runner verifies this table against executable test names, so a removed or
renamed historical/control test requires an explicit coverage update. The
canonical corpus also checks `Constant`, `K`, `idem_at`, `Named` and
`named_fold` in [initial_models.cubist](../../cubist-tests/initial_models.cubist).

| Coverage ID | Test file | Executable test name |
| --- | --- | --- |
| H1 | [references.test.mjs](../references.test.mjs) | `declaration identities survive every syntax transformation independently of spelling` |
| H2 | [theory-resolution.test.mjs](../theory-resolution.test.mjs) | `initial and free models retain imported global types and law constants` |
| H3 | [theory-resolution.test.mjs](../theory-resolution.test.mjs) | `family indices carry captured syntax through generated homomorphisms and isomorphisms` |
| H4 | [theory-hygiene.test.mjs](../theory-hygiene.test.mjs) | `theory capture uses opened fields before globals and retains them across imports and selections` |
| H5 | [theory-hygiene.test.mjs](../theory-hygiene.test.mjs) | `inlining preserves a helper's free fields under a caller's binders` |
| P1 | [theory-hygiene.test.mjs](../theory-hygiene.test.mjs) | `generated evidence links nowhere and written compound headers link once` |
| P2 | [theory-hygiene.test.mjs](../theory-hygiene.test.mjs) | `freshened parameters and operation arguments keep their public names in diagnostics and inspection` |
| P3 | [theory-hygiene.test.mjs](../theory-hygiene.test.mjs) | `substitution considers enclosing binders before refusing a fixed pattern capture` |
| P4 | [theory-hygiene.test.mjs](../theory-hygiene.test.mjs) | `generated recursive calls retain their declaration under same-named parameters and patterns` |
| P5 | [theory-hygiene.test.mjs](../theory-hygiene.test.mjs) | `catch-all path clauses respect recursive boundaries and require coherence` |

G7 is a historical symptom, not a currently reproduced defect. FG1 must
inject a genuine failed parent projection and verify its dependents,
publication rollback and progress; the downstream publication and
failed-dependency injection tests do so. It must not repurpose a now-passing
capture example as evidence of an open bug.

## Coverage by executable case

| Case ID | Finding | Behavior and context |
| --- | --- | --- |
| `G1` | G1 | Definition followed by inductive; preserve the first binding |
| `G1-initial` | G1 | Definition followed by initial model; no model/fold published |
| `G1-reverse` | G1 | Inductive followed by definition, including the original constructor |
| `G1-same-kind` | G1 | Definition followed by definition |
| `G2` | G2 | Fixed argument domains; Hom/Iso, preservation, level and computation at U0/U1; an ordinary Hom stays in U0 |
| `G3` | G3 | Law-dependent transport; usable base with its constructor and no partial families |
| `G4` | G4 | Nested derived match; distinct nil/off/yes results and refused constant result |
| `G4-flat` | G4 | Flat derived match; distinct nil/cons results and refused constant result |
| `G5` | G5 | Grouped operation binder; supported call, Hom and initial-model (`model`, `fold`) clients |
| `G5-single` | G5 | Single operation binder with the same interface checks |
| `G6` | G6 | Parent cause, child dependency and unrelated recovery |
| `G8` | G8 | Wildcard diagnostic endpoints, exact body range and no coherence search |
| `G9` | G9 | Freshened binder and every use: public labels and navigation |
| `G10` | G10 | Pattern/helper collision: intended law and rejected captured equation |
| `G11` | G11 | Direct intended and captured equations |
| `G11-grouped-dependent` | G11 | Helper chain with grouped/dependent parameters |
| `G11-inherited` | G11 | Inherited helper chain |
| `G11-initial` | G11 | Initial-model helper client |
| `G12` | G12 | Direct `twice` zero/one/two-step computations and refused base-only result |
| `G12-inherited` | G12 | Inherited `twice` zero/one/two-step computations and refused base-only result |
| `G12-initial` | G12 | Initial-model `twice` zero/one/two-step computations and refused base-only result |
| `G12-shadowed` | G12 | Local recursive-name shadowing; intended/captured equations |
| `G12-range` | G12 | Legitimate type-unfolding refusal over the original reference |
| `FG6-predecessor-k` | FG6 | A recursive call's predecessor named `k` survives a nested match |
| `FG6-predecessor-T` | FG6 | The same with the predecessor named `T` |
| `B1` | control | File-level `use` precedence over later globals in one file |
| `B1-definitions` | control | The definitions `B1-imported` imports |
| `B1-imported` | control | The same precedence across an import |
| `B1-changed` | control | A later selection changes only later declarations |
| `control-helpers` | control | Inherited, bare and partial helpers under colliding law binders |
| `control-helpers-ordinary` | control | Ordinary inherited, bare and partial helper clients |
| `control-local-recursion` | control | A local recursive name remains local in a field type |
| `control-paths` | control | Explicit path bodies remain checked |
| `control-paths-wrong` | control | A wrong explicit path body is refused without a coherence obligation |
| `control-paths-wrong-multi` | control | The same beside another scrutinee |
| `control-recursion` | control | Inherited recursion and initial-model clients compute |

## Verification

```sh
npm test -- tests/frontend-generation.test.mjs tests/frontend-generation-observer.test.mjs
node tools/frontend-generation-mutations.mjs build/frontend-generation-mutations.json
npm run test:browser
```

The mutation gate selects these cases by their group prefixes and the control
names it lists. Commit-specific results belong in the PR record.
