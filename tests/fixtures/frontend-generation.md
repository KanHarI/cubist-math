# Frontend generation cases

These are active cases, integrated from [#217](https://github.com/KanHarI/cubist-math/pull/217)
(the replacement for #205). Each case is a Cubist module in
[`frontend-generation/`](frontend-generation/), headed `// ID (phase): contract.`,
with its own ID, finding group and responsible phase.
[frontend-generation.test.mjs](../frontend-generation.test.mjs) checks every
module with this checkout's fresh WASM build in the normal `npm test` suite,
and any difference from a case's desired outcome fails through `assert`. RC0
retired the known-defect records and the expected-failure lifecycle. Run the cases alone with
`npm test -- tests/frontend-generation.test.mjs`, and one of them with
`--test-name-pattern`, for example `\[G12-inherited\]`. `00d4ecce` is the
historical revision where the inventory's defects were observed, not a
runtime pin.

## Desired outcomes

A module states its desired check as
[`tools/inline-errors.mjs`](../../tools/inline-errors.mjs) writes it: an
`// Error:` comment above each declaration that must be refused, giving the
exact message, and nothing above a declaration that must check. Every
client must also check without assumptions.

That comparison sees each error and warning the checker reports, with its
exact text, at the line of its declaration. It does not see a declaration
with no output, which reports nothing, where in its line a refusal lies, or
the work a check did. So every case also requires each declaration without a
comment to have an output of its own, and
[frontend-generation-cases.mjs](../frontend-generation-cases.mjs) observes a
refusal's range in its line, the links at each use of a name, the names a
case must not publish and work counters, for the cases that need them,
beside their desired values. Lint advice needs no observation of its own: it
is a warning, and a module without a `// Warning:` comment admits none. The
cases module's `gaps` lookup gives the provenance and browser tests a case's
source by ID.

The clients and their statements are written by hand, independently of the
generator. The desired messages, ranges and links are those of this
branch's fixing compiler at `1b64229b`, each reviewed against the
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
  `found U1, expected U0`.
- **G3** keeps the base theory usable, refuses both its Hom and its Iso client
  with E817 naming operation `op`, argument `p` and law `l`, and publishes
  nothing under `T.Hom` or `T.Iso`.
- **G4** and **G4-flat** compute nested and flat matches with distinct branch
  results, and refuse a constant-result equation.
- **G5** and **G5-single** use positional operation calls, a Hom identity, a
  named generated-constructor client (`T.Hom.make` with `map :=` and
  `map_op :=`) and an initial model; named operation calls are separately
  unsupported (E378).
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
  meaning.
- **G10** refuses a capture with E871 naming helper `k` and field `c`, over the
  conflicting binder: the `c` of `succ(c)`, not its use in `k(c)`.
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
- The **controls** must check today: B1's file-level `use` precedence over
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

Fixed examples are protected by existing tests, which this runner does not
duplicate:

| ID | Existing test |
| --- | --- |
| H1 | `Constant`, `K`, `idem_at`, `Named` and `named_fold` in [`initial_models.cubist`](../../cubist-tests/initial_models.cubist) |
| H2 | “initial and free models retain imported global types and law constants” in [theory-resolution.test.mjs](../theory-resolution.test.mjs) |
| H3 | “family indices carry captured syntax through generated homomorphisms and isomorphisms” in [theory-resolution.test.mjs](../theory-resolution.test.mjs) |
| H4 | “theory capture uses opened fields before globals and retains them across imports and selections” in [theory-hygiene.test.mjs](../theory-hygiene.test.mjs) |
| H5 | “inlining preserves a helper's free fields under a caller's binders” in [theory-hygiene.test.mjs](../theory-hygiene.test.mjs) |

Passing controls in [theory-hygiene.test.mjs](../theory-hygiene.test.mjs):
“generated evidence links nowhere and written compound headers link once”,
“freshened parameters and operation arguments keep their public names in
diagnostics and inspection”, “substitution considers enclosing binders
before refusing a fixed pattern capture”, “generated recursive calls retain
their declaration under same-named parameters and patterns” and “catch-all
path clauses respect recursive boundaries and require coherence”.

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
| `G2` | G2 | Fixed argument domains; Hom/Iso, preservation, level and computation at U0/U1 |
| `G3` | G3 | Law-dependent transport; usable base and no partial families |
| `G4` | G4 | Nested derived match; distinct nil/off/yes results and refused constant result |
| `G4-flat` | G4 | Flat derived match; distinct nil/cons results and refused constant result |
| `G5` | G5 | Grouped operation binder; supported call, Hom and initial-model clients |
| `G5-single` | G5 | Single operation binder with the same interface checks |
| `G6` | G6 | Parent cause, child dependency and unrelated recovery |
| `G8` | G8 | Wildcard diagnostic endpoints, exact body range and no coherence search |
| `G9` | G9 | Freshened binder and every use: public labels and navigation |
| `G10` | G10 | Capture refusal over the written binder |
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
npm test -- tests/frontend-generation.test.mjs tests/frontend-provenance.test.mjs
npm run test:generation:mutations
npm run test:browser
```

The mutation gate selects these cases by their group prefixes and the control
names it lists. Commit-specific results belong in the PR record.
