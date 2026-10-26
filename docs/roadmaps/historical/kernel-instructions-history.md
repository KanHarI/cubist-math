# Kernel instructions: migration history

Split on 2026-10-26 from [kernel instructions](../kernel/kernel-instructions.md),
which keeps the instruction kernel's design, trust boundary, driver and
stage-6 work. This record keeps how the trusted kernel moved from the term
checker to the instructions: the status notes written during the migration,
where the term checker searched, the primitive instructions since retired,
the risks as first assessed, stages 4 and 5, and the term checker's
retirement (I1.2a, I1.2b). Dated measurements keep their revisions.

## Status notes during the migration

2026-09-30 update: Nat and W are now source-defined H1 inductives. Their
primitive formation, constructor and elimination instructions have been
removed; their ABI numbers remain reserved and are refused. The primitive
API and stage milestones below describe the earlier implementation. See the
[migration record](../historical/h1-program-types.md) for the current API and validation.

2026-10-01 update: pushouts are source-defined too, as an H1 declaration
with a path constructor in `pushout.cubist`. `Pushout`, `PushPoint`,
`PushPath` and `PushElim` have been removed and their ABI numbers reserved,
like Nat's and W's. `HComp` and `Trans` are now for declared higher sorts
only; the term checker has no rule for them. Sums stay native.

Status: merged into `proof-ergonomics-roadmap` on 2026-09-26 (PR #38). The
instruction kernel is the trusted kernel, and elaboration checks every term
through it. Since K1.4 on 2026-09-27 the driver uses its own guide. The
term checker and its conversion oracle were retired on
2026-10-02 (work plan I1.2b; see
[what remained of it](#what-remains-of-the-term-checker)); stage 6 is
started (see [Stages](../kernel/kernel-instructions.md#stages)). The
[audit of 2026-09-28](../historical/audits/2026-09-28-audit.md) found that separation
incomplete: reduction called the old conversion, and its memo could change
an instruction's acceptance. Work-plan I1.2a corrected both the same day,
and enforces the boundary at run time; that section records how.
H1's signature instructions (K2.2) are on by default since H1's release on
2026-10-02; `CC_EXTENSION_H1` can switch them off. The ABI version is 3.
Every later kernel item (G0, H) is a set of instructions; the
[work plan](../work-plan.md#the-instruction-kernel-and-this-plan) records how
that changes the plan.

- Stage 1 is implemented: `kernel/src/instructions.c`, tested by
  `kernel/tests/test_instructions.c`.
- Stage 2 is implemented:
  - the WASM bridge and `web/cubical-instructions.mjs`;
  - the driver `web/cubical-instruction-driver.mjs`;
  - the workbench's **Kernel graph** view (`web/cubical-graph-view.mjs`);
  - the Elaboration panels, which now show the instruction derivation.
- Stage 3 is implemented: paths at any interval formula (`PathAt`),
  composition, with an equality on each overlap of two tubes' faces
  (`System`, `SystemTube`, `SystemOverlap`, `Comp`), pushouts
  (`Pushout`, `PushPoint`, `PushPath`, `PushElim`), W types (`W`, `Sup`,
  `WElim`), homogeneous composition and transport (`HComp`, `Trans`), and
  Glue (`GlueBase`, `GluePiece`, `GlueOverlap`, `Glue`, the Glue term's
  three, and `Unglue`).
- Stage 4 is implemented: the instruction kernel admits every definition,
  in the proof pages, the REPL, the CLI, the benchmark and the tests, and each
  tactic's check is derived as the tactic runs. See
  [Stage 4](#stage-4-the-trusted-kernel) below.
- Stage 5 is implemented: the term checker leaves elaboration. The driver
  derives source syntax itself, and every check and query the elaborator
  makes is derived by the instruction kernel. See
  [Stage 5](#stage-5-the-term-checker-leaves-elaboration) below.
- The review run at `fabb174` on 2026-09-27 reports zero archive gaps and
  re-derives all 3,916 stored definitions with the driver's own guide
  (`node tools/instruction-coverage.mjs`): 30.7 s for the archive check and
  10.7 s for the second derivation. These are one run's observations.
  Every derived term is its source syntax, annotations included. The
  first proof and the library also use this admission path.
  Since I1.3 the command fails, with exit status 1, unless every import
  checks, no gap remains and every definition derives again; its report
  also gives the kernel work each phase cost (see [the driver](../kernel/kernel-instructions.md#the-driver)).

## Where the term checker searched

The term checker, the trusted kernel before this work, takes a finished term
and checks it top-down (`kernel/src/check*.c`). Selecting each rule is not
search: every node kind has one rule. The search is in how it decides that
two types are equal, and where it reduces:

| Where | What it decides | Files |
| --- | --- | --- |
| Conversion `A ≡ B` | A strategy: compare folded, then with the elaborator's unfolding hints, then with definitions exposed, then computed to head normal form with congruence into arguments; eta for functions, pairs and paths; a memo of results | `term_conversion.c` (~500 lines) |
| Unfolding hints | Which definitions the hinted pass may unfold | `unfolding_hints.c`, `term_conversion.c` |
| Demanded heads | About 30 implicit `ck_whnf` calls in the typing rules: an application's function type is reduced until it is a `Π`, a pair's type until it is a `Σ`, a type until it is a universe | `check_*.c` |
| Evaluation | Normal forms for `evaluate` and `computable`; deterministic | `term_normalize.c`, `*_compute.c` |

`opaque def` never reached the kernel, and has been removed (#37).

## Retired primitive instructions

The primitive `Nat` instructions (`Zero`, `Succ`, `NatElim`) and those of W
types were removed on 2026-09-30, and those of pushouts on 2026-10-01, when
the types became source declarations; their ABI numbers stay reserved. The
instruction list described the pushout and W instructions as follows:

- **Pushouts** (CHM §3.3.5): `Pushout` forms `Pushout(C, A, B, (f, g))`
  from `C, A, B : U` and the maps, a pair `C → A`, `C → B`. `PushPoint` gives
  `inl(a)` or `inr(b)`, `PushPath` gives `push^r(c)` at an interval formula
  `r`, and `PushElim` gives the dependent eliminator from a motive and its
  left, right and bridge cases, the bridge a dependent path over `push(c)`
  from the left case at `f(c)` to the right case at `g(c)`. The pushout type
  must be one as written, so the driver reduces an annotation such as
  `Susp(A)` first, as it does for a pair's. `Iota` computes the eliminator
  on a point or a path, and a path at an endpoint to a point; that step
  reads the maps off the pushout type's weak head, which involves no choice.
- **W types:** `W` forms `W(x : L). B` from an entry and a family, as `Π` and
  `Σ` do, and `Domain` and `Family` give `L` and `B[l/x]`. `Sup` gives
  `sup(l, c)` of a W type as written, and `WElim` gives W recursion from a
  motive, a step and a value, at the types the term checker states. `Iota`
  computes recursion on `sup`.

## Costs and risks

- **Proof size and speed.** Every node becomes an instruction, and every
  conversion carries its steps. The search moves out of C; running it in
  JavaScript is slower, so it may live in an untrusted C/WASM module beside the
  kernel instead. `Normalize`, and the sharing of repeated instructions, bound
  the cost.
- **The cubical rules.** Composition for each type former, `Glue` and pushouts
  make up most of the kernel's rules and computation; each needs an
  instruction and positioned contraction steps.
- **Migration.** The rebuilt library and the 365 archived modules must check in
  instruction mode, with the same judgements.
- **Surfaces.** The bridge, the JavaScript kernel wrapper, the program, the
  inspector, the workbench and the CLI's `assembly` all change.

## Stage 4: the trusted kernel

Historical migration stage, completed before the term checker was removed.
Its checker/oracle descriptions below record that intermediate architecture;
[current retirement status](#what-remains-of-the-term-checker) governs today.

**Admission.** Every definition, whatever its source (a declaration, a
universe specialization, a `with unfolding` helper, a builtin such as `ua`),
goes through `NativeCubicalElaborator.admit`: the term checker elaborates the
body, reconstructing annotations and splitting faces; the driver derives the
checked body at its type; and `Define` registers the closed judgement. A body
the instruction kernel cannot derive is not a definition: the declaration
fails with an error beginning "Instruction kernel:". The kernel enforces the
boundary itself: each definition records whether `Define` admitted it, and
`Lookup` refuses any other, so a definition the term checker registered can
never enter a derivation.

**Tactics.** Each committed check a tactic makes, the checks it builds its
proof from, is derived at once, through one driver shared by the declaration,
and the declaration's admission reuses those derivations. A term the kernel
cannot derive fails at the tactic that checked it, with its source position.
The elaborator's queries (`infer`, `nf`, `equal`, `expect`, speculative checks)
steer elaboration: about 180,000 `infer` and 170,000 `nf` calls on the archive
against 7,300 committed checks. In Stage 4 they were answered by the term checker
alone and were not evidence; Stage 5 derives them too. The driver
lives on the kernel and is dropped after each admission, at the end of each
declaration's transaction and at each inspection, so no search depends on
another declaration's.

**Hints.** `with unfolding` hints steer only the term checker: withholding
them from it leaves every archive definition admissible except five F4
proofs that then elaborate too slowly for a 5 s limit. Nothing the
instruction kernel accepts depends on them.

**Cost.** With a 5 s limit per declaration, the archive's 3761 declarations
take 20 s, against about 10 s for the term checker alone; the admissions themselves
take 2.3 s, because the tactics' derivations are reused. The JS test suite
takes 61 s, up from 34 s.

**Not done** in Stage 4: the term checker still elaborated, and the driver
derived its output. Stage 5 removes it.

## Stage 5: the term checker leaves elaboration

Historical migration evidence. Stage 5 completed; I1.2b subsequently removed
the remaining checker APIs and oracle on 2026-10-02.

**Raw syntax.** The elaborator hands the driver the source syntax, not the
term checker's output, and the driver does what the term checker did before
it:

- it restores a constructor's annotation after reducing it, and derives a
  path lambda at its own family, so that the derived term is the source's;
- it splits a composition's faces into clauses and restricts each tube to
  its clause, with an equality on each overlap;
- it tracks the live interval dimensions in each scope, and moves a
  dimension binder to a free index when its parts could not tell it from a
  live one: a composition's faces lie outside its binder, and a variable's
  type may mention the outer dimension. Otherwise a binder keeps its index,
  so derived types stay the source's, and sharing survives;
- it names apart a binder whose name another entry has at another type.
  Displays show the source's name again wherever nothing in the body can
  tell the two apart.

**Everything is derived.** `check`, `infer`, `equal`, `expect` and speculative
checks all go through the driver, and the term checker's check count during
elaboration is zero. What remains of it is its conversion, the search's
guide, and the kernel's own reduction (`Whnf`, `Normalize`), which is trusted
computation. A mismatch is reported as the term checker reported it, "Type
mismatch", with the two types; running out of time or budget is passed on as
such; any other refusal begins "Instruction kernel:". The Elaboration panels
have no other derivation to fall back to: a declaration whose view cannot be
derived shows the reason.

**Deadlines.** Each instruction polls the declaration's deadline, and a
derivation polls it before reusing an earlier judgement. The syntax services
(`rename`, `endpointTerm`, `equivType`) now report the kernel's error rather
than a zero handle.

**Costs.** Deriving raw syntax exposed two caches keyed by more than they
depend on. Decoding a result was cached per whole dimension context, and the
driver's alpha comparison per whole renaming. A tower of 32 nested path
lambdas then took exponential time and ran out of memory. Both are now keyed
by the dimensions the terms mention, and the tower checks in 50 ms. With a
5 s limit per declaration, the archive's 3761 declarations check in 25 s,
against 20 s in Stage 4. The JS test suite takes 76 s, up from 61 s.

## What remains of the term checker

**Retired on 2026-10-02 (work plan I1.2b).** Nothing remains of it. The
typing rules (`check.c` and the `check_*.c` files), the check cache, the
restricted contexts of `face_context.c`, the unfolding hints, the trace, and
the conversion search with its modes are deleted, with `cc_kernel_check`,
`cc_kernel_check_in_cube`, `cc_kernel_define`, `cc_kernel_convertible`,
`cc_kernel_set_unfolding_hints`, the trace API and `CC_REUSE_CHECKS`. The
folded comparison stays in `term_conversion.c` as the comparison's only
mode, unchanged; the queries the driver asks moved to `queries.c`. In
JavaScript, `CubicalKernel.check`, `define` and `convertible`,
`CubicalSyntax.check`, the driver's `oracle` option and the coverage tool's
`--oracle` are gone, and so is `tools/differential-driver.mjs`, which
compared the driver with the term checker. Source `with unfolding [names] {
e }` is still accepted: its names must be checked definitions, and its body
is checked as a definition of its own, but the names steer nothing. Archive
coverage with the driver's guide is unchanged, to the instruction and the
step. The record below is how it stood before.

The instruction kernel uses two pieces of the old checker's files, and only
they are trusted: the folded comparison of `term_conversion.c`, which is
alpha equality (`ck_alpha_equal`) and syntactic cumulativity
(`ck_syntactic_cumulative`), and the builder of a pushout's bridge type
(`ck_pushout_bridge_type`) in `check_pushout.c`. The reducers of
`term_normalize.c`, which `Step`, composition and transport call, are
trusted computation, as decision 1 of the [kernel instructions](../kernel/kernel-instructions.md#decisions) states. The rest is untrusted:

- the typing rules (`ck_check`, `ck_infer` in `check_*.c`), reachable through
  `cc_kernel_check` for `CubicalSyntax.check`, which only tests use;
- the conversion search (`ck_convertible` in `term_conversion.c`) and the
  unfolding hints, reachable through `cc_kernel_convertible`, which the
  driver asks only with its `oracle` option;
- `cc_kernel_define`, whose definitions `Lookup` refuses.

**Corrected on 2026-09-28 (I1.2a).** The audit of that day (finding 1)
found two paths across this boundary. `Step(Whnf)` and `Step(Normalize)`
reached `ck_convertible` through the reducers' Glue and pair eta rules.
And a successful conversion comparison entered the memo table that the
folded comparison also read, so a public `cc_kernel_convertible` query
could satisfy a later instruction's syntactic side condition: the audit's
probe has an `Apply` refused, then accepted after the query, with no
equality judgement among its premises. The equality involved was valid beta
equality, so this was history-dependent acceptance, not a false equality.
The correction:

- **The memo keeps two facts per pair.** The folded result is written and
  read only by the folded comparison; a conversion success is reused only
  by conversion.
- **Reduction decides eta by syntax.** Pair eta contracts `(fst p, snd p)`
  and Glue eta `glue [φ ↦ b|φ] (unglue b)` only when the two sides are the
  same up to bound names. `Normalize` still reaches the contraction when
  the normal forms of the parts agree; for Glue eta it compares each piece
  with the normal form of the base's restriction, since restricting can
  make a new redex, as `p @ i` at `i = 0` is `p`'s left endpoint.
  Conversion makes both eta contractions itself, decided by conversion, on
  either side of a comparison, so two pairs with different annotations
  still compare, and it exposes a Glue term's base through such eta, for
  nested Glue terms, within the comparison's depth limit. The driver's
  last-resort `glue` move makes a `Glue` step, within its own step budget,
  when nothing else agrees the two sides, so its searches still find the
  contraction. The step reduces the two Glue types, and each piece and the
  base on the piece's face, only as far as comparing them takes: part by
  part under a common head, each pair once, so that parts already equal are
  never normalized. It exposes a nested base through nested Glue steps, as
  conversion does, within the reduction depth of 1,024. The move first took
  the whole term's normal form instead, which also walked the base's
  annotations, whose endpoints can hold large shared graphs. Before the
  move, the driver's eta move expands a neutral side against a Glue term,
  `g` to `glue [φ ↦ g] (unglue g)`, so that the two Glue terms compare part
  by part with every move of the search: a base equal to `unglue g` only by
  pair eta, or a Glue type equal to the other only below its head. The Glue
  step remains for a piece that is the base only on its face, which
  congruence cannot show.
- **The boundary is enforced.** `ck_convertible` fails, with an internal
  error, while an instruction runs; every public entry point that may reach
  it starts a query first.
- **The call graph.** A static call graph of `kernel/src` at this revision
  finds no path from any of the 76 instruction entry points to
  `ck_convertible`, `ck_expect`, `ck_check`, `ck_infer` or the typing rules.
  Reached old-checker code is the folded comparison with its helpers and
  `ck_pushout_bridge_type`. The folded comparison shares one function,
  `alpha`, with the conversion modes; at run time the folded mode never
  enters them, and I1.2b gives it its own file.

`kernel/tests/test_isolation.c` covers each point, and reverting any one of
them fails it. Measured on the archive: with the driver's guide, reduction's
conversion accepted an eta contraction that syntax refused twice, and the
driver found other derivations for both; archive coverage stays complete,
at 5,524,203 check instructions (6 fewer) and 147,448,289 re-derivation
steps (0.006% more). With the conversion oracle, which the leaky memo
actually affected (a counting build found dozens of side conditions
answered by conversion's evidence where syntax disagreed), coverage stays
complete at about 1% more kernel steps: those side conditions are now
derived.

The JavaScript reference checker (`lib/cubical/core.mjs`) was in the same
position: its `Checker` served the tests of the CCHM fragment and the
JavaScript-only elaboration tests. It was removed on 2026-10-02, when those
tests moved to the instruction kernel; `core.mjs` keeps the syntax
constructors and substitution the path builders use.

**Decision (2026-09-26).** Neither is extended. G0 and H are implemented as
instructions and as the driver's search, once; the term checker's rules and
the reference checker stay at today's fragment. An error or an exhausted
budget from the conversion oracle is "not known" to the driver, which then
searches on its own. The oracle retires when the driver no longer benefits
from it. On 2026-09-26 it still did: without it the archive checked in 62 s
against 33 s, three declarations ran out of kernel budget
(`finite_subgroup_fixed_degree_upper_bound`, `f4_base_field_is_f2` and
`f2_embedded_compositum_is_f2`) and five dependents went untranslated, and
deriving every definition again took 34 s against 10 s. The driver's own
guide ([the driver](../kernel/kernel-instructions.md#the-driver)) closed that gap on 2026-09-27 (work plan K1.4), and is now the
default: the driver no longer asks the term checker anything. It retired
on 2026-10-02 (I1.2b), as recorded above: the folded comparison, with the
level, formula and scope helpers it uses, and the pushout bridge builder
moved to their own files, and `check_*.c`, the rest of
`term_conversion.c` and `unfolding_hints.c` were deleted, together with
`cc_kernel_check`, `cc_kernel_convertible` and `cc_kernel_define`. Stage 6
was conditional on JavaScript being too slow; its first performance work
landed on 2026-10-06 (see [Stages](../kernel/kernel-instructions.md#stages)).
