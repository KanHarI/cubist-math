# Evaluation demand marks: `!` and `!!`

Status: proposed on 2026-10-21, nothing implemented. This is the
observation contract that EVAL5 of the
[runtime roadmap](runtime-evaluation-roadmap.md#eval5-demand-only-the-result-being-observed)
requires before evaluation behavior changes, and it resolves decision D1 of
the [rational normalization debugging plan](https://github.com/KanHarI/cubist-math/pull/302)
in the direction of lazy by default and strict on request. It proposes no
kernel change and no new reduction: the two marks name the kernel's two
existing reduction queries.

## What evaluation does today

Every form of evaluation computes the full normal form. The `evaluate`
directive calls the checker's `verify` (`web/translator/translate.mjs:388`),
which asks the kernel to normalize the checked expression and decodes the
answer (`web/cubical-elaborator.mjs:755`); `print(evaluate(e))` does the
same (`translate.mjs:415-420`), and the REPL's bare `evaluate e` is
`print(evaluate(e))` (`web/repl-session.mjs:239`). An expected value with
holes is matched part by part against that decoded normal form
(`translate.mjs:396`, `web/translator/evaluation.mjs`), so a hole saves no
work; the roadmap records this. Only the `nonempty` and `empty` assertions
infer a type without normalizing.

The kernel offers exactly two reduction queries, `cc_kernel_whnf` and
`cc_kernel_normalize` (`kernel/src/queries.c:16-32`), both certifying
nothing. The workbench already exposes both per selected subtree as WHNF and
Normalize. A weak head of any handle is available to the driver through the
head query; the normalize query is additionally guarded to derived handles
(`web/cubical-kernel.mjs:250-263`).

The cost of the full normal form is now attributed. On main `6d1bd75b`, in a
fresh program with a fixed budget, the rational literal `2/3` normalizes in
3.5M ticks, all of it the retained sort annotation, and `bq_inv(-2/3)` in
71.5M ticks with a 1,149,838-node normal form, almost all of it the nonzero
certificate's body under its binder. A demand-driven walk of the same
inverse, taking the weak head of each constructor argument and pair
component and stopping at the certificate's lambda, costs **15,382 ticks**,
of which 12,645 are the first head. The data is cheap; the proofs and
annotations under binders are not. Nothing in this note makes the full
normal form smaller; the debugging plan's experiments remain the way to do
that.

## Proposal

Three demand levels, written where evaluation is requested, by analogy with
Haskell's bang pattern and `$!` for weak head normal form and `$!!` and
`deepseq` for full normal form:

| Mark | Demand on the marked part | Kernel query |
| --- | --- | --- |
| none | as far as the pattern or the printer observes it | head queries on observed positions |
| `!` | its weak head, whether or not anything observes it | `cc_kernel_whnf` |
| `!!` | its full normal form | `cc_kernel_normalize` |

Grammar, with the marks as fixed language forms like `~`, `++`, `&` and `|`
(`docs/roadmaps/high-level-abstractions/notation.md`: no view binds a fixed
form, and `!` is not a token today, `web/cubist/parser.mjs:205-216`):

```text
evaluate [! | !!] term ;
evaluate [! | !!] term expecting pattern ;
print(evaluate([! | !!] term));

pattern ::= _ | ! pattern | !! pattern
          | (pattern, pattern) | left(pattern) | right(pattern)
          | c(pattern, …) | typed(T, pattern) | expression
```

`!!` is one token. The marks are directives of `evaluate`, `expecting` and
`print(evaluate(…))`, never term formers, so nothing about them reaches the
kernel but the queries they select.

## Semantics

**Observation demand** (unmarked). A pattern demands of its part exactly what
deciding the match needs:

- `_` demands nothing and matches.
- `(p, q)` demands the weak head, requires a pair, and continues into the
  components; `left(p)`, `right(p)` and a constructor pattern `c(p, …)`
  demand the weak head, require that head, and continue into the arguments
  in the kernel's order, each read at its field's type as today.
- `typed(T, p)` is `p` read at `T`.
- An expression leaf, as `5` or `nat.(2 + 3)`, demands the part's full normal
  form and compares it with the leaf's, exactly as today: exact
  expected-value checks are preserved, and a leaf is a `!!` on its part.

Printing is an observation too. Plain `evaluate e;` prints the **value
form**: weak heads descended through constructor arguments, pair components
and injection values, stopping at term lambdas, path lambdas, sort instances
and neutral heads, which are shown as suspended. How a suspended part prints
is open question 1 below.

**`!p`.** The part is reduced to its weak head before `p` is matched. With
`_`, the head query must succeed and nothing more is asked. At the top,
`evaluate !e;` prints the weak head with its arguments as written, which is
the workbench's WHNF view in source form. `!` on a part whose head is a
lambda is vacuous: a lambda is its own weak head.

**`!!p`.** The part is fully normalized and `p` is matched against the
normal form as today. `expecting !!_` is today's `expecting _`, and
`evaluate !!e;` is today's `evaluate e;`.

**What `!` does not say.** `!` makes no claim about a proof. The inverse's
certificate is a lambda, so `!` on it checks nothing; only `!!` says that a
certificate normalizes. The reference must say this plainly so that `!` is
not read as a computability check for certificates.

**Failure contract.** Each demanded query carries the session's budget and
deadline, and budget, deadline and resource stops are reported as today, with
the part of the pattern whose demand failed. An unmarked position with no
observer requests nothing, so it cannot fail. Closedness and the assumption
check on the evaluated term are unchanged. The kernel's isolation property
is unchanged: queries certify nothing, and a cached weak head or normal form
changes no instruction's acceptance.

**Lints**, in the style of the unneeded-binding lint: `!` directly on a
pair, injection or constructor pattern is redundant with that pattern's own
head demand; any mark under `!!` is redundant; `! !p` is refused.

**`witness TERM;`** keeps its own specification (L2.9b): it reads a
constructor off a closed truncation under formal compositions, which is a
weak-head walk and not a full normalization, so its behavior does not change.

## Why three levels and not two

The two marked levels are the kernel's two queries and the workbench's two
operations; the syntax exposes what exists rather than inventing a third
reducer. `!` earns its place at the top of `evaluate` as the inspection view,
and in a pattern as the rare check that a part reaches some canonical head
without naming it. `!!` keeps the normalization engine testable from source:
every full-normalization gate in the NUM2 contracts is written with it, so
the lazy default cannot silently weaken a gate.

## Migration

Every existing `expecting _` is classified as a value check, which stays `_`
or becomes a constructor pattern, or as an engine gate, which becomes `!!_`.
On main the wildcard form occurs once in `tests/fixtures/contracts`, twice in
`tests/fixtures`, three times in `docs`, never in `cubist-tests`, and in
several JavaScript tests that embed sources, `tests/normalization-sharing.test.mjs`
and `tests/quotient-descent.test.mjs` among them; #283 adds
`normalize_wide_inverse` with it. The non-wildcard patterns (33 in
`cubist-tests`, 8 in the contracts) are expression leaves or constructor
patterns and keep their meaning.

The evaluation baseline's `euclid-4-pattern` case, `evaluate euclid(4)
expecting (5, _)`, changes outcome: it no longer forces the certificate. The
fixture is re-recorded with `--write`, and a `!!` twin of each changed case
is added so that the recorded engine outcome stays measured. The roadmap's
sentence that patterns match the full normal form, the work plan's L2.9a row,
and the reference chapters that show `evaluate … expecting` are updated with
the three levels. The formatter and the lint learn the tokens and the
redundancy rules.

## Acceptance for the implementation

- `evaluate bq_inv(-2/3);` prints `-3/2` in the selected notation within
  100,000 query ticks in a fresh program; today's demand-driven walk costs
  15,382 before printing.
- `evaluate bq_inv(-2/3) expecting !!_;` reproduces today's counters and
  normal-form digest exactly; the engine gate is unchanged.
- `evaluate euclid(4) expecting (5, _);` completes, and
  `expecting (5, !!_)` reproduces the baseline's recorded failure.
- Every contract and Cubist test keeps its outcome after classification, and
  the baseline fixture carries both twins.
- A lazy result is visibly distinct from a full normal form in the REPL, the
  CLI and the workbench's copied trace, as EVAL5's acceptance requires, and
  forcing a suspended part after a later session operation is either safe or
  a documented expiry error.

## Work items

| ID | Work | Depends on | Size |
| --- | --- | --- | --- |
| DM0 | This decision record, the open questions answered, the roadmap and work plan rows updated | — | S |
| DM1 | Tokens `!` and `!!`, grammar in `evaluate`, `expecting` and `print(evaluate(…))`, formatter, lints | DM0 | S |
| DM2 | Demand-driven matcher over kernel handles: head queries on observed positions, decoding only observed parts, `!!` through the existing normalize path | DM1 | M |
| DM3 | Value-form printer with suspended parts for the REPL, CLI and workbench | DM2, open question 1 | M |
| DM4 | Classification and migration of `expecting _`, baseline re-recording with twins, reference and roadmap text | DM2 | S |
| DM5 | Report with the acceptance measurements, fresh-session fixed budgets and digests | DM2–DM4 | S |

## Open questions

1. **Printing a suspended part.** Print it as written under the printer's
   output budget, or elide it with a marker and let the workbench expand it.
   The second keeps printed values short; the first keeps them complete.
2. **Expression leaves.** Keeping them as `!!` on their part preserves
   exactness; a weaker rule, normalizing only as far as comparison needs,
   would be a third demand and is not proposed.
3. **`evaluate !e;` when the head is a lambda.** Printed as written; whether
   to warn that the mark did nothing.
4. **REPL bindings.** Whether `let x := !!e;` should exist; out of scope here.
