# Evaluation demand marks: `!` and `!!`

Status: proposed on 2026-10-21, nothing implemented. This is the
observation contract that EVAL5 of the
[runtime roadmap](runtime-evaluation-roadmap.md#eval5-demand-only-the-result-being-observed)
requires before evaluation behavior changes. It proposes no kernel change
and no new reduction: the two marks name the kernel's two existing reduction
queries.

It does not resolve decision D1 of the
[rational normalization debugging plan](https://github.com/KanHarI/cubist-math/pull/302).
D1 asks what a full normal form unfolds, and `!!` below keeps today's full
normal form unchanged, so D1 still bounds every engine gate written with
`!!`. This note takes full normalization out of inspection, patterns and
printing only. If it is adopted, the plan's statement that the
`expecting _` contract changes only with D1 needs updating.

## What evaluation does today

Every form of evaluation computes the full normal form. In a file,
`evaluate term expecting value;` is the evaluation directive
(`web/cubist/parser.mjs:1292-1308`): it calls the checker's `verify`
(`web/translator/translate.mjs:388`), which asks the kernel to normalize the
checked expression and decodes the answer (`web/cubical-elaborator.mjs:755-757`).
`print(evaluate(e));` does the same (`translate.mjs:415-420`). The REPL's
`evaluate e`, and a term entered alone, are `print(evaluate(e))`
(`web/repl-session.mjs:140-147`, `:239`). An expected value with holes is
matched part by part against the decoded normal form (`translate.mjs:396`,
`web/translator/evaluation.mjs`), so a hole saves no work; the roadmap
records this. `print(witness(t));` and the REPL's `witness t` normalize in
full too, and only then read the constructor under formal compositions
(`translate.mjs:417-423`). Only the `nonempty` and `empty` assertions infer a
type without normalizing.

`computable def` checks only that a declaration uses no assumption
(`translate.mjs:789-792`). An `evaluate … expecting _;` is therefore the
source-level statement that a closed result computes.

The kernel offers exactly two reduction queries, `cc_kernel_whnf` and
`cc_kernel_normalize` (`kernel/src/queries.c:16-32`), both certifying
nothing. The workbench's WHNF and Normalize are the matching `Step` rules,
`CC_STEP_WHNF` and `CC_STEP_NORMALIZE` (`kernel/include/cubical_kernel.h:186-191`),
which run the same strategies inside a checked instruction. The driver asks
for a weak head of any handle through the head query, but its normalize query
accepts only handles the elaborator recorded as derived
(`web/cubical-kernel.mjs:250-263`, `web/cubical-elaborator.mjs:545-546`). A
part of a weak head is not such a handle: for every row of the table below,
the normalize query refuses the first part the walk reaches.

The weak head contracts by eta. `ck_whnf` turns `fun x => f(x)` into `f`
when `x` is not free in `f`, likewise a path lambda `path i => p @ i` and a
level lambda, and continues with the contracted head
(`kernel/src/term_normalize.c:219-243`). The weak head of
`fun (n : UNat) => succ(n)` is the constructor `succ`; the weak head of
`fun (n : UNat) => n` is that lambda.

### Measurements

Measured on main `0b914137` (kernel sources `ee8b2f32`) with
[`probe.mjs`](evaluation-demand-marks/probe.mjs): a fresh checked program
for each query, a fixed budget of 100M ticks; a repeated run gives identical
counters. The rational definitions are the debugging plan's main-only
reproduction: `small_inverse` is `q_inv` of 2/3 and `small_inverse_neg` of
−2/3, without #283, whose `bq_inv(-2/3)` they stand for. The walk is the
value form proposed below, taken by head queries: weak heads through pairs,
injections and constructor arguments, stopping at lambdas, path lambdas,
types, formal compositions and neutral heads.

| Definition | Weak head | Value-form walk | Full normal form |
| --- | --- | --- | ---: |
| `two_thirds` | constructor, 10,692 ticks | 16 heads, 11,527 ticks | 3,528,706 ticks |
| `small_inverse` | constructor, 12,669 ticks | 16 heads, 27,918 ticks | 71,478,538 ticks |
| `small_inverse_neg` | constructor, 21,657 ticks | 16 heads, 39,177 ticks | 72,202,363 ticks |
| `euclid(3)` | pair, 134 ticks | 21 heads, 151,363 ticks | 221,976 ticks |
| `euclid(4)` | pair, 134 ticks | `K344` at the fourth head, 648,690 ticks | `K344`, 649,818 ticks |
| `euclid(4).1` | `succ` applied, 220 ticks | `K344` at the third head, 648,691 ticks | `K344`, 648,696 ticks |

Each rational walk reaches 11 constructors and 4 pairs and stops at one
lambda, the nonzero certificate. The data is cheap; the 3.5M of a literal is
its retained sort annotation, and the inverse's 71.5M is its certificate's
body under that binder, as the debugging plan attributes them. Nothing in
this note makes the full normal form smaller.

The Euclid rows say something else. The prime of `euclid(4)` cannot be
computed by either query: after two `succ` heads, the head of `i`, obtained
from `prime_divisor_exists`, exceeds the syntax-depth guard (`K344`); a unary
numeral of 512 or more cannot be built at all, as the baseline's `2 * 256`
shows. Skipping the certificate therefore does not make
`evaluate euclid(4) expecting (5, _);` succeed. That needs an evaluator
change, packed numbers (EVAL6) or a representation without the depth limit,
and EVAL5's Euclid acceptance depends on it; the marks do not provide it.

## Proposal

Three demand levels, written where evaluation is requested, by analogy with
Haskell's bang pattern and `$!` for weak head normal form and `$!!` and
`deepseq` for full normal form:

| Mark | Demand on the marked part | Kernel query |
| --- | --- | --- |
| none | as far as the pattern or the printer observes it | head queries on observed positions |
| `!` | its weak head, whether or not anything observes it | `cc_kernel_whnf` |
| `!!` | its full normal form | `cc_kernel_normalize` |

Grammar, in a file:

```text
evaluate [! | !!] term expecting pattern ;
print(evaluate([! | !!] term));

pattern ::= _ | ! pattern | !! pattern
          | (pattern, pattern) | left(pattern) | right(pattern)
          | c(pattern, …) | c | typed(T, pattern) | expression
```

and in the REPL, where `evaluate` needs no expected value:

```text
evaluate [! | !!] term ;
[! | !!] term ;            a term alone, as today, is print(evaluate(term))
```

`!` is not a token today: the scanner splits it off as one character and
`tokenize` refuses it with `E106: Unexpected character !`
(`web/cubist/parser.mjs:13`, `:28-33`). DM1 adds both marks to the accepted
tokens, `!!` among the multi-character ones so that it is one token. The
marks are prefix forms read only directly after `evaluate`, after
`print(evaluate(`, and at the start of a pattern, never term formers, so
nothing about them reaches the kernel but the queries they select.

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

A part is read by its type, never by its weak head's node kind: after eta a
function's weak head can be a constructor (`succ` above) or another head, so
a constructor pattern applies only at the declared type, as
`evaluation.mjs` already requires. At a higher inductive or truncated type a
weak head can be a formal composition rather than a constructor; a
constructor pattern does not match it, as today.

**A bare `_` is refused.** `evaluate e expecting _;` would demand nothing and
check only the type, silently turning today's computability statement into
none. It is an error whose message asks for `!_`, a weak head, or `!!_`, a
full normal form. A pattern with a pair, an injection or a constructor at
its top still demands that head.

Printing is an observation too. The REPL's `evaluate e` and
`print(evaluate(e));` print the **value form**: weak heads descended through
constructor arguments, pair components and injection values, stopping at
term lambdas, path lambdas, types, formal compositions and neutral heads,
which are shown as suspended. How a suspended part prints is open question 1
below.

**`!p`.** The part is reduced to its weak head before `p` is matched. With
`_`, the head query must succeed and nothing more is asked. At the top, the
REPL's `evaluate !e;` and `print(evaluate(!e));` print the weak head with its
arguments unreduced, which is the workbench's WHNF view in source form. `!`
is not a no-op on a lambda: the weak head contracts it by eta when it can
and continues with the result, so
`print(evaluate(!(fun (n : UNat) => succ(n))));` prints `succ`. Only a
lambda that does not contract is its own weak head.

**`!!p`.** The part is fully normalized and `p` is matched against the
normal form as today. `expecting !!_` is today's `expecting _`, and in the
REPL `evaluate !!e;` is today's `evaluate e;`.

**Normalizing a part.** The normalize query accepts only derived handles, and
the parts a walk reaches are not derived, so `!!` and expression leaves below
the top need a decision in DM2: either record the parts of a weak head
computed from a derived handle as derived, which holds for closed well-typed
terms by subject reduction but changes the driver's guard and must be
reviewed as such, or re-derive each demanded part by elaborating its access
path from the evaluated term (projections, and a `match` for a constructor's
field), which checks it again at the cost of repeated elaboration. This is
open question 3.

**What `!` does not say.** `!` makes no claim about a proof. The inverse's
certificate is a lambda, so `!` on it checks nothing; only `!!` says that a
certificate normalizes. The reference must say this plainly so that `!` is
not read as a computability check for certificates.

**Failure contract.** Each demanded query carries the session's budget and
deadline, and budget, deadline and resource stops (`K344` included) are
reported as today, with the part of the pattern whose demand failed. An
unmarked position with no observer requests nothing, so it cannot fail.
Closedness and the assumption check on the evaluated term are unchanged. The
kernel's isolation property is unchanged: queries certify nothing, and a
cached weak head or normal form changes no instruction's acceptance.

**Lints**, in the style of the unneeded-binding lint: `!` directly on a
pair, injection or constructor pattern is redundant with that pattern's own
head demand, and any mark under `!!` is redundant. `! !p` is refused with a
message that suggests `!!p`, so that a space never weakens a demand.

**`witness`** keeps its specification (L2.9b) and its cost. It normalizes the
truncation in full and then reads the constructor under formal compositions,
so it is a `!!` followed by that readout, and its outcomes do not change. A
weak-head readout would be a separate change with its own failure contract.

## Why three levels and not two

The two marked levels are the kernel's two queries and the workbench's two
`Step` rules; the syntax exposes what exists rather than inventing a third
reducer. `!` earns its place at the top of `evaluate` as the inspection view,
and in a pattern as the check that a part reaches some canonical head without
naming it. `!!` keeps the normalization engine testable from source: every
full-normalization gate in the NUM2 contracts is written with it, so the
lazy default cannot silently weaken a gate.

## Migration

**Wildcard gates.** Every existing `expecting _` is classified as a value
check, which becomes `!_` or a constructor pattern, or as an engine gate,
which becomes `!!_`; none can stay bare. On main the form occurs once in the
contracts (`tests/fixtures/contracts/binary_integer_domain_contracts.cubist:43`),
once more in `tests/fixtures/quotient-normalization.cubist`, three times in
`docs` (the runtime roadmap and the rational normalization report), never in
`cubist-tests`, three times in `tests/normalization-sharing.test.mjs` and
three times in `tools/substitution-cost-probe.mjs`; #283 adds
`normalize_wide_inverse` with it. The non-wildcard patterns, 33 in
`cubist-tests` and 10 in the contracts, are expression leaves or constructor
patterns and keep their meaning.

**Printed values.** `cubist-tests` has 102 `print(evaluate(…))`. Fifteen
expect, in their `// Output:` comments, a value the value form would
suspend: functions in 13 printer tests (`box_notation`, `glue_printed`,
`induction_printed` twice and `printer_lint` nine times), the type `0 = 0`
and the path `refl(1)` in `quotient_effectiveness`. These test the normal
form and become `print(evaluate(!!e))`. The other 87 print data; DM3 runs
them unmarked, and each keeps its text or is classified like the fifteen.
The reference's seven printed examples are classified the same way: the
cubical chapter's `join_by_box` prints a function and becomes `!!`; the
checking, kernel computation and theories chapters print numbers.

**Baseline.** The evaluation baseline's `repl`, `print` and `pattern`
workloads are re-recorded with `--write`, each with a `!!` twin so that the
recorded engine outcome stays measured. `euclid-4-pattern`,
`evaluate euclid(4) expecting (5, _)`, keeps its `K344` outcome: the failure
is at the prime, not the certificate.

**Text.** The roadmap's sentence that patterns match the full normal form,
the work plan's L2.9a row and the language reference (below) are updated
with the three levels. The formatter and the lint learn the tokens, the
redundancy rules and the refusals.

## Language reference

The implementation is complete only when the
[language reference](../../../web/language.html) documents it, with examples
the reference test checks, incorrect ones carrying their `// Error:`:

- chapter 12, [`evaluate`](../../../web/reference/assumptions.html#evaluate):
  the three demand levels, the value form and its suspended parts, `!` and
  `!!` in patterns, the refusal of a bare `_`, the failure contract, and that
  `!` says nothing about a certificate;
- chapter 13, [checking](../../../web/reference/checking.html), whose list of
  directives shows `print(evaluate(…))`: the marks in that form, and the REPL's
  `evaluate` and term-alone entries;
- chapter 17, [weak-head normal form](../../../web/reference/kernel-computation.html#whnf):
  `!` as the source form of `cc_kernel_whnf`, eta included;
- chapter 18, [errors](../../../web/reference/errors.html): every new message;
- `language.html`'s summary of chapter 12, the REPL help (`replHelp` in
  `web/repl-session.mjs`, and the CLI's), and the proof workspace's quick
  reference.

## Acceptance for the implementation

- In the REPL, `evaluate small_inverse;` on the main-only reproduction prints
  its numerator and denominator with the certificate suspended within
  100,000 query ticks in a fresh program (the probe's walk costs 27,918).
  With #283, `evaluate bq_inv(-2/3);` prints `-3/2` in its notation within the
  same bound.
- `evaluate small_inverse expecting !!_;` reproduces today's counters and
  normal-form digest exactly; the engine gate is unchanged.
- `evaluate euclid(3) expecting (7, _);` completes without forcing the
  certificate. In the REPL, `evaluate !euclid(4);` prints the pair head, and
  `evaluate euclid(4) expecting (5, _);` still stops with `K344` at the prime
  until the evaluator change above; neither the marks nor this acceptance
  claims otherwise.
- `evaluate e expecting _;` is refused with the message above, and
  `print(evaluate(!(fun (n : UNat) => succ(n))));` prints `succ`.
- Every contract and Cubist test keeps its outcome after classification, and
  the baseline fixture carries both twins.
- A lazy result is visibly distinct from a full normal form in the REPL, the
  CLI and the workbench's copied trace, as EVAL5's acceptance requires, and
  forcing a suspended part after a later session operation is either safe or
  a documented expiry error: node handles move when a checkpoint is committed
  or rolled back (`web/cubical-kernel.mjs:288`, `cc_kernel_relocated`).
- The language reference documents the marks as listed above, and its
  examples pass the reference test.

## Work items

| ID | Work | Depends on | Size |
| --- | --- | --- | --- |
| DM0 | This decision record, the open questions answered, the roadmap and work plan rows updated | — | S |
| DM1 | Tokens `!` and `!!`, grammar in `evaluate`, `expecting` and `print(evaluate(…))`, formatter, lints, the bare-`_` and `! !p` refusals | DM0 | S |
| DM2 | Demand-driven matcher over kernel handles: head queries on observed positions, reading parts by type, decoding only observed parts, `!!` and leaves on parts through the answer to open question 3 | DM1 | M |
| DM3 | Value-form printer with suspended parts for the REPL, CLI and workbench; the 87 data prints checked unmarked | DM2, open question 1 | M |
| DM4 | Classification and migration of `expecting _` and of the fifteen printed tests and the reference examples, baseline re-recording with twins, roadmap and work plan text | DM2, DM3 | S |
| DM5 | Report with the acceptance measurements, fresh-session fixed budgets and digests | DM2–DM4 | S |
| DM6 | The language reference chapters, error entries, REPL help and quick reference listed above | DM1–DM4 | S |

## Open questions

1. **Printing a suspended part.** Print it as written under the printer's
   output budget, or elide it with a marker and let the workbench expand it.
   The second keeps printed values short; the first keeps them complete.
2. **Expression leaves.** Keeping them as `!!` on their part preserves
   exactness; a weaker rule, normalizing only as far as comparison needs,
   would be a third demand and is not proposed.
3. **Normalizing a part.** Widen the driver's guard to the parts of a derived
   handle's weak head, or re-derive each demanded part by elaboration. The
   first is cheaper; the second keeps the guard as it is.
4. **`!` in terms.** The marks are read only in the positions above, so a
   view could still bind a postfix `!`, as a factorial `n!`, in terms. Whether
   to allow it, given that a pattern leaf starting with `!` is always a mark.
5. **REPL bindings.** Whether `let x := !!e;` should exist; out of scope here.
