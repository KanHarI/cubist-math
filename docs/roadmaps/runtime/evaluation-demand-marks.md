# Evaluation demand marks: `!` and `!!`

Status: proposed on 2026-10-21 and decided the same day (DM0, the
[decisions](#decisions) below). The marks in `evaluate … expecting` (DM1,
DM2) are implemented in [#304](https://github.com/KanHarI/cubist-math/pull/304),
and the value form of printed values (DM3), with the migration (DM4) and
the reference (DM6), in [#305](https://github.com/KanHarI/cubist-math/pull/305);
the [acceptance report](evaluation-demand-marks/report.md) (DM5), in
[#306](https://github.com/KanHarI/cubist-math/pull/306), measures them
against main. This is the observation
contract that EVAL5 of the
[runtime roadmap](runtime-evaluation-roadmap.md#eval5-demand-only-the-result-being-observed)
requires before evaluation behavior changes. It proposes no kernel change
and no new reduction: the two marks name the kernel's two existing reduction
queries.

It does not resolve decision D1 of the
[rational normalization debugging plan](rational-normalization-debug-plan.md).
D1 asks what a full normal form unfolds, and `!!` below keeps today's full
normal form unchanged, so D1 still bounds every engine gate written with
`!!`. This note takes full normalization out of inspection, patterns and
printing only. The plan now states its contract as `expecting !!_`.

## What evaluation did before the marks

Before #304, every form of evaluation computed the full normal form. In a file,
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
injections and constructor arguments, stopping at term, path and level
lambdas, types, formal compositions and neutral heads.

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
- `typed(T, p)` is `p` read at `T`. `T` and the part's type are compared
  lazily, by their weak heads part by part, and a difference found so
  computes nothing of a part the pattern leaves unobserved. Where that
  comparison cannot tell (eta, a cubical construction), conversion decides,
  and a conversion that fails normalizes both types.
- An expression leaf, as `5` or `nat.(2 + 3)`, demands the part's full normal
  form and compares it with the leaf's, exactly as today: exact
  expected-value checks are preserved, and a leaf is a `!!` on its part.

A part is read by its type, never by its weak head's node kind: after eta a
function's weak head can be a constructor (`succ` above, or `squash` for
`mere_is_prop(U0, UNat)`), so a constructor pattern applies only at the
declared type, as `evaluation.mjs` already requires. A path's weak head is
a path lambda or a path constructor: `loop`, `relate(1, 3, tt)`,
`squash(point(1), point(2))`, a free model's law path. At a higher inductive
or truncated type a closed value can be a formal composition rather than a
constructor: transport in `Circle` gives what today prints as
`hcomp(Circle, base)`. A constructor pattern does not match it, as today,
although `witness` reads through it; decision 6.

**A bare `_` is refused.** `evaluate e expecting _;` would demand nothing and
check only the type, silently turning today's computability statement into
none. It is an error whose message asks for `!_`, a weak head, or `!!_`, a
full normal form. A pattern with a pair, an injection or a constructor at
its top still demands that head.

Printing is an observation too. The REPL's `evaluate e` and
`print(evaluate(e));` print the **value form**: weak heads descended through
constructor arguments, pair components, injection values and a glue value's
base and faces, stopping at
term, path and level lambdas, types, formal compositions and neutral heads,
which are shown as suspended, by a marker naming the kind of head
(`<fun>`, `<path>`, `<level fun>`, `<type>`, `<composition>`,
`<neutral>`; decision 1). A path constructor is a weak head like any
constructor and is shown with its arguments, and an eliminator not yet
applied to a value, which eta makes of `fun (n : UNat) => induction n …`,
is a function. The walk computes parts in the order the printer shows
them, a constructor's fields in source order, and charges each as the
printer does, an applied constructor twice; it stops where the printer's
budget of 4,000 nodes ends, so the printer shows every part it computed, and
a value form is shown whole, never cut at a width. It stops too at the depth
of the kernel's own syntax, 512 levels (`K344`), as deep as any printer is
given a term; data past either is not computed and is shown as `…`. A
constructor is shown by its name, without its type's parameters. Each head the walk computes is shallow, so it
can show data whose normal form is too deep to build:
`print(evaluate((2 * 255, 2 * 255)))`, at type `UNat and UNat`, shows
`(510, 510)`, where `!!` stops with `K344`.

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
decision 3.

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

## Coverage of the language

[`constructs.json`](evaluation-demand-marks/constructs.json) holds one closed
example of every construct that yields a term to evaluate, with its weak
head on main `0b914137`; `node probe.mjs constructs` runs it at a fixed
budget of 20M ticks. It has 197 examples:

- 64 declaration forms: every `def` form, `computable def`, implicit and
  universe-generic parameters, recursion, inductive and higher inductive
  types with point, path and square constructors, truncations and
  quotients, theories with their models, fields, parents, homomorphisms and
  isomorphisms, `initial`, `free`, `notation` and `section`;
- 98 term forms: lambdas, application, named arguments and holes, pairs,
  projections, `unpack`, injections, every `match` and `induction` form,
  path and interval forms and the path builtins, boxes and `comp` and `fill`
  at each type former, Glue, `FunExt`, `ua` and `UnivalenceBeta`, the
  assumption builtins, universes and type formers, literals and operators;
- 26 proof-block statements, as the definitions they build;
- 9 evaluation directives and REPL forms.

Every example elaborates, has a weak head, and completes its value-form
walk. No walk met a neutral head. The weak heads are:

| Weak head | Examples | Among them |
| --- | ---: | --- |
| constructor, applied or alone | 104 | numerals, `cons`, `class`, `b_positive`, and seven path constructors: `loop` (also from `path i => loop @ i`), `relate(1, 3, tt)`, a square, both squashes, a free model's law path |
| path lambda | 30 | `refl`, `++`, `cong`, `ua`, `FunExt`, proofs by `rfl`, `calc`, `rw` and `simp` |
| lambda | 16 | functions, partial applications, laws |
| pair | 12 | tuples, dependent pairs, theory models |
| `tt`, `left`, `right` | 10 | including `comp` at `Unit` and at a sum |
| type | 18 | universes, Π, Σ, sums, paths, declared sorts, `Unit` from `3 > 2`, the empty Glue of `comp` in a universe, a level Π |
| level lambda | 4 | `List`, `Monoid`, universe-generic definitions unapplied |
| formal composition | 3 | transport in `Circle` and in two truncations |

In each of the 105 walks that reached a part, the normalize query refused
that part, so decision 3 is not hypothetical. `!!` completes on every
example except seven. The four that depend on an assumption (`TruncateIntro`,
`Truncate`, `LEM`, `ExcludedMiddle`) are refused by evaluation today
(`E324`) and stay refused under every mark, although the kernel computes
their heads. Three exceed the fixed 20M budget although today's evaluation,
with its growing budget, completes them: `rationals.(2/3)`,
`rationals.(0.5)` and the theory value `integers.additive_`. Their
value-form walks cost 3,060, 4,366 and 21,999 ticks.

The constructs with no closed example need no mark, since the marks apply
to terms:
- `import`, rule registrations and test pragmas;
- interval points and face formulas, which occur only under a path binder or
  in a box;
- `hcomp` and `transp`, which have no source syntax;
- the forms that never reduce: `print(typeof(…))`, `print(inspect(…))`, the
  REPL's `typeof` and `let`, and the CLI's `beta` and `delta`;
- `evaluate nonempty` and `empty`, which only infer.

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
In #305 all 87 keep their text unmarked, and the fifteen are the only
prints marked.
The reference's seven printed examples are classified the same way: the
cubical chapter's `join_by_box` prints a function and becomes `!!`; the
checking, kernel computation and theories chapters print numbers. So are
its REPL transcripts: the first-proof and terms chapters evaluate proofs,
functions and the types `2 < 7` and `7 < 2` to show the terms they are,
and those nine entries become `evaluate !!…`.

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
- Every example in `constructs.json` evaluates unmarked, under `!` and under
  `!!`: `!` gives the weak head recorded there, unmarked printing completes,
  and the four assumption examples are refused with `E324`.
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
| DM0 | This decision record, the open questions answered, the roadmap and work plan rows updated. **Done** in #304 | — | S |
| DM1 | Tokens `!` and `!!`, grammar in `evaluate`, `expecting` and `print(evaluate(…))`, formatter, lints, the bare-`_` and `! !p` refusals. **Done** in #304, and in `print(evaluate(…))` and the REPL in #305 | DM0 | S |
| DM2 | Demand-driven matcher over kernel handles: head queries on observed positions, reading parts by type, decoding only observed parts, `!!` and leaves on parts through decision 3, tested on `constructs.json`. **Done** in #304 | DM1 | M |
| DM3 | Value-form printer with suspended parts for the REPL, CLI and workbench; the 87 data prints and `constructs.json` checked unmarked. **Done** in #305; the workbench shows no evaluation, and its trace already names its WHNF and Normalize steps | DM2, decision 1 | M |
| DM4 | Classification and migration of `expecting _` and of the fifteen printed tests and the reference examples, baseline re-recording with twins, roadmap and work plan text. **Done**: `expecting _`, the pattern workload's twin and the patterns' text in #304, the rest in #305 | DM2, DM3 | S |
| DM5 | Report with the acceptance measurements, fresh-session fixed budgets and digests. **Done** in #306: [report.md](evaluation-demand-marks/report.md), with [`report.mjs`](evaluation-demand-marks/report.mjs); it found the search's guide pruned in #304, since fixed there | DM2–DM4 | S |
| DM6 | The language reference chapters, error entries, REPL help and quick reference listed above. **Done**: patterns and their marks, in chapters 12, 13, 17 and 18, in #304, and printing, the REPL help, the REPL page and the quick reference in #305 | DM1–DM4 | S |

## Decisions

Decided on 2026-10-21, before DM1, answering the open questions as they
were posed:

1. **Printing a suspended part.** A marker names the kind of weak head the
   value form stopped at: `<fun>` for a term lambda, `<path>` for a path
   lambda, `<level fun>` for a level lambda, `<type>` for a type (a
   universe, Π, Σ, a sum, a path type, a declared sort, Glue, a level Π),
   `<composition>` for a formal composition (`hcomp`, `comp`, `transp`) and
   `<neutral>` for a neutral head, which no closed, assumption-free term
   should reach and is shown, not refused. A position a pattern never
   observed, whose kind is not known, is `<unevaluated>`: an evaluation
   shows its value as far as the pattern computed it, as
   `(7, <unevaluated>)` for `evaluate euclid(3) expecting (7, _);`. Every
   marker is in angle brackets, so nothing in them is a value. The value
   form's walk stops where the printer's output budget ends. Suspended parts
   are not retained, so nothing is forced after a later session operation:
   a part is seen with `!!` or a pattern, evaluated again.
2. **Expression leaves** stay a `!!` on their part, as proposed.
3. **Normalizing a part.** The driver's guard is widened: the elaborator's
   `derivedHead` records the weak head of a derived handle, and that head's
   data parts (a pair's components, an injection's value, a constructor's
   arguments), as derived, so that normalize accepts them. The weak head of
   a closed, well-typed term is well-typed by subject reduction, and its
   data parts are closed, well-typed subterms, so their normalization
   terminates as the term's does; a query certifies nothing, so no
   instruction's acceptance depends on it. The head of a handle that is not
   derived records nothing.
4. **`!` in terms.** Not allowed: the marks are read only after `evaluate`,
   in `print(evaluate(…))` and at the start of a pattern's part; elsewhere a
   mark is refused (`E004`), and inside an expression of a pattern too
   (`E484`).
5. **REPL bindings.** Out of scope.
6. **Patterns through formal compositions.** A constructor pattern does not
   read through a formal composition, as before: such a part is shown as
   `<composition>`, and `!_` and `!!_` still check that it computes. Whether
   an empty-system composition on a declared sort should compute to its base
   is decision D2 of the debugging plan; if the kernel makes it so, patterns
   match with no rule of their own.
