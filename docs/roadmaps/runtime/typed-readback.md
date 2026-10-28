# Typed readback: runtime values as kernel terms (EVAL5)

Status: decided on 2026-10-28: the user accepted every recommendation of
[section 11](#11-decisions) (D1–D6). Written on
[#324](https://github.com/KanHarI/cubist-math/pull/324)'s branch at
`6f5604e9`. This is step 2.4 of the work plan's
[first actions](../work-plan.md#first-actions): typed readback, with the
written readback correspondence that EVAL3/EVAL4's acceptance asks for and
the applicable part of EVAL8's review. It also answers the condition of the
decision of 2026-10-26 that constructor patterns stay on the kernel's queries
"until typed readback and the applicable EVAL8 review"
([REPL integration](runtime-evaluation-roadmap.md#repl-integration)).
Nothing here is implemented yet, and nothing here changes the kernel. W1
and W2 are next ([8](#8-work-items)).

## Summary

- **Readback is syntax-directed; the type is for checking.** The runtime
  keeps every annotation as a cell and never erases one, so a runtime value
  can be read back into a closed kernel term without consulting its type:
  data by its constructor, and a closure as the β-redex it stands for. The
  type enters only where the kernel is asked to check the term.
- **No verdict should consume a readback (D1, recommended).** For a verdict
  the kernel would have to establish `e ≡ R(e)` itself. Measured today
  ([section 1.4](#14-what-a-re-check-costs-today)), that costs 37 times the
  kernel's own folded normal form for `euclid(3)` and about 1,800 times it
  for `2/3 + 1/6`. It also fails wherever the kernel's own reduction fails
  (K344 for `count_into(2 * 255, 0)`). Readback buys nothing for patterns,
  exact expected values or the `!!_`/`!!!_` gates, which stay on the
  kernel's queries.
- **Where readback helps:** a fallback in mid-computation (W2): a node the
  runtime does not execute, such as a composition, is read back and its
  weak head asked of the kernel, and the runtime goes on. Today the whole
  walk restarts. Since [#326](https://github.com/KanHarI/cubist-math/pull/326)
  every library Euclid value form falls back at NUM1's transports, so this
  matters most. Readback also gives printed `!!` normal forms partly
  computed by the runtime (W3, if measurement shows a gain), and a strong
  test oracle for the runtime itself: `normalize(R(e))` must equal
  `normalize(e)`.
- **`!!!`, `!`, `witness`, patterns and exact expected values stay on the
  kernel's queries.** This narrows the work plan's expectation that `!!!`
  and exact expected values "can then go through the runtime"
  ([section 12](#12-findings-against-the-roadmap-and-the-work-plan)).
- **Session safety holds by construction.** Readback writes kernel syntax
  only while the bridge's handle generation is the query's. User paths
  retain no runtime value across an entry, and `expired` is the documented
  outcome for an API that does.

## 1. What exists today

### 1.1 What the runtime holds

`RuntimeQuery` (`web/cubical-runtime.mjs`) executes a closed typing
judgement (`judged`). Its cells are syntax thunks, a code handle with a
linked environment, or application thunks. Forcing a cell updates it to its
value and drops its code and environment (the `update` frame of `#run`).
The values are:

| Value | Holds |
| --- | --- |
| `Con` | signature, constructor index, the instance cell, the argument cells so far (a partial application has fewer than its arity) |
| `Pair` | type, first and second cells |
| `Inl`, `Inr` | type and item cells |
| `Point` | nothing |
| `Lam`, `LLam` | binder symbol, body code, environment, and the binder's annotation as a cell (`domain`) |
| `PLam` | body code and environment only: its dimension and annotation are not kept |
| `Type` | nothing: a type former's parts are dropped |
| `Elim` | signature, motive cell, clause cells |
| `Lift` | a higher-order recursive hypothesis: eliminator, position, arguments still to take |

An environment frame is `{parent, symbol, cell}`, made by β only (the
`apply` frame). It does not record the binder's annotation. Every cell in
an environment stands for a closed term: the judgement is closed, and the
machine enters a binder only by applying it. No dimension is ever bound,
since applying a path is unsupported. So a readback cannot capture a
variable, and never touches an interval formula.

Annotations are cells and are never erased: pair and injection types,
constructor instances, binder domains and eliminator motives. This keeps
the roadmap's contract that no proof or annotation is erased
([types and computation](runtime-evaluation-roadmap.md#types-and-computation)).
It is also why readback needs no type to produce a term.

### 1.2 What the kernel accepts from untrusted code

- **Building syntax:** `cc_kernel_term` (`kernel/src/term_store.c`) builds
  raw syntax, interned when syntax is shared. It takes no step and makes no
  judgement, and refuses a node deeper than 512 (`K344`, in `ck_make`).
- **Weak heads:** `cc_kernel_whnf` takes any handle; it "certifies nothing,
  including under free names" (`kernel/include/cubical_kernel.h`).
  `CubicalKernel.head` (`web/cubical-kernel.mjs`) has no guard.
- **Normal forms:** `normalize` and `normalizeFolded` accept only the
  handles in `derivedHandles`. The elaborator's `derivedHead` widens that
  set to a derived weak head's data parts, by the demand marks' decision 3.
  A raw readback term is refused.
- **Equality:** an equality judgement is built from reflexivity by targeted
  `Step` rules (β, δ, ι, path, normalize, weak head, face, Glue, split),
  `Replace`, `Symmetry`, `Transitivity` and `Convert`. The untrusted
  `InstructionDriver` searches for these steps. Its heuristic first
  normalizes a long closed computation (`heuristicPolicy`, `settle` in
  `web/cubical-instruction-driver.mjs`).

### 1.3 How each observation is computed and decided

| Observation | Computed by | Verdict decided by |
| --- | --- | --- |
| Value form: `evaluate e;`, `print(evaluate(e));` | the runtime; on unsupported demand, the kernel's head queries redo the whole walk from the start (`valueFormOf`, `web/translator/translate.mjs`) | none: a display |
| `!e` | `cc_kernel_whnf` | none |
| Printed `!!e`, `!!!e` | `normalizeFolded`, `normalize` | none |
| Patterns, `!_`, `!!_`, `!!!_` | the kernel's head and normalize queries (`demandQueries`), matched in JavaScript (`observe` in `web/translator/evaluation.mjs`) | the C queries and the untrusted matcher. An expression leaf compares two normal forms by an instruction-checked conversion (`scope.equal`) |
| Exact expected value | `normalForm` of both sides, a query (`translate.mjs:408`) | an instruction-checked conversion of the two normal forms (`translate.mjs:432`, `NativeCubicalElaborator.equal`). `e ≡ nf(e)` is not derived |
| `witness` | the full normal form, a query, read in JavaScript | the kernel's typing of the witness (`scope.accepts` in `witnessOf`) |

No verdict today is derived by instructions from the evaluated term itself.
Every verdict rests on the reviewed C reducer's queries, which certify
nothing formally. A runtime result in a verdict would replace those queries.

### 1.4 What a re-check costs today

How much would it cost the kernel to check a readback `r` of `e` by today's
means? Here `r` is the best readback the runtime could produce for `!!`:
the kernel's own folded normal form of `e`. Each row ran in its own
rolled-back checkpoint, so the kernel's caches were cleared
(`cc_kernel_rollback`). The run was a scratch probe, not retained, on
`6f5604e9` with a fresh `make wasm`, Node 24.13.0, macOS arm64 (Apple M3
Pro). Each workload ran once in one process, while other jobs loaded the
machine (load average 17–22). The counters are the kernel's; the times are
not speed claims. Its core, after `def probe_e := e;` in a REPL session:

```js
const e = checker.definitionViews.get("probe_e").term;
const r = checker.normalForm(checker.evaluated(e).expression); // folded, a query
checker.infer(r);       // the kernel's typing of r: instructions
checker.equal(e, r);    // e ≡ r by the driver's conversion: instructions
```

| Workload | Kernel's value-form walk | Folded normal form | Full normal form | Typing `r` | Checking `e ≡ r` |
| --- | --- | --- | --- | --- | --- |
| archive `euclid(3)` | 151,398 ticks | 11,342 ticks | 211,194 ticks | 648 instructions, 125,896 steps, 5,037 ticks | 759 instructions, 362,644 steps, 62,030 ticks |
| `count_into(2 * 255, 0)` | `K344` after 44,475 ticks (the runtime shows `510`) | `K344` | `K344` | `r` from `2 * 255`: 516 instructions, 1,553 steps | `K344` |
| `2/3 + 1/6`, `binary_rationals` | 47,801 ticks | 26,013 ticks | 3,509,337 ticks | 12,812,491 instructions, 14,571,311 steps, 415,614 ticks, 26.0 s | 17,778,995 instructions, 46,220,385 steps, 677,691 ticks, 36.2 s, peak 4,051 MiB |

Steps and ticks are both units of the kernel's step budget. Re-checking
by conversion costs far more than the kernel computing the answer itself:
424,674 steps and ticks against 11,342 for `euclid(3)`, 37 times, and
46,898,076 against 26,013 for `2/3 + 1/6`, about 1,800 times. And it fails
exactly where the kernel's reduction fails.

`2/3 + 1/6`'s folded normal form is 993 handles, but 5,439,106 nodes as a
tree. Its decoded term keeps that sharing: 1,015 JavaScript objects.
Typing it still took 12.8M instructions, of the order of the tree's size,
so the derivation fails to share somewhere. Where is not attributed. The
same typing is part of today's exact expected values, since
`NativeCubicalElaborator.equal` first infers its left side's type:
`evaluate 2/3 + 1/6 expecting 5/6;` fails with `E326` (the representatives
differ) after 27,678,916 instructions and 48.0 s, peaking at 4,738 MiB. The binary
contracts compare rationals only through `binary_rational_equal(…)
expecting bnat.(1)`.

## 2. Who checks a readback (D1)

**Precisely:** the runtime stays untrusted as long as no verdict, judgement
or instruction consumes a runtime result. Under that rule the kernel
re-checks nothing about a readback. Correctness of the readback is then a
testing obligation ([W1](#8-work-items)), as the value forms' is today.

If a verdict were to consume `R(e)`, the kernel would have to establish
`e ≡ R(e)` by instruction, or the part of it the verdict observes. A
typing check `R(e) : A` is not enough, as the roadmap's
[trust contract](runtime-evaluation-roadmap.md#trust-and-lifecycle) says: a
well-typed `6` passes where `5` is the value.

Options:

- **A. Display only (recommended).** Readback feeds displays and the
  kernel's queries (W2, W3). Verdicts stay on the kernel's queries as today,
  and patterns stay there with them.
- **B. Reviewed runtime verdicts.** After EVAL8's review, a pattern's
  skeleton is decided by the runtime and its leaves by conversion against
  `R(part)`. This is a new and weaker trust tier: a directive's verdict
  would rest on a JavaScript evaluator, reviewed once, instead of the C
  reducer. It would let `evaluate euclid(4) expecting (5, _);` pass on the
  archive. Not recommended.
- **C. Kernel re-check by conversion.** Verdicts would become
  instruction-derived from `e`, which is stronger than today's
  query-based patterns. But the cost is [section 1.4](#14-what-a-re-check-costs-today)'s
  (37 to about 1,800 times the folded normal form), and it fails where the
  kernel's reduction fails. It buys trust, not speed. Not recommended until
  the driver's sharing defect above is understood.
- **D. Runtime-guided derivation.** The runtime's trace would direct
  targeted `Step`s in call-by-value order, with read-back values put in
  place by `Replace` and chained by `Transitivity`: existing instructions,
  no new rule. The kernel would check every step, and each β would
  substitute a computed value rather than an unevaluated argument. Such
  substitutions are what the roadmap traces the archive Euclid's K344 to,
  and `tools/runtime-repl-probe.mjs` traces `count_into`'s. A research
  option: measure it (W5) before reopening D1.
- **E. A trusted environment machine in C.** It would make the kernel's
  own queries cheap, but it grows the trusted kernel by a second reducer
  and its readback. Not recommended: the user wants the kernel small.

## 3. The readback correspondence

### 3.1 Interpretation

As in the [shared runtime report](../../reports/shared-runtime-evaluation.md#reduction-correspondence-for-the-fragment),
an environment stands for a simultaneous substitution of the closed terms
its cells stand for. A syntax thunk stands for its code under that
substitution, and an application thunk for the application of what its two
cells stand for. Readback `R` makes the substitution explicit, as β-redexes
(D2), so that it never has to be performed in JavaScript.

### 3.2 By value kind

`R(cell)`:

- a **forced cell** whose value is data (`Con`, `Pair`, `Inl`/`Inr`,
  `Point`) is read back by its value, below;
- a **forced cell** whose value is not data is read back by its value; for
  a normal-form readback it is read back by its origin instead
  ([3.4](#34-origins-provenance-and-folding));
- an **unforced syntax cell** is `closure(code, env)`;
- an **unforced application cell** is `App(R(fn), R(argument))`;
- a **cell pending** when a fallback leaves a force keeps its code and
  environment, since a failure resets it (`#run`'s `catch`), and is a
  closure too.

| Value | At type | Read back as |
| --- | --- | --- |
| `Con` `c` with arguments `a1…ak` | its declared sort `Sort(s; …)`, or a Π while partial | `App(…App(Con(c; R(instance)), R(a1))…, R(ak))`, in the kernel's argument order |
| `Pair` | Σ | `Pair(R(type), R(first), R(second))` |
| `Inl`, `Inr` | a sum | `Inl(R(type), R(item))`, likewise `Inr` |
| `Point` | `Unit` | `Point` |
| `Lam`, `LLam`, `PLam`, `Type`, `Elim` | Π, level Π, a path type, a universe, Π | `closure` of the node the value was made from: the runtime does not evaluate under it. Values are to keep that node: `PLam` and `Type` drop what readback needs today |
| `Lift` | Π | refused (`unsupported`): its λ needs the domains of the constructor's field telescope at the instance, the one place readback would need types ([3.7](#37-what-readback-refuses)) |

A first-order hypothesis is an application cell `#apply(eliminator,
position)`. It reads back as `App(Elim(…), R(position))`, which is
`ck_eliminate`'s hypothesis. A clause applied by ι is application cells
too, and reads back as the clause applied to the constructor's arguments
and hypotheses, as `ck_eliminate` builds it.

### 3.3 Closures as redexes (D2)

`closure(code, env)`:

- If no variable free in `code` is bound in `env`, it is `code`, the
  original kernel handle. Every closed definition body is such a code.
- If `code` is a variable `x`, it is `R(env(x))`.
- Otherwise it nests `App(L(x; R(annotation_x), …), R(cell_x))` over
  `code`'s free variables. Each free variable takes its nearest binding, as
  the machine's `lookup` does. `L` is a `Lam` or `LLam` like the binder β
  contracted, and `annotation_x` is that binder's `domain` cell. Environment
  frames record the β'd value for this (a one-field change at the `apply`
  frame).

Each binding's annotation is read back under its own environment, so it is
closed. The order of the nest therefore does not matter, and a readback
redex is well typed whenever the β the machine did was. Free-variable sets
are computed once per copied node, binding as `ck_term_free` does (`Pi`,
`Lam`, `Sigma`, `LPi` and `LLam` bind their payload in their second child),
within the query's budget. This is the pruning that EVAL4's
closed-environment item needs for retention as well.

The alternative is to substitute in JavaScript. That needs a capture- and
shadowing-aware substitution over kernel syntax, a walk of the code for
every code and environment pair, and level canonicalization:
`ck_level_instantiate` canonicalizes the levels it substitutes
(`kernel/src/levels.c`), and a JavaScript copy of that algebra would
duplicate the kernel. Redexes need none of these. Their price is that `R`'s
terms are not shown as they are: every display normalizes them in the
kernel first. So `!e` stays on the kernel (section 4).

- **Levels:** a level binding is a level redex
  `LApp(LLam(l; …, body), level)`. The kernel contracts it with canonical
  levels, so no level arithmetic is done in JavaScript.
- **Names:** the readback redexes reuse the checked binders' symbols. No
  name is invented, and the display's one naming pass
  (`web/display-naming.mjs`) settles names on the normal form shown.
- **Dimensions:** the fragment binds and substitutes none. Dimension
  binders and face formulas are copied, as written, inside the closures
  that hold them. All dimension work stays with the kernel.
- **Annotations:** read back as closures only when `R` reaches them, and
  never evaluated.

**Why "typed":** the term `R` builds carries every annotation that the
kernel's typing needs, taken from the checked syntax, so it is a closed
term well typed at the value's type. No type is consulted to build it.
Type-directed η-expansion, the textbook typed readback, is not used: the
kernel's heads are η-contracted (`ck_whnf`), and η-long terms would disagree
with its normal forms.

### 3.4 Origins: provenance and folding

The roadmap asks readback to keep "the provenance of certificates". A
certificate is a non-data part, such as `2/3 + 1/6`'s
`bint_mul_nonzero(class(…), class(…), fun (p : …) => …)`. Read back by its
value, it is a λ, and folding it would show that λ's body, not the lemma.

So a query made for normal-form readback keeps, for each forced cell whose
value is not data, the code and environment it was forced from: its
origin. It reads that cell back as `closure(origin)`. Value forms need no
origins and keep none, so their retention does not change.

The argument that the folding then agrees runs on the kernel's own
semantics. `folding_head` (`kernel/src/term_normalize.c`) watches the steps
of a part's reduction and remembers the first definition spine it passes:

- `closure(origin)` β-reduces to the kernel's term at that position, except
  that parts the runtime forced to data stand computed.
- Data computes in full under both normal forms.
- A readback redex is a β step through no definition.
- So the reduction passes the same definition spines, and the kernel keeps
  the same definitions folded.

The tests in W1 must confirm this: differential agreement on every
construct, and a mutation that reads values instead of origins must fail
them.

`!!` is then the kernel's folded normal form of `R(root)`, and `!!!` its
full normal form. `R` itself is neither: it is the value as far as the
runtime computed it.

### 3.5 Sharing

- `R` is memoized per cell for the query's generation.
- A closure reuses its code's handle as it is, and the kernel's interning
  merges identical syntax.
- The output has one node per cell reached, plus two per closure binding.
  So it is a DAG of the runtime's reachable graph, never a tree.
- `R` is never decoded to JavaScript. Only the final normal form is,
  under the printer's budget, and that decoding keeps sharing (1,015
  objects for 993 handles, [1.4](#14-what-a-re-check-costs-today)).
- No readback path goes through `checker.infer` or `checker.equal`, whose
  derivations cost the tree.

### 3.6 What readback guarantees, to be tested

1. `R(c)` is a closed kernel term, well typed at `c`'s type, given a
   correct runtime (subject reduction).
2. `R(c) ≡ t`, the term `c` stands for: the readback redexes are β, and the
   runtime's own steps are the kernel's.
3. Their full normal forms are α-equal wherever both complete, by
   confluence and unique normal forms. This is the oracle.
4. With origins, their folded normal forms are α-equal
   ([3.4](#34-origins-provenance-and-folding)).
5. Its size is linear in the cells reached ([3.5](#35-sharing)).
6. It captures nothing, and its nearest-binding rule is the machine's
   lookup.

Equality in tests is `cc_kernel_alpha_equal`, syntax only. A test never
decides by conversion.

### 3.7 What readback refuses

- **`Lift` values**, as `unsupported`. Reading one back needs the domains
  of the field's Π telescope at the instance, from the admitted signature,
  as `kernel/src/signatures.c` instantiates them. This is deferred until a
  workload needs it.
- **Any write after the generation moved**, as `expired`
  ([section 7](#7-session-safety)).
- **A term deeper than 512**, with the kernel's own `K344`: a unary numeral
  past 510 cannot be read back, just as the kernel cannot build one.
- **Work and cells past the query's limits**, as for any observation.

## 4. Which observations move, and in what order

| Observation | After this plan | What the kernel still checks | Expected effect, on the measured workloads |
| --- | --- | --- | --- |
| Value form | runtime, with the per-node fallback (W2) instead of a restart | nothing: no verdict | Every library Euclid value form, for any `n`, falls back after about 65,000 runtime steps today (#326's report). With W2 the runtime keeps the walk, and the kernel computes only the transports' heads. The effect is unmeasured (M2). In `factorial(40)` (51M kernel ticks) and the 37 constructs that fall back, the kernel would compute only the nodes the runtime does not. |
| Printed `!!e`, REPL `evaluate !!e` | runtime data, then `R`, then the kernel's folded normalization (W3), only if M3 shows a gain | nothing: a display | Gains where data dominates: the wide binary-integer product (kernel walk 6,962,688 ticks, runtime 4,329,313 steps) and the archive Euclid (kernel `K344`). None expected for `2/3 + 1/6` (kernel folded normal form 26,013 ticks). |
| Printed `!!!e` | the kernel's queries | — | Proofs dominate (`2/3 + 1/6`: 3,509,337 ticks full against 26,013 folded), and the runtime adds nothing until it evaluates under binders and executes cubical terms (completion-path stages 3 and 4). |
| `!e` | the kernel's queries | — | Its contract shows the weak head with its arguments as written; `R`'s arguments are partly computed or redexes. The kernel's weak head is cheap. |
| Patterns, `!_`, `!!_`, `!!!_`, exact expected values | the kernel's queries (D1, D5) | as today | A re-check costs more than the kernel's own computation ([1.4](#14-what-a-re-check-costs-today)). `!!_` and `!!!_` are engine gates by the folded normal forms' decision 5, and must measure the kernel. |
| `witness` | the kernel's queries (D6) | as today | It reads the full normal form, so `R` would save only the truncation's outer data. |
| Fallback in mid-computation | W2, for value forms and for W3's `!!` | nothing | Above |

**Order:** W1 (readback and its oracle, no user-visible change), then W2,
then M3, then W3 if M3 shows a gain. W4, the review, closes each.

## 5. Fallback in mid-computation (D4)

Today a `RuntimeError` of kind `unsupported` abandons the runtime's walk,
and `valueFormOf` computes the whole walk again by the kernel's head
queries. This was decided on 2026-10-26 as the one fallback. EVAL3/EVAL4
had asked for unsupported constructs to "fall back through a specified
typed readback boundary to the current reducer", without "repeatedly
restart[ing] the same fallback"
([EVAL3 and EVAL4](runtime-evaluation-roadmap.md#eval3-and-eval4-evaluate-with-environments-and-an-explicit-stack)).

**Proposal (option c, recommended).** The machine meets a node it does not
execute: a composition, a path applied, η of a path abstraction, Glue,
`unglue` or `abort`. It then:

1. forces first the parts that the kernel's rule demands first, as it reads
   them: a transport's family and base (`ck_hit_reduce`), the path of a path
   application, `unglue`'s value; W4 checks this rule by rule. The kernel
   then receives values, not unevaluated arguments, which are what grows its
   syntax;
2. reads back the node's closure;
3. asks `cc_kernel_whnf` for its head, spending the query's fuel as the
   head queries do now;
4. continues with that head as a cell in an empty environment, copied
   lazily like any kernel syntax.

A read-back handle met again in the kernel's answer maps back to its cell,
so the runtime does not recompute it.

A head that the runtime cannot interpret further, such as a formal
composition at a higher sort, is an observation in its own right. It shows
as `<composition>`, as the kernel's walk shows it, and is never asked
again. A kernel stop (`K344`, budget) is reported as the kernel's. Each
round trip computes a node the runtime did not, so nothing restarts.

Showing a path constructor applied to its data is the separate decision
recorded on 2026-10-28; this mechanism would show it as the kernel's walk
does.

The other options:

- **(a)** Keep the whole restart. It is simplest, but every library Euclid
  value form pays about 65,000 wasted runtime steps first.
- **(b)** Hand the rest of the part's walk to the kernel, from `R(part)`.
  This is simpler than (c), but it gives up the runtime at the first
  transport, and NUM1's transports are everywhere in the library's
  arithmetic.

Take (b) if M2 shows that (c)'s round trips cost more than they save.

## 6. EVAL8 interaction

[EVAL8](runtime-evaluation-roadmap.md#eval8-integrate-with-the-trusted-computation-rules)'s
"integrate with the trusted computation rules" means here:

- **No kernel reducer is replaced, and no instruction is added or
  changed.** Readback uses syntax building and the existing queries.
  Option D would use the existing instructions. The kernel stays as it is.
  The redex closures avoid the one kernel-side addition considered: a query
  exposing level canonicalization.
- **The rules the correspondence imitates are named, so that a review can
  compare them:**

  | Readback or runtime step | Kernel rule |
  | --- | --- |
  | readback redexes | `ck_whnf`'s β (`ck_substitute`) |
  | level redexes | `ck_level_instantiate` |
  | η | `ck_whnf` on `Lam` and `LLam` |
  | ι for point constructors | `ck_eliminate` with no path application |
  | projections, sum and `Unit` eliminations | `weak` |
  | origins | `folding_head` and `computed_data` |
  | the pre-forcing order of W2 | `ck_hit_reduce`, `ck_reduce_composition` and the `PApp` and `Unglue` cases of `weak` |
- **The review covers:**
  - claims 1 to 6 of [3.6](#36-what-readback-guarantees-to-be-tested);
  - lazy annotations, which `R` never evaluates;
  - the fallback boundary;
  - the generation;
  - budgets and cancellation in the middle of a readback;
  - a malformed handle, which is refused;
  - query-before-instruction isolation. Readback interns nodes, and
    W2's head queries fill the weak cache, as head queries do now. A test
    shows an instruction's verdict unchanged with and without a readback
    before it, in the manner of `kernel/tests/test_isolation.c`.
- **Syntax equality and conversion stay apart:** readback's tests compare
  by syntax only.

## 7. Session safety

- **Writes:** every readback write first checks `handlesHeld`, the same
  test as `#kernel()`. The copied syntax's child handles name the right
  nodes only in the generation the query was made in, and a write in
  another generation would build a term of other nodes. On expiry, `R`
  fails as `expired` and its memo is dropped.
- **User paths:** they make the query, read back and dispose of it inside
  one check (`valueFormOf`), before the declaration's transaction ends.
  An expiry there is a defect (`E490`), as today. Read-back nodes live in
  the entry's checkpoint and roll back with it.
- **Retained fields:** by the demand marks' decision 1, suspended parts
  are not retained. A user inspects a part by evaluating it again, as
  `evaluate !!euclid(5).2;`. This meets EVAL5's acceptance on its first
  branch: nothing retained is forced after a session operation.
- **The documented expiry error:** the asynchronous `observe` can hold a
  query across a session operation, and its outcome there is `expired`.
  Copied and computed parts stay observable, and reads and readback fail.
  W1 documents this in the runtime report. It gets a diagnostic code of its
  own only where a user can meet it, and today none can.
- **Retained REPL values** would need REPL bindings, which the demand marks
  put out of scope (decision 5). They are not proposed. Nor is relocating
  a query's handles through `cc_kernel_relocated` at a commit instead of
  expiring them.

## 8. Work items

Each is one PR, reviewed under the roadmap's rule.

| ID | Work | Acceptance and tests | Size |
| --- | --- | --- | --- |
| W1 | **Readback and its oracle.** In `web/cubical-runtime.mjs`: environment frames record the β'd value; values keep their node; queries made for normal forms keep origins; an internal `readback(handle)` returning a kernel handle; free-variable sets per copied node; the generation check; readback counted in the query's work and cells. The correspondence goes into the runtime report. No user-visible change. | **Differential:** for every value form the runtime computes (156 constructs, 40 binary contract values, the `cubist-tests` prints), `normalize(R(root))` α-equals `normalize(e)` wherever the full normal form completes within a fixed budget, and `normalizeFolded(R(root))` α-equals `normalizeFolded(e)`, with origins. **Typing:** `R(root)` is typed by instructions on the small constructs only, since 1.4's cost rules out more. **Mutations that must fail:** swapped pair components, a wrong constructor index, a dropped or foreign instance, a value read instead of its origin, the farthest binding instead of the nearest, a free variable skipped, a memo reused across generations. **Cases:** capture and shadowing; an unused argument never read back; a cell reached twice read back as one handle; readback after a rollback and after a commit is `expired`; a `Lift` refused. M1 recorded. | M |
| W2 | **Per-node fallback** ([section 5](#5-fallback-in-mid-computation-d4)), replacing the whole restart in `valueFormOf`, by D4. | Every value form unchanged against the kernel's queries alone: constructs, `cubist-tests`, contracts and the reference. A count of fallbacks now partial. No node asked twice, and a kernel head the runtime cannot interpret shown by its marker. A kernel stop reported as the kernel's. M2 recorded, slower rows said plainly. | M |
| W3 | **`!!` printed through the runtime**, only if M3 shows a gain: the runtime's data, `R(root)` with origins, then the kernel's folded normalization. | Identical text on every `print(evaluate(!!…))` and REPL transcript in `cubist-tests`, the contracts and the reference. `expecting !!_` stays on the kernel. M3 re-recorded. | S |
| W4 | **EVAL8 review record** for the readback fragment and the fallback boundary, [section 6](#6-eval8-interaction)'s list. | Review rounds by the roadmap's rule. Applicable suites: C and JavaScript, `make sanitize SANITIZERS=undefined` (ASan runs in CI), canonicity fixtures, browser and CLI evaluation, archive checking, definition re-derivation, isolation. | S |
| W5 | **Optional, by D1: runtime-guided derivation, measured only** (option D), as a scratch tool like the closure experiment. | M5 recorded; D1 reopened with it, or not. | M |

## 9. Measurements to take

- **M0:** taken, [section 1.4](#14-what-a-re-check-costs-today).
- **M1, readback:** for each workload of `tools/runtime-repl-probe.mjs`:
  nodes built, readback work, memo hits, DAG and tree sizes of `R(root)`,
  and arena growth.
- **M2, the fallback (W2):** round trips, nodes read back, kernel ticks
  and runtime steps against the kernel's queries alone. Workloads:
  - the library Euclid for 3 to 10, and the 7 that the kernel stops on
    with `K344` (#326);
  - `factorial(40)`;
  - `bq_decide(1/2 + 1/3, 5/6)`;
  - the transport and path constructs.
- **M3, `!!` by the runtime against the kernel's `!!`:**
  - the archive `euclid(3)` and `euclid(4)`, and `euclid(5)` if it fits;
  - the library `euclid(5)` (312,544 ticks by the kernel, with W2);
  - `2/3 + 1/6`, the wide inverse and the wide binary-integer product.
- **M4, retention with origins:** the archive's `euclid(5).1` and list
  parity, with and without origins.
- **M5 (W5):** instructions, steps and peak memory for derivations of
  `count_into(2 * 255, 0) ≡ 510`, the archive's `euclid(4).1 ≡ 5` and the
  library's `euclid(7).1`.
- **Separately, for the driver:** attribute the 12.8M instructions that
  typing a 993-handle normal form took ([1.4](#14-what-a-re-check-costs-today)).
  It is today's exact-expected-value cost, independent of readback.

## 10. Risks

- **Readback volume.** A closure's environment can reach much of the
  heap. Pruning to free variables and the per-cell memo bound `R` by the
  cells reached. The 20M-cell cap and the arena (`K347`) bound the rest.
  M1 measures it.
- **Kernel work from read-back parts in W2.** The kernel reduces whatever
  a node demands, with its own substitution. The pre-forcing order must
  match the kernel's rules, or the kernel recomputes the runtime's work.
  M2 will show it.
- **Divergence from folding.** Origins must reproduce `folding_head`'s
  choices. The differential and mutation tests of W1 carry this, and a
  mismatch fails `!!` text tests, never a verdict.
- **The widened guard (D3).** A wrong readback can be ill typed. Normalizing
  it then fails with an "Unchecked … reached reduction" error, or runs to
  its budget. It affects a display only, and W1's typing tests catch it on
  small terms.
- **Trust creep.** A display computed partly by the runtime must be
  documented so, as value forms are on the REPL page, in the reference's
  printing section and in the CLI guide. D1 keeps every verdict off it.
- **Depth.** `R` cannot exceed the 512 syntax depth, so a deep unary value
  shown by the runtime's value form still has no readback.
- **Cost of the runtime itself.** For the library Euclid the kernel alone
  is cheap (26,666 ticks for `euclid(3)`), and W2 may be slower than it
  for small `n`. Routing by workload is not proposed.

## 11. Decisions

Decided by the user on 2026-10-28, each as recommended:

1. **D1. Who decides verdicts.** Option A: no verdict consumes a readback,
   and readback serves displays and the kernel's queries. Option D is
   measured (W5) before verdicts are reopened. Rejected for now: B (a weaker
   trust tier), C (the cost in 1.4, and failure where the kernel fails), E
   (kernel growth).
2. **D2. How a closure is read back.** As β-redexes over its free
   variables, the kernel doing every substitution, rather than by
   substitution in JavaScript.
3. **D3. Normalizing a readback.** Admit `R`'s handles to the normalize
   queries as derived, widening the JavaScript guard on them
   (`derivedHandles`) as the demand marks' decision 3 did. The justification is the written correspondence, under
   EVAL8's review. Type-check `R` by instructions in tests only, since its
   cost today is 1.4's. The alternative, an instruction typing of every
   readback, costs 12.8M instructions for `2/3 + 1/6`.
4. **D4. The fallback.** Per node, through readback and the kernel's head
   query (option c). This revises the 2026-10-26 decision's "computed again
   from the start", and keeps its other half: a stop at the runtime's limits
   is reported, not retried.
5. **D5. Constructor patterns and exact expected values.** Both stay on the
   kernel's queries, as long as D1 is A. Typed readback alone does not meet
   the condition of 2026-10-26, because a pattern's verdict would need the
   kernel to check `e ≡ R(e)`. The work plan's step 2.4 should say that only
   displays and the fallback move.
6. **D6. `!!!`, `!` and `witness`.** All three stay on the kernel's
   queries: `!!!` is the engine gate, `!` shows arguments as written, and
   `witness` reads the full normal form.

## 12. Findings against the roadmap and the work plan

1. **Step 2.4 expects more than readback can give.** It expects that "`!!`,
   `!!!`, exact expected values and a fallback in mid-computation can then
   go through the runtime". Only displays and the fallback can, unless a
   verdict is allowed to rest on the runtime (D1, D5).
2. **Exact expected values on binary rationals were very costly:**
   48.0 s, 27.7M instructions and 4.7 GiB to refuse `2/3 + 1/6 expecting
   5/6`. Typing the 993-handle folded normal form alone takes 12.8M
   instructions. This is a driver cost, independent of the runtime,
   [1.4](#14-what-a-re-check-costs-today).
   [#331](https://github.com/KanHarI/cubist-math/pull/331) found the cause, a
   derivation memo keyed by the whole scope, and brings the refusal to
   120,258 instructions and 2.4 s; until it merges, 1.4's figures hold.
3. **The work plan's runtime-track paragraph is stale since #324.** It
   still says that the runtime's "signatures must be untruncated, without
   path constructors, so quotient values such as `BInt`'s and `BQ`'s fall
   back"
   ([runtime evaluation track](../work-plan.md#runtime-evaluation-track)).
4. **The roadmap index is stale since 2026-10-26.** Its runtime entry
   still says that EVAL3/EVAL4's query is "not yet integrated"
   ([README](../README.md#runtime)).
5. **EVAL5's Euclid acceptance no longer needs the runtime for small
   inputs.** With #326's library Euclid, the kernel's queries show the
   prime (`euclid(5).1`, 157,971 ticks) and the folded certificates
   (`!!euclid(5)`, 312,544 ticks, 387 characters) for `n` up to 6. The
   runtime falls back on every library Euclid value form. Its role in that
   acceptance becomes `n ≥ 7`, where the kernel stops with `K344`, and
   depends on W2, not on readback for display.
