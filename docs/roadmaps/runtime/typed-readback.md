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
W1 is implemented (2026-10-29): `RuntimeQuery.readback`, internal, reads
back the values of a query made for readback, by value and, on a query
made with origins, by origin, with W1's tests, the oracle over every value
form the runtime computes among them, and M1; the
[runtime report](../../reports/shared-runtime-evaluation.md#typed-readback-w1)
records the correspondence as implemented and where it reads this note
more precisely. No observation changes, and nothing here changes the
kernel. W2 is next ([8](#8-work-items)).

## Summary

- **Readback is syntax-directed; the type is for checking.** The runtime
  keeps every annotation as a cell and never erases one, so a runtime value
  can be read back into a closed kernel term without consulting its type:
  data by its constructor, and a closure as the β-redex it stands for. The
  type enters only where the kernel is asked to check the term.
- **No verdict consumes a readback (D1).** For a verdict the kernel would
  have to establish `e ≡ R(e)` itself. Measured today
  ([section 1.4](#14-what-a-re-check-costs-today)), checking it by
  conversion costs about 3 times the kernel's own folded normal form for
  `euclid(3)` and about 580 times it for `2/3 + 1/6`. It also fails wherever
  the kernel's own reduction fails (K344 for `count_into(2 * 255, 0)`).
  Readback buys nothing for patterns, exact expected values or the
  `!!_`/`!!!_` gates, which stay on the kernel's queries.
- **Where readback helps:** a fallback in mid-computation (W2): a node the
  runtime does not execute, such as a composition, is read back and its
  weak head asked of the kernel, and the runtime goes on. Today the whole
  walk restarts. Since [#326](https://github.com/KanHarI/cubist-math/pull/326)
  the library Euclid's value forms fall back at NUM1's transports for every
  input measured but 0, so this matters most. Readback also gives printed
  `!!` normal forms partly computed by the runtime (W3, if W1's folded
  tests pass and measurement shows a gain), and a strong test oracle for
  the runtime itself: read back by value, `normalize(R(e))` must equal
  `normalize(e)`.
- **`!!!`, `!`, `witness`, patterns and exact expected values stay on the
  kernel's queries.** This narrows the work plan's expectation that `!!!`
  and exact expected values "can then go through the runtime"
  ([section 12](#12-findings-against-the-roadmap-and-the-work-plan)).
- **Session safety holds by construction.** Readback starts, writes kernel
  syntax and returns a handle only while the bridge's handle generation is
  the query's. User paths retain no runtime value across an entry, and
  `expired` is the documented outcome for an API that does.

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
the kernel's own folded normal form of `e`.

Each operation ran alone, from cold caches, in a process of its own, by
the script below. The script checks the workload's setup and
`def probe_e := e;` as REPL entries, then runs one operation in a
declaration transaction of its own. A transaction's end clears the
kernel's weak-head, normal-form and folded caches and its syntax and α
memos, and drops the judgements made since its checkpoint
(`cc_kernel_rollback`, `cc_kernel_commit_checkpoint`); it also drops the
elaborator's syntax caches and the instruction driver
(`CubicalDeclarationTransaction.finish`). So no operation reuses another's
work. For typing and conversion, `r` is computed and decoded first, in a
transaction that is rolled back. The value-form walk is the REPL entry
`evaluate probe_e;`, with the runtime off. The counters are the kernel's
(`CubicalKernel.work`): ticks are query steps and steps are instruction
steps, both units of the kernel's step budget. Every operation ran at
`f7f082b3` with a fresh `make wasm`, Node 24.13.0, macOS arm64 (Apple M3
Pro, 36 GiB), one process at a time with no other heavy job (load average
about 4). All but the rational's typing and conversion ran twice, with the
same counters. Times and peaks, each the process's maximum resident size
with its setup, are not speed claims. Saved in the repository root as
`recheck-probe.mjs`, the walk is
`node recheck-probe.mjs euclid-3 "evaluate probe_e;"` and the conversion
`node recheck-probe.mjs euclid-3 conversion`:

```js
// node recheck-probe.mjs WORKLOAD OPERATION, from the repository root. An
// operation is folded, full, typing, conversion, or a REPL entry.
import createCubical from "./web/dist/cubical.mjs";
import { CubicalProgram } from "./web/cubical-program.mjs";
import { ReplSession } from "./web/repl-session.mjs";
import { CubicalDeclarationTransaction } from "./web/cubical-transaction.mjs";
import { sourceReader } from "./tools/module-sources.mjs";

const workloads = { // setup, e, and the term whose folded normal form is r
  "euclid-3": ["import euclid; use unat;", "euclid(3)", "euclid(3)"],
  "count-into-510": ["import unat; use unat; def count_into(n, total : UNat) : UNat := match n "
    + "{ zero => total; succ(k) => count_into(k, succ(total)); };", "count_into(2 * 255, 0)", "2 * 255"],
  "rational": ["import binary_rationals; use binary_rationals;", "2/3 + 1/6", "2/3 + 1/6"],
};
const [name, operation] = process.argv.slice(2), [setup, e, source] = workloads[name];
const program = new CubicalProgram(await createCubical(), sourceReader(), { runtimeEvaluation: false });
const session = new ReplSession(program), { kernel, checker } = program;
for (const entry of [setup, `def probe_e := ${e};`, `def probe_r := ${source};`])
  for (const line of await session.run(entry)) if (line.kind === "error") throw new Error(line.text);
// A REPL entry is a module, repl_N: its definitions are named repl_N__name.
const probe = n => ({ tag: "DefRef", name: [...checker.definitionViews.keys()].find(key => key.endsWith(`__${n}`)) });
// Each transaction's end clears the kernel's caches, the elaborator's and
// the driver's (web/cubical-transaction.mjs), so each operation starts cold.
const alone = run => {
  const transaction = new CubicalDeclarationTransaction(kernel, checker);
  try { return run(); } finally { transaction.finish(false); }
};
const r = ["typing", "conversion"].includes(operation) // folded, a query
  ? alone(() => checker.normalForm(checker.evaluated(probe("probe_r")).expression)) : null;
const before = kernel.work(), started = performance.now();
let outcome = "ok";
try {
  if (!["folded", "full", "typing", "conversion"].includes(operation))
    outcome = (await session.run(operation)).map(line => line.text).join(" ").slice(0, 60);
  else alone(() => {
    if (operation === "typing") checker.infer(r);
    else if (operation === "conversion") checker.equal(probe("probe_e"), r);
    else kernel[operation === "folded" ? "normalizeFolded" : "normalize"](checker.evaluated(probe("probe_e")).expression);
  });
} catch (error) { outcome = error.message.slice(0, 60); }
const after = kernel.work(), delta = field => Number(after[field] - before[field]);
console.log(JSON.stringify({ name, operation, outcome, instructions: delta("instructions"),
  steps: delta("instructionSteps"), ticks: delta("querySteps"), seconds: +((performance.now() - started) / 1000).toFixed(1),
  peakMiB: Math.round(process.resourceUsage().maxRSS / 1024) }));
```

| Workload | Kernel's value-form walk | Folded normal form | Full normal form | Typing `r` | Checking `e ≡ r` |
| --- | --- | --- | --- | --- | --- |
| archive `euclid(3)` | 130,944 ticks | 142,619 ticks | 204,633 ticks | 648 instructions, 116,397 steps, 5,005 ticks | 753 instructions, 348,342 steps, 63,219 ticks |
| `count_into(2 * 255, 0)` | `K344` after 41,649 ticks (the runtime shows `510`) | `K344` after 41,649 ticks | `K344` after 41,649 ticks | `r` from `2 * 255`, 512 deep: 516 instructions, 1,553 steps | `K344` building the equation, one deeper than `r` |
| `2/3 + 1/6`, `binary_rationals` | 57,192 ticks | 73,503 ticks | 3,526,680 ticks | 11,664,972 instructions, 13,416,894 steps, 425,683 ticks; 17.9 s, peak 2,729 MiB | 16,625,131 instructions, 42,034,778 steps, 672,111 ticks; 28.8 s, peak 3,708 MiB |

Re-checking by conversion costs more than the kernel computing the answer
itself: 411,561 steps and ticks against 142,619 for `euclid(3)`, about 3
times, and 42,706,889 against 73,503 for `2/3 + 1/6`, about 580 times. And
it fails where the kernel's reduction fails: for `count_into`, already in
building the equation.

`2/3 + 1/6`'s folded normal form is 986 handles, but 5,439,086 nodes as a
tree. Its decoded term keeps that sharing: 1,007 JavaScript objects.
Typing it still took 11.7M instructions, of the order of the tree's size,
so the derivation fails to share somewhere. Where is not attributed. The
same typing is part of today's exact expected values, since
`NativeCubicalElaborator.equal` first infers its left side's type:
`evaluate 2/3 + 1/6 expecting 5/6;`, run as the script's operation, fails
with `E326` (the representatives differ) after 25,571,213 instructions and
42.4 s, peaking at 4,596 MiB. The binary contracts compare rationals only
through `binary_rational_equal(…) expecting bnat.(1)`.

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

- **A. Display only (decided).** Readback feeds displays and the
  kernel's queries (W2, W3). Verdicts stay on the kernel's queries as today,
  and patterns stay there with them.
- **B. Reviewed runtime verdicts.** After EVAL8's review, a pattern's
  skeleton is decided by the runtime and its leaves by conversion against
  `R(part)`. This is a new and weaker trust tier: a directive's verdict
  would rest on a JavaScript evaluator, reviewed once, instead of the C
  reducer. It would let `evaluate euclid(4) expecting (5, _);` pass on the
  archive. Rejected.
- **C. Kernel re-check by conversion.** Verdicts would become
  instruction-derived from `e`, which is stronger than today's
  query-based patterns. But the cost is [section 1.4](#14-what-a-re-check-costs-today)'s
  (about 3 to 580 times the folded normal form), and it fails where the
  kernel's reduction fails. It buys trust, not speed. Rejected, at least
  until the driver's sharing defect above is understood.
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
  and its readback. Rejected: the user wants the kernel small.

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
  a normal-form readback it is read back by its origin instead, and so is
  every cell inside that origin
  ([3.4](#34-origins-provenance-and-folding));
- an **unforced syntax cell** is `closure(code, env)`;
- an **unforced application cell** is `App(R(fn), R(argument))`;
- a **cell pending** when a fallback leaves a force keeps its code and
  environment, since a failure resets it (`#run`'s `catch`), and is a
  closure too.

| Value | At type | Read back as |
| --- | --- | --- |
| `Con` `c` with arguments `a1…ak` | its declared sort `Sort(s; …)`, or a Π while partial | `App(…App(Con(c; S), R(a1))…, R(ak))`, in the kernel's argument order, where `c` is the value's constructor index and `S` its instance cell rebuilt one level ([3.3](#33-closures-as-redexes-d2)) |
| `Pair` | Σ | `Pair(R(type), R(first), R(second))` |
| `Inl`, `Inr` | a sum | `Inl(R(type), R(item))`, likewise `Inr` |
| `Point` | `Unit` | `Point` |
| `Lam`, `LLam` | Π, level Π | `closure` of the λ built from the value's symbol, domain and body, under the value's environment: the runtime does not evaluate under it |
| `Elim` | Π | the eliminator rebuilt one level from the value's signature, motive and clause cells |
| `PLam`, `Type` | a path type, a universe | `closure` of the node the value was made from, under the environment it was made in, a `PLam`'s with the value's body |
| `Lift` | Π | refused (`unsupported`): its λ needs the domains of the constructor's field telescope at the instance, the one place readback would need types ([3.7](#37-what-readback-refuses)) |

A constructor is read back from the value's own fields, which observation
and elimination use: its index, and its instance cell, rebuilt one level
into a literal `Sort`, whose signature must be the value's. Read back from
the node the value was made from instead, a value whose index the runtime
got wrong would pass the oracle. The instance is never read back as its
closure, which can be a redex, because the kernel requires a literal
`Sort` in the instance slot: `admitted_signature`
(`kernel/src/signatures.c`) checks the slot's node kind without reducing
it, for `cc_instr_construct` and, through `ck_instance_signature`, for
`ck_eliminate`. In a probe on `f7f082b3`, with
`inductive Box(A : U0) { box(a : A); }`,
`Con(box; (λ (A : U0). Box(A))(Unit))(tt)` was refused by the driver, and
its elimination by `unbox` by `kernel.head`; rebuilt one level, the
instance gives `box(tt)` itself, which both accept.

Every value is read back so from the fields the machine executes: a λ's
symbol, body and environment (β, in the `apply` frame), an eliminator's
signature, motive and clauses (ι, in the `eliminate` frame), a
constructor's index, instance and arguments. The node the value was made
from supplies only what the value does not hold: a λ's domain where its
cell has lost its code, a path abstraction's dimension and family, a
type's parts, under the type's environment. Read back from its node
alone, a λ whose `body` the runtime had changed from `Unit` to `Void`
would still read back as the original, and the oracle would compare the
source, not the computation.

Values are to keep the node they were made from, and the environment it
was made in where they hold none, with origins off too. A `Type` value
holds neither today: `#run`'s `update` frame drops the forced cell's code
and environment, and the value is `{tag: "Type"}`. Its node alone cannot
be read back: in `(fun (A : U0) => A -> A)(Unit)`, the node `A -> A`
has `A` free. A `Con` value is to keep its instance cell's code and
environment, which forcing drops today, and a `PLam` value its node's
dimension and family.

A first-order hypothesis is an application cell `#apply(eliminator,
position)`. It reads back as `App(Elim(…), R(position))`, which is
`ck_eliminate`'s hypothesis. A clause applied by ι is application cells
too, and reads back as the clause applied to the constructor's arguments
and hypotheses, as `ck_eliminate` builds it.

### 3.3 Closures as redexes (D2)

`closure(code, env)`:

- If `code` is a variable `x`, it is `R(env(x))`.
- If `code` is a reference to a definition whose cell the walk has forced,
  it is `R` of that cell: the machine keeps one cell per definition
  (`#definitions`, the `DefRef` case of `#run`).
- If no variable free in `code` is bound in `env`, and no definition that
  `code` references outside its term binders has a forced cell, it is
  `code`, the original kernel handle.
- If `code` is a spine node, an application `App(f, a)` or `LApp(f, ℓ)`,
  a projection or a path application (`spine_node` in
  `kernel/src/term_normalize.c`), or a node that is no term binder and
  references a forced definition outside its term binders, it is rebuilt
  one level, as below: an application is `closure(f, env)` applied to
  `closure(a, env)`, or to the level `ℓ` read back as below.
- Otherwise it abstracts the frames that `code` needs as one telescope and
  applies it to their cells:
  `App(…App(L1(x1; D1, … Ln(xn; Dn, code)…), R(c1))…, R(cn))`. The frames
  needed are the nearest binding of each variable free in `code`, as the
  machine's `lookup` takes it, and, for each frame needed, the nearest
  binding above it of each variable free in its binder's domain. They keep
  their order in the environment, outermost first. `Li` is a `Lam` or
  `LLam` like the binder β contracted at frame `i`, and `Di` is that
  binder's domain as written, whose free variables the telescope's earlier
  binders bind. Environment frames record the β'd value for this (a
  one-field change at the `apply` frame), which keeps its node (3.2).

The domains are not closed one by one, because a domain can mention an
earlier frame's variable. For a closure capturing `A : U0` and `x : A`,
with `A` bound to `Unit` and `x` to `tt`, closing `x`'s domain to `Unit`
leaves `A` abstract in the body. In a probe on `f7f082b3`, two nested
redexes with domains closed one by one, `A`'s outside or `x`'s, over
`(x, x) : A and A` were both refused, while the telescope
`(λ (A : U0). λ (x : A). (x, x))(Unit, tt)` was typed, with the same full
normal form. The arguments `R(ci)` are closed, so applying them outside
the telescope captures nothing, and the telescope is the context the code
was checked in, less the binders it does not need: a readback redex is well
typed whenever the β steps the machine did were.

The spine rule keeps definition spines where `folding_head` sees them.
First, the kernel's η never removes one: `ck_whnf` contracts a `Lam`
whose body applies a function to the bound variable, not free in that
function, and an `LLam` whose body is such an `LApp` (`weak` in
`kernel/src/term_normalize.c`). `folding_head`
watches only its own steps, not those that compute the head of a function
for one of them, so `(λx. cert(x))(tt)` reaches `cert`'s body without
passing through `cert(tt)`. In a probe on `f7f082b3`, `(tt, cert(tt))`,
whose folded normal form keeps `cert(tt)`, read back with such a wrapper
gave `(tt, fun (y : Unit) => tt)` under folding, with the same full normal
form; the spine rule reads it back as `(tt, cert(tt))` itself. Second, a
telescope never cuts a spine in its head. Closed only at its application,
`(fun x => (tt, x.1(tt)))(certPair(tt))`, with `certPair(tt)` the pair
`(fun a => fun b => tt, tt)`, reads back as
`(tt, ((λx. x.1)(certPair(tt)))(tt))`, whose head the kernel computes in a
query `folding_head` does not watch: in a probe on `f7f082b3` it folded to
`(tt, fun b => tt)`, while the original folds to `(tt, certPair(tt).1(tt))`,
with the same full normal form. With the projection rebuilt too, the
readback is `(tt, certPair(tt).1(tt))` itself. Under the spine rule a
telescope's body is never a spine node, so it is never η-contracted and
never stands for part of a spine.

**One level.** Rebuilding a node one level keeps its kind and payload as
written and reads back each child under the same environment: a term as
its closure, a level as below, and a list or a system of tubes rebuilt one
level in turn. An annotation the kernel reads by its node kind is rebuilt
one level too, never read back as a closure, which can be a redex: a path
application's `Path` type, which `weak` reads, and a constructor's `Sort`
instance (3.2). It is applied only to nodes
that are not term binders (`ck_term_binder`). A node that binds a
dimension receives only values computed outside it, which mention no
dimension (section 5), so nothing is captured. It keeps a literal node
where the kernel reads a node's kind without reducing it: a spine node,
whose spine `folding_head` reads, and a constructor's instance.

A definition referenced under a term binder stays as written, and the
kernel computes it again: reading its cell back there would put a value
under the binder, which only a substitution does, and readback leaves
substitution to the kernel (D2).

Free-variable sets are computed once per copied node, binding as
`ck_term_free` does (`Pi`, `Lam`, `Sigma`, `LPi` and `LLam` bind their
payload in their second child), within the query's budget, and so are
the definitions each node references outside its term binders. This is the
pruning that EVAL4's closed-environment item needs for retention as well.

The alternative is to substitute in JavaScript. That needs a capture- and
shadowing-aware substitution over kernel syntax, a walk of the code for
every code and environment pair, and level canonicalization:
`ck_level_instantiate` canonicalizes the levels it substitutes
(`kernel/src/levels.c`), and a JavaScript copy of that algebra would
duplicate the kernel. Redexes need none of these. Their price is that `R`'s
terms are not shown as they are: every display normalizes them in the
kernel first. So `!e` stays on the kernel (section 4).

- **Levels:** a level binding is a level redex, an `LLam` of the telescope
  applied by `LApp`. The kernel contracts it with canonical levels
  (`ck_level_instantiate`), so no level arithmetic is done in JavaScript.
  A level argument's code is a level expression, which cannot be a redex.
  Where it mentions a level variable bound in its environment, readback
  takes the closure of the universe at that level, asks the kernel's head
  query for its weak head, and reads the level off the universe returned:
  the kernel substitutes and canonicalizes. In a probe on `f7f082b3`, with
  `l := 2` and `m := max(l + 1, 1)`, the level `max(m, l) + 1` came back
  as `4`.
- **Names:** the readback redexes reuse the checked binders' symbols. No
  name is invented, and the display's one naming pass
  (`web/display-naming.mjs`) settles names on the normal form shown.
- **Dimensions:** the fragment binds and substitutes none, and W2 keeps
  it so: a fallback forces nothing (section 5).
  Dimension binders and face formulas are copied, as written, inside the
  closures that hold them. All dimension work stays with the kernel.
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

So a query made for normal-form readback keeps, for each forced cell, the
code and environment it was forced from: its origin. A cell whose value is
not data reads back as `closure(origin)`, and inside that closure every
cell with an origin reads back by its origin too, data included. Data
reaches the result by value only outside every non-data part. Value forms
need no origins and keep none, so their retention does not change.

A data origin matters where a non-data part uses the data in place of a
definition spine. In `(fun x => (tt, x.1))(certPair(tt))`, where
`certPair(tt)` is the pair `(fun y => tt, tt)`, forcing `x.1` forces `x` to
data. With `x` read back by its value, the second part is
`(λx. x.1)((fun y => tt, tt))`, which folds to `fun y => tt`; by its
origin, it is `(λx. x.1)(certPair(tt))`, which keeps `certPair(tt).1`
folded, as the kernel's folded normal form of the original term does (a
probe on `f7f082b3`; all three have the same full normal form).

The aim is that folding then agrees with the kernel's folded normal form
of the original term. `folding_head` (`kernel/src/term_normalize.c`)
watches the steps of a part's reduction and remembers the first
definition spine it passes, and the rules are made so that a readback
passes the same spines:

- `closure(origin)`, the cells inside it read back by origin, β-reduces to
  the kernel's term at that position.
- Data outside every non-data part computes in full under both normal
  forms, and a head that is data is never kept folded (`computed_data`).
- A readback redex is a β step through no definition, which the kernel
  never η-contracts and which never stands for part of a spine
  ([3.3](#33-closures-as-redexes-d2)).

But the folded form depends on exactly which steps `folding_head` watches,
and each of these rules covers a case where a simpler readback misses the
kernel's fold: an η-contracted wrapper, a data origin, a closure memo
shared across modes, a spine closed in its head. Others may remain. So
the folded correspondence is a target, not a guarantee. W1's folded
oracle, with origins on, tests it, with those cases as regressions and a
mutation that reads values instead of origins, and W3 waits on it. A
mismatch fails a `!!` text test, never a verdict. What the design
guarantees is the full-normal-form correspondence, with origins off
([3.6](#36-what-readback-guarantees-to-be-tested)).

With origins, a non-data cell is read back as the computation it was
forced from, not as the value the runtime computed. So the folded check
cannot catch a wrong non-data value: a runtime returning `λ_:Unit. Void`
for `λ_:Unit. Unit` would pass it. The value readback, with origins off,
is what tests those values ([3.6](#36-what-readback-guarantees-to-be-tested)).

W3's `!!` would then be the kernel's folded normal form of `R(root)`. `!!!`
stays the kernel's full normal form of the original term `e` (D6); the
full normal form of `R(root)` is only the tests' oracle. `R` itself is
neither: it is the value as far as the runtime computed it.

### 3.5 Sharing

- `R` is memoized per cell, and a closure per code and environment, both
  by mode too, by value or by origin, for the query's generation. A
  closure read by value, as a constructor's instance is, must not answer
  a readback by origin of the same code and environment.
- Each memo entry records whether it is stable: every cell it read was
  forced, and every definition it references outside term binders, as
  3.3 reads them, has a forced cell. Only a stable entry is reused by a
  later readback: a forced cell never changes again (`#run`'s `update`
  frame sets it once), while a suspended one can be forced in between,
  and a definition never demanded has no cell yet (`#definitions` gets
  one at the first `DefRef` demand) but can get one and have it forced.
  Reused, an unstable entry would hand the kernel a closure or a
  definition's original handle instead of the computed value. It serves
  only the readback that made it.
- A closure reuses its code's handle as it is, and the kernel's interning
  merges identical syntax.
- The output has one node per cell reached, one per node a closure is
  rebuilt through, and two per binding of each telescope built.
  Telescopes are not shared between closures: n distinct closures over
  the same n variables build n telescopes of n bindings each. So the
  output is bounded by the cells and code reached plus the sum of the
  telescopes' sizes, which can be quadratic in the runtime's graph. It is
  a DAG, never the tree that a decoding would expand.
- `R` is never decoded to JavaScript. Only the final normal form is,
  under the printer's budget, and that decoding keeps sharing (1,007
  objects for 986 handles, [1.4](#14-what-a-re-check-costs-today)).
- No readback path goes through `checker.infer` or `checker.equal`, whose
  derivations cost the tree.

### 3.6 What readback guarantees, to be tested

1. `R(c)` is a closed kernel term, well typed at `c`'s type, given a
   correct runtime (subject reduction), also where a binder's domain
   mentions an earlier binder ([3.3](#33-closures-as-redexes-d2)).
2. `R(c) ≡ t`, the term `c` stands for: the readback redexes are β, and the
   runtime's own steps are the kernel's.
3. Read back by value, with origins off, their full normal forms are
   α-equal wherever both complete, by confluence and unique normal forms.
   This is the oracle: it compares every value the runtime computed,
   functions included, and each head an observation returned after η
   (W1).
4. With origins, their folded normal forms are to be α-equal
   ([3.4](#34-origins-provenance-and-folding)): a target that W1 tests,
   not a guarantee. It tests folding, not the runtime's non-data values,
   which claim 3 tests.
5. Its size is at most the cells and code nodes reached plus the sum of
   its telescopes' bindings ([3.5](#35-sharing)).
6. It captures nothing, and its nearest-binding rule is the machine's
   lookup.

Equality in tests is `cc_kernel_alpha_equal`, syntax only. A test never
decides by conversion.

### 3.7 What readback refuses

- **`Lift` values**, as `unsupported`. Reading one back needs the domains
  of the field's Π telescope at the instance, from the admitted signature,
  as `kernel/src/signatures.c` instantiates them. This is deferred until a
  workload needs it; until then a fallback node whose readback reaches one
  restarts the walk, as today ([section 5](#5-fallback-in-mid-computation-d4)).
- **Any readback, write or returned handle after the generation moved**,
  as `expired` ([section 7](#7-session-safety)).
- **A term deeper than 512**, with the kernel's own `K344`: a unary numeral
  past 510 cannot be read back, just as the kernel cannot build one.
- **Work and cells past the query's limits**, as for any observation.

## 4. Which observations move, and in what order

| Observation | After this plan | What the kernel still checks | Expected effect, on the measured workloads |
| --- | --- | --- | --- |
| Value form | runtime, with the per-node fallback (W2) instead of a restart, kept only where a rebuild reaches a `Lift` | nothing: no verdict | On `f7f082b3` the library Euclid's value form completes in the runtime at 0 (19,654 steps) and falls back at a composition at every other input measured, 1 to 10: after 3,159 to 5,130 runtime steps at 1 to 6, 9 and 10, while at 7 and 8 the kernel's walk after the fallback stops with `K344` (#326's report had about 65,000 steps at its revision). With W2 the runtime keeps the walk, and the kernel computes only the transports' heads. The effect is unmeasured (M2). In `factorial(40)` (51M kernel ticks) and the 37 constructs that fall back, the kernel would compute only the nodes the runtime does not. |
| Printed `!!e`, REPL `evaluate !!e` | runtime data, then `R`, then the kernel's folded normalization (W3), only if W1's folded tests pass and M3 shows a gain | nothing: a display | Gains where data dominates: the wide binary-integer product (kernel walk 6,962,688 ticks, runtime 4,329,313 steps) and the archive Euclid (kernel `K344`). None expected for `2/3 + 1/6` (kernel folded normal form 73,503 ticks). |
| Printed `!!!e` | the kernel's queries | — | Proofs dominate (`2/3 + 1/6`: 3,526,680 ticks full against 73,503 folded), and the runtime adds nothing until it evaluates under binders and executes cubical terms (completion-path stages 3 and 4). |
| `!e` | the kernel's queries | — | Its contract shows the weak head with its arguments as written; `R`'s arguments are partly computed or redexes. The kernel's weak head is cheap. |
| Patterns, `!_`, `!!_`, `!!!_`, exact expected values | the kernel's queries (D1, D5) | as today | A re-check costs more than the kernel's own computation ([1.4](#14-what-a-re-check-costs-today)). `!!_` and `!!!_` are engine gates by the folded normal forms' decision 5, and must measure the kernel. |
| `witness` | the kernel's queries (D6) | as today | It reads the full normal form, so `R` would save only the truncation's outer data. |
| Fallback in mid-computation | W2, for value forms and for W3's `!!` | nothing | Above |

**Order:** W1 (readback and its oracle, no user-visible change), then W2,
then M3, then W3 if W1's folded tests pass and M3 shows a gain. W4, the
review, closes each.

## 5. Fallback in mid-computation (D4)

Today a `RuntimeError` of kind `unsupported` abandons the runtime's walk,
and `valueFormOf` computes the whole walk again by the kernel's head
queries. This was decided on 2026-10-26 as the one fallback. EVAL3/EVAL4
had asked for unsupported constructs to "fall back through a specified
typed readback boundary to the current reducer", without "repeatedly
restart[ing] the same fallback"
([EVAL3 and EVAL4](runtime-evaluation-roadmap.md#eval3-and-eval4-evaluate-with-environments-and-an-explicit-stack)).

**Decided (D4): option c.** The machine meets a node it does not execute:
a composition, a path applied, η of a path abstraction, Glue, `unglue` or
`abort`. It forces none of the node's parts: the node reads back as its
closure (3.3), so cells the walk had already forced, in its environment
or as definitions it references outside its term binders, read back as
values, the rest as closures, and the kernel's head query decides what it
needs. A definition referenced under a term binder is computed again by
the kernel. Forcing a part first would add demand
wherever the kernel's rule does not inspect that part: a composition at a
function type is a λ at once (`ck_reduce_composition`), so
`comp(fun (i : Interval) => Unit -> Unit, slow(2 * 255))` shows `<fun>`
today without computing `slow`'s countdown (on `f7f082b3`). The machine:

1. checks first the kernel's conditions for that node that read syntax
   only, as `weak` and `ck_expose` check them: a path application at the
   endpoint `0` or `1` under its `Path` annotation is that endpoint of the
   annotation; a composition with a tube on the total face is that tube's
   end; a transport on the total face is its base; an `unglue` whose
   `Glue` type has a total face applies that face's equivalence to the
   value. Where such a condition holds, the machine continues with the part
   it selects and reads back nothing the rule discards. An endpoint of the
   annotation and a transport's base are parts of the node's code, and the
   equivalence's first projection applied to the value is built from two;
   each continues as cells under the node's environment, with no kernel
   query. A composition's total tube needs its end at the dimension, which
   is the kernel's substitution: only that tube is read back, and
   `cc_kernel_endpoint_term`, the query the instruction driver already
   uses (`endpointTerm`), gives the term the machine continues with. These
   shortcuts earn their place because a discarded part is never read back:
   it costs no readback, and a `Lift` in it forces no restart (below). In a
   higher-order `Tree` induction,
   `((fun (g : Unit -> Unit) => refl(tt))(below)) @ 0`, with `below` a
   `Lift`, shows `tt` today (on `f7f082b3`, after the runtime stops at the
   `PApp`), and reading back its path would refuse it;
2. otherwise reads the node back as its closure
   ([3.3](#33-closures-as-redexes-d2)). The closure keeps the node's
   annotations literal, since the kernel's β substitutes into the node
   without changing their kinds, as `weak` needs of `unglue`'s `Glue` type
   and a path application's `Path` type. In a probe on `f7f082b3`, with an
   empty system, the head of `(λA. unglue(Glue(A), glue(tt)))(Unit)` was
   the point, while `unglue` under `(λA. Glue(A))(Unit)` failed with
   "Unchecked Glue projection reached reduction.";
3. asks `cc_kernel_whnf` for its head, spending the query's fuel as the
   head queries do now;
4. continues with that head as a cell in an empty environment, copied
   lazily like any kernel syntax.

Since a fallback forces nothing, the machine never evaluates under a
dimension binder, and no value mentions a dimension. That matters because
dimensions are numbered slots, and only the kernel's substitution renames
a binder that would capture one (`ck_fresh_dimension` in
`kernel/src/term_substitution.c`). With `hold(A) := comp^i U0 [1 ↦ A] A`
inside `comp^i hold(swapped @ i) [] (tt, 3)`, both binders on one slot, a
forced outer family would put `swapped @ i` into the inner tube, whose end
would then substitute the outer dimension too.

A read-back handle met again in the kernel's answer maps back to its cell,
so the runtime does not recompute it.

A node whose readback reaches a `Lift`, a higher-order recursive
hypothesis, cannot be sent, since readback refuses it (3.7). For such a
node W2 keeps today's fallback: the walk restarts on the kernel's head
queries. In a higher-order `Tree` induction, the clause
`comp(fun (i : Interval) => Unit -> Unit, below)(tt)` has `below`, a
`Lift`, as its composition's base, and no shortcut of step 1 applies; on
`f7f082b3`, applied to `node(fun (u : Unit) => leaf)` with `leaf => tt`,
it shows `tt` that way. A shortcut that discards the `Lift` needs no
restart. Reading a `Lift` back as `λ ys. elim(q(ys))`, with the domains of
the constructor's field at the instance, would remove this restart; it
stays deferred until M2 shows that it matters.

The kernel's head can be one the runtime cannot interpret further, such as
a formal composition at a higher sort or a glue value. The cell then holds
it as an opaque head, which is never asked again. A frame that consumes an
opaque head, an application, a projection, a `Unit` or sum elimination or
an eliminator, rebuilds the node it stands for with the opaque head in the
consumed place and its other parts as closures, and sends that node
through the same fallback. For this the `unit` and `sum` frames keep their
node's motive, which they drop today. A circle eliminator applied to a
transported `base` is such a case: with
`def c : Circle := transport(fun (x : Circle) => Circle, base, base, loop, base);`,
`evaluate c;` shows `<composition>`, the kernel's head of `c` being an
`HComp`, but `evaluate to_nat(c);`, for a `to_nat` whose clauses both
return `3`, shows `3` (both on `f7f082b3`): `ck_eliminate` hands a formal
composition to `ck_eliminate_hcomp`, whereas the runtime's `eliminate`
frame refuses anything but a constructor today. Where the opaque head is
itself the observation requested, with no frame left to consume it, the
kernel's walk completes that part's value form from it, as `valueFormOf`
walks the whole value today. `def g : Glue(UNat) := glue(1 + 1);
evaluate g;` shows `glue(2)` on `f7f082b3`, after the runtime refuses the
glue value, since `shownHead` shows a glue value's base and system
(`web/translator/evaluation.mjs`). A marker, such as `<composition>`,
appears only where that walk shows one. A kernel stop (`K344`, budget) is
reported as the kernel's. Each round trip computes a node the runtime did
not, so nothing restarts.

Showing a path constructor applied to its data is the separate decision
recorded on 2026-10-28; this mechanism would show it as the kernel's walk
does.

The other options:

- **(a)** Keep the whole restart. It is simplest, but the library
  Euclid's value form pays 3,159 to 5,130 wasted runtime steps first at
  the inputs measured, 1 to 6, 9 and 10, and every other fallback its own.
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
  | the syntax-only shortcuts of W2 | `ck_expose`, and the `PApp` and `Unglue` cases of `weak` |
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

- **The generation:** readback checks `handlesHeld`, the same test as
  `#kernel()`, when it starts, before every write and before it returns or
  publishes a handle. The copied syntax's child handles name the right
  nodes only in the generation the query was made in: a write in another
  generation would build a term of other nodes, and a handle returned
  there would name another node. A readback can write nothing at all: a
  closed code is read back as its own handle
  ([3.3](#33-closures-as-redexes-d2)), and a memoized cell as the handle
  made for it earlier ([3.5](#35-sharing)). Neither touches the kernel,
  since what the query copied stays readable without it (#324), so only
  the checks at entry and before returning catch an expired generation
  there. On expiry, `R` fails as `expired` and its memo is dropped.
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
| W1 | **Readback and its oracle.** In `web/cubical-runtime.mjs`: environment frames record the β'd value; values keep their node, `Type` values their environment, and `Con` values their instance cell's code; readback by value from the fields the machine executes; queries made for normal forms keep every forced cell's origin; an internal `readback(handle)` returning a kernel handle; free-variable sets per copied node; the generation check at entry, before each write and before a handle is returned; readback counted in the query's work and cells. The correspondence goes into the runtime report. No user-visible change. | **Differential, by value:** for every value form the runtime computes (156 constructs, 40 binary contract values, the `cubist-tests` prints), with origins off, `normalize(R(root))` α-equals `normalize(e)` wherever the full normal form completes within a fixed budget. **Observed heads:** each head an observation returns after `#head`'s η steps is read back too, and its full normal form α-equals that of the cell it was asked of: η leaves that cell holding the λ, so `R(root)` alone never reads back the head η computed. **Folding, by origin:** with origins on, `normalizeFolded(R(root))` α-equals `normalizeFolded(e)`, the target of 3.4, with these regressions: a closure over `cert(x)` inside a pair keeps `cert(tt)` folded (3.3), `(fun x => (tt, x.1))(certPair(tt))` keeps `certPair(tt).1` folded (3.4), and so does a pair of a `Box(x)` constructor and `(fun y => y.1)(x)`, with `x = certPair(tt)`, whose instance reads `x` by value first (3.5), and `(fun x => (tt, x.1(tt)))(certPair(tt))` keeps `certPair(tt).1(tt)` folded (3.3). **Typing:** `R(root)` is typed by instructions on the small constructs only, since 1.4's cost rules out more, and on a closure capturing `A : U0` and `x : A` (3.3) a constructor of `Box(A)` read back from a closure, which `kernel.head` must also eliminate, and the type value of `(fun (A : U0) => A -> A)(Unit)` read back by value, whose full normal form is `Unit -> Unit` (3.2). **Mutations that must fail:** swapped pair components; a constructor value whose index, signature or instance is changed in its own fields, the node it was made from left as it was; likewise a λ's body, symbol or environment and an eliminator's motive or clauses; a dropped instance; an η-produced constructor index changed (`zero` for `succ` in `fun (n : UNat) => succ(n)`); a function value replaced by another of its type (`λ_:Unit. Void` for `λ_:Unit. Unit`, which the folding check passes), a value read instead of its origin, a data cell inside a non-data origin read by its value, the farthest binding instead of the nearest, a free variable skipped, domains closed one by one instead of the telescope, a memo reused across generations. **Cases:** capture and shadowing; a level argument that mentions a bound level variable; an unused argument never read back; a cell reached twice read back as one handle; a scaling test, n closures over the same n variables for growing n, whose readback stays within 3.5's bound and grows as n²; readback after a rollback and after a commit is `expired`, for a readback that writes and for one that writes nothing (a closed code's own handle, a memoized handle); a `Lift` refused. M1 recorded. | M |
| W2 | **Per-node fallback** ([section 5](#5-fallback-in-mid-computation-d4)), replacing the whole restart in `valueFormOf`, by D4, except where a rebuild reaches a `Lift` (section 5). | Every value form unchanged against the kernel's queries alone: constructs, `cubist-tests`, contracts and the reference. A count of fallbacks now partial. No node asked twice. A fallback forces nothing: `comp(fun (i : Interval) => Unit -> Unit, slow(2 * 255))` shows `<fun>` without computing `slow`, and cells the walk forced, in the node's environment or as definitions it references outside its term binders, read back as values, whose computation the kernel's ticks for the node do not include: in `(expensive, comp(fun (i : Interval) => Unit, expensive))`, with `expensive : Unit` a computation the kernel stops with `K344`, the composition's base reads back from the definition cell the first field forced. A readback across forcing: a function-valued composition reads back a suspended `x`, a later field forces `x`, a `count_into(2 * 255, 0)`-based computation of the identity, and `comp(fun (i : Interval) => Unit, x(tt))` then reads `x` back from its value, not from the first readback's memo of its closure, which the kernel stops with `K344`. The same holds when `x` is a definition first read back before it has a cell, then demanded and forced: the second readback takes the forced cell, not the definition's original handle. An unused expensive path: `p @ 0` under its `Path` annotation gives the endpoint without `p` being forced or read back. A discarded part holding a `Lift`: the higher-order `Tree` induction's `((fun (g : Unit -> Unit) => refl(tt))(below)) @ 0` still shows `tt`. A rebuild that reaches a `Lift` restarts as today: the higher-order `Tree` clause `comp(fun (i : Interval) => Unit -> Unit, below)(tt)` still shows `tt`. Two binders on one dimension slot: `comp^i hold(swapped @ i) [] (tt, 3)`, with `hold(A) := comp^i U0 [1 ↦ A] A`, shows `(3, tt)`. An `unglue` whose `Glue` type depends on the environment computes as the kernel's queries alone do. An opaque head consumed by a frame sent through the fallback: the circle eliminator on a transported `base` computes `3`. An opaque head that is the observation completed by the kernel's walk: `def g : Glue(UNat) := glue(1 + 1); evaluate g;` shows `glue(2)`, and a marker appears only where that walk shows one. A kernel stop reported as the kernel's. M2 recorded, slower rows said plainly. | M |
| W3 | **`!!` printed through the runtime**, only if W1's folded tests pass and M3 shows a gain: the runtime's data, `R(root)` with origins, then the kernel's folded normalization. | Identical text on every `print(evaluate(!!…))` and REPL transcript in `cubist-tests`, the contracts and the reference. `expecting !!_` stays on the kernel. M3 re-recorded. | S |
| W4 | **EVAL8 review record** for the readback fragment and the fallback boundary, [section 6](#6-eval8-interaction)'s list. | Review rounds by the roadmap's rule. Applicable suites: C and JavaScript, `make sanitize SANITIZERS=undefined` (ASan runs in CI), canonicity fixtures, browser and CLI evaluation, archive checking, definition re-derivation, isolation. | S |
| W5 | **Optional, by D1: runtime-guided derivation, measured only** (option D), as a scratch tool like the closure experiment. | M5 recorded; D1 reopened with it, or not. | M |

## 9. Measurements to take

- **M0:** taken, [section 1.4](#14-what-a-re-check-costs-today).
- **M1, readback:** for each workload of `tools/runtime-repl-probe.mjs`:
  nodes built, readback work, memo hits, DAG and tree sizes of `R(root)`,
  and arena growth.
- **M2, the fallback (W2):** round trips, nodes read back, restarts at a
  `Lift`, kernel ticks and runtime steps against the kernel's queries
  alone. Workloads:
  - the library Euclid for 3 to 10, with 7 and 8, where the kernel's
    queries stop with `K344` (#326);
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
- **Separately, for the driver:** attribute the 11.7M instructions that
  typing a 986-handle normal form took ([1.4](#14-what-a-re-check-costs-today)).
  It is today's exact-expected-value cost, independent of readback.

## 10. Risks

- **Readback volume.** A closure's environment can reach much of the
  heap. Pruning to free variables and the memos bound `R` by the cells
  and code nodes reached plus its telescopes' bindings, which can be
  quadratic (3.5). The 20M-cell cap and the arena (`K347`) bound the
  rest. M1 measures it.
- **Kernel work in W2.** The kernel computes, with its own substitution,
  whatever part of a fallback node its rule inspects and the walk had not
  forced. That avoids demand the kernel would not make, but repeats work
  the runtime could have done; M2 will show how much.
- **Divergence from folding.** The folded correspondence is a target
  ([3.4](#34-origins-provenance-and-folding)). W1's folded tests and their
  regressions check it, W3 waits on them, and a mismatch fails `!!` text
  tests, never a verdict.
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
   readback, costs 11.7M instructions for `2/3 + 1/6`.
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
   42.4 s, 25.6M instructions and 4.5 GiB to refuse `2/3 + 1/6 expecting
   5/6`. Typing the 986-handle folded normal form alone takes 11.7M
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
5. **EVAL5's Euclid acceptance no longer needs the runtime for most
   inputs.** With #326's library Euclid, the kernel's queries show the
   prime (`euclid(5).1`, 157,971 ticks) and the folded certificates
   (`!!euclid(5)`, 312,544 ticks, 387 characters). They stop with `K344`
   where the least-divisor search is long, not past some `n`: #326's report
   records `euclid(7).1` and `euclid(8).1`, whose searches take 70 and 60
   candidates, stopping, and `euclid(9).1` and `euclid(10).1`, with 18 and
   10, computing (`node tools/runtime-repl-probe.mjs binary-euclid-10-prime
   kernel` returns `11`). The runtime falls back on the library Euclid's
   value form at every input measured but 0 (section 4). Its role in that
   acceptance becomes the long searches, and depends on W2, not on
   readback for display.
