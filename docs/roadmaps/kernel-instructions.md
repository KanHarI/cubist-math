# Kernel instructions: a THTH-style forward kernel

Status: on the `kernel-instructions` branch, beside the current term checker,
which it does not change:

- Stage 1 is implemented: `kernel/src/instructions.c`, tested by
  `kernel/tests/test_instructions.c`.
- Stage 2 is implemented:
  - the WASM bridge and `web/cubical-instructions.mjs`;
  - the driver `web/cubical-instruction-driver.mjs`;
  - the workbench's **Kernel graph** view (`web/cubical-graph-view.mjs`);
  - the Elaboration panels, which now show the instruction derivation.
- Stage 3 is under way: paths at any interval formula (`PathAt`), and
  composition with tubes on disjoint faces (`System`, `SystemTube`, `Comp`).
- In instruction mode, the first proof checks, and so does all of
  `library/naturals`. So does every one of the 41 definitions behind the
  archive's Euclid theorem, and 3800 of the archive's 3938 definitions
  (96.5%), in 14 s for the whole archive; `node tools/instruction-coverage.mjs`
  measures it again. The rest need:

  | Need | Definitions |
  | --- | --- |
  | Pushouts | 67 |
  | Overlapping or multi-clause faces | 40 |
  | W types | 18 |
  | Glue | 8 |
  | `HComp` | 1 |
  | A better search | 4 |

## Goal

Move every *search* decision out of the trusted C kernel into the untrusted
elaborator, as in THTH. The kernel becomes a set of rule instructions that the
elaborator issues one at a time, each checked and answered with a judgement,
and it decides nothing on its own: no conversion strategy, no implicit
reduction, no unfolding hints. `with unfolding` and any future notion of
opacity become elaborator features only.

## Where the kernel searches today

The kernel takes a finished term and checks it top-down (`kernel/src/check*.c`).
Choosing each rule is not search: every node kind has one rule. The search is
in how it decides that two types are equal, and where it reduces:

| Where | What it decides | Files |
| --- | --- | --- |
| Conversion `A ≡ B` | A strategy: compare folded, then with the elaborator's unfolding hints, then with definitions exposed, then computed to head normal form with congruence into arguments; eta for functions, pairs and paths; a memo of results | `term_conversion.c` (~500 lines) |
| Unfolding hints | Which definitions the hinted pass may unfold | `unfolding_hints.c`, `term_conversion.c` |
| Demanded heads | About 30 implicit `ck_whnf` calls in the typing rules: an application's function type is reduced until it is a `Π`, a pair's type until it is a `Σ`, a type until it is a universe | `check_*.c` |
| Evaluation | Normal forms for `evaluate` and `computable`; deterministic | `term_normalize.c`, `*_compute.c` |

`opaque def` never reached the kernel, and has been removed (#37).

## Two hash graphs

As in THTH's graph store, the kernel's state is two graphs.

**The syntax graph.** Terms are hash-consed: identical syntax is one node,
children point to earlier nodes, and a handle is the node's identity. Sharing
used to be a lossy cache of 65,536 slots that could evict; it is now an exact
open-addressing table that grows with the arena. Handles discarded by a
rollback act as tombstones, and the survivors of a checkpoint's compaction are
indexed again. On the benchmark corpus this alone cut final-check arena nodes
by 26% (636M to 473M) and the run from 12.1 s to 11.3 s, and let three Artin
declarations that hit the time limit check, unblocking five more.

**The judgement graph.** Each judgement records the instruction that derived
it: its rule, its premises (earlier judgements), the context entry it bound or
used, its immediate operands, and, for a step or a replacement, the
highlighted position. The same instruction on the same operands returns the
same judgement, so the graph is a derivation DAG, as THTH's Merkle graph of
judgements was. Premises always have smaller ids.

**Context entries** play THTH's context fragments: a term entry is a symbol, a
type, the judgement that the type is a type, and the entries that type needs.
There is one dimension entry per interval index.

Differences from THTH, for now:

- **Named binders, not de Bruijn indices.** Every reduction in the C kernel
  works on named terms, so alpha-equivalent terms can be different nodes. The
  rules compare with alpha equality, so this costs sharing, not soundness.
- **Dense integer ids, not content hashes.** Ids are valid within a session.
  Stable content hashes (THTH used blake3) would matter for exporting and
  caching certificates, and can be added then.

## The instruction kernel

An instruction takes handles of earlier judgements and entries, plus small
immediate data (a symbol, a level, a position), checks its side conditions
**syntactically** — types must be identical up to bound names — and returns
the handle of a new judgement, or 0 with an error. Nothing is reduced or
unfolded unless an instruction says so. The first proof, forward:

```
nat  = NatForm()                       // {} ⊢ Nat : U0
n    = CtxExt(nat, n)                  // {n : Nat}
nv   = Vble(n)                         // {n : Nat} ⊢ n : Nat
sn   = NatIntroS(nv)                   // {n : Nat} ⊢ succ(n) : Nat
lt   = DefLookup(lt)                   // {} ⊢ lt : Nat → Nat → U0
goal = PiElim(PiElim(lt, nv), sn)      // {n : Nat} ⊢ lt(n, succ(n)) : U0
u    = Refl(goal)                      // lt(n, succ(n)) ≡ lt(n, succ(n))
u    = Step(u, right, [0, 0], Delta)   //   unfold the highlighted lt
u    = Step(u, right, [0], Beta)       //   ≡ (λm. Σ(k : Nat). …)(succ(n))
u    = Step(u, right, [], Beta)        //   ≡ Σ(k : Nat). succ(n + k) = succ(n)
…
p    = Conv(pair, Symm(u))             // {n : Nat} ⊢ (0, <i> succ(n)) : lt(n, succ(n))
```

### Instructions

- **Contexts:** `Extend` (an entry `x : A` from `Γ ⊢ A : U_i`; the symbol must
  be new), `Dimension` (the entry of an interval index), `Variable`.
- **Formation, introduction and elimination:** universes, `Π` (`Pi`,
  `Lambda`, `Apply`), `Σ` (`Sigma`, `Pair`, `First`, `Second`), `Nat` (`Zero`,
  `Succ`, `NatElim`), `Unit` (`Point`, `UnitElim`), `Void` (`Abort`), sums
  (`Sum`, `Inject`, `SumElim`), paths (`Path`, `PathLambda`, `PathApply` at a
  dimension or an endpoint). `Domain` and `Family` give the parts of a `Π` or
  `Σ` type as types in its universe.
- **Definitions:** `Define` registers a closed judgement under a symbol and
  returns its lookup; `Lookup` recalls any checked definition, including
  those of the term checker.
- **Equality judgements** `Γ ⊢ a ≡ b : T`, from `Refl`:
  - `Step(eq, side, position, rule)` contracts the highlighted redex, and only
    it: `Beta`, `Delta` (unfold the highlighted definition), `Iota` (an
    eliminator or projection on a constructor), `Path` (a path lambda at a
    point, or a path at an endpoint of its annotated type), or `Normalize`
    (the normal form of the highlighted subterm, by the kernel's fixed
    strategy; THTH's `BetaReduceGrossKnuth`).
  - `Replace(eq, side, position, a ≡ b)` swaps a highlighted occurrence of `a`
    for `b`: a targeted definitional-equality rewrite. When `a` or `b` uses a
    name bound on the way down, the given equality must have that name as a
    context entry of the binder's type — THTH's view of a bound variable as a
    context fragment — and the entry is discharged. Entry types are followed
    outwards, so a dependent binder's domain must agree too.
  - `Eta` (a term of a `Π`, `Σ` or path type equals its expansion), `Side`,
    `Symmetry`, `Transitivity`.
- **Conversion:** `Convert(t : A, A ≡ B)` gives `t : B`; `Lift` raises
  `t : A` to a cumulative `B` (universes by level, `Π`/`Σ` by codomain).
  `Step` and `Replace` also rewrite the term or the type of a typing judgement
  in place, as THTH's `HighType` with a pointed reduction did: a reduct of a
  type is a type, so no typing judgement for the type is needed.
- **Endpoints:** `Endpoint` substitutes 0 or 1 for a dimension in a typing
  judgement, for the endpoint types of a dependent path family.
- **Composition:** `comp^i A [φ ↦ u] a0` is built one tube at a time.
  - `System` starts from the family `A : U` over `i` and the base `a0 : A(0)`.
  - `SystemTube` adds a tube on a face of one clause. The tube is typed at `A`
    restricted to the face, and an equality shows it starts at the base
    there: `u(0) ≡ a0` on the face.
  - `Comp` closes the system into `comp … : A(1)` and discharges `i`.
  - Faces may not overlap yet; an overlap would need its own equality.
  - `PathAt` applies a path at any interval formula, such as `1 - i`.

Highlighting stays in the kernel on purpose: a short targeted reduction or
rewrite can replace normalizing a whole type.

### Contexts

A judgement keeps only the entries it depends on, and the contexts of premises
merge. Each context is closed under the entries' own dependencies. A binder
discharges one entry, only when no other entry of the context depends on it.
The free names and dimensions of a judgement's terms are always entries of its
context; this is what makes discharging, and replacement under binders,
capture-free.

### Soundness

The instructions reuse the kernel's single-step contractions, substitution,
alpha equality and normalizer, which the term checker already trusts, and
the metatheory the term checker relies on (subject reduction, uniqueness of
types up to conversion and cumulativity). The judgement graph is truncated
with the syntax arena on rollback and commit. `test_instructions.c` derives
`add`, `lt` and `lt_succ` forward and has the term checker accept the
definitions, and checks the rejections: capture, dependency, mismatched binder
types, open definitions, and misplaced steps.

The interval and face algebra keeps its decision procedure in the kernel: it
decides equality of De Morgan formulas, with no strategy to choose.

### What moves to the elaborator

- **Driving the rules.** Today's top-down checker becomes an untrusted driver:
  it walks the term the elaborator built and issues the instruction for each
  node. Later, tactics issue instructions directly (`intro` is `Extend` then
  `Lambda`, `exact` a `Convert`).
- **Conversion search.** Where a rule needs two types to agree, or a type in a
  particular shape, the driver searches for the steps — the strategy
  `term_conversion.c` uses today — and emits them as equality instructions.
- **Unfolding hints** order that search. A notion of opacity, if it returns,
  would be the search never emitting `Delta` for a definition.

### What the kernel keeps

The typing rules as instructions, the single-step contractions, alpha
equality, the interval and face algebra, deterministic normalization, the two
hash graphs, budgets and deadlines. It loses the conversion strategy, the
hints and every implicit reduction.

## The driver

`InstructionDriver` replays a checked term as instructions, one per node. Where
a rule needs two types to agree, it makes them agree without trust:

- by congruence on common heads, when their parts are equal;
- by weak-head steps: beta, iota and path steps first, then unfolding
  definitions lazily. The one defined later is unfolded first, and both when
  they are the same (lazy delta reduction, as in Lean);
- by `Whnf`, the kernel's own weak head normal form, for heads the steps do
  not take: composition, transport, Glue, pushouts;
- by eta, expanding a neutral term against a lambda, path lambda or pair:
  - the neutral term is derived again at its position, and `Replace` puts its
    `Eta` expansion there;
  - below binders, the derivation uses entries named as the binders;
- by `Normalize` when that runs long;
- by `Lift` for cumulativity.

Where a function's domain and its argument's type must agree, both are
rewritten in place, toward a common form.

**Search aids.** The kernel offers two queries that decide nothing:
`cc_kernel_convertible` answers whether the term checker's conversion finds
two terms equal, within a small step budget, and `cc_kernel_rename` renames a
free name.

The driver asks the first query only where the answer changes its choice: on a
common head that could also be reduced. Before comparing parts under binders,
it renames the right side's bound names to match the left's. Every step it
then takes is still an instruction the kernel checks.

The driver caches judgement reads, scopes and derivations; the kernel indexes
entries by symbol. Together, these took the archive from 457 s to 14 s.

A learned policy for this search, trained against the kernel with the
heuristic as its teacher and derivation cost as its objective, is designed
in [learned-search.md](learned-search.md).

A rule's expected type comes either from a premise the driver can rewrite in
place, or from a typing judgement it derives for that type. It reduces a
constructor's annotation once, as an equality, and converts the result back
along it.

## Inspection: the graphs in the workbench

The instructions the elaborator sends are the derivation. The kernel
workbench's **Kernel graph** view (`?view=graph`) explores it:

- **Judgements:** each with its rule, operands and highlighted position,
  rendered as `Γ ⊢ t : T` or `Γ ⊢ a ≡ b : T` in mathematical notation; its
  premises and its consumers are links, so a derivation can be walked in
  either direction. A `Step` shows its highlighted subterm on the side it
  changed.
- **Context entries:** the fragment, its type's judgement, what depends on it.
- **Syntax:** a node's kind, payload and children, with sharing visible:
  every judgement and definition that uses the node.

The Elaboration panels show the same derivation in THTH's form:

- each context entry is a `CtxExt` step, with its fragment as the comment;
- each reduction step names its rule, position and subterm;
- exact's ascription is marked as the elaborator's.

For a term the driver cannot derive yet, a panel falls back to the derivation
reconstructed from the term checker's trace (#36).

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

## Stages

1. **Core instructions** in C, beside today's checker — done: the judgement
   and syntax hash graphs, contexts, universes, `Π`, `Σ`, `Nat`, `Unit`,
   `Void`, sums, paths without composition, definitions, equality judgements
   with highlighted steps, replacement, eta, conversion and lift.
2. **Untrusted driver and search** in JavaScript, done:
   - the WASM bridge and a kernel wrapper;
   - turning a checked term into instructions and conversion steps;
   - the first proof and `library/naturals` (except `nat_add_comm`) check in
     instruction mode, at the term checker's types;
   - the workbench explores the graphs;
   - the Elaboration panels show the instructions.
3. **W types and the cubical rules**, under way:
   - done: paths at any interval formula;
   - done: composition with tubes on disjoint faces;
   - remaining: overlapping faces (an equality on each overlap), `HComp`,
     `Trans`, `Glue`, pushouts and W types;
   - remaining: the archive checks in instruction mode.
4. **Tactics issue instructions directly**, and the term checker leaves the
   trusted kernel. Unfolding hints leave the kernel.
5. **Performance:** an untrusted native search module if JavaScript is too
   slow; certificate compaction; content hashes for exported certificates;
   a learned search policy for cheaper derivations
   ([learned-search.md](learned-search.md)).

## Decisions

1. `Normalize` is allowed: it involves no choice, so it is computation, not
   search, and it keeps large computations in C.
2. The conversion search starts in JavaScript.
3. Contexts are minimal and merge, as THTH's context fragments did.
4. Highlighted steps and targeted replacement stay in the kernel, for short
   derivations instead of normalizing whole types.
5. The kernel's state is the syntax and judgement hash graphs, explorable in
   the workbench; binders stay named, and ids stay dense, for now.
