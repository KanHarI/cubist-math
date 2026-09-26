# Kernel instructions: a THTH-style forward kernel

Status: on the `kernel-instructions` branch. The instruction kernel is the
trusted kernel; the term checker is an untrusted elaborator beside it.

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
- Every one of the archive's 3938 definitions is admitted this way, and so
  are the first proof and `library/naturals`. Every derived term is its
  source syntax, annotations included. The benchmark page measures it, and
  `node tools/instruction-coverage.mjs` derives every stored definition again.

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

- **Contexts:** `Extend` (an entry `x : A` from `Γ ⊢ A : U_i`; a symbol names
  one entry, and extending it again at an alpha-equal type returns that
  entry, whatever judgement shows the type is a type), `Dimension` (the entry
  of an interval index), `Variable`.
- **Formation, introduction and elimination:** universes, `Π` (`Pi`,
  `Lambda`, `Apply`), `Σ` (`Sigma`, `Pair`, `First`, `Second`), `Nat` (`Zero`,
  `Succ`, `NatElim`), `Unit` (`Point`, `UnitElim`), `Void` (`Abort`), sums
  (`Sum`, `Inject`, `SumElim`), paths (`Path`, `PathLambda`, `PathApply` at a
  dimension or an endpoint). `Domain` and `Family` give the parts of a `Π` or
  `Σ` type as types in its universe.
- **Definitions:** `Define` admits a closed judgement under a symbol and
  returns its lookup; `Lookup` recalls an admitted definition, and refuses the
  term checker's own (`cc_kernel_define`).
- **Equality judgements** `Γ ⊢ a ≡ b : T`, from `Refl`:
  - `Step(eq, side, position, rule)` contracts the highlighted redex, and only
    it: `Beta`, `Delta` (unfold the highlighted definition), `Iota` (an
    eliminator or projection on a constructor), `Path` (a path lambda at a
    point, or a path at an endpoint of its annotated type), `Face` (a
    composition with a tube on a face that holds, to that tube at the end of
    its dimension), `Whnf` (the kernel's weak head normal form), or
    `Normalize` (the normal form of the highlighted subterm, by the kernel's
    fixed strategy; THTH's `BetaReduceGrossKnuth`).
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
    there: `u(0) ≡ a0` on the face. The face may be `1`, the clause with no
    equations. A tube on the face `0`, as a substitution into a type can
    leave it, is never used and needs only a typing judgement.
  - `SystemOverlap` shows that the newest tube agrees with an earlier one
    where their faces meet: an equality between the two, restricted to the
    overlap. `SystemTube` records which earlier tubes the new face meets,
    and until each has its equality, the kernel neither adds a tube nor
    closes the system. The term checker asks the same, of its conversion.
  - `Comp` closes the system into `comp … : A(1)` and discharges `i`.
  - `HComp` closes it into `hcomp^i A [φ ↦ u] a0 : A` when the family does
    not vary along `i`, and `Trans` into `transp^i A φ a0 : A(1)` when its
    tubes are the base on each clause of `φ`, at the family there, which is
    constant on `φ`. As in the term checker, both are for pushout types,
    which each reads off the family's weak head. `Face` takes a transport
    whose face holds to its base.
  - `PathAt` applies a path at any interval formula, such as `1 - i`.
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
- **Glue:** `Glue [φ ↦ (T, e)] A` is built piece by piece, as a composition's
  system is: `GlueBase` from `A : U`; `GluePiece` adds a type `T` on a face and
  an equivalence `e` at `Equiv(T, A)` there, the type the term checker
  states; where two pieces' faces meet, `GlueOverlap` takes equalities of
  their types and of their equivalences; `Glue` closes it. A Glue term is
  built the same way, a value `t : T` for each piece in order with an
  equality `fst(e)(t) ≡ a` on its face, and `SystemOverlap` where faces meet;
  `Unglue` gives the base. A search aid, `cc_kernel_equiv_type`, builds
  `Equiv(T, A)` as syntax for the driver. Glue computes by `Whnf`.
- **W types:** `W` forms `W(x : L). B` from an entry and a family, as `Π` and
  `Σ` do, and `Domain` and `Family` give `L` and `B[l/x]`. `Sup` gives
  `sup(l, c)` of a W type as written, and `WElim` gives W recursion from a
  motive, a step and a value, at the types the term checker states. `Iota`
  computes recursion on `sup`.

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

The trusted base is the instructions and what they call: the single-step
contractions, substitution, alpha equality, the normalizer and weak head
normal form (for `Normalize` and `Whnf`), the interval and face algebra, and
the metatheory the typing rules rely on (subject reduction, uniqueness of
types up to conversion, cumulativity). The kernel's weak head normal form of
a Glue element consults conversion for Glue's eta rule; that is a reduction
rule's side condition, and any answer yields a convertible term. The term
checker's typing rules and its conversion strategy are not in it, nor are the
unfolding hints. The judgement graph is truncated with the syntax arena on
rollback and commit. `test_instructions.c` derives `add`, `lt` and `lt_succ`
forward and has the term checker accept the definitions, and checks the
rejections: capture, dependency, mismatched binder types, open definitions,
misplaced steps, and lookups of definitions `Define` did not admit.

The interval and face algebra keeps its decision procedure in the kernel: it
decides equality of De Morgan formulas, with no strategy to choose.

### What moves to the elaborator

- **Driving the rules.** The top-down checker becomes an untrusted driver: it
  walks the term the elaborator built and issues the instruction for each
  node, as each tactic's check runs and again when the declaration is
  defined.
- **Conversion search.** Where a rule needs two types to agree, or a type in a
  particular shape, the driver searches for the steps — the strategy
  `term_conversion.c` uses today — and emits them as equality instructions.
- **Unfolding hints** do not move with it: the search finds its own order,
  so that proofs need no hints. A notion of opacity, if it returns, would be
  the search never emitting `Delta` for a definition.

### What the kernel keeps

The typing rules as instructions, the single-step contractions, alpha
equality, the interval and face algebra, deterministic normalization, the two
hash graphs, budgets and deadlines. The conversion strategy, the hints and
every implicit reduction are now the untrusted term checker's alone.

## The driver

`InstructionDriver` replays a checked term as instructions, one per node. Where
a rule needs two types to agree, it makes them agree without trust:

- by congruence on common heads, when their parts are equal, and never twice
  on the same two terms: a failed attempt can leave an eta expansion that a
  step contracts again;
- by weak-head steps: beta, iota, path and face steps first, then unfolding
  definitions lazily. The one defined later is unfolded first, and both when
  they are the same (lazy delta reduction, as in Lean). A face step takes a
  composition whose face holds to its tube, where `Whnf` would go on to
  compute the tube's head, perhaps a large number in unary;
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

**Search aids.** The kernel offers queries that decide nothing:
`cc_kernel_convertible` answers whether the term checker's conversion finds
two terms equal, within a budget of 20,000 steps; `cc_kernel_rename` renames a
free name; `cc_kernel_equiv_type` builds `Equiv(A, B)` as syntax; and
`cc_kernel_fresh_symbol` allocates symbols, so the driver's names and the
kernel's never share an id.

The driver asks the first query only where the answer changes its choice: on a
common head that could also be reduced. Where the head reduces by computation
(beta, iota, path or face), it reduces unless the parts are known equal;
where only unfolding a definition would, it compares parts not known to
differ. Nearly all of the query's cost was in answers that ran out of budget,
so 20,000 steps rather than 200,000 halved the admission time of the
algebraic modules. Before comparing parts under binders, it renames the right
side's bound names to match the left's. Every step it then takes is still an
instruction the kernel checks.

After 64 steps on two closed subterms the query finds equal, such as a
numeral's arithmetic, the driver normalizes both, one instruction each:
single steps each rebuild the judgement's term, and a factorial's took 1.1M
arena nodes where 62k now do. Open terms keep to lazy steps, since their
normal forms can be enormous. A path lambda applied at a compound interval
formula contracts its body's computing head first, before the formula is
substituted; the driver's alpha comparison is memoized over the shared term
graph, since walking it as a tree is exponential in its depth.

A binder's variant name, when its own is taken at another type, is
remembered by name and type and used again, and the kernel reuses an entry at
an alpha-equal type: two entries for one variable would make terms that
mention it differ for ever.

The driver caches judgement reads, scopes and derivations; the kernel indexes
entries by symbol. Together, these took the archive from 457 s to 14 s.

A rule's expected type comes either from a premise the driver can rewrite in
place, or from a typing judgement it derives for that type. It reduces a
constructor's annotation once, as an equality, and rewrites the result's
annotation and type back along it; a path lambda is derived at its own
family. So a derived term is always its source syntax, and a type derived as
evidence is the type it stands for.

The driver does not use `with unfolding` hints: the search must not need
them. Letting hinted definitions unfold first changed about 1% of the
judgements of the 54 hinted archive definitions, and fixed nothing.

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

If a derivation cannot be shown, a panel falls back to the derivation
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
3. **W types and the cubical rules**, done:
   - paths at any interval formula;
   - composition, with an equality on each overlap of two faces;
   - pushouts, W types, `HComp`, `Trans` and `Glue`;
   - the whole archive checks in instruction mode.
4. **Tactics issue instructions directly**, and the term checker leaves the
   trusted kernel. Unfolding hints leave the kernel. Done; see below.
5. **Performance:** an untrusted native search module if JavaScript is too
   slow; certificate compaction; content hashes for exported certificates.

## Stage 4: the trusted kernel

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
against 7,300 committed checks. They are answered by the term checker alone
and are not evidence, as the driver's own conversion query is not. The driver
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

**Not done:** the term checker still elaborates, and tactics still build
terms rather than judgements. Tactics that build judgements, with the
term checker removed from elaboration too, would need the driver to
elaborate raw syntax itself.

## Decisions

1. `Normalize` is allowed: it involves no choice, so it is computation, not
   search, and it keeps large computations in C.
2. The conversion search starts in JavaScript.
3. Contexts are minimal and merge, as THTH's context fragments did.
4. Highlighted steps and targeted replacement stay in the kernel, for short
   derivations instead of normalizing whole types.
5. The kernel's state is the syntax and judgement hash graphs, explorable in
   the workbench; binders stay named, and ids stay dense, for now.
6. The instruction kernel is the trusted kernel: only `Define` admits a
   definition, and only admitted definitions can be looked up. The term
   checker and the unfolding hints are untrusted elaboration aids.
