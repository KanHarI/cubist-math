# Kernel instructions: a THTH-style forward kernel

Status reconciled on 2026-10-26 against main `7230825e`. The instruction
kernel is the trusted kernel: elaboration checks every term through it, and
the driver searches with its own guide. Stages 1–5 are done, and the term
checker retired on 2026-10-02. Stage 6's performance and certificate work
remains open. Declared inductive types use H1's signature instructions
(K2.2), on by default since H1's release on 2026-10-02. The
[migration history](../historical/kernel-instructions-history.md), split out on
2026-10-26, records the stages, the retired primitive instructions and the
term checker's retirement. Dated measurements and review decisions below
retain their original revisions.

The merged [refactoring work](../historical/refactoring-and-testing.md) adds WASM enum parity
checks, a shared step-budget wrapper and explicit builtin dispatch. Stage-6
performance/certificate work remains open; instruction-driver reorganization
is deferred.

Kernel changes since come from the
[runtime track](../runtime/runtime-evaluation-roadmap.md), which records them:
the full-normalization cache (#269), bounded continuations for full
normalization (#291), weak-head tail chains (#292), stack-safe substitution
and dependency scans (#294), comparison and level worklists (#297), resource
failures preserved across the kernel and elaborator APIs (#285), and the
folded normal-form query `cc_kernel_normalize_folded` (#309). They do not
close stage 6's native search, certificate compaction or content hashes.
After the WebAssembly stack was placed below the static data (#321), the
recursion guards became one, `ck_enter`, which bounds a recursion's stack
bytes as well as its steps.
The kernel chapters of the language reference (#301) and the
[kernel guide](../../guides/kernel.md) (#299) document the trusted terms,
reduction and instructions.

## Goal

Move every *search* decision out of the trusted C kernel into the untrusted
elaborator, as in THTH. The kernel becomes a set of rule instructions that the
elaborator issues one at a time, each checked and answered with a judgement,
and it decides nothing on its own: no conversion strategy, no implicit
reduction, no unfolding hints. `with unfolding` and any future notion of
opacity become elaborator features only.

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
unfolded unless an instruction says so. The first proof, forward, as it was
written with the primitive `Nat` instructions, which were retired on
2026-09-30 when `Nat` became a declared type:

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
- **Levels (G0):** `Level` gives a level entry `x < ω`, a universe variable
  that only levels may mention; `Universe` takes a level expression to normal
  form, whose variables' entries are its context; `LevelPi`, `LevelLambda`
  and `LevelApply` are `Π (x < ω). B`, `λ (x < ω). t` and `f {ℓ}` at a
  finite `ℓ`. `Beta` and `Eta` cover them, `Lift` compares universes by level
  order, and composition at a level Π is pointwise.
- **Formation, introduction and elimination:** universes (`Universe`), `Π` (`Pi`,
  `Lambda`, `Apply`), `Σ` (`Sigma`, `Pair`, `First`, `Second`), `Unit`
  (`Point`, `UnitElim`), `Void` (`Abort`), sums
  (`Sum`, `Inject`, `SumElim`), paths (`Path`, `PathLambda`, `PathApply` at a
  dimension or an endpoint). `Domain` and `Family` give the parts of a `Π` or
  `Σ` type as types in its universe.
- **Definitions:** `Define` admits a closed judgement under a symbol and
  returns its lookup; `Lookup` recalls an admitted definition, and nothing
  else.
- **Equality judgements** `Γ ⊢ a ≡ b : T`, from `Refl`:
  - `Step(eq, side, position, rule)` contracts the highlighted redex, and only
    it: `Beta`, `Delta` (unfold the highlighted definition), `Iota` (an
    eliminator or projection on a constructor), `Path` (a path lambda at a
    point, or a path at an endpoint of its annotated type), `Face` (a
    composition with a tube on a face that holds, to that tube at the end of
    its dimension), `Whnf` (the kernel's weak head normal form), `Normalize`
    (the normal form of the highlighted subterm, by the kernel's fixed
    strategy; THTH's `BetaReduceGrossKnuth`), or `Glue` (Glue eta,
    `glue [φ ↦ t] (unglue b)` to `b`, when the two Glue types agree and `t`
    is `b` on each clause of `φ`, compared as they are, as weak heads, part
    by part under a common head, or as normal forms, with nothing else
    reduced; the `unglue` is the base's weak head, or what a nested Glue step
    exposes), or `Split` (a composition's system written one clause to a
    tube: a tube on a face of several clauses becomes one tube per clause,
    each the same term, and a tube on the face 0 goes; CCHM's systems are
    partial elements, the same whichever clauses their faces are written in,
    and a substitution of a compound point, `p @ (i ∧ j)`, leaves a tube on
    `i = 0 ∨ j = 0` where a derivation has one tube per clause).
  - `Replace(eq, side, position, a ≡ b)` swaps a highlighted occurrence of `a`
    for `b`: a targeted definitional-equality rewrite. When `a` or `b` uses a
    name bound on the way down, the given equality must have that name as a
    context entry of the binder's type — THTH's view of a bound variable as a
    context fragment — and the entry is discharged. Entry types are followed
    outwards, so a dependent binder's domain must agree too.
  - `Eta` (a term of a `Π`, `Σ`, path or Glue type equals its expansion;
    for `g` of a Glue type, `glue [φ ↦ g] (unglue g)`), `Side`, `Symmetry`,
    `Transitivity`.
- **Conversion:** `Convert(t : A, A ≡ B)` gives `t : B`; `Lift` raises
  `t : A` to a cumulative `B` (universes by level, `Π`/`Σ` by codomain).
  `Step` and `Replace` also rewrite the term or the type of a typing judgement
  in place, as THTH's `HighType` with a pointed reduction did: a reduct of a
  type is a type, so no typing judgement for the type is needed.
- **Endpoints:** `Endpoint` substitutes 0 or 1 for a dimension in a typing
  judgement, for the endpoint types of a dependent path family.
- **Faces:** `Restrict` gives `Γ, φ ⊢ t|φ : T|φ` from `Γ ⊢ t : T` and a
  face `φ` of one consistent clause: each of the clause's dimensions at its
  endpoint, in the context with `φ`'s face entry (see Contexts). It is what
  a partial element needs when it names a variable whose type mentions the
  face's dimensions, as a Glue term's value `g` on `i = 0` does for
  `g : Glue [i = 0 ↦ (T, e)] A`: there `g : T`, and Endpoint cannot show it,
  since `g` depends on `i`. The driver restricts a judgement by Restrict
  only where Endpoint would fail. It derives a partial element as it always
  did, and only where that fails, while a variable in scope has a type that
  mentions the face's dimensions, derives it again in a restricted scope,
  where each such variable is restricted where it is used, once for each
  face around it. So every derivation that needed no restriction is
  unchanged, and archive coverage is the same to the instruction and the
  step. The translator reads source the same way: it translates a part of a
  partial element on its face, where each of the face's coordinates is its
  endpoint (`Scope.onFace`), so `typed(loop @ 0, x)` inside a wall on
  `k = 0` checks for `x : loop @ k`. The cases are Cubist modules,
  `cubist-tests/face_restriction.cubist`, which the workspace opens to show
  each `Restrict` step.
- **Composition:** `comp^i A [φ ↦ u] a0` is built one tube at a time.
  - `System` starts from the family `A : U` over `i` and the base `a0 : A(0)`.
  - `SystemTube` adds a tube on a face of one clause. The tube is typed at `A`
    restricted to the face, and an equality shows it starts at the base
    there: `u(0) ≡ a0` on the face. Both may hold only on the face, typed
    by `Restrict`: the tube discharges the face entries its face implies. The face may be `1`, the clause with no
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
    constant on `φ`. Since 2026-10-01 both are for declared higher sorts
    only; before, they were for the primitive pushout types. `Face` takes a
    transport whose face holds to its base.
  - `PathAt` applies a path at any interval formula, such as `1 - i`.
- **Glue:** `Glue [φ ↦ (T, e)] A` is built piece by piece, as a composition's
  system is: `GlueBase` from `A : U`; `GluePiece` adds a type `T` on a face and
  an equivalence `e` at `Equiv(T, A)` there, the type the term checker
  states; where two pieces' faces meet, `GlueOverlap` takes equalities of
  their types and of their equivalences; `Glue` closes it. A Glue term is
  built the same way, a value `t : T` for each piece in order with an
  equality `fst(e)(t) ≡ a` on its face, and `SystemOverlap` where faces meet;
  as with tubes, a piece, a value and the equalities may hold only on their
  face, and the instruction that takes them discharges its face's entries;
  `Unglue` gives the base. A search aid, `cc_kernel_equiv_type`, builds
  `Equiv(T, A)` as syntax for the driver. Glue computes by `Whnf`.

Highlighting stays in the kernel on purpose: a short targeted reduction or
rewrite can replace normalizing a whole type.

### Contexts

A judgement keeps only the entries it depends on, and the contexts of premises
merge. Each context is closed under the entries' own dependencies. A binder
discharges one entry, only when no other entry of the context depends on it.
The free names and dimensions of a judgement's terms are always entries of its
context; this is what makes discharging, and replacement under binders,
capture-free.

A context may also hold **face entries**, CCHM's `Γ, φ`: the assumption that
a clause `φ`, a conjunction of endpoint equations, holds. `Restrict` adds
one, at most one per clause. A face entry is no variable: it has no symbol
and no type, and `Variable` and the binders refuse it. Its own context is
the clause's dimension entries, so while it is there no binder or `Endpoint`
discharges those dimensions, and `Define`, which takes only a closed
judgement, refuses it. It is discharged only by an instruction that takes a
partial element on a face implying its clause: `SystemTube` and
`SystemOverlap`, `GluePiece`, `GlueOverlap` and `GlueTermPiece`, each for its
own premises on its face. A face entry its face does not imply stays in the
result. One that an entry still depends on, a variable extended at a type
that holds only on the face, is refused, as any discharge is.

### Soundness

The trusted base is the instructions and what they call: the single-step
contractions, substitution, alpha equality, the normalizer and weak head
normal form (for `Normalize` and `Whnf`), the interval and face algebra, and
the metatheory the typing rules rely on (subject reduction, uniqueness of
types up to conversion, cumulativity). Since I1.2a, the pair and Glue eta
side conditions in reduction use syntax, not conversion search; the old
conversion checker was deleted with I1.2b. The driver's search is untrusted:
each proposed equality step must be admitted by the instructions. The judgement graph is truncated with the syntax arena on
rollback and commit. `test_instructions.c` derives addition and trees
forward over source-shaped Nat and W, and refuses the retired primitive
syntax; `test_kernel_api.c` checks that `Lookup` recalls only admitted
definitions and that `Define` refuses an open judgement.

The interval and face algebra keeps its decision procedure in the kernel: it
decides equality of De Morgan formulas, with no strategy to select.

Face entries rest on two facts of the cubical type theory, for a clause `φ`
and its substitution `σ` of each dimension by its endpoint: `Γ ⊢ J` gives
`Γ, φ ⊢ J`, and under `φ`, `t ≡ tσ` and `T ≡ Tσ`, since each dimension of
the clause equals its endpoint there. So `Restrict` derives only what holds
on `φ`. An instruction that discharges a face entry `ψ` takes premises that
CCHM's rule asks to hold on its face `φ` (a tube's `Γ, φ ⊢ u : A`, a Glue
value's `Γ, φ ⊢ t : T`, …); when `φ` implies `ψ`, `Γ, ψ ⊢ J` gives
`Γ, φ ⊢ J`. No other instruction removes a face entry, so a judgement whose
context holds none holds on the whole cube.

### What moves to the elaborator

- **Driving the rules.** The top-down checker becomes an untrusted driver: it
  walks the term the elaborator built and issues the instruction for each
  node, as each tactic's check runs and again when the declaration is
  defined.
- **Conversion search.** Where a rule needs two types to agree, or a type in a
  particular shape, the driver searches for the steps — the strategy
  `term_conversion.c` used then — and emits them as equality instructions.
- **Unfolding hints** do not move with it: the search finds its own order,
  so that proofs need no hints. A notion of opacity, if it returns, would be
  the search never emitting `Delta` for a definition.

### What the kernel keeps

The typing rules as instructions, the single-step contractions, alpha
equality, the interval and face algebra, deterministic normalization, the two
hash graphs, budgets and deadlines. The conversion strategy, the hints and
the implicit reductions were the term checker's, and were deleted with it on
2026-10-02.

## The driver

`InstructionDriver` derives a term's source syntax as instructions, one per
node. Where a rule needs two types to agree, it makes them agree without
trust:

- by congruence on common heads, when their parts are equal, and never twice
  on the same two terms: a failed attempt can leave an eta expansion that a
  step contracts again;
- by weak-head steps: beta, iota, path and face steps first, then unfolding
  definitions lazily. The one defined later is unfolded first, and both when
  they are the same (lazy delta reduction, as in Lean). A face step takes a
  composition whose face holds to its tube, where `Whnf` would go on to
  compute the tube's head, perhaps a large number in unary. A projection's
  or an eliminator's argument whose next step would unfold a definition or
  contract a lambda goes to its weak head in one `Whnf` step
  (`scrutineeStep`), where single steps took dozens of instructions;
- by `Whnf`, the kernel's own weak head normal form, for heads the steps do
  not take: composition, transport, Glue, pushouts;
- by eta, expanding a neutral term against a lambda, path lambda, pair or
  Glue term:
  - the neutral term is derived again at its position, and `Replace` puts its
    `Eta` expansion there;
  - below binders, the derivation uses entries named as the binders;
- by `Normalize` when that runs long;
- by `Lift` for cumulativity.

Where a function's domain and its argument's type must agree, both are
rewritten in place, toward a common form.

**Search aids.** The kernel offers queries that decide nothing:
`cc_kernel_whnf` gives a term's weak head normal form within a step budget,
or nothing when it or a nested computation runs out; `cc_kernel_rename`
renames a free name; `cc_kernel_equiv_type` builds `Equiv(A, B)` as syntax;
and `cc_kernel_fresh_symbol` allocates symbols, so the driver's names and the
kernel's never share an id. Two bridge reads, outside the trusted kernel,
serve the search: `cb_position_set` sets a position up to 64 children deep
in one call, and `cb_subterm` reads the subterm at it in a side of a
judgement. Neither changes the graph.

**The guide.** Whether two terms are equal, the driver answers itself (K1.4,
2026-09-27): it compares them lazily through their weak head normal forms,
the kernel's trusted reduction asked as a query. They are equal when
alpha-equal before or after taking heads; different when the heads are
constructors or neutral terms that differ, since normal forms are unique;
unknown when eta could relate them, a head is a cubical construction, or its
fuel runs out (400 pairs of subterms per question, 4000 kernel steps per
head). A path at an endpoint of its annotated type is that endpoint, as the
path step takes it, with nothing computed: otherwise a head would unfold a
whole proof. The driver asks only where the answer changes its choice: on a
common head that could also be reduced. Where the head reduces by computation
(beta, iota, path or face), it reduces unless the parts are known equal;
where only unfolding a definition would, it compares parts not known to
differ. Every step it then takes is still an instruction the kernel checks.

The K1.4 measurement before L1.1 recorded 37 s for the archive check and
13.9 s for re-derivation; with the old conversion oracle, 34.9 s and 10.1 s.
In that comparison, the oracle run failed one second derivation,
`group_homomorphisms.group_hom_laws_prop`, with "The argument has the wrong
type". The current guide's observation is recorded above. The oracle
comparison can no longer be rerun; the option was removed on 2026-10-02.

After 64 steps in one comparison, two closed subterms the guide does not
find different, such as a numeral's arithmetic, are normalized, one
instruction each: single steps each rebuild the judgement's term, and a
factorial's took 1.1M arena nodes where 58k now do. Steps are counted over the
whole comparison, since congruence splits a computation into many short
ones, often under a binder. Past the limit, a comparison of open subterms
inside a closed one gives up, and the closed one tries normal forms, once;
if that fails, the steps go on. Each normal form may take 250,000 kernel
steps (`NORMAL_FORM_STEPS`). A term whose normal form was not reached is
remembered, and later comparisons with it keep to lazy steps at once, since
normalization is deterministic. Open terms keep to lazy steps, since their
normal forms can be enormous. A path lambda applied at a compound interval
formula contracts its body's computing head first, before the formula is
substituted; the driver's alpha comparison is memoized over the shared term
graph, since walking it as a tree is exponential in its depth. Its renaming
of dimensions is first cut to the dimensions the two terms mention, so a
subterm met under many different binders is still compared once.

Levels (G0) are compared by normal form, never part by part: the driver
reads a universe's or an instantiation's level as a normal form, names each
variable bound on the way down by its binder, and issues `Convert` when two
levels are equal and `Lift` when they differ, so only the kernel decides
their order. A level lambda instantiated at a level contracts by `Beta`, as
a lambda applied does.

A binder's variant name, when its own is taken at another type, is
remembered by name and type and used again, and the kernel reuses an entry at
an alpha-equal type: two entries for one variable would make terms that
mention it differ for ever.

The driver caches judgement reads, scopes and derivations; the kernel indexes
entries by symbol. Together, these took the archive from 457 s to 14 s.
A derivation is cached by the part of its scope it reads
(`InstructionDriver.narrow`): the entries of its free variables, the live
dimensions, the faces and the dimensions the scope's types mention, so a
subterm met under many binders it does not mention, as a folded normal
form's closed parts are, is derived once
([report](../../reports/driver-derivation-sharing.md)).
Since 2026-10-06 the kernel wrapper also keeps each node read and each weak
head for the declaration, and keeps reads of settled nodes from one
declaration to the next.

A learned policy for this search, trained against the kernel with the
heuristic as its teacher and derivation cost as its objective, is designed
in [learned-search.md](learned-search.md).

**Branch points.** Each time round, `agree` stops at a branch point and lists the
moves open there: normalize both sides (a long closed computation, once per
comparison), split a side's composition where two compositions' tubes are
on different faces and its tubes are not one clause each (the split move,
first), descend by congruence, a weak-head step on either side or both
(beta, iota, path, face or delta), a side's weak head normal form, eta, or,
last, a `Glue` step on a side that is a Glue term (the glue move). Normal
forms keep each system's faces as written, so when a conversion falls back
to normal forms that differ and either has a tube on several clauses, it
compares them once more, where the split move applies. The list
is syntactic; the kernel checks the rest when a move is made. A
policy (`heuristicPolicy` and the interface beside it) ranks the moves,
and the driver makes them in that order until one applies. The default
policy is the order described above, lazily, since its tests ask the
guide; it derives the archive with an identical elaboration fingerprint.
Policies are untrusted: a bad one only fails, and one that picks a move the
point did not offer is refused.

**Cost.** The kernel counts its work cumulatively (`cc_kernel_work`, read
by `CubicalKernel.work()`), so the difference of two readings is the work
done between them. Every operation starts with the step budget: an
instruction, or a query, which is the term checker, `whnf`, normalization,
conversion, or the substitution and renaming services. One step is one unit
of that budget: an inference or reduction step, a conversion comparison, a
substituted node, a level normal-form node, and the step each instruction
takes on entry, so an instruction answered from the derivation memo still
costs one. Work nested in an operation shares its budget. Instructions and
queries are counted apart, with their steps and their failures, and so are
exhausted budgets and deadlines. Nothing resets the counters: not errors,
not rollback, not a retry with a larger budget, whose work is counted
again. `kernel/tests/test_work.c` and `tests/driver-search.test.mjs` check
the accounting against direct calls.

`node tools/instruction-coverage.mjs` reports this cost for the archive
check and for each definition derived again, rejected instructions and the
guide's queries included, with the driver's branch points and the outcome
of each move. It pins the revision, the machine, the budgets and the
session mode in its report, can write every branch point of every
derivation as JSON lines (`--trajectories=FILE`), and exits with status 1
unless every import checks, no gap remains and every definition derives.

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

If a derivation cannot be shown, a panel shows the reason; since Stage 5
there is no term checker's trace to fall back to.

Since [#298](https://github.com/KanHarI/cubist-math/pull/298) (2026-10-20)
the workbench's AST view applies an existing kernel reduction rule to one
selected occurrence by issuing the `Step` instruction
(`web/cubical-kernel-step.mjs`), and can undo it. The rules include β, δ, eliminators, paths, composition, Glue, WHNF and
normalization. Each attempt and its counters are recorded in a copyable
trace. No C rule changes.

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
   trusted kernel. Unfolding hints leave the kernel. Done; see the
   [migration history](../historical/kernel-instructions-history.md#stage-4-the-trusted-kernel).
5. **The term checker leaves elaboration:** the driver derives source syntax
   itself. Done; see the
   [migration history](../historical/kernel-instructions-history.md#stage-5-the-term-checker-leaves-elaboration).
   The term checker then retired on 2026-10-02
   ([I1.2b](../historical/kernel-instructions-history.md#what-remains-of-the-term-checker)).
6. **Performance:** an untrusted native search module if JavaScript is too
   slow; certificate compaction; content hashes for exported certificates;
   a learned search policy for cheaper derivations
   ([learned-search.md](learned-search.md)). Started on 2026-10-06
   (#194–#197): the bridge reads a focused subterm in one call; the kernel
   wrapper keeps node reads and weak heads; normal forms are bounded and not
   retried; and a projection's argument goes to its weak head in one step.
   The recorded library measurement was about four times faster than
   before #194; this reconciliation did not rerun that benchmark. The native search module, certificate compaction, content
   hashes and a learned policy remain.

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
   checker and the unfolding hints were untrusted elaboration aids, retired
   on 2026-10-02.
7. Elaboration checks nothing with the term checker. Its conversion was a
   search aid only, until both were retired.
8. Every later kernel feature is instructions only. The term checker's rules
   and the JavaScript reference checker were not extended, and they retired
   once the driver no longer benefited from the conversion oracle.
9. (2026-09-28) An instruction's acceptance may not depend on an untrusted
   query. The folded comparison reads only its own memo entries, reduction
   decides its eta rules by syntax, and the conversion search refuses to
   run inside an instruction. I1.2a established this before I1.2b deletes
   code.
10. (2026-10-28) The recursion guard, `ck_enter`, bounds both stack bytes
    (`CC_STACK_BUDGET`, 4 MiB) and steps (`CC_RECURSION_LIMIT`). The user
    decided its three open questions: the step bound stays beside the byte
    bound, since under WebAssembly the engine's own stack, which the kernel
    cannot measure, runs out first; the limit is 448 steps, 28% and 37%
    under the depths at which a Chromium worker's stack ran out for the
    cycles measured (622 and 708); and it holds on every platform, native
    included. The [kernel guide](../../guides/kernel.md) records the
    measurements.
