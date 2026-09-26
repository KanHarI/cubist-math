# Kernel instructions: a THTH-style forward kernel

Status: design, on the `kernel-instructions` branch. Nothing here changes the
current kernel yet.

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

## The instruction kernel

The kernel keeps a store of checked judgements `Γ ⊢ t : T` and contexts, as
THTH's graph store did, and offers one instruction per typing rule. An
instruction takes handles of earlier judgements and contexts, plus small
immediate data (a bound name, a definition, a position), checks its side
conditions **syntactically** — types must be identical up to bound names — and
returns the handle of a new judgement. Nothing is reduced or unfolded unless an
instruction says so.

```
nat  = NatForm()                      // {} ⊢ Nat : U0
ctx  = CtxExt(nat)                    // {n : Nat}
n    = Vble(ctx)                      // {n : Nat} ⊢ n : Nat
sn   = NatIntroS(n)                   // {n : Nat} ⊢ succ(n) : Nat
lt   = DefLookup(first__lt)           // {} ⊢ lt : Nat → Nat → U0
ltn  = PiElim(lt, n)                  // {n : Nat} ⊢ lt(n) : Nat → U0
goal = PiElim(ltn, sn)                // {n : Nat} ⊢ lt(n, succ(n)) : U0
…
p    = Conv(pair, goal,               // {n : Nat} ⊢ (0, refl(succ(n))) : lt(n, succ(n))
          [expected, [], Delta(lt)],  //   unfold lt at the head of the expected type
          [expected, [], Beta], …)
```

### Instruction families

Following THTH's 67 opcodes, adapted to the cubical theory:

- **Contexts:** `CtxExt` (a context gains `x : A` from `Γ ⊢ A : U_i`), `Vble`,
  and, for cubical terms, dimension and face extension.
- **Formation, introduction and elimination** for each type former:
  universes, `Π`, `Σ`, `Nat`, `Unit`, `Void`, sums, `W`, paths, composition and
  transport, `Glue`, pushouts.
- **Definitions:** `Define` registers a closed judgement under a name;
  `DefLookup` recalls it.
- **Conversion:** `Conv(j, B, steps)` turns `Γ ⊢ t : A` into `Γ ⊢ t : B`.
  Each step names a side (the type found or the type expected), a position (a
  path of child indices), and one rule: `Beta`, `Delta(d)` (unfold definition
  `d`), `Iota` (an eliminator or projection on a constructor), `Eta`, or one of
  the cubical computation rules. The kernel checks that the named node is a
  redex of that rule and contracts it there, using the single-step reductions
  it already has. After the steps, the two types must be identical up to bound
  names; universe cumulativity remains a rule.
- **Normalization (proposed):** `Normalize(side, position)` replaces a subterm
  by its normal form, with the kernel's fixed, complete strategy. THTH had this
  too (`BetaReduceGrossKnuth`). It involves no choice, so it is computation,
  not search, and it keeps large computations — a factorial, a binary numeral
  — in C instead of in million-step certificates.

The interval and face algebra keeps its decision procedure in the kernel: it
decides equality of De Morgan formulas, with no strategy to choose.

### What moves to the elaborator

- **Driving the rules.** Today's top-down checker becomes an untrusted driver:
  it walks the term the elaborator built and issues the instruction for each
  node, as the kernel does now. Later, tactics can issue instructions directly
  (`intro` is `CtxExt` then `PiIntro`, `exact` a `Conv`).
- **Conversion search.** Where a rule needs two types to agree, or a type in a
  particular shape, the driver searches for the steps — the strategy
  `term_conversion.c` uses today — and emits them in a `Conv`.
- **Unfolding hints** order that search. A notion of opacity, if it returns,
  would be the search never emitting `Delta` for a definition.

### What the kernel keeps

The typing rules as instructions, the single-step contractions, alpha
equality, the interval and face algebra, deterministic normalization,
hash-consing of syntax, budgets and deadlines. It loses the conversion
strategy, the hints and every implicit reduction.

### Inspection

The instructions the elaborator sends are the derivation: the Elaboration
panel shows them directly, instead of reconstructing a derivation from a trace
(#36). Each `Conv` shows exactly which positions were reduced.

## Costs and risks

- **Proof size and speed.** Every node becomes an instruction, and every
  conversion carries its steps. The search moves out of C; running it in
  JavaScript is slower, so it may live in an untrusted C/WASM module beside the
  kernel instead.
- **The cubical rules.** Composition for each type former, `Glue` and pushouts
  make up most of the kernel's rules and computation; each needs an
  instruction and positioned contraction steps.
- **Migration.** The rebuilt library and the 365 archived modules must check in
  instruction mode, with the same judgements.
- **Surfaces.** The bridge, the JavaScript kernel wrapper, the program, the
  inspector, the workbench and the CLI's `assembly` all change.

## Stages

1. **Core instructions** in C, beside today's checker: the judgement store,
   `CtxExt`, `Vble`, `UIntro`, `Π`, `Σ`, `Nat`, `Unit`, `Void`, sums, paths
   without composition, `Define`/`DefLookup`, `Conv` with `Beta`, `Delta`,
   `Iota`, `Eta` and `Normalize`. Kernel tests for each.
2. **Untrusted driver and search** in JavaScript: turn a checked term into
   instructions and conversion steps. The first proof and `library/naturals`
   check in instruction mode, with the same judgements as the term checker;
   the Elaboration panel shows the instructions.
3. **W types and the cubical rules:** composition, transport, `Glue`,
   pushouts. The archive checks in instruction mode.
4. **Tactics issue instructions directly**, and the term checker leaves the
   trusted kernel. Unfolding hints leave the kernel.
5. **Performance:** an untrusted native search module if JavaScript is too
   slow; certificate compaction.

## Decisions to make

1. Whether `Normalize` is allowed, or every conversion is single steps.
2. Where the conversion search lives: JavaScript, or an untrusted native
   module.
3. How contexts combine: THTH's context fragments with explicit dependencies,
   or ordered contexts with explicit weakening.
