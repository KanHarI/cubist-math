# Universe-generic checking (G0): rules and consistency

Status: specification for review. Written on 2026-09-25 as work-plan item
K1.1, and revised the same day with the user's decisions on tiered
universes. It specifies [kernel roadmap](cubical-kernel-roadmap.md) item G0.
Nothing here is implemented. K1.2 (reference checker), K1.3 (C kernel) and
L1.1 (language) implement it, and section 5 is their acceptance list.

## Revision

The first version (PR #10) kept universe-generic statements outside every
universe. This revision applies four decisions:

- Universes are indexed by ordinals below ω², in tiers: `U0, U1, …`, then
  `UU0, UU1, …`, then `UUU0, …`. Every universe is a term.
- The universe binder is `U < UU0`. It replaces `U : Universe` and the
  kernel's `Uω` marker. The word `Universe` leaves the language.
- Generic statements are ordinary types. `forall U < UU0, B` lives in `UU0`
  when `U` occurs in the level of `B`, and at the level of `B` otherwise. The
  judgment for large types is gone, and composition gains one pointwise rule
  for level quantification.
- `LEM`, `Choice` and `Truncate` are generic over small universes only.

Q2 and Q3 are resolved by these decisions. The remaining questions were
answered on 2026-09-25: Q1, Q4, Q5, Q6, Q8 and Q9 as recommended. Q7 and Q10
are deferred as [language enhancement proposals](language-enhancement-proposals.md)
E1 and E2 (section 6).

## Decisions in brief

- **Levels** are ordinals below ω². A constant `ω·k + n` has tier `k`. Level
  expressions are constants, `ℓ + 1`, `max(ℓ, ℓ')` and level variables. In
  this version every level variable ranges over the natural numbers, tier 0.
- **Universe constants** always carry their index: `U0, U1, …` (level `n`),
  `UU0, UU1, …` (level `ω + n`), `UUU0, …` (level `ω·2 + n`), one more `U`
  per tier. The shape `U+[0-9]+` is reserved. `U`, `UU` and `UUU` are
  ordinary names.
- **Every universe is a term.** `U(ℓ) : U(ℓ + 1)` at every tier, and
  cumulativity crosses tiers: `U(n) ≤ U(ω) ≤ U(ω + 1) ≤ … ≤ U(ω·2) ≤ …`.
- **The binder `U < UU0`** binds a level variable that ranges over the levels
  below ω. Its bound is binder syntax, never a term. Only tier bases may be
  bounds, and this version implements only `< UU0`.
- **Generic statements are ordinary types.** `Π (x < ω). B` lives at `ω` when
  `x` occurs in the level of `B`, and at that level otherwise. Every type
  lives in some universe.
- **Instantiation** `t {ℓ}` requires `ℓ < ω`. It has a β-rule that
  substitutes the level, and an η-rule.
- **Cumulativity is symbolic**, decided on level normal forms, and extends to
  level-Π codomains.
- **One new composition rule.** Composition at a level Π is pointwise under
  the binder. No reduction rule reads a level.
- **`LEM`, `Choice` and `Truncate`** are generic over `U < UU0` only. They
  have no instances at tier 1 or above.
- **Consistency.** Levels are interpreted as ordinals below ω², with a
  Grothendieck universe for each, from ω² inaccessible cardinals. A level Π
  is an ℕ-indexed product, which lies in `U_ω`. No binder ranges over all
  tiers, so no universe above them all is needed.

## Notation

| Symbol | Meaning |
| --- | --- |
| `x`, `y`, `z` | level variables |
| `a`, `b`, `f` | term variables |
| `t`, `u` | terms |
| `i`, `j` | interval dimensions |
| `ℓ`, `ℓ'` | level expressions |
| `n`, `c` | natural numbers |
| `κ` | a level constant `ω·k + n` below ω², of tier `k` |
| `ω` | the constant `ω·1 + 0`, the level of `UU0`; also the bound of a binder over tier 0 |
| `Π (x < ω). B` | level quantification (source: `forall U < UU0, B`) |
| `λ (x < ω). t` | level abstraction (source: `fun (U < UU0) => t`) |
| `t {ℓ}` | instantiation of `t` at level `ℓ` (source: `t(E)`) |
| `U(ℓ)` | the universe at level `ℓ`; `U0` is `U(0)`, `UU0` is `U(ω)`, `UU3` is `U(ω + 3)`, `UUU0` is `U(ω·2)` |
| `Γ` | a context of term entries `a : A` and level entries `x < ω`; dimensions are tracked separately, as today |

`ω` is kernel notation. The source writes `UU0`.

"The kernel" means both checkers: the reference checker in
`lib/cubical/core.mjs` and the C kernel in `kernel/src`. They implement the
same rules independently.

## 1. Syntax

### 1.1 Levels

```text
κ ::= ω·k + n                      k, n ∈ ℕ; written n when k = 0, and ω + n when k = 1
ℓ ::= κ  |  ℓ + 1  |  max(ℓ, ℓ')  |  x
```

- Levels are not terms. A level occurs in exactly two places: as the argument
  of `U(ℓ)`, and as the argument of an instantiation `t {ℓ}`.
- A level variable is bound by `Π (x < ω)`, by `λ (x < ω)`, or by a level
  entry `x < ω` of a context. It ranges over the levels below ω: the natural
  numbers.
- Levels contain no term variables and no dimensions. So a level never varies
  along a line: every type family over the interval lives in one universe.
- ω² is not a level. No constant names it, and no level expression denotes
  it.

### 1.2 Level binders and bounds

A level binder carries a bound: a tier base `ω·k` with `k ≥ 1`. The binder
`x < ω·k` ranges over the levels below `ω·k`. This version admits only the
bound `ω`; section 1.5 describes the others.

The bound may appear only:

- in a level binder, `Π (x < ω). B` or `λ (x < ω). t`;
- in a level entry `x < ω` of a context. Declaration parameters and entries
  of the kernel's assumption telescope are such entries.

The bound is binder syntax, never a term. It may not appear:

- as an argument, a function, a body, a pair component, a system piece, or a
  definition's value;
- as the type of a term, including an expected type or an ascription;
- with a type: no judgment gives the bound a type;
- in a comparison: no conversion or cumulativity rule mentions it, except by
  matching two level binders;
- in any binder other than Π and λ. There is no `Σ (x < ω)`.

The bound `ω` and the level `ω` are different things. The level is the
argument of `U(ω)`, the term `UU0`. The bound only marks a binder's range.
They share a symbol because `x < ω` means what the order judgment `ℓ < ω` of
2.4 means: `x` ranges over the finite levels.

### 1.3 Kernel forms

| Form | Status |
| --- | --- |
| `U(ℓ)` | Changed: the argument is a level expression instead of a numeral. |
| `Π (x < ω). B`, `λ (x < ω). t`, `t {ℓ}` | New. `Π (x < ω). B` is an ordinary type. |
| every other former | Unchanged. Its type arguments may live at any level. |

The C kernel represents level binders by their own node kinds rather than by
Π and λ with a special domain (section 4.2). Code that handles Π therefore
cannot meet a level binder by accident.

### 1.4 Source surface

This follows the kernel roadmap's G0 item and ergonomics milestone 5.

- **Universe constants.** A name of the shape `U+[0-9]+` is a universe
  constant. `k + 1` letters `U` followed by the decimal numeral `n` denote
  `U(ω·k + n)`: `U2` is `U(2)`, `UU0` is `U(ω)`, `UUU3` is `U(ω·2 + 3)`. The
  numeral has no leading zeros, so `U01` is malformed. Every name of this
  shape is reserved: it cannot be bound or declared. A constant always
  carries its index. `U`, `UU` and `UUU` are not constants and remain free
  for user variables.
- **Universe binders.** `U < UU0` binds a universe variable `U` that ranges
  over `U0, U1, …`. Grouping works as today: `(U V < UU0, A : U, B : V)`.
  Examples:
  - `def identity(U < UU0, A : U, x : A) = x;`
  - `forall U < UU0, B` is `Π (x < ω). B`;
  - `fun (U < UU0) => t` is `λ (x < ω). t`.
- **Bounds.** A bound must be a tier base: `UU0`, `UUU0`, … . L1.1 accepts
  only `UU0`. `U < U5` and `U < UU1` are rejected because they are not tier
  bases, and `U < UUU0` because it is not implemented yet (1.5).
- **Universe expressions** are constants, universe variables, `next(E)` and
  `max(E, F)`. They denote levels: a constant its level, a variable `U` its
  level variable `x`, `next(E)` the level `ℓ_E + 1`, and `max(E, F)` the
  level `max(ℓ_E, ℓ_F)`.
- In term position a universe expression denotes the term `U(ℓ_E)`:
  `A : U`, `x =[next(U)] y`, `Group(U) : next(U)`, `T : UU0`.
- As the argument of a universe parameter it denotes the level `ℓ_E`, which
  must be below ω. `identity(U2, U1, U0)` instantiates `identity` at level
  2. `identity(UU0, T, x)` is rejected.
- **`Universe` is removed.** The old binder `U : Universe` is an error whose
  message suggests `U < UU0`.
- Universe arguments stay explicit in L1.1. Ergonomics milestone 5, which
  absorbs HoTT A9, later infers them from level constraints. An undetermined
  level remains an error, and the inspector shows inferred levels.
- Examples elsewhere that write `A : U` with `U` unbound, such as
  `inductive List(A : U)` in the H design, presuppose milestone 5's implicit
  binders. Under L1.1 they read `(U < UU0, A : U)`.
- The source has no separate level syntax: no `Level` type, no bare numerals
  as levels, and no `ω`.

### 1.5 Later extension: bounds above `UU0`

The design admits a binder `V < UUU0`, whose variable ranges over the levels
below ω·2: every `U_n` and every `UU_n`. One definition then serves both
tiers, as in `identity2(V < UUU0, A : V, x : A)` used at `U1` and at `UU1`.
This version does not implement it. What it would need:

- Level variables carry their bound. A constant absorbs a variable only when
  the constant is at least the variable's bound. So for `v < ω·2`,
  `max(ω, v)` stays as written: it is `ω` at `v = 3` and `ω + 2` at
  `v = ω + 2`.
- The order test of Lemma 2 sets each variable to a large value within its
  own range.
- `Π (v < ω·2). B` lives at `ω·2` when `v` occurs in the level of `B`.
  Instantiation requires `ℓ < ω·2`.
- The model uses the discrete presheaf on the ordinal ω·2 instead of ℕ. The
  composition rule of 2.11 is unchanged.

Even then no binder ranges over all tiers. Every bound is a tier base below
ω², so every level Π lives below ω² (3.3). The extension needs its own
review. It changes none of L1.1's syntax.

## 2. Judgments and rules

### 2.1 Judgment forms

| Judgment | Meaning |
| --- | --- |
| `⊢ Γ` | `Γ` is a well-formed context. |
| `Γ ⊢ ℓ level` | `ℓ` is a level whose variables are level entries of `Γ`. |
| `ℓ ≤ ℓ'`, `ℓ = ℓ'`, `ℓ < ℓ'` | Level order and equality. They depend only on the two expressions. |
| `Γ ⊢ A : U(ℓ)` | `A` is a type in `U(ℓ)`. |
| `Γ ⊢ t : A` | `t` has type `A`, where `Γ ⊢ A : U(ℓ)` for some `ℓ`. |
| `A ≡ B` | Conversion: the kernel's untyped definitional equality. |
| `A ≤ B` | Cumulativity: directed typing between checked types. |

Every type lives in some universe. The first version's judgment for large
types is gone, together with its rules for a Π with a large part.

### 2.2 Contexts

```text
C-Empty                                         ⟹  ⊢ ·
C-Term    ⊢ Γ    Γ ⊢ A : U(ℓ)    a ∉ Γ           ⟹  ⊢ Γ, a : A
C-Level   ⊢ Γ    x ∉ Γ                          ⟹  ⊢ Γ, x < ω
```

- Term and level entries may interleave. No entry's type can depend on a
  level entry except through level expressions.
- Level and term variables share one name supply. A name is bound once in a
  context; the kernel renames binders to avoid shadowing, as today.
- A term entry may have a generic statement as its type. That is how a
  parameter or an assumption can be universe-generic. Its type lives in
  `U(ω)`.

### 2.3 Level well-formedness

```text
L-Const   ⊢ Γ                                   ⟹  Γ ⊢ κ level
L-Var     ⊢ Γ    (x < ω) ∈ Γ                    ⟹  Γ ⊢ x level
L-Succ    Γ ⊢ ℓ level                           ⟹  Γ ⊢ ℓ + 1 level
L-Max     Γ ⊢ ℓ level    Γ ⊢ ℓ' level           ⟹  Γ ⊢ max(ℓ, ℓ') level
```

Side conditions: `top(ℓ) ≤ LEVEL_MAX` and `tier(ℓ) ≤ TIER_MAX`, where `top`
and `tier` are defined in 2.4, `LEVEL_MAX = 65535` and `TIER_MAX = 255`. A
term variable, a term, or a bound in level position is rejected.

The bounds are resource limits, not logical rules: they can only cause
rejection. `LEVEL_MAX` bounds the finite part within each tier. Together they
keep native level arithmetic within 32 bits with room for successor and
substitution, and no mathematics needs more (Q9).

### 2.4 Level normal form, equality and order

**Normal forms.** A normal form is one of two kinds:

- **finite** `(c, m)`: a tier-0 constant `c ∈ ℕ` plus variable offsets. `m`
  maps finitely many variables to offsets in ℕ, and `c ≥ m(x)` for every
  `x`;
- **constant** `κ` of tier 1 or above. It absorbs every tier-0 variable.

```text
nf(κ)            = (n, ∅)                   if κ = n has tier 0
                 = κ                        otherwise
nf(x)            = (0, {x ↦ 0})
nf(ℓ + 1)        = (c + 1, {x ↦ m(x) + 1})  if nf(ℓ) = (c, m)
                 = κ + 1                    if nf(ℓ) = κ, where (ω·k + n) + 1 = ω·k + (n + 1)
nf(max(ℓ, ℓ'))   = (max(c, c'), m ⊔ m')     if nf(ℓ) = (c, m) and nf(ℓ') = (c', m')
                 = κ                        if one side is κ and the other is finite
                 = max(κ, κ')               if both sides are constants
```

`m ⊔ m'` keeps the larger offset of each variable. Constants compare as
ordinals: `ω·k + n ≤ ω·k' + n'` when `k < k'`, or `k = k'` and `n ≤ n'`.
`top(ℓ)` is `c` for a finite form and `n` for `κ = ω·k + n`. `tier(ℓ)` is 0
for a finite form and `k` for `κ`. For example `nf(x + 1) = (1, {x ↦ 1})` and
`nf(max(x + 3, ω)) = ω`.

**Meaning.** For an assignment `ρ` of natural numbers to variables,
`⟦(c, m)⟧ρ = max(c, max over x of ρ(x) + m(x))`, a natural number, and
`⟦κ⟧ρ = κ`. Expressions are evaluated with ordinal successor and maximum.

**Lemma 1 (soundness).** `⟦ℓ⟧ρ = ⟦nf(ℓ)⟧ρ` for every `ρ`. By induction on
`ℓ`. There are two absorptions:

- absorbing offsets into `c` is harmless because `ρ(x) + m(x) ≥ m(x)`;
- absorbing a finite form into a constant `κ` of tier 1 or above is harmless
  because every finite value is below `ω ≤ κ`.

**Lemma 2 (order).** `⟦ℓ⟧ρ ≤ ⟦ℓ'⟧ρ` for every `ρ` if and only if the
condition below holds. Here `κ` and `κ'` are constant normal forms, of tier
1 or above.

| `nf(ℓ)` | `nf(ℓ')` | Condition |
| --- | --- | --- |
| `(c, m)` | `(c', m')` | `c ≤ c'`, and every `x` in `m` is in `m'` with `m(x) ≤ m'(x)` |
| `(c, m)` | `κ'` | always |
| `κ` | `(c', m')` | never |
| `κ` | `κ'` | `κ ≤ κ'` as ordinals |

- If: in the first row every part of `ℓ` is bounded by a part of `ℓ'`. In
  the second, finite values are below `κ'`. The fourth compares constants.
- Only if, first row: the assignment `ρ = 0` gives `c ≤ c'`. For `x` in `m`,
  set `ρ(x) = N` with `N > c'` and every other variable to 0. The left side
  is at least `N + m(x)`. The right side is `max(c', N + m'(x))` if `x` is in
  `m'`, and `c' < N` otherwise.
- Only if, third row: at `ρ = 0` the right side is `c' < ω ≤ κ`.

**Corollary 3 (equality).** `ℓ` and `ℓ'` agree for every `ρ` if and only if
`nf(ℓ) = nf(ℓ')`. A finite form never equals a constant of tier 1 or above,
by the third row. So the normal form is unique, and equality is identity of
normal forms.

**Definitions.** `ℓ ≤ ℓ'` and `ℓ = ℓ'` mean the conditions of Lemma 2 and
Corollary 3. `ℓ < ℓ'` means `ℓ + 1 ≤ ℓ'`. In particular `ℓ < ω` holds
exactly when `nf(ℓ)` is finite; such a level is **finite**. Every check is
linear in the size of the normal forms.

**Printing.** A finite form prints as `max(c, x + m(x), …)`, omitting `c`
when `m` is non-empty and `c` equals its largest offset, omitting `+ 0`, and
ordering variables by name. A constant prints as `ω + n` or `ω·k + n`,
omitting `+ 0`. The source prints universe expressions: `max(U, U1)`, `UU3`,
`UUU0`.

| Expression | `nf` | Printed |
| --- | --- | --- |
| `max(x, x)` | `(0, {x↦0})` | `x` |
| `max(x + 1, x)` | `(1, {x↦1})` | `x + 1` |
| `max(0, x)` | `(0, {x↦0})` | `x` |
| `max(1, x + 1)` | `(1, {x↦1})` | `x + 1` |
| `max(1, x)` | `(1, {x↦0})` | `max(1, x)` |
| `max(x, y) + 1` | `(1, {x↦1, y↦1})` | `max(x + 1, y + 1)` |
| `3` | `(3, ∅)` | `3` |
| `max(x, ω)` | `ω` | `ω` |
| `max(x + 2, ω + 1) + 1` | `ω + 2` | `ω + 2` |
| `max(ω + 7, ω·2)` | `ω·2` | `ω·2` |

Level variables are unconstrained: there are no declared constraints such as
`x < y` between variables. A binder's bound is not such a constraint; it
fixes the variable's range. So validity for all assignments is the whole
theory, and no constraint solving or loop checking is needed (Q7).

### 2.5 Universes and cumulativity

```text
U-Form   Γ ⊢ ℓ level    top(ℓ) < LEVEL_MAX      ⟹  Γ ⊢ U(ℓ) : U(ℓ + 1)
U-Eq     nf(ℓ) = nf(ℓ')                         ⟹  U(ℓ) ≡ U(ℓ')
U-Cum    ℓ ≤ ℓ'                                 ⟹  U(ℓ) ≤ U(ℓ')
Sub      Γ ⊢ t : A    Γ ⊢ B : U(ℓ)    A ≤ B      ⟹  Γ ⊢ t : B
```

- Universes are à la Russell: an element of `U(ℓ)` is itself a type.
- Every universe is a term, at every tier. `U(ω) : U(ω + 1)`, and
  `U(ω·2 + 3) : U(ω·2 + 4)`. Successor stays within a tier.
- Cumulativity crosses tiers:
  `U(n) ≤ U(ω) ≤ U(ω + 1) ≤ … ≤ U(ω·2) ≤ …`. So `U(n) : U(ω)` for every `n`,
  and `x < ω ⊢ U(x) : U(ω)`.
- Cumulativity is subsumption, as today
  ([cumulativity.md](../cubical/cumulativity.md)). There are no lift terms,
  and two universes are convertible only when their levels are equal.
- Examples: `U(x) : U(x + 1)`, `U(x) : U(max(x + 1, y))`, `Nat : U(x)` and
  `U(x) : U(ω)`. But not `U(x) : U(x)`, not `U(x) : U(1)`, and not
  `U(ω) : U(ω)`. `A : U(x)` does not give `A : U(0)`, and `A : U(ω)` does
  not give `A : U(x)`.

### 2.6 Type formers

The existing rules stand, with level expressions in place of numerals. The
result's level is the `max` of the inferred levels of its parts:

| Former | Result universe |
| --- | --- |
| `Nat`, `Unit`, `Void` | `U(0)` |
| `U(ℓ)` | `U(ℓ + 1)` |
| `Π (a : A). B`, `Σ (a : A). B`, `W (a : A). B` | `U(max(ℓ_A, ℓ_B))` |
| `Π (x < ω). B` | `U(lim_x(ℓ_B))`, by 2.7 |
| `A + B` | `U(max(ℓ_A, ℓ_B))` |
| `Pushout(C, A, B, maps)` | `U(max(ℓ_C, ℓ_A, ℓ_B))` |
| `Path(i. A, a, b)` with `Γ, i : I ⊢ A : U(ℓ)` | `U(ℓ)` |
| `Glue [φ ↦ (T, e)] A` | `U(max(ℓ_A, ℓ_T, …))` |

The inferred level is the least one. A check against a larger universe uses
`U-Cum`. Every former accepts types of every level and tier, including
generic statements. The same holds wherever an existing rule asks for a
type: eliminator motives may land in any universe, and pair annotations,
Glue annotations and `Abort` targets may be at any level.

### 2.7 Level quantification

```text
∀-Form    Γ, x < ω ⊢ B : U(ℓ)                           ⟹  Γ ⊢ Π (x < ω). B : U(lim_x(ℓ))
∀-Intro   Γ, x < ω ⊢ t : B                              ⟹  Γ ⊢ λ (x < ω). t : Π (x < ω). B
∀-Elim    Γ ⊢ f : Π (x < ω). B    Γ ⊢ ℓ level    ℓ < ω   ⟹  Γ ⊢ f {ℓ} : B[x := ℓ]
∀-β       (λ (x < ω). t) {ℓ}  ≡  t[x := ℓ]
∀-η       f  ≡  λ (x < ω). f {x}                        when x is not free in f
```

**The limit rule.**

```text
lim_x(ℓ) = ω         if x occurs in nf(ℓ)
         = nf(ℓ)     otherwise, read back as an expression
```

A generic statement lives at `max(ω, the rest of B's level)` when `x` occurs
in the level of `B`. In this version the rest is finite whenever `x` occurs,
because a constant of tier 1 or above would have absorbed `x`. So the `max`
is `ω`. Reading back the normal form matters: `max(x, ω)` mentions `x` but
denotes `ω`, and the conclusion must not mention the bound variable.

The rule follows the model (3.2). A level Π is the product of the types
`B[x := n]` over all `n`. If `x` occurs in `ℓ`, their levels are unbounded
below ω, and the product lives at ω. Otherwise they all live at `ℓ`, and each
universe is closed under ℕ-indexed products.

| Statement | Level of `B` | Level of the statement |
| --- | --- | --- |
| `Π (x < ω). Π (A : U(x)). A → A` | `x + 1` | `ω` (source: `UU0`) |
| `Π (x < ω). Nat` | `0` | `0` |
| `y < ω ⊢ Π (x < ω). U(max(x, y))` | `max(x + 1, y + 1)` | `ω` |
| `y < ω ⊢ Π (x < ω). U(y)` | `y + 1` | `y + 1` |
| `Π (x < ω). U(x) → U(ω)` | `ω + 1` | `ω + 1` |
| `Π (x < ω). Π (z < ω). U(max(x, z))` | `ω`, the inner statement's level | `ω` |

Three properties carry the metatheory:

- **Monotone.** `ℓ ≤ ℓ'` implies `lim_x(ℓ) ≤ lim_x(ℓ')`. If `x` occurs in
  `nf(ℓ)`, Lemma 2 forces `nf(ℓ')` to contain `x` or to be a constant of tier
  1 or above, so `lim_x(ℓ') ≥ ω`. Otherwise
  `lim_x(ℓ) = ℓ ≤ ℓ' ≤ lim_x(ℓ')`. So the inferred level of `B` gives the
  least level of the statement, and a smaller inferred level after
  substitution or reduction never raises it.
- **Above its argument.** `ℓ ≤ lim_x(ℓ)`.
- **Stable.** For `y ≠ x` and a finite `ℓ₀` in which `x` is not free,
  `lim_x(ℓ)[y := ℓ₀] = lim_x(ℓ[y := ℓ₀])`. Substituting a finite level for
  `y` neither adds `x` to a normal form nor removes it.

Further points:

- As the roadmap adopted, level quantification is a type former, not only a
  prefix of declarations. `Π (n : Nat). Π (x < ω). U(x)` is a type in
  `U(ω)`, and a parameter may have a level-Π type, so a result can take a
  universe-generic function as an argument.
- Generic statements are ordinary types. `Endo := Π (x < ω). U(x) → U(x)` is
  a definition of type `U(ω)`. `Path(Endo, f, g)` and `Σ (f : Endo). Nat`
  are types in `U(ω)`.
- `∀-Elim` requires the function's type to reduce to a level Π. Term
  application `f u` requires a term Π. The kernel keeps the two application
  forms distinct.
- `∀-Elim` requires a finite level. `f {ω}` is rejected, and so is the source
  `identity(UU0, T, x)`. Section 3.3 shows why substituting `ω` would be
  unsound for the level judgments.
- `∀-Elim` also rejects a result type `B[x := ℓ]` in which a level exceeds
  `LEVEL_MAX`.
- A level abstraction may return a type: `λ (x < ω). U(x)` has type
  `Π (x < ω). U(x + 1)`, which lives in `U(ω)`. A generic family such as
  `Group : Π (x < ω). U(x + 1)` is of this kind.

### 2.8 Level substitution

`t[x := ℓ]` replaces each free occurrence of `x` in the level expressions of
`t`. Those are the arguments of `U(·)` and of instantiations.

- **Capture.** Before descending under a binder of `t`, the substitution
  renames the binder if its name occurs free in `ℓ`. This applies to level
  binders and, because names share one supply, to term binders too.
- **Scope.** It does not touch term variables, dimensions, faces, bounds or
  the bodies of definitions, which are closed.
- **Commutation.** Level substitution commutes with term substitution and
  with dimension substitution, since they act on disjoint positions.

**Lemma 4 (substitution).** If `Γ, x < ω, Δ ⊢ J` and `Γ ⊢ ℓ level` with
`ℓ < ω`, then `Γ, Δ[x := ℓ] ⊢ J[x := ℓ]`, unless a level of the result
exceeds a bound. By induction on the derivation. Three facts carry it:

1. Level judgments are stable. If `ℓ₁ ≤ ℓ₂` holds for every assignment, it
   holds after substituting `ℓ` for `x`: an assignment `ρ` for the result
   gives the assignment `ρ[x ↦ ⟦ℓ⟧ρ]` for the original. This is an
   assignment of a natural number because `ℓ` is finite. Equality likewise.
2. No rule has a negative level premise, such as `ℓ ≠ 0` or `ℓ ≰ ℓ'`. The
   finiteness premise of `∀-Elim` survives, because a finite level
   substituted into a finite level stays finite.
3. `lim` is stable (2.7), so `∀-Form` survives.

The inferred type of `t[x := ℓ]` may be smaller than the substituted
inferred type, as with term substitution today. The cumulativity closure in
2.9 and the monotonicity of `lim` cover this.

### 2.9 Conversion and cumulativity

Conversion is the kernel's existing untyped algorithm: folded comparison,
then weak-head reduction, with η for functions, pairs and paths. G0 adds:

```text
U-Eq      U(ℓ) ≡ U(ℓ')                        when nf(ℓ) = nf(ℓ')
Inst      f {ℓ} ≡ f' {ℓ'}                     when f ≡ f' and nf(ℓ) = nf(ℓ')
∀-Cong    Π (x < ω). B ≡ Π (y < ω). B'         when B ≡ B'[y := x]
∀-Lam     λ (x < ω). t ≡ λ (y < ω). t'         when t ≡ t'[y := x]
∀-β, ∀-η  as in 2.7
```

- Levels are compared by normal form, never by reduction.
- Under binders, level variables are compared through the comparison's
  current renaming. So `λ (x < ω). U(x) ≡ λ (y < ω). U(y)`. Comparing stored
  payloads, as the C kernel compares universes today, is not enough.
- `∀-η` applies when one side is a level λ and the other is not. The other
  side is instantiated at the fresh variable.
- In this version both binders have the bound `ω`. With the extension of
  1.5, `∀-Cong` and `∀-Lam` also require equal bounds.

Cumulativity is directed, and holds only between checked types:

```text
≤-Conv   A ≡ B                                          ⟹  A ≤ B
≤-U      ℓ ≤ ℓ'                                         ⟹  U(ℓ) ≤ U(ℓ')
≤-Π      A ≡ A'    Γ, a : A ⊢ B ≤ B'[a' := a]            ⟹  Π (a : A). B ≤ Π (a' : A'). B'
≤-Σ      A ≡ A'    Γ, a : A ⊢ B ≤ B'[a' := a]            ⟹  Σ (a : A). B ≤ Σ (a' : A'). B'
≤-∀      Γ, x < ω ⊢ B ≤ B'[y := x]                      ⟹  Π (x < ω). B ≤ Π (y < ω). B'
```

`≤-∀` is new. It is needed for the same substitution reason as `≤-Π`. For
example, `λ (A : U(1)). λ (x < ω). A` has type
`Π (A : U(1)). Π (x < ω). U(1)`. Applied to `Nat`, it reduces to
`λ (x < ω). Nat`, whose inferred type is `Π (x < ω). U(0)`. The reduct must
still check at `Π (x < ω). U(1)`.

Unchanged:

- domains must be convertible, with no contravariance;
- no universes are identified and nothing is lowered;
- there is no cumulativity inside `Path`, Glue or other formers.

### 2.10 Definitions and assumptions

- **Definitions.** A definition `d : A := t` is checked once, in the empty
  context: `· ⊢ A : U(ℓ)` and `· ⊢ t : A`. `A` may be a generic statement,
  and so may `t`: `def Endo = forall U < UU0, U -> U;` is a definition of
  type `UU0` (Q2). Uses are `d` and `d {ℓ}`. δ-unfolding is unchanged.
- **Assumption telescope.** Entries of the kernel's assumption telescope
  (`cc_assumption`) may be level entries `x < ω` and term entries of any
  type, including generic statements. A generic axiom is one entry, such as
  `LEM : Π (x < ω). Π (A : U(x)). ((A → Void) → Void) → Truncate {x} A`.
  Level entries let the elaborator check open goals under `U < UU0`.
- **Small universes only.** `LEM`, `Choice` and the `Truncate` family are
  generic over `x < ω` only. They have no instances at tier 1 or above:
  `LEM {ω}` is rejected by `∀-Elim`, and no separate entry for a UU-tier
  universe is added. Classical reasoning and truncation therefore apply to
  types in `U(n)` only.
- **Expected types.** The expected type of a check may be any type.
- **Non-computing dependencies.** These are computed from the checked term,
  as today. A generic assumption contributes one name, whatever levels it is
  used at (Q4).

### 2.11 Interaction with the cubical rules

- **Levels are constant along lines.** Levels contain no dimensions. In a
  family `Γ, i : I ⊢ A : U(ℓ)` the universe does not depend on `i`. There is
  no transport between universes of different levels, and no rule compares
  levels at two endpoints.
- **Path and PathP.** The family may be any type, at any tier, including a
  level Π. The path type lives in the family's universe:
  `Path(Π (x < ω). B, f, g)` lives at `lim_x(ℓ_B)`. Pointwise equality gives
  equality of generic functions, by a definition that computes:

  ```text
  levelExt : Π (f g : Π (x < ω). B). (Π (x < ω). Path(B, f {x}, g {x})) → Path(Π (x < ω). B, f, g)
  levelExt := λ f g p. ⟨i⟩ λ (x < ω). p {x} @ i
  ```

  Here `B` is a fixed family under `x < ω`, as for function
  extensionality.
- **Composition at a level Π.** This is the one new composition rule:

  ```text
  comp^i (Π (x < ω). B) [φ ↦ u] u₀  ⟶  λ (x < ω). comp^i B [φ ↦ u {x}] (u₀ {x})
  ```

  - `x` is chosen fresh for `φ`, `u` and `u₀`.
  - Typing: on `φ`, `u {x} : B`, and `u₀ {x} : B(i0)`. So the reduct has
    type `Π (x < ω). B(i1)`.
  - Boundary: on `φ` the reduct is `λ (x < ω). u(i1) {x}`, which is `u(i1)`
    by `∀-η`.
  - Soundness: levels never vary along `i`, so the binder `x` is the same at
    every point of the line. The family is a product of lines of types
    indexed by a discrete set, and composition in such a product is computed
    factor by factor (3.2).
  - Transport and filling are derived from composition in both checkers, so
    they inherit the rule. `hcomp` and the C kernel's `CC_TRANS` apply only
    to pushouts and are unaffected.
  - Unlike composition at a term Π, the rule needs no backward filling,
    because the domain is not a type and has no line.
- **Other families.** Every other composition rule is unchanged. Tubes and
  base may be terms of any type, including generic statements, and
  restricting to a face acts on them like on any term.
- **Fibrancy of `U(ℓ)`.** Composition in a universe reduces as it does today,
  by CCHM §7.1:

  ```text
  comp^i U(ℓ) [φ ↦ E] A  ⟶  Glue [φ ↦ (E(1), transport of the identity equivalence)] A
  ```

  The rule never reads `ℓ`, so composition in `U(ω)` or `U(ω·2 + 3)` is the
  same Glue construction. `UU0` is a fibrant universe like any other. In the
  C kernel, `composition_compute.c` sends a `CC_U` family to
  `ck_universe_composition` in `glue_compute.c`. In the reference checker,
  `normal` sends a `U` family to `universeComposition`. Neither reads the
  level. The reduct's inferred level is `max(ℓ_A, ℓ_{E(1)}) ≤ ℓ`, so it
  checks at `U(ℓ)` by `U-Cum`, a symbolic check.
- **Glue.** The base and the partial types may be at any levels. The Glue
  type lives at the `max` of their levels. The equivalence type
  `Equiv(T, A)` is formed at `max(ℓ_T, ℓ_A)`, and the overlap checks are
  unchanged. CCHM puts `T` and `A` in one universe; with cumulativity,
  taking the `max` is equivalent. `check_glue.c` and `core.mjs` already
  compute a `max`, and under G0 it becomes a level expression.
- **Univalence.** One computable generic definition replaces the
  per-universe builtins `builtin__ua__U<n>`:

  ```text
  ua : Π (x < ω). Π (A B : U(x)). Equiv(A, B) → Path(U(x), A, B)
  ua := λ (x < ω). λ (A B : U(x)). λ (e : Equiv(A, B)).
          ⟨i⟩ Glue [i = 0 ↦ (A, e), i = 1 ↦ (B, idEquiv(B))] B
  ```

  It is checked once. Its Glue type lives at `max(x, x) = x`. `ua` cannot be
  instantiated at `ω` in this version. Univalence for a UU-tier universe
  would be the same body written at that constant level, a closed term that
  checks by the same Glue rule and computes (K10). The source language does
  not provide it in this version (Q10, proposal E2).
- **The other composition rules** cover Π, Σ, Path, `Nat`, `Unit`, sums, W,
  pushouts and Glue. Each dispatches on the head former of the family. None
  reads a level.

**Conclusion: G0 needs exactly one new composition rule, for the level Π.**

1. The level-Π rule is pointwise and reads no level.
2. Every other composition and transport rule dispatches on the head of the
   family and ignores levels.
3. The universe's rule is the same Glue construction at every level and
   tier.
4. Levels are constant along lines.

Otherwise G0 changes one thing in cubical checking: level comparisons inside
typing become symbolic. That covers Glue's `max`, the result universe of
Path, and composition's expected types.

### 2.12 Interaction with the H stages

Every H declaration is level-generic, so H1–H4 must fit these rules.

- **Level parameters.** A signature's shared parameter telescope may begin
  with level entries `x < ω`. Generated constants (sort formers,
  constructors, eliminators) are level-abstracted over these entries. For
  example, `Trunc : Π (x < ω). Π (A : U(x)). U(x)`. Like the assumptions, a
  generic signature ranges over small universes only. A signature may also
  be stated at a fixed UU-tier level.
- **A sort's level** is the `max` of the levels of the types of its data, its
  position arities and its indices. Parameters count only through those
  types (Q6). So `Trunc {x} A` lives in `U(x)`, which makes truncation
  universe-preserving. Index types count: a family indexed by `U(x)` lives
  in `U(x + 1)` or above, and one indexed by a generic statement lives in
  `U(ω)` or above.
- **Eliminator motives** may land in any universe, including `U(ℓ')` at a
  level variable and universes of tier 1 or above.
- **Kan structure.** Formal composition, transport along parameter lines,
  index-line matching and boundary reduction read no level. Parameter lines
  never vary a level. A level Π over generated types is composed pointwise
  by 2.11. So H needs no composition rule beyond G0's.
- **Soundness notes.** By the decomposition in 3.2, each H stage can argue at
  a fixed level assignment. Level parameters add no H obligation. The model
  must interpret sorts at levels below ω², which the Grothendieck universes
  of 3.1 provide.
- **Distinct instances.** `Trunc {0} A` and `Trunc {1} A` are different
  types, even for `A : U(0)` (Q1).

## 3. Consistency note

### 3.1 Baseline

Call **CCHM_ω** the theory the kernel checks today once templates are
specialized. It is De Morgan CCHM with:

- Π, Σ, Path and Glue;
- a cumulative Russell-style hierarchy `U_0 ⊆ U_1 ⊆ …`, by subsumption;
- natural numbers, unit, empty type, sums and W types;
- pushouts as a higher inductive type.

Its trust base is the cubical-set model:

- CCHM build the model in presheaves on the De Morgan cube category, with a
  universe obtained by Hofmann–Streicher lifting from a Grothendieck
  universe. The universe is fibrant by Glue.
- A hierarchy iterates this. Fix Grothendieck universes `V_0 ∈ V_1 ∈ …`,
  each containing ℕ, and let `U_n` classify `V_n`-small fibrant families. A
  fibration structure is the same data at every level, so `U_n ⊆ U_{n+1}`
  as presheaves. The Glue composition of `U_{n+1}` restricts to that of
  `U_n`. This models subsumptive cumulativity without lift terms.
- Pushouts follow Coquand–Huber–Mörtberg. W types and sums are standard.

**Call CCHM_{ω²} the same theory with universes `U_α` for every ordinal
`α < ω²`.** Its model is the same iteration, indexed by ordinals:

- Fix Grothendieck universes `V_α` for `α < ω²`, each containing ℕ, with
  `V_α ∈ V_β` whenever `α < β`. ZFC with ω² inaccessible cardinals provides
  them: take the first ω² inaccessibles in increasing order.
- At a limit such as `ω`, `V_ω` is a Grothendieck universe that contains
  every `V_n`. It is not their union, which is not a Grothendieck universe.
  That is why each limit needs an inaccessible of its own.
- `U_α` classifies `V_α`-small fibrant families. For `α ≤ β`,
  `U_α ⊆ U_β`, and the Glue compositions agree, as in the countable case.

G0 is CCHM_{ω²} with level variables and level quantification added.

### 3.2 Interpretation of G0

- **Levels.** For an assignment `ρ` of natural numbers to level variables, a
  level denotes an ordinal `⟦ℓ⟧ρ < ω²`. Lemmas 1–3 make the level rules
  sound and complete for this reading.
- **Contexts.** A level entry contributes the constant presheaf `Δℕ`, whose
  restriction maps are identities: `⟦Γ, x < ω⟧ = ⟦Γ⟧ × Δℕ`. Term entries
  are interpreted by comprehension, as in CCHM.
- **Decomposition lemma.** `Δℕ` is discrete, and level variables depend on
  nothing. So `⟦Γ⟧ ≅ ∐_ρ ⟦Γ[ρ]⟧`, where `ρ` ranges over assignments to the
  level entries, and `Γ[ρ]` drops those entries and evaluates every level at
  `ρ`.
  - A type over `⟦Γ⟧` is then exactly a `ρ`-indexed family of fibrant types
    over the presheaves `⟦Γ[ρ]⟧`, and a term is a `ρ`-indexed family of
    terms. CCHM's model interprets types over any presheaf, so the
    CCHM_{ω²} rules apply at each `ρ`.
  - The rules of G0 other than level quantification are the CCHM_{ω²} rules
    applied at each `ρ`. The only new ingredient is that level premises are
    checked for all `ρ` at once, which is what the normal forms decide.
- **Universes.** `⟦U(ℓ)⟧` is `U_{⟦ℓ⟧ρ}` on the summand for `ρ`. It is
  fibrant because each `U_α` is. Its composition structure is defined
  summand by summand, and it is uniform because restriction maps preserve
  summands.
- **Level Π.** `⟦Π (x < ω). B⟧` is the dependent product along
  `⟦Γ⟧ × Δℕ → ⟦Γ⟧`. Since `Δℕ` is discrete, this is the pointwise ℕ-indexed
  product `∏_n ⟦B⟧(–, n)`.
  - **Size.** Let `ℓ` be the level of `B`. If `x` occurs in `nf(ℓ)`, then
    `ℓ` is finite, so every factor is `V_n`-small for some `n` and hence
    `V_ω`-small. `V_ω` is closed under products indexed by its elements, and
    ℕ is one. So the product is `V_ω`-small and lies in `U_ω`. If `x` does
    not occur, every factor is `V_{⟦ℓ⟧ρ}`-small, and so is the product. This
    is the limit rule of 2.7.
  - **Fibrancy.** A composition problem in the product is solved factor by
    factor. The result is uniform because restriction maps act factorwise.
    This is the composition rule of 2.11, so the rule adds no data beyond
    the product's own structure.
  - `∀-β` and `∀-η` hold for the product.
- **Consistency.** A closed term of `Void` in the empty context would give a
  global element of `⟦Void⟧ = ∅`. The empty context has no level entries, so
  no decomposition is involved. G0 is therefore consistent relative to ZFC
  with ω² inaccessible cardinals. A single derivation mentions finitely many
  tiers, so it needs only `ω·k` of them for some `k`.

### 3.3 Why there is still no `U_κ`

The Rust THTH kernel had `UUOmega : UUKappa`, and the question of what
`UUKappa` lives in recurred. G0 avoids that recurrence:

- **Nothing ranges over all tiers.** A level variable ranges over the levels
  below its bound, and a bound is a tier base below ω². In this version
  every level variable ranges over ℕ, and a level Π lives at `ω` or at its
  body's level (2.7). So every level Π lives below ω², and some universe
  contains it.
- **Bounds are never terms.** A bound cannot be passed, abstracted, computed
  or compared as a value. So no expression denotes a tier, and no definition
  is generic over tiers: `Π (k : Tier). …` has no syntax. If bounds were
  terms, a variable could range over every tier at once. A level Π over it
  would need a universe at ω², above everything, which is `UUKappa` again.
- **ω² is not a level.** Every constant has finitely many letters `U`, and
  no level expression evaluates to ω².
- **Level variables denote finite levels only.** `∀-Elim` requires `ℓ < ω`.
  If a variable could stand for `ω`, the judgment `x < ω ⊢ U(x) : U(ω)`,
  which holds at every finite `x`, would fail at `x = ω`, and Lemma 4 would
  break. The finiteness premise is what keeps level judgments stable.
- **Nothing contains a quantification over itself.** Every level Π lives
  strictly above the universes its variable ranges over: `Π (x < ω). U(x)` is
  in `U(ω)` and in no `U(n)`. Girard's paradox, in Hurkens' form, needs a
  universe that contains a quantification over itself, which is
  Type-in-Type.
- **Relation to the first version.** The first version kept generic
  statements out of every universe. Consistency did not require that,
  because an ℕ-indexed product of fibrant `V_ω`-small presheaves is fibrant
  and `V_ω`-small. The revision takes that route. It gains Σ, Path, Glue and
  composition at generic statements, and named generic statements, at the
  cost of one composition rule and a Grothendieck universe per level below
  ω².

### 3.4 Conservativity over templates

Call the **prenex fragment** the derivations with three properties:

- every level Π is the statement of a top-level definition or assumption, of
  the form `Π (x₁ < ω). … Π (x_r < ω). A` with no level binder in `A`;
- no level of tier 1 or above occurs;
- every use of such a constant is instantiated at once, at `r` levels.

**Claim.** On the prenex fragment, every closed judgment at a type of finite
level is derivable in CCHM_ω, by specializing each generic constant at the
levels it is used at. This is exactly what today's elaborator templates do.

- By Lemma 4, each specialized copy checks.
- A closed term needs finitely many copies, since each copy mentions
  finitely many instances at closed levels.

So on this fragment G0 proves nothing that templates could not. It checks
each constant once, for every level. The converse fails on purpose: a
template that checks only at particular levels is rejected by G0, and the
archive recheck lists such templates.

Higher-rank uses, generic statements as values, and types of tier 1 or above
have no template counterpart. They rely on the model of 3.2.

### 3.5 Canonicity and computability

**Reduction is level-parametric.** No reduction rule reads a level. The
rules are:

- β and `∀-β`, δ and projections;
- eliminators on constructors, and path application at endpoints;
- composition and transport by type former (Π, level Π, Σ, Path, `Nat`,
  `Unit`, sums, W, pushouts, Glue, `U`);
- Glue and `unglue`.

The universe case builds a Glue type without inspecting its level. The
level-Π case dispatches on the binder form and moves the level variable,
without inspecting any level.

**Lemma 5 (instantiation commutes with reduction).** Let `σ` be a
substitution of finite levels.

1. **Every rule is stable.** If `t ⟶ t'`, then `t[σ] ⟶ t'[σ]` by the same
   rule at the same position. A side condition that compares two subterms,
   by syntax or by conversion, still holds after `σ`.
2. **Most rules gain no redex.** For β, `∀-β`, δ, projections, eliminators on
   constructors, path application at endpoints, composition and transport by
   type former including the level Π, and `unglue` of `glue`, every redex of
   `t[σ]` is the image of a redex of `t`. Their patterns mention only term
   formers and binder forms. `σ` changes only level expressions, which are
   leaves for reduction.
3. **Comparing contractions can gain one.** A few η-contractions in the
   normalizers compare two subterms, such as surjective pairing
   `(fst p, snd q) ⟶ p` and `glue` of an `unglue`. `σ` can make two
   different levels equal: `g {x}` and `g {y}` coincide under `x, y := 0`.
   These contractions relate convertible terms.

Hence `nf(t[σ]) = nf(nf(t)[σ])`, and the outer normalization performs only
contractions of the third kind. If `nf(t)[σ]` has none, then
`nf(t[σ]) = nf(t)[σ]`. Canonical values of data types have none. So for a
generic definition `d := λ (x < ω). t` whose instances compute to canonical
data, `nf(d {n}) = nf(t)[x := n]`. Computing the generic body once and
instantiating gives the value that each specialized copy computed before
G0. In general the two agree up to those η-contractions, and they are
always convertible.

**Canonicity.** Suppose `· ⊢ t : A`, where `A` is a closed data type as in
invariant 10 and `t` uses no assumption. Then `t` reduces to a canonical
value. The argument extends Huber's computability predicates:

- The predicates are defined by well-founded induction on levels below ω²,
  and at each level by induction on the structure of types, as Huber does
  for one universe. The predicate for `U_α` uses those at all levels below
  `α`.
- `Π (x < ω). B` is a computable type when every `B[x := n]` is. `t` is
  computable at it when `t {n}` is computable at `B[x := n]` for every
  numeral `n`. This clause branches over ℕ, like that of a Π over `Nat`. The
  types `B[x := n]` lie at the statement's level or below, and they are
  instances of its body, as the codomains `B[a := u]` of a term Π are. So
  the definition stays well founded, as for Π.
- A level λ is a canonical form. Composition at a level Π reduces to a level
  λ by 2.11, whose instances are compositions at the types `B[x := n]`.
  Those are computable by the case for `B[x := n]`.
- The fundamental lemma gains the cases `∀-Form`, `∀-Intro`, `∀-Elim`, `∀-β`
  and composition at a level Π. Each follows from these definitions and from
  Lemma 5.

So G0 has canonicity whenever CCHM_{ω²} has it, and in the same sense.

**Computability tracking.**

- Non-computing dependencies are computed from the term, which does not
  depend on the level. So a generic definition has the same dependencies at
  every level. `computable def` on a generic definition covers every
  instance.
- A closed result at a type of tier 1 or above computes like any other. The
  rules that reduce it are the level-generic ones.
- `evaluate t expecting v` requires `t` closed, including no free level
  variable.
- The canonicity fixture gains instantiated generic results and a transport
  along a line of generic statements (section 5.8).

### 3.6 What is proved, argued and assumed

| Claim | Status |
| --- | --- |
| Level normal forms with tiers are unique; the decision procedure is sound and complete for levels below ω² with variables in ℕ | Proved here (Lemmas 1–3). |
| `lim` is monotone and stable under finite level substitution | Proved here (2.7). |
| Level substitution lemma | Proved here in outline (Lemma 4). Standard. |
| Reduction commutes with level substitution, exactly for canonical data and up to comparing η-contractions in general | Proved here (Lemma 5), given the invariant that no rule reads a level. K1.2 and K1.3 check that invariant by review and by the tests in section 5. |
| Conservativity over templates on the prenex fragment | Proved here in outline (3.4). |
| The model of G0: discrete level contexts, level Π as an ℕ-indexed product in `U_ω`, and its pointwise composition | Argued from standard constructions (discrete presheaf, dependent product along a discrete projection, closure of Grothendieck universes under small products). Not written out in full. |
| Canonicity for G0 | Argued: reduced to canonicity for CCHM_{ω²} by extending Huber's predicates with the level-Π clauses. |
| Consistency and canonicity of CCHM_{ω²} with the kernel's formers | Assumed. This is the existing kernel's trust base extended to ordinal levels: CCHM and Huber for the core, Coquand–Huber–Mörtberg for pushouts, and the standard iteration for the hierarchy, now over ω² Grothendieck universes. Huber treats a single universe; neither the countable hierarchy nor the transfinite one, nor the kernel's pushouts, is covered by a published canonicity proof that we know of. |
| Decidable conversion | Levels are decidable (Lemma 2). Normalization for the kernel's De Morgan system is not established by a published proof that we know of; the kernel relies on budgets, as today. |

### 3.7 Literature

- Cohen, Coquand, Huber, Mörtberg, *Cubical Type Theory: a constructive
  interpretation of the univalence axiom*, TYPES 2015 (LIPIcs 69, 2018). The
  theory, its cubical-set model, Glue, and composition in the universe
  (§7.1), which the kernel implements.
- Huber, *Canonicity for Cubical Type Theory*, J. Automated Reasoning 63,
  2019. The computability argument that 3.5 extends.
- Coquand, Huber, Mörtberg, *On Higher Inductive Types in Cubical Type
  Theory*, LICS 2018. Pushouts in the kernel and the semantic route of H.
- Licata, Orton, Pitts, Spitters, *Internal Universes in Models of Homotopy
  Type Theory*, FSCD 2018. Fibrant universes built uniformly, which supports
  "every `U_α` is fibrant by one construction".
- Hofmann, Streicher, *Lifting Grothendieck Universes*, 1997 (unpublished
  note). Presheaf universes from set-theoretic universes; iterating gives the
  hierarchy.
- Luo, *ECC, an Extended Calculus of Constructions*, LICS 1989. Cumulativity
  as subsumption, covariant in Π codomains with equal domains, as the kernel
  does.
- Harper, Pollack, *Type Checking with Universes*, TCS 89, 1991. Symbolic
  level checking for cumulative hierarchies.
- Sozeau, Tabareau, *Universe Polymorphism in Coq*, ITP 2014. Level-generic
  constants checked once and instantiated by substitution.
- Timany, Sozeau, *Cumulative Inductive Types in Coq*, FSCD 2018. Treating
  instances of an inductive at different levels as related, which bears on
  Q1.
- Bezem, Coquand, Dybjer, Escardó, *Type Theory with Explicit Universe
  Polymorphism*, TYPES 2022 (LIPIcs 269, 2023). Levels built by successor
  and supremum, with products indexed by levels. The closest published
  treatment of G0's level Π.
- Bezem, Coquand, *Loop-checking and the uniform word problem for
  join-semilattices with an inflationary endomorphism*, TCS 913, 2022.
  Deciding level constraints with `max` and successor. G0 needs only the
  constraint-free case, which normal forms decide.
- Kovács, *Generalized Universe Hierarchies and First-Class Universe Levels*,
  CSL 2022. Hierarchies over richer level structures, including transfinite
  levels. G0 uses the ordinals below ω², with levels that are never
  first-class terms.
- Agda user manual, *Universe Levels* and *Sort System*. `∀ ℓ → Set ℓ`
  lives in `Setω`, and `Setω, Setω₁, …` form a tier above every `Set ℓ`
  with no level variables ranging over it. G0's UU tier plays that role, as
  ordinary cumulative and fibrant universes, and G0 adds further tiers.
- de Moura, Ullrich, *The Lean 4 Theorem Prover and Programming Language*,
  CADE 2021; Carneiro, *The Type Theory of Lean*, MSc thesis, CMU, 2019.
  Prenex universe parameters with successor, `max` and `imax`, level
  equality by normalization, and a soundness proof relative to ZFC with
  inaccessible cardinals.
- Hurkens, *A Simplification of Girard's Paradox*, TLCA 1995. Why no
  universe may contain a quantification over itself.
- The Rust THTH kernel (`KanHarI/thth`). The project's precedent:
  `UUOmega : UUKappa`, whose recurrence G0 avoids (3.3).

## 4. Implementation consequences

Both checkers implement section 2 independently. The reference checker lands
first.

### 4.1 K1.2: reference checker (`lib/cubical/core.mjs`)

**Data.**

- **Level nodes.** `{tag:"LConst", tier, value}` for `ω·tier + value`,
  `{tag:"LSucc", level}` and `{tag:"LMax", left, right}`. Level variables are
  ordinary `{tag:"Var", name}` nodes in level position. This mirrors the C
  kernel, and substitution and free-variable code then covers levels.
- **Universes.** `{tag:"U", level}` takes a level node. For the many existing
  callers, `T.universe(n)` with a number builds a tier-0 `LConst`.
- **Level binders.** `{tag:"LPi", name, bound, body}`,
  `{tag:"LLam", name, bound, body}` and `{tag:"LApp", fn, level}`. `bound`
  is `{tag:"LBound", tier}`, and this version requires `tier` to be 1.
- **Level entries.** `{tag:"LBound", tier:1}` appears as the type of a level
  entry in `verify`'s assumptions and in the checker's context map. It
  appears nowhere else.
- **Definitions.** A definition registry: `define(name, value, type)` checks
  once, and `DefRef` infers the stored type and unfolds in `normal`. The
  reference checker has no inference rule for `DefRef` today. Without one it
  cannot test "checked once, instantiated at two levels" as the C kernel
  will.
- **Level module.** A new `lib/cubical/levels.mjs` provides
  `normalizeLevel`, `levelLeq`, `levelEqual`, `levelFinite`, `levelLimit`
  (the `lim` of 2.7), `printLevel`, `LEVEL_MAX` and `TIER_MAX`. The
  elaborator may use it for display. The C kernel does not share it.

**Checks.**

- **`type()`** returns `{term, level}` for every type, including a level Π.
  The first version's split into small and large sorts is gone.
- **`infer`.**
  - `U` checks its level and both bounds.
  - `Var` rejects a level entry ("a universe variable is not a term").
  - `LBound` is rejected everywhere except as a binder's bound or an entry's
    type.
  - `LPi` infers its body's level under the level entry and returns
    `U(levelLimit(x, level))`.
  - `LLam` follows `∀-Intro`. `LApp` requires a finite level.
  - `App` rejects a level Π, and `LApp` rejects a term Π.
- **`cumulative`.** `U` uses `levelLeq`. Add the `≤-∀` case.
- **`free`, `substitute`, `alpha`, `normal`.** These become level-aware.
  - `alpha` renders `U` and `LApp` levels as normal forms, with bound
    variables replaced by binder indices.
  - `normal` adds `∀-β`, and η-contraction of `λ (x < ω). f {x}`, as it
    already contracts term η.
  - `normal` adds composition at `LPi` next to the `Pi` case (2.11).
- **Type formers.** Every former accepts types of any level; only the level
  arithmetic changes.

**Tests** (`lib/cubical/tests/levels.test.mjs` and
`lib/cubical/tests/g0.test.mjs`):

- every case of section 5, by its ID;
- a property test comparing `levelLeq` and `levelEqual` with brute-force
  evaluation over assignments up to `2·top + 2`, with constants of tiers 0
  to 2;
- a property test that `levelLimit` is monotone and stable (2.7);
- a property test for Lemma 5: for random well-typed generic terms `t` and
  numerals `n`, `nf(t[x := n])` equals `nf(nf(t)[x := n])`, and equals
  `nf(t)[x := n]` when the result is canonical data;
- a property test for the level-Π composition rule: instantiating its reduct
  at `n` gives the composition at `B[x := n]` after one `∀-β`.

### 4.2 K1.3: C kernel, ABI, serialization, sanitizers

**Node kinds.** Tags 1–42 keep their numbers. The new kinds are appended:

| Tag | Kind | Payload and children |
| --- | --- | --- |
| 43 | `CC_LBOUND` | payload `k ≥ 1`, the bound `ω·k`; `k = 1` in this version. Valid only as a level binder's child 0 or a level entry's type. |
| 44 | `CC_LCONST` | payload `k·2¹⁶ + n` for `ω·k + n`, with `n ≤ LEVEL_MAX` and `k ≤ TIER_MAX` |
| 45 | `CC_LSUCC` | child 0: level |
| 46 | `CC_LMAX` | children 0 and 1: levels |
| 47 | `CC_LPI` | payload: binder symbol; child 0: `CC_LBOUND`; child 1: body |
| 48 | `CC_LLAM` | payload: binder symbol; child 0: `CC_LBOUND`; child 1: body |
| 49 | `CC_LAPP` | child 0: function; child 1: level |

- **`CC_U` changes.** Child 0 is a level node and the payload must be zero.
  Today the payload is the level. `ck_arity(CC_U)` becomes 1.
- **Level variables** are `CC_VAR` nodes bound by `CC_LPI`, `CC_LLAM` or a
  level entry.
- **Generic binder code.** `ck_term_binder` includes `CC_LPI` and `CC_LLAM`.
  Their layout matches the other binders (symbol in the payload, body in
  child 1), so substitution, free-variable computation and α-comparison
  apply unchanged.

**Internal functions.**

- `ck_level(k, raw, ctx, &level)` checks well-formedness and returns a
  canonical level node. `ck_level_normal`, `ck_level_leq`, `ck_level_equal`,
  `ck_level_finite`, `ck_level_limit`, `ck_level_max` and `ck_level_succ`
  work on a `cc_level_nf`:
  `{uint32_t tier; uint32_t constant; uint32_t count; {uint64_t key; uint32_t offset} terms[]}`,
  sorted by key, with `count = 0` whenever `tier ≥ 1`.
- A key is the variable's symbol when it is free. During α-comparison it is
  the identity of the binding it resolves to, so renamed binders compare
  equal.
- `ck_type` returns a level handle instead of `uint32_t`. Binder domains,
  assumption types, definition types and expected types use it as today.
  There is no separate check for large types.
- Every site that builds `CC_U` from a computed level builds a canonical
  level node. Every `>` comparison of levels becomes `ck_level_leq`. The
  sites are:
  - `check.c` (U);
  - `check_functions.c` (Π, Σ, and the level Π with `ck_level_limit`);
  - `check_inductives.c` (`Nat`, `Unit`, `Void`, W, sums);
  - `check_paths.c`;
  - `check_glue.c`;
  - `check_pushout.c`.
- `term_conversion.c`:
  - `alpha_inner` compares `CC_U` and `CC_LAPP` levels by normal form under
    the current `alpha_binding` environment. It no longer compares payloads.
  - η for `CC_LLAM` builds `CC_LAPP`.
  - `cumulative` uses `ck_level_leq` and gains the `CC_LPI` case.
- `term_normalize.c` and weak-head reduction add `∀-β`. A `CC_LAPP` of a
  non-λ is neutral.
- `composition_compute.c`: `ck_reduce_composition` gains a `CC_LPI` case
  beside `CC_PI`. It takes a fresh symbol, renames the family's binder to
  it, maps the tubes through `CC_LAPP` (a new operation of `map_tubes`),
  applies the base, and returns a `CC_LLAM`. It needs no call to `ck_fill`.
- `cc_context` entries whose type is `CC_LBOUND` are level entries. `CC_VAR`
  inference rejects them, and `ck_level` accepts them.
- Glue, universe and pushout computation need no rule change. An audit test
  checks that no code outside the level functions reads a `CC_U` child or a
  `CC_LCONST` payload.

**Public API.**

- `cc_kernel_check` and `cc_kernel_check_in_cube` accept level entries,
  whose `cc_assumption.type` is a `CC_LBOUND` handle.
- `cc_kernel_define` is unchanged apart from levels: any checked type may be
  a definition's type.
- `cc_kernel_node` exposes level nodes. Inspection functions treat malformed
  level nodes as inert syntax.

**ABI impact.**

- The encoding of `CC_U` changes from a payload to a child, which breaks
  every existing client.
- Seven kinds are appended, and assumption telescopes may contain
  `CC_LBOUND`-typed entries.
- Add `cc_kernel_abi_version()` and a matching constant in the JavaScript
  loaders. The WASM bridge and `kernel-cli` refuse a mismatch. A
  serialization written with the old `CC_U` encoding is refused and must be
  regenerated.

**Resources and safety.**

- Level arithmetic uses 64-bit intermediates and rejects results above
  `LEVEL_MAX` or `TIER_MAX`. The bounds are checked for level literals, for
  `U-Form`, for instantiation results and whenever a level is normalized,
  including during conversion.
- Normal forms are heap-allocated with checked sizes.
- Deep `CC_LSUCC` chains are handled iteratively or under the recursion
  counter.
- Canonical level nodes may be interned. That is an optimization and never a
  typing certificate.

**Serialization and bridges.**

- `lib/cubical/native.mjs` gains the new kinds. `N` lines keep their format.
  An `A` line may name a `CC_LBOUND` handle as a type.
- `web/cubical-syntax.mjs` and `web/cubical-kernel.mjs` encode and decode
  level nodes, and decode `CC_U` from its child.
- `cb_context_add` in `wasm/cubical_bridge.c` accepts `CC_LBOUND`.
- Every consumer of a numeric universe level moves to level expressions:
  - the renderers `web/cubical-notation.mjs` and `web/math-notation.mjs`,
    which print tiers (`UU3`, `𝒰_{ω+3}`);
  - the bridges `web/cubical-syntax.mjs` and `lib/cubical/native.mjs`;
  - `core.mjs` and `translate.mjs`.

  The template inspection in `web/cubical-program.mjs` is removed (4.3).

**Tests.**

- `kernel/tests/test_levels.c`: normal forms across tiers, order, the
  bounds, and malformed nodes.
- `test_conversion.c`: α-renamed levels and level η.
- A composition test for the `CC_LPI` case, including its boundary on a
  face.
- `test_kernel_api.c`: level entries, generic statements as definitions'
  types and values, and the ABI version.
- `tests/cubical-wasm.test.mjs` runs every case of section 5 through both
  checkers and compares verdicts and normal forms.
- `make test` and `make CC=clang sanitize`, including a fuzz of random level
  nodes.

### 4.3 L1.1: language and removal of templates

**Elaboration.**

- **Parser** (`web/mathscript/parser.mjs`).
  - A binder head `name < bound` is a universe binder, in parameter lists,
    after `forall` and in `fun`. Elsewhere `<` keeps its meaning as the
    less-than operator. The bound must be a tier-base constant, and L1.1
    accepts only `UU0`.
  - Names of the shape `U+[0-9]+` are universe constants at every tier.
    Binding or declaring one is an error, and so is a numeral with a leading
    zero.
  - `next(E)` and `max(E, F)` are new universe expressions.
  - `Universe` is no longer recognized. Its old binder form gets an error
    that suggests `U < UU0`.
- **Scope.** `translate.mjs` gains a scope entry for universe variables,
  mapping a source name to a kernel level variable. A universe expression
  translates to a level in argument position, and to `U(level)` in term
  position. Today a bound name shadows a constant such as `U0`, because the
  environment is consulted first; after L1.1 such a binder is rejected. The
  same regular expression changes in `web/mathscript/notation.mjs` and in
  the highlighter in `web/proof.mjs` (`^U[0-9]+$` becomes `^U+[0-9]+$`).
- **Declarations.** `def d(U < UU0, …) : T` becomes one kernel definition,
  with value `λ (x < ω). …` and type `Π (x < ω). …`, checked once. A use
  `d(E, …)` becomes `d {ℓ_E} …`, and a universe argument that is not finite
  is rejected with a message that names the bound.
- **Generic statements.** `forall U < UU0, B` may appear wherever a type is
  expected. `def Endo = forall U < UU0, U -> U;` is accepted with type
  `UU0`.
- **Kept.** The `typed(E, T)` ascription and explicit universe arguments.
- **Inspector.** It shows level abstractions and instantiations in source
  notation (`identity(U2, …)`), and prints levels as universe expressions
  (`max(U, U1)`, `UU0`).
- **Generic rules.** Rule environments, caches and goal contexts key on level
  variables instead of specializations. Rewriting with a generic rule matches
  a level argument only when the rule's level is a variable. Anything harder
  waits for milestone 5.

**Removed:**

- the word `Universe`;
- `UniverseSchema`, `expandUniverseBinders`, `specializeSchema` and the
  "not-translated" status of schemas;
- the per-universe builtins `builtin__ua__U<n>` and their closures;
- the per-universe keys of `libraryAssumption` (`${name}_U${level}`) in
  `web/cubical-assumptions.mjs`, and the origin kind
  `universe-specialized-assumption`;
- the template provenance panel `web/cubical-specialization.mjs`, and the
  inspector's `U0`–`U3` picker for templates;
- the "Universe templates" category of the benchmark page
  (`web/benchmark.mjs`, `web/benchmark-runner.mjs`, `web/benchmark.html`);
- the migration verifier's specialization probes;
- the rule that withholds "Replace with simp only" for templates. One check
  now covers every level.

**Assumptions.** Each archive assumption becomes one entry, generic over
`U < UU0` only, with the same content:

- `Truncate : Π (x < ω). U(x) → U(0)` keeps the archive's resizing signature
  until H1 and G2 replace it with the universe-preserving `Trunc` (Q5);
- `TruncateIntro`, `TruncateProp` and `TruncateElim` follow the archive
  schema, with `A` and `P` in one universe `U(x)`;
- likewise `LEM` and `Choice`.

None has an instance at tier 1 or above.

**Computing builtins.** Builtins such as `ua`, `UnivalenceBeta` and `FunExt`
take a universe argument and use no assumption. Each becomes one generic
definition over `U < UU0`. A universe argument of tier 1 or above, such as
`ua(UU0, A, B, e)`, is rejected in this version (Q10). Proposal E2 records how
the elaborator could build the same closed body at a UU-tier constant.

**Migration of today's templates.**

- **Binders.** `U : Universe` becomes `U < UU0`, mechanically, in the archive
  and in every example.
- **Dependency names.** Dependency names change from `Choice(U0)` to
  `Choice` (Q4). The migration verifier maps old per-level names to the
  generic name with a fixed table, so the rename does not count as a change
  of assumptions. The computability examples in
  `web/reference/assumptions.html` and the help text in `web/proof.html`
  quote `LEM(U0), Truncate(U0)`, and the reference harness checks those
  messages, so they are updated with it.
- **Archive recheck.** Elaborate each of the archive's 43 templates
  generically, together with its dependents. Record each template that fails
  in a checked-in list: the rule that failed, and the levels at which it used
  to check. Typical causes are using the universe variable as an element of
  a fixed universe (`U : U1`) and relying on `Truncate`'s resizing. Do not
  weaken a rule to accept a template.
- **Reference.** Rewrite `web/reference/universes.html`, and the universe
  paragraphs of `web/reference/assumptions.html`.

**Sequencing.** The elaborator checks through the native kernel
(`NativeCubicalElaborator`). The reference checker is used only in tests.
So L1.1 can be developed against K1.2 in tests, but the template removal and
the archive recheck land only after K1.3.

### 4.4 Documents and examples to update when L1.1 lands

These still use `U : Universe` or `Uω` syntax, or describe templates. This
revision changes only this specification and the G0 item of the kernel
roadmap.

- `docs/roadmaps/cubical-kernel-roadmap.md`: the G2 item
  (`Trunc : ∀ U : Uω, U → U`).
- `docs/roadmaps/README.md`: the G0 summary line.
- `docs/roadmaps/work-plan.md`: the K1.3 and L1.1 text (`Uω` as a binder
  type, large types, `U : Universe`).
- `docs/roadmaps/proof-ergonomics-roadmap.md`: consecutive `Universe`
  parameters, and the specialization of universe parameters.
- `docs/roadmaps/higher-inductive-types-design.md` and
  `docs/roadmaps/inductive-language-features.md`: examples with an unbound
  `A : U` (1.4), and the H design's "parameters" clause (Q6).
- `docs/guides/mathscript.md`, `docs/guides/cli.md` and
  `docs/tactical/univalence.md`: `U : Universe` parameters and templates.
- `web/reference/universes.html`, `web/reference/assumptions.html` and
  `web/proof.html`: `U : Universe` examples, template text, and per-level
  assumption names in quoted errors.
- `archive/first-library/{equivalence_from_inverse,group_hom_universes,group_universes,paths}.cubist`:
  `U : Universe` binders.
- `lib/cubical/tests/translation.test.mjs` and
  `docs/examples/hott-automation/measure.mjs`: template tests and detection
  of `Universe` binders.

## 5. Acceptance cases

Each case has an ID for K1.2's and K1.3's tests. "Accept" and "Reject" are
the verdicts of both checkers. `Γ` is empty unless stated. `x, y, z < ω` are
level entries where they occur. Cases marked "source" belong to L1.1.

### 5.1 Level normal forms and order

Test equality as `U(ℓ) ≡ U(ℓ')`. Test order by checking
`λ (A : U(ℓ)). A` against `U(ℓ) → U(ℓ')`: domains must be convertible, so
this isolates the codomain `≤`.

| ID | Judgment | Verdict | Reason |
| --- | --- | --- | --- |
| L1 | `max(x, x) = x` | Accept | Both are `(0, {x↦0})`. |
| L2 | `max(x + 1, x) = x + 1` | Accept | Largest offset kept. |
| L3 | `max(0, x) = x` | Accept | The constant 0 is absorbed. |
| L4 | `max(1, x + 1) = x + 1` | Accept | `c = 1` equals the largest offset. |
| L5 | `max(x, y) = max(y, x)` | Accept | Commutativity. |
| L6 | `max(x, max(y, z)) = max(max(x, y), z)` | Accept | Associativity. |
| L7 | `max(x, y) + 1 = max(x + 1, y + 1)` | Accept | Successor distributes. |
| L8 | `max(1, x) = x + 1` | Reject | `(1, {x↦0})` vs `(1, {x↦1})`; they differ at `x = 3`. |
| L9 | `max(1, x) = x` | Reject | They differ at `x = 0`. |
| L10 | `0 ≤ x`; `x ≤ 0` | Accept; Reject | Constant check `0 ≤ 0`; `x` is missing on the right. |
| L11 | `1 ≤ x`; `1 ≤ x + 1` | Reject; Accept | `1 ≤ 0` fails; `1 ≤ 1`. |
| L12 | `x ≤ max(x, y)`; `max(x, y) ≤ x` | Accept; Reject | `y` is missing on the right. |
| L13 | `x + 1 ≤ max(x, y + 1)` | Reject | Offset of `x`: `1 > 0`. |
| L14 | `x ≤ y` and `y ≤ x` | Reject both | Incomparable variables. |
| L15 | `U(x) ≡ U(y)` | Reject | Distinct normal forms. |
| L16 | `U(65534)` | Accept | Its type `U(65535)` is within the bound. |
| L17 | `U(65535)` | Reject | Successor exceeds `LEVEL_MAX`. |
| L18 | `U(z)` with `z` not in `Γ` | Reject | Unbound level variable. |
| L19 | `a : Nat ⊢ U(a)` | Reject | A term variable is not a level. |
| L20 | `max(x, ω) = ω` | Accept | `ω` absorbs `x`. |
| L21 | `max(x + 3, ω) + 1 = ω + 1` | Accept | Absorption, then successor within tier 1. |
| L22 | `x ≤ ω`; `ω ≤ x` | Accept; Reject | Finite below a constant; a constant is never below a finite form (fails at `x = 0`). |
| L23 | `ω + 5 ≤ ω·2`; `ω·2 ≤ ω + 1000` | Accept; Reject | Tiers compare first. |
| L24 | `max(ω + 7, ω·2) = ω·2` | Accept | Ordinal maximum. |
| L25 | `ω = x + 1`; `ω = max(x, y)` | Reject both | A constant never equals a finite form. |
| L26 | `U(ω + 65534)`; `U(ω + 65535)` | Accept; Reject | `LEVEL_MAX` bounds the finite part in each tier. |
| L27 | `U(ω·255)`; `U(ω·256)` | Accept; Reject | `TIER_MAX`. |

### 5.2 Bounds and binders

| ID | Judgment | Verdict | Reason |
| --- | --- | --- | --- |
| B1 | infer the bound `ω` as a term | Reject | A bound is not a term. |
| B2 | `(λ (A : U(1)). A)` applied to the bound | Reject | A bound as an argument. |
| B3 | the bound checked against `U(ℓ)` for any `ℓ` | Reject | A bound has no type. |
| B4 | `Σ (x < ω). U(x)` | Reject | Only Π and λ bind levels. |
| B5 | `Π (x < ω + 1). U(x)`; `Π (x < 3). U(x)` | Reject both | Only tier bases are bounds. |
| B6 | `Π (x < ω·2). U(x)` | Reject | Not in this version (1.5). |
| B7 | `x < ω ⊢ x : A` for any `A` | Reject | A universe variable is not a term; write `U(x)`. |
| B8 | `(λ (x < ω). U(x)) {Nat}`; `(λ (x < ω). U(x)) Nat` | Reject both | Instantiation needs a level; term application needs a term Π. |
| B9 | `x < ω ⊢ U(x) : U(x + 1)` | Accept | Level entry used in a level. |
| B10 | `(λ (A : U(ω + 1)). A) U(ω)` | Accept | `UU0` is a term. |
| B11 | source: `def u = Universe;`; `def f(U : Universe, A : U) = A;` | Reject both | `Universe` is removed. |
| B12 | source: `def f(U < UU1, A : U) = A;`; `(U < U5, …)`; `(U < UUU0, …)` | Reject all | Not tier bases; `UUU0` is not in this version. |
| B13 | source: `def UU2 = Nat;`; `fun (U1 : U0) => U1`; `U01` | Reject all | Reserved names; malformed constant. |
| B14 | source: `def g(UU : U1, x : UU) = x;`; `def h = UU;` | Accept; Reject | `UU` is an ordinary name; unbound, and not a constant. |
| B15 | source: `def v : UU1 = UU0;`; `def w : UU0 = U7;` | Accept both | Universes of both tiers are terms; cumulativity crosses tiers. |
| B16 | source: `next(Nat)`; `identity(Nat, …)` | Reject both | A non-universe where a universe is required. |
| B17 | source: `forall n < 3, n = n` | Reject | A binder bound must be a tier-base universe. |

### 5.3 Generic statements as types

| ID | Judgment | Verdict | Reason |
| --- | --- | --- | --- |
| G1 | `Π (x < ω). U(x) → U(x) : U(ω)`; the same at `U(ω + 1)` | Accept both | `x` occurs in the body's level; cumulativity. |
| G2 | the statement of G1 at `U(ℓ)` for a finite `ℓ`, including `y < ω ⊢ … : U(y + 5)` | Reject | Its level is `ω`. |
| G3 | `Π (x < ω). Nat : U(0)` | Accept | `x` does not occur in the body's level. |
| G4 | `y < ω ⊢ Π (x < ω). U(y) : U(y + 1)` | Accept | `x` does not occur. |
| G5 | `Π (x < ω). U(x) → U(ω)` at `U(ω + 1)`; at `U(ω)` | Accept; Reject | Body level `ω + 1` absorbs `x`. |
| G6 | `Π (x < ω). Π (z < ω). U(max(x, z)) : U(ω)` | Accept | The inner statement is at `ω`, which has no `x`. |
| G7 | `Path(Π (x < ω). U(x) → U(x), f, g) : U(ω)` | Accept | Path at a generic statement (Q3). |
| G8 | `Σ (f : Π (x < ω). U(x) → U(x)). Nat : U(ω)` | Accept | Σ with a generic domain. |
| G9 | `Glue [φ ↦ (E, idEquiv(E))] E : U(ω)` with `E := Π (x < ω). U(x) → U(x)` | Accept | Glue at tier 1. |
| G10 | definition `Endo := Π (x < ω). U(x) → U(x)` of type `U(ω)` | Accept | A named generic statement (Q2). |
| G11 | `NatRec` with motive `λ n. Π (x < ω). U(x) → U(x)` | Accept | The motive lands in `U(ω)`. |
| G12 | `Truncate {0} (Π (x < ω). U(x) → U(x))` | Reject | The argument must be in `U(0)`. |
| G13 | `λ (f : Π (x < ω). Π (A : U(x)). A → A). f {0} Nat zero` | Accept | Parameter of generic type; the function type lives in `U(ω)`. |
| G14 | `Π (n : Nat). Π (x < ω). U(x) : U(ω)` | Accept | Small domain, generic codomain. |

### 5.4 Cumulativity

| ID | Judgment | Verdict | Reason |
| --- | --- | --- | --- |
| C1 | `x < ω ⊢ Nat : U(x)` | Accept | `0 ≤ x`. |
| C2 | `x, y < ω ⊢ U(x) : U(max(x + 1, y))` | Accept | `x + 1 ≤ max(x + 1, y)`. |
| C3 | `x < ω ⊢ U(x) : U(x)` | Reject | `x + 1 ≤ x` fails. |
| C4 | `x < ω ⊢ U(x) : U(1)` | Reject | A universe variable used at a smaller universe. Fails at `x = 1`. |
| C5 | `x < ω, A : U(x) ⊢ A : U(0)` | Reject | Downward lifting. |
| C6 | `x < ω, A : U(x + 1) ⊢ A : U(x)` | Reject | Downward lifting. |
| C7 | `x, y < ω, A : U(x) ⊢ A : U(max(x, y))` | Accept | `x ≤ max(x, y)`. |
| C8 | `x, y < ω, A : U(max(x, y)) ⊢ A : U(x)` | Reject | `y` is missing on the right. |
| C9 | `x < ω, A : U(max(1, x)) ⊢ A : U(x + 1)`; the converse | Accept; Reject | `(1,{x↦0}) ≤ (1,{x↦1})`, but not conversely. |
| C10 | `x < ω, B : U(x) ⊢ λ (a : Nat). B : Nat → U(x + 1)` | Accept | `≤-Π` with a symbolic level. |
| C11 | `λ (x < ω). Nat : Π (x < ω). U(1)`, the reduct of `(λ (A : U(1)). λ (x < ω). A) Nat` | Accept | `≤-∀`: the reduct infers `Π (x < ω). U(0)` and must keep the redex's type. |
| C12 | `λ (A : U(0)). A : U(1) → U(1)` | Reject | Domains must be convertible. |
| C13 | `Π (x < ω). U(x) ≤ Π (y < ω). U(y + 1)` | Accept | `≤-∀` under renaming. |
| C14 | `Π (x < ω). U(x + 1) ≤ Π (y < ω). U(y)` | Reject | No downward lifting under a level Π. |
| C15 | `x < ω ⊢ U(x) : U(ω)` | Accept | `x + 1 ≤ ω`. |
| C16 | `U(5) : U(ω)`; `U(ω) : U(5)` | Accept; Reject | Cumulativity crosses tiers upward only. |
| C17 | `A : U(ω) ⊢ A : U(x)`; `A : U(ω + 1) ⊢ A : U(ω)` | Reject both | Downward lifting. |
| C18 | `A : U(ω + 3) ⊢ A : U(ω·2)` | Accept | Into the next tier. |

### 5.5 Instantiation and substitution

Let `id := λ (x < ω). λ (A : U(x)). λ (a : A). a`.

| ID | Judgment | Verdict | Reason |
| --- | --- | --- | --- |
| S1 | `id : Π (x < ω). Π (A : U(x)). A → A`, registered once; its type is in `U(ω)` | Accept | One check covers every level. |
| S2 | `id {0} Nat 3 : Nat` reducing to `3`, and `id {1} U(0) Nat : U(0)` reducing to `Nat` | Accept | The same definition at two levels; both compute. |
| S3 | `id {0} U(0)` | Reject | `U(0) : U(1)`, not `U(0)`. |
| S4 | `x < ω ⊢ id {x + 1} U(x) : U(x) → U(x)` | Accept | Symbolic instantiation. |
| S5 | `y < ω ⊢ ((λ (x < ω). λ (y < ω). U(max(x, y))) {y}) {0} ≡ U(y)`, and `≢ U(0)` | Accept; Reject | Capture-avoiding: the inner binder is renamed. Without renaming the result would be `U(0)`. |
| S6 | level substitution under a term binder with the same symbol (C kernel) | Accept, renamed | One name supply; term binders are renamed too. |
| S7 | `f : Π (x < ω). U(x) → U(x) ⊢ f ≡ λ (x < ω). f {x}` | Accept | `∀-η`. |
| S8 | `(λ (x < ω). U(x)) {2} ≡ U(2)` | Accept | `∀-β` at the type level. |
| S9 | `(λ (x < ω). U(x + 65000)) {1000}` | Reject | The instantiated type exceeds `LEVEL_MAX`. |
| S10 | `λ (x < ω). λ (g : U(1) → Nat). g U(x)` | Reject | `U(x) : U(1)` needs `x + 1 ≤ 1`. The body checks only at `x = 0`: the template case G0 must reject. |
| S11 | `d {0}` vs `d {max(0, 0)}` | Accept (convertible) | `Inst` compares levels by normal form. |
| S12 | `id {ω} (Π (x < ω). U(x) → U(x))`; source `identity(UU0, T, x)` | Reject | Instantiation requires a finite level. |
| S13 | `x < ω ⊢ id {max(x, ω)}` | Reject | The level normalizes to `ω`. |

### 5.6 Cubical rules at variable levels and higher tiers

| ID | Judgment | Verdict | Reason |
| --- | --- | --- | --- |
| K1 | `ua` of 2.11 at type `Π (x < ω). Π (A B : U(x)). Equiv(A, B) → Path(U(x), A, B)` | Accept | Glue at `max(x, x) = x`, checked once. |
| K2 | `x, y < ω, A : U(x), T : U(y), e : Equiv(T, A) ⊢ Glue [φ ↦ (T, e)] A : U(max(x, y))`; the same at `U(x)` | Accept; Reject | Glue lives at the `max`. |
| K3 | `x < ω, A : U(x)`, `E` a line in `U(x)` with `E(0) ≡ A` on `φ` `⊢ comp^i U(x) [φ ↦ E(i)] A : U(x)` | Accept | Universe composition at a variable level. The Glue reduct also checks at `U(x)`. |
| K4 | transport of `inl(tt)` along `ua {0} Two Two swap` and along `ua {1} Two Two swap`, with `Two := Unit + Unit` | Accept; both reduce to `inr(tt)` | One definition, two levels, same value (Lemma 5). |
| K5 | `x < ω, A : U(x), a : A ⊢ Path(A, a, a) : U(x)`; `Path(U(x), A, A) : U(x + 1)`; `Path(U(x), A, A) : U(x)` | Accept; Accept; Reject | Path lives in its family's universe. |
| K6 | `f : Π (x < ω). Nat → Nat, i : I ⊢ comp^j Nat [i = 0 ↦ f {0} zero] (f {0} zero)` | Accept | Tubes may mention a variable of generic type. |
| K7 | `f : Π (x < ω). Nat → Nat, i : I ⊢ comp^j (Π (x < ω). Nat → Nat) [i = 0 ↦ f] f` | Accept; reduces to `λ (x < ω). comp^j (Nat → Nat) [i = 0 ↦ f {x}] (f {x})` | The level-Π composition rule. |
| K8 | `(transport^i (Π (x < ω). (ua {0} Two Two swap) @ i) (λ (x < ω). inl(tt))) {0}`, and the same at `{7}` | Accept; both reduce to `inr(tt)` | A closed transport along a line of generic statements computes pointwise. The family lives in `U(0)`. |
| K9 | `A : U(ω)`, `E` a line in `U(ω)` with `E(0) ≡ A` on `φ` `⊢ comp^i U(ω) [φ ↦ E(i)] A : U(ω)` | Accept | Universe composition at tier 1; the Glue reduct checks at `U(ω)`. |
| K10 | kernel only (the source builtin rejects `UU0`, Q10): the body of `ua` written with `U(ω)` in place of `U(x)`, checked as a closed term of type `Π (A B : U(ω)). Equiv(A, B) → Path(U(ω), A, B)`; transport of `inl(tt)` along it at `Two Two swap` | Accept; reduces to `inr(tt)` | Univalence for `UU0` by the same Glue rule. |
| K11 | `levelExt` of 2.11 for `B := Nat → Nat`; `(levelExt f f (λ (x < ω). refl(f {x}))) @ 0 ≡ f` | Accept; Accept | Pointwise paths give a path of generic functions, by `∀-η`. |

### 5.7 Definitions, assumptions and dependencies

| ID | Judgment | Verdict | Reason |
| --- | --- | --- | --- |
| D1 | telescope `[Truncate : Π (x < ω). U(x) → U(0), LEM : Π (x < ω). Π (A : U(x)). ((A → Void) → Void) → Truncate {x} A]` | Accept | Generic assumptions are single entries. |
| D2 | telescope `[x < ω, A : U(x), a : A]` checking `a : A` | Accept | Level entries for open goals. |
| D3 | telescope `[x < ω, x : Nat]` | Reject | Duplicate name. |
| D4 | `LEM {ω}`; source `LEM(UU0, T, …)` | Reject | Small universes only (2.10). |
| D5 | `computable def` using `LEM(U0, …)`; one using `ua(U0, …)` | Reject; Accept | Dependencies are unchanged by genericity. |
| D6 | the dependencies of a result using `Choice` at `U0` and at `U1` | `Choice`, listed once | One name per generic assumption (Q4). |
| D7 | `evaluate` of a term with a free level variable | Reject | Not closed. |
| D8 | telescope `[x < ω·2]` | Reject | Not in this version (1.5). |

### 5.8 Canonicity fixture

`docs/examples/hott-automation/canonicity.cubist` keeps every existing
declaration. After L1.1:

- `winding_two` elaborates `concatenate(U1, …)` as an instantiation of one
  generic definition checked once. It must still compute to
  `nonnegative(2)`.
- New declarations, each marked `computable` and proved by `rfl`, as
  `tests/hott-automation.test.mjs` requires:
  - `winding(concatenate(U2, S1, base, base, base, loop, loop)) = nonnegative(2)`.
    This is the same generic definition at a second level, with the same
    value.
  - `generic_identity(U0, Nat, 3) = 3` and
    `generic_identity(U1, U0, Nat) = Nat`: one definition at two levels.
  - transport of `left(tt)` along `ua(U0, Two, Two, swap)` and along
    `ua(U1, Two, Two, swap)`, each equal to `right(tt)` (K4).
  - `apply_at_nat(generic_identity) = 5`, where
    `apply_at_nat(f : forall U < UU0, forall A : U, A -> A) = f(U0, Nat, 5)`.
    This passes a generic definition as an argument (higher rank).
  - `transport(fun (X : U0) => (forall U < UU0, X), Two, Two, ua(U0, Two, Two, swap), fun (U < UU0) => left(tt))(U3) = right(tt)`.
    This transports along a line of generic statements and instantiates the
    result (K8).
- The helpers `generic_identity`, `apply_at_nat`, `Two` and `swap` live in an
  imported support module, because the harness requires every fixture
  declaration to be an `rfl` statement.
- Add `evaluate winding(concatenate(U2, S1, base, base, base, loop, loop)) expecting nonnegative(2);`,
  and raise the harness's expected evaluation count.

The test normalizes each instantiated result and compares it with the stated
value. The values are canonical data, so by Lemma 5 this equals
instantiating the generic normal form. For the kernel-level twins S2, K4 and
K8, K1.2's test also checks `nf(d {n} …) = nf(body)[x := n] …` directly.

### 5.9 Resources and malformed input (C kernel)

| ID | Input | Verdict | Reason |
| --- | --- | --- | --- |
| R1 | a chain of 10⁶ `CC_LSUCC` nodes | Reject, no crash | Recursion or step budget; sanitizers clean. |
| R2 | `CC_LMAX` with a term child; `CC_U` with no level; `CC_LPI` whose child 0 is not `CC_LBOUND`; `CC_LBOUND` as a term or with payload 0; `CC_LCONST` with a finite part above `LEVEL_MAX` | Reject; inspection stays inert | Malformed raw syntax. |
| R3 | 1,000 nested level binders, with a level mentioning all of them | Accept within budget | Heap-allocated normal forms. |
| R4 | a WASM or CLI build with a mismatched ABI version | Refused | The encoding of `CC_U` changed. |
| R5 | a deep chain of definitions whose instantiations push an intermediate level past `LEVEL_MAX` during conversion | Reject, no overflow | Checked arithmetic. The rejection point may differ between checkers, as for step budgets. |

## 6. Open questions

The numbers of the first version are kept.

| Question | Status |
| --- | --- |
| Q1. Level irrelevance for neutral type formers | Decided: no |
| Q2. Named generic statements | Resolved: yes |
| Q3. Σ, Path and composition at generic statements | Resolved: yes |
| Q4. How dependencies name generic assumptions | Decided: the name only, e.g. `LEM` |
| Q5. Truncation between G0 and H1 | Decided: keep the archive signature |
| Q6. Levels in H signatures | Decided as recommended |
| Q7. Level constraints | Deferred: proposal E1 |
| Q8. Universe binders in source | Decided as recommended |
| Q9. The level bounds | Decided: `LEVEL_MAX = 65535`, `TIER_MAX = 255` |
| Q10. Tier-1 uses of generic definitions before the extension | Deferred: proposal E2 |

**Q1. Level irrelevance for neutral type formers.** `Trunc {0} A` and
`Trunc {1} A` are distinct, non-convertible types for `A : U(0)`. The same
holds for assumptions such as `Truncate`. Generic code instantiated at `U1`
then meets values built at `U0`. Coq's cumulative inductive types make such
instances convertible when the level only bounds parameters.
*Decided:* no. Different truncations are different types. The elaborator
always picks the least level, the principal level of the argument's inferred type, so one type
appears in practice. Revisit at H1 with the rebuild's evidence. The rule
would need its own soundness argument; it is plausible because the model of
a higher inductive type does not depend on the ambient universe.

**Q2. Named generic statements. Resolved: yes.** A definition's value may be
a generic statement: `def Endo = forall U < UU0, U -> U;` is a definition of
type `UU0`. No new judgment is needed, because generic statements are
ordinary types.

**Q3. Σ, Path and composition at generic statements. Resolved: yes.** Every
former accepts types at every level and tier. Composition at a level Π is
pointwise (2.11), and Glue, univalence and universe composition at UU-tier
levels come from the level-generic rules.

**Q4. How dependencies name generic assumptions.** Should the dependency
list say `LEM` or `LEM(U0)`? *Decided:* the name only, `LEM`, since it is
one assumption. The inspector lists the level arguments at each use. The
error texts quoted in the reference change accordingly.

**Q5. Truncation between G0 and H1.** Should the generic `Truncate` keep the
archive's resizing signature `Π (x < ω). U(x) → U(0)`, or become
universe-preserving now? *Decided:* keep the archive signature, so
that the archive recheck tests G0 alone and changes no statement. H1 and
G2's policy then replace it with `Trunc : Π (x < ω). U(x) → U(x)`.

**Q6. Levels in H signatures.** Should parameter types count toward a sort's
level? *Decided:*

- a sort's level is the `max` of its data, arity and index types;
- index types count, including index types of tier 1 or above;
- parameters count only through those types.

This makes `Trunc` universe-preserving, as the kernel roadmap states. The
first version also recommended forbidding large indices and large
parameters; with no large types, that part is moot. The H design's sentence
"the maximum of the levels of its indices, data, arities and parameters"
should drop "parameters" when H is next edited. Read literally, it puts
`Trunc(A)` in `next(U)`.

**Q7. Level constraints.** Should declarations be able to state constraints
between level variables, such as `x < y`, as Coq allows? A binder's bound is
not such a constraint. *Deferred:* not in G0; recorded as proposal E1 in
the [language enhancement proposals](language-enhancement-proposals.md).
Unconstrained variables with `max` and successor express every signature we
know of, as in
`Group(U) : next(U)` and quotients at `max(U, V)`. Constraints would bring in
the Bezem–Coquand constraint problem and its loop checking.

**Q8. Universe binders in source. Decided.** The spelling is
decided: `U < UU0`, with `Universe` removed. The kernel allows a level
binder anywhere in a telescope. *Decided:* in L1.1, keep universe parameters leading in declarations,
as templates require today. Allow `forall U < UU0` anywhere in types, so
that higher-rank parameters and generic statements can be written. With
milestone 5, let an unbound universe name in a declaration header become an
implicit leading `U < UU0` parameter, as the H design's examples assume. The
inspector shows it.

**Q9. The level bounds.** `LEVEL_MAX = 65535` rejects universes the current
kernel accepts, such as `U(70000)`; today's native limit is about 2³².
*Decided:* accept the smaller bound. It simplifies overflow reasoning
in the C kernel, and no mathematics uses such levels. The revision adds
`TIER_MAX = 255` on the same grounds, which lets a level constant fit one
32-bit payload.

**Q10. Tier-1 uses of generic definitions before the extension.** In this
version a generic definition cannot be instantiated at `UU0`. A result about
types in `UU0` can use a generic library definition only through a closed
copy at a constant level. Cumulativity limits the cost: a definition at
`UU0` also accepts every type in `U(n)`. *Deferred:* not in this version.
No result needs it yet, so a universe argument of tier 1 or above is
rejected, including by the computing builtins. Proposal E2 in the
[language enhancement proposals](language-enhancement-proposals.md) records
both the extension of 1.5 and building builtin bodies at a UU-tier constant,
to be taken up when a library result needs them.
