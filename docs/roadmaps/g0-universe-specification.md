# Universe-generic checking (G0): rules and consistency

Status: specification for review, written on 2026-09-25 as work-plan item
K1.1. It specifies [kernel roadmap](cubical-kernel-roadmap.md) item G0.
Nothing here is implemented. K1.2 (reference checker), K1.3 (C kernel) and
L1.1 (language) implement it, and section 5 is their acceptance list.

## Decisions in brief

- **Levels** are `0`, `ℓ + 1`, `max(ℓ, ℓ')` and level variables. Two levels
  are equal, or ordered, exactly when they are for every assignment of natural
  numbers to their variables. A normal form decides both.
- **`Uω` is a binder marker, not a term.** It is the domain of a level binder
  and the type of a level entry in a context. Nothing else.
- **Types are small or large.** A small type is an element of some `U(ℓ)`. A
  large type is a level Π, or a Π with a large domain or codomain. A judgment
  classifies large types; no universe contains them.
- **Level quantification is a Π type** with instantiation `f {ℓ}`, a β-rule
  that substitutes the level, and an η-rule.
- **Cumulativity is symbolic.** `U(ℓ) ≤ U(ℓ')` when `ℓ ≤ ℓ'`, and the
  existing closure under Π and Σ codomains extends to level Π codomains.
- **No new composition rule.** Every Kan operation stays at small types, and
  no reduction rule reads a level.
- **Consistency.** Levels are interpreted in ℕ. A context with level variables
  is then a family of ordinary contexts indexed by level assignments. A large
  type is a presheaf that lies above every universe and is never
  internalized.

## Notation

| Symbol | Meaning |
| --- | --- |
| `x`, `y`, `z` | level variables |
| `a`, `b`, `f` | term variables |
| `i`, `j` | interval dimensions |
| `ℓ`, `m` | level expressions |
| `n` | a numeral level `0 + 1 + … + 1` |
| `Π (x : Uω). B` | level quantification (a large type) |
| `λ (x : Uω). t` | level abstraction |
| `t {ℓ}` | instantiation of `t` at level `ℓ` (source: `t(E)`) |
| `U(ℓ)` | the universe at level `ℓ`; `U0` is `U(0)` |
| `Γ` | a context of term entries `a : A` and level entries `x : Uω`; dimensions are tracked separately, as today |

"The kernel" means both checkers: the reference checker in
`lib/cubical/core.mjs` and the C kernel in `kernel/src`. They implement the
same rules independently.

## 1. Syntax

### 1.1 Levels

```text
ℓ ::= 0  |  ℓ + 1  |  max(ℓ, ℓ')  |  x
```

- Levels are not terms. A level occurs in exactly two places: as the argument
  of `U(ℓ)`, and as the argument of an instantiation `t {ℓ}`.
- A level variable is bound by `Π (x : Uω)`, by `λ (x : Uω)`, or by a level
  entry `x : Uω` of a context.
- Levels contain no term variables and no dimensions. So a level never varies
  along a line: every type family over the interval lives in one universe.
- There is no level `ω`. `U(ω)` does not exist.

### 1.2 Where `Uω` may appear

`Uω` may appear only:

- as the domain of a level binder, `Π (x : Uω). B` or `λ (x : Uω). t`;
- as the type of a level entry `x : Uω` in a context. Declaration parameters
  and entries of the kernel's assumption telescope are such entries.

`Uω` may not appear:

- as a term: an argument, a function, a body, a pair component, a system
  piece, a definition's value;
- as the type of a term, including an expected type or an ascription;
- with a type: no judgment `Uω : T` is derivable, and no `U(ℓ)` contains it;
- in a comparison: no conversion or cumulativity rule mentions `Uω`, except by
  matching two level binders;
- as the domain of Σ, W, a Path family, or any other small type former.

The elements of `Uω` are levels. The source language presents them as
universes: a source variable `U : Universe` stands for a level variable `x`,
and the source `U` in term position is `U(x)`. Levels and universes are in
bijection, `ℓ ↔ U(ℓ)`, so the two readings agree.

### 1.3 Kernel forms

| Form | Status |
| --- | --- |
| `U(ℓ)` | Changed: the argument is a level expression instead of a numeral. |
| `Π (x : Uω). B`, `λ (x : Uω). t`, `t {ℓ}` | New. |
| `Π (a : A). B`, `λ (a : A). t`, `f u` | Unchanged forms; `A` and `B` may now be large. |
| every other former | Unchanged; its type arguments must be small. |

The C kernel represents level binders by their own node kinds rather than by
Π and λ with a special domain (section 4.2). Code that handles Π therefore
cannot meet a level binder by accident.

### 1.4 Source surface

This follows the kernel roadmap's G0 text and ergonomics milestone 5.

- `Universe` is the source spelling of `Uω`. `U : Universe` binds a universe
  variable. Grouping works as today: `(U V : Universe, A : U, B : V)`.
- Universe expressions are `U0`, `U1`, …, a universe variable, `next(E)` and
  `max(E, F)`. They denote levels: `U0` is `0`, a variable `U` is its level
  variable `x`, `next(E)` is `ℓ_E + 1` and `max(E, F)` is `max(ℓ_E, ℓ_F)`.
- In term position a universe expression denotes the term `U(ℓ_E)`:
  `A : U`, `x =[next(U)] y`, `Group(U) : next(U)`.
- As the argument of a universe parameter it denotes the level `ℓ_E`:
  `identity(U2, U1, U0)` instantiates `identity` at level 2.
- `forall U : Universe, B` is `Π (x : Uω). B`, and
  `fun (U : Universe) => t` is `λ (x : Uω). t`.
- Universe arguments stay explicit in L1.1. Ergonomics milestone 5, which
  absorbs HoTT A9, later infers them from level constraints. An undetermined
  level remains an error, and the inspector shows inferred levels.
- Examples elsewhere that write `A : U` with `U` unbound, such as
  `inductive List(A : U)` in the H design, presuppose milestone 5's implicit
  binders. Under L1.1 they read `(U : Universe, A : U)`.
- The source has no separate level syntax: no `Level` type and no bare
  numerals as levels.

## 2. Judgments and rules

### 2.1 Judgment forms

| Judgment | Meaning |
| --- | --- |
| `⊢ Γ` | `Γ` is a well-formed context. |
| `Γ ⊢ ℓ level` | `ℓ` is a level whose variables are level entries of `Γ`. |
| `ℓ ≤ ℓ'`, `ℓ = ℓ'` | Level order and equality. They depend only on the two expressions. |
| `Γ ⊢ A : U(ℓ)` | `A` is a small type, an element of `U(ℓ)`. |
| `Γ ⊢ A type` | `A` is a type, small or large. |
| `Γ ⊢ t : A` | `t` has type `A`, where `Γ ⊢ A type`. |
| `A ≡ B` | Conversion: the kernel's untyped definitional equality. |
| `A ≤ B` | Cumulativity: directed typing between checked types. |

A type `A` is **large** when `Γ ⊢ A type` holds but `A` is an element of no
universe. Section 2.7 shows that this is decided by syntax.

### 2.2 Contexts

```text
C-Empty                                         ⟹  ⊢ ·
C-Term    ⊢ Γ    Γ ⊢ A type    a ∉ Γ             ⟹  ⊢ Γ, a : A
C-Level   ⊢ Γ    x ∉ Γ                          ⟹  ⊢ Γ, x : Uω
```

- Term and level entries may interleave. No entry's type can depend on a
  level entry except through level expressions.
- Level and term variables share one name supply. A name is bound once in a
  context; the kernel renames binders to avoid shadowing, as today.
- A term entry may have a large type. That is how a parameter or an
  assumption can be universe-generic.

### 2.3 Level well-formedness

```text
L-Zero    ⊢ Γ                                   ⟹  Γ ⊢ 0 level
L-Var     ⊢ Γ    (x : Uω) ∈ Γ                   ⟹  Γ ⊢ x level
L-Succ    Γ ⊢ ℓ level                           ⟹  Γ ⊢ ℓ + 1 level
L-Max     Γ ⊢ ℓ level    Γ ⊢ ℓ' level           ⟹  Γ ⊢ max(ℓ, ℓ') level
```

Side condition: `top(ℓ) ≤ LEVEL_MAX`, where `top` is defined in 2.4 and
`LEVEL_MAX = 65535`. A term variable, a term, or `Uω` in level position is
rejected.

The bound is a resource limit, not a logical rule: it can only cause
rejection. It keeps native level arithmetic within 32 bits with room for
successor and substitution, and no mathematics needs more.

### 2.4 Level normal form, equality and order

**Normal form.** `nf(ℓ) = (c, m)`, where `m` maps finitely many variables to
offsets in ℕ, and `c` is a constant with `c ≥ m(x)` for every `x`:

```text
nf(0)            = (0, ∅)
nf(x)            = (0, {x ↦ 0})
nf(ℓ + 1)        = (c + 1, {x ↦ m(x) + 1})      where nf(ℓ) = (c, m)
nf(max(ℓ, ℓ'))   = (max(c, c'), m ⊔ m')         where m ⊔ m' keeps the larger offset of each variable
```

`top(ℓ)` is `c`. Each variable keeps its largest offset, and the constant
absorbs every offset. For example `nf(x + 1) = (1, {x ↦ 1})`.

**Meaning.** For an assignment `ρ` of natural numbers to variables,
`⟦(c, m)⟧ρ = max(c, max over x of ρ(x) + m(x))`.

**Lemma 1 (soundness).** `⟦ℓ⟧ρ = ⟦nf(ℓ)⟧ρ` for every `ρ`. By induction on
`ℓ`. Absorbing offsets into `c` is harmless because `ρ(x) + m(x) ≥ m(x)`.

**Lemma 2 (order).** `⟦ℓ⟧ρ ≤ ⟦ℓ'⟧ρ` for every `ρ` if and only if `c ≤ c'`,
and every `x` in `m` is in `m'` with `m(x) ≤ m'(x)`.

- If: every part of `ℓ` is bounded by a part of `ℓ'`.
- Only if: the assignment `ρ = 0` gives `c ≤ c'`. For `x` in `m`, set
  `ρ(x) = N` with `N > c'` and every other variable to 0. The left side is at
  least `N + m(x)`. The right side is `max(c', N + m'(x))` if `x` is in `m'`,
  and `c' < N` otherwise.

**Corollary 3 (equality).** `ℓ` and `ℓ'` agree for every `ρ` if and only if
`nf(ℓ) = nf(ℓ')`. So the normal form is unique, and equality is identity of
normal forms.

**Definitions.** `ℓ ≤ ℓ'` and `ℓ = ℓ'` mean the conditions of Lemma 2 and
Corollary 3. `ℓ < ℓ'` means `ℓ + 1 ≤ ℓ'`. Both checks are linear in the size
of the normal forms.

**Printing.** `max(c, x + m(x), …)`, omitting `c` when `m` is non-empty and
`c` equals its largest offset, omitting `+ 0`, and ordering variables by
name:

| Expression | `nf` | Printed |
| --- | --- | --- |
| `max(x, x)` | `(0, {x↦0})` | `x` |
| `max(x + 1, x)` | `(1, {x↦1})` | `x + 1` |
| `max(0, x)` | `(0, {x↦0})` | `x` |
| `max(1, x + 1)` | `(1, {x↦1})` | `x + 1` |
| `max(1, x)` | `(1, {x↦0})` | `max(1, x)` |
| `max(x, y) + 1` | `(1, {x↦1, y↦1})` | `max(x + 1, y + 1)` |
| `3` | `(3, ∅)` | `3` |

Level variables are unconstrained: there are no declared constraints such as
`x < y`. So validity in ℕ is the whole theory, and no constraint solving or
loop checking is needed (see Q7).

### 2.5 Universes and cumulativity

```text
U-Form   Γ ⊢ ℓ level    top(ℓ) < LEVEL_MAX      ⟹  Γ ⊢ U(ℓ) : U(ℓ + 1)
U-Eq     nf(ℓ) = nf(ℓ')                         ⟹  U(ℓ) ≡ U(ℓ')
U-Cum    ℓ ≤ ℓ'                                 ⟹  U(ℓ) ≤ U(ℓ')
Sub      Γ ⊢ t : A    Γ ⊢ B type    A ≤ B        ⟹  Γ ⊢ t : B
```

- Universes are à la Russell: an element of `U(ℓ)` is itself a type.
- Cumulativity is subsumption, as today
  ([cumulativity.md](../cubical/cumulativity.md)). There are no lift terms,
  and two universes are convertible only when their levels are equal.
- Examples: `U(x) : U(x + 1)`, `U(x) : U(max(x + 1, y))`, and `Nat : U(x)`.
  But not `U(x) : U(x)`, not `U(x) : U(1)`, and `A : U(x)` does not give
  `A : U(0)`.

### 2.6 Small type formers

The existing rules stand, with level expressions in place of numerals. Every
premise that asks for a type asks for a small one. The result's level is the
`max` of the inferred levels of its parts:

| Former | Result universe |
| --- | --- |
| `Nat`, `Unit`, `Void` | `U(0)` |
| `U(ℓ)` | `U(ℓ + 1)` |
| `Π (a : A). B`, `Σ (a : A). B`, `W (a : A). B`, all parts small | `U(max(ℓ_A, ℓ_B))` |
| `A + B` | `U(max(ℓ_A, ℓ_B))` |
| `Pushout(C, A, B, maps)` | `U(max(ℓ_C, ℓ_A, ℓ_B))` |
| `Path(i. A, a, b)` with `Γ, i : I ⊢ A : U(ℓ)` | `U(ℓ)` |
| `Glue [φ ↦ (T, e)] A` | `U(max(ℓ_A, ℓ_T, …))` |

The inferred level is the least one. A check against a larger universe uses
`U-Cum`. A large type in any premise of these formers is rejected. The same
holds wherever an existing rule asks for a type: eliminator motives must
land in a universe, and pair annotations, Glue annotations and `Abort`
targets must be small.

### 2.7 Large types

```text
Ty-Small  Γ ⊢ A : U(ℓ)                              ⟹  Γ ⊢ A type
∀-Form    Γ, x : Uω ⊢ B type                        ⟹  Γ ⊢ Π (x : Uω). B type
Π-Large   Γ ⊢ A type    Γ, a : A ⊢ B type    A or B large
                                                    ⟹  Γ ⊢ Π (a : A). B type
```

**Size is syntactic.** `A` is large exactly when `A` is `Π (x : Uω). B`, or
`A` is `Π (a : A₁). B` with `A₁` or `B` large. Small and large exclude each
other:

- no rule puts a level Π in a universe;
- the small Π rule needs both parts small;
- no term reduces to a large type. A large type is never the value of a
  variable, a definition or an application, because nothing could type such
  a term: that would need a sort of large types.

So whether a type is large is decided by its syntax alone, and it is stable
under every substitution.

A large type may be:

- the type of a definition (its statement);
- the type of a context entry, as a parameter or an assumption;
- the domain or codomain of a Π, or the body of a level Π.

It may be nothing else. In particular it is never an element of a universe,
and never an argument of `Path`, `PathP`, Σ, W, sums, pushouts, Glue,
composition, transport, truncation or an eliminator motive.

The terms of a large type are variables, definitions, λ, level λ,
applications and instantiations. No pair, path or composition has a large
type.

### 2.8 Level quantification

```text
∀-Form    Γ, x : Uω ⊢ B type                        ⟹  Γ ⊢ Π (x : Uω). B type        (large)
∀-Intro   Γ, x : Uω ⊢ t : B                         ⟹  Γ ⊢ λ (x : Uω). t : Π (x : Uω). B
∀-Elim    Γ ⊢ f : Π (x : Uω). B    Γ ⊢ ℓ level      ⟹  Γ ⊢ f {ℓ} : B[x := ℓ]
∀-β       (λ (x : Uω). t) {ℓ}  ≡  t[x := ℓ]
∀-η       f  ≡  λ (x : Uω). f {x}                   when x is not free in f
```

- As the roadmap adopted, level quantification is a type former, not only a
  prefix of declarations. `Π (n : Nat). Π (x : Uω). U(x)` is a type, and a
  parameter may have a level Π type, so a result can take a universe-generic
  function as an argument.
- `∀-Elim` requires the function's type to reduce to a level Π. Term
  application `f u` requires a term Π. The kernel keeps the two application
  forms distinct.
- `∀-Elim` also rejects a result type `B[x := ℓ]` in which a level exceeds
  `LEVEL_MAX`.
- A level abstraction may return a type: `λ (x : Uω). U(x)` has type
  `Π (x : Uω). U(x + 1)`. A generic family such as
  `Group : Π (x : Uω). U(x + 1)` is of this kind.

### 2.9 Π with a large part

```text
Π-Large   Γ ⊢ A type    Γ, a : A ⊢ B type    A or B large
                                                    ⟹  Γ ⊢ Π (a : A). B type        (large)
Lam       Γ ⊢ A type    Γ, a : A ⊢ t : B            ⟹  Γ ⊢ λ (a : A). t : Π (a : A). B
App       Γ ⊢ f : Π (a : A). B    Γ ⊢ u : A         ⟹  Γ ⊢ f u : B[a := u]
β, η      as for small Π
```

These are the existing λ, application, β and η, typed with `type` instead
of a universe. For example,
`Π (f : Π (x : Uω). Π (A : U(x)). A → A). Nat` is large because its domain
is.

### 2.10 Level substitution

`t[x := ℓ]` replaces each free occurrence of `x` in the level expressions of
`t`. Those are the arguments of `U(·)` and of instantiations.

- **Capture.** Before descending under a binder of `t`, the substitution
  renames the binder if its name occurs free in `ℓ`. This applies to level
  binders and, because names share one supply, to term binders too.
- **Scope.** It does not touch term variables, dimensions, faces or the
  bodies of definitions, which are closed.
- **Commutation.** Level substitution commutes with term substitution and
  with dimension substitution, since they act on disjoint positions.

**Lemma 4 (substitution).** If `Γ, x : Uω, Δ ⊢ J` and `Γ ⊢ ℓ level`, then
`Γ, Δ[x := ℓ] ⊢ J[x := ℓ]`, unless a level of the result exceeds
`LEVEL_MAX`. By induction on the derivation. Two facts carry it:

1. Level judgments are stable. If `ℓ₁ ≤ ℓ₂` holds for every assignment, it
   holds after substituting `ℓ` for `x`: an assignment `ρ` for the result
   gives the assignment `ρ[x ↦ ⟦ℓ⟧ρ]` for the original. Equality likewise.
2. No rule has a negative level premise, such as `ℓ ≠ 0` or `ℓ ≰ ℓ'`. No
   rule uses a level for anything but `≤` and `=`.

The inferred type of `t[x := ℓ]` may be smaller than the substituted
inferred type, as with term substitution today. The cumulativity closure in
2.11 covers this.

### 2.11 Conversion and cumulativity

Conversion is the kernel's existing untyped algorithm: folded comparison,
then weak-head reduction, with η for functions, pairs and paths. G0 adds:

```text
U-Eq      U(ℓ) ≡ U(ℓ')                      when nf(ℓ) = nf(ℓ')
Inst      f {ℓ} ≡ f' {ℓ'}                   when f ≡ f' and nf(ℓ) = nf(ℓ')
∀-Cong    Π (x : Uω). B ≡ Π (y : Uω). B'     when B ≡ B'[y := x]
∀-Lam     λ (x : Uω). t ≡ λ (y : Uω). t'     when t ≡ t'[y := x]
∀-β, ∀-η  as in 2.8
```

- Levels are compared by normal form, never by reduction.
- Under binders, level variables are compared through the comparison's
  current renaming. So `λ (x : Uω). U(x) ≡ λ (y : Uω). U(y)`. Comparing
  stored payloads, as the C kernel compares universes today, is not enough.
- `∀-η` applies when one side is a level λ and the other is not. The other
  side is instantiated at the fresh variable.

Cumulativity is directed, and holds only between checked types:

```text
≤-Conv   A ≡ B                                          ⟹  A ≤ B
≤-U      ℓ ≤ ℓ'                                         ⟹  U(ℓ) ≤ U(ℓ')
≤-Π      A ≡ A'    Γ, a : A ⊢ B ≤ B'[a' := a]            ⟹  Π (a : A). B ≤ Π (a' : A'). B'
≤-Σ      A ≡ A'    Γ, a : A ⊢ B ≤ B'[a' := a]            ⟹  Σ (a : A). B ≤ Σ (a' : A'). B'
≤-∀      Γ, x : Uω ⊢ B ≤ B'[y := x]                     ⟹  Π (x : Uω). B ≤ Π (y : Uω). B'
```

`≤-∀` is new. It is needed for the same substitution reason as `≤-Π`. For
example, `λ (A : U(1)). λ (x : Uω). A` has type `Π (A : U(1)). Π (x : Uω). U(1)`.
Applied to `Nat`, it reduces to `λ (x : Uω). Nat`, whose inferred type is
`Π (x : Uω). U(0)`. The reduct must still check at `Π (x : Uω). U(1)`.

Unchanged:

- domains must be convertible, with no contravariance;
- no universes are identified and nothing is lowered;
- there is no cumulativity inside `Path`, Glue or other formers.

### 2.12 Definitions and assumptions

- **Definitions.** A definition `d : A := t` is checked once, in the empty
  context: `· ⊢ A type` and `· ⊢ t : A`. `A` may be large. Its value is a
  term; it is never a large type (Q2). Uses are `d` and `d {ℓ}`. δ-unfolding
  is unchanged.
- **Assumption telescope.** Entries of the kernel's assumption telescope
  (`cc_assumption`) may be level entries `x : Uω` and term entries of large
  type. A generic axiom is one entry, such as
  `LEM : Π (x : Uω). Π (A : U(x)). ((A → Void) → Void) → Truncate {x} A`.
  Level entries let the elaborator check open goals under `U : Universe`.
- **Expected types.** The expected type of a check may be large.
- **Non-computing dependencies.** These are computed from the checked term,
  as today. A generic assumption contributes one name, whatever levels it is
  used at (Q4).

### 2.13 Interaction with the cubical rules

- **Levels are constant along lines.** Levels contain no dimensions. In a
  family `Γ, i : I ⊢ A : U(ℓ)` the universe does not depend on `i`. There is
  no transport between universes of different levels, and no rule compares
  levels at two endpoints.
- **Path and PathP.** The family must be small, and the path type lives in
  its universe. There are no paths between elements of a large type. State
  such facts pointwise under a level Π:
  `Π (x : Uω). Path(B, f {x}, g {x})`.
- **Composition, `hcomp` and transport.** The family must be small. Tubes and
  base are terms of small types. They may mention variables of large type,
  and restricting to a face acts on those like on any term. Nothing composes
  in a large type.
- **Fibrancy of `U(ℓ)`.** Composition in a universe reduces as it does today,
  by CCHM §7.1:

  ```text
  comp^i U(ℓ) [φ ↦ E] A  ⟶  Glue [φ ↦ (E(1), transport of the identity equivalence)] A
  ```

  The rule never reads `ℓ`. In the C kernel, `composition_compute.c` sends a
  `CC_U` family to `ck_universe_composition` in `glue_compute.c`. In the
  reference checker, `normal` sends a `U` family to `universeComposition`.
  Neither reads the level. The reduct's inferred level is
  `max(ℓ_A, ℓ_{E(1)}) ≤ ℓ`, so it checks at `U(ℓ)` by `U-Cum`, a symbolic
  check.
- **Glue.** The base and the partial types must be small. The Glue type lives
  at the `max` of their levels. The equivalence type `Equiv(T, A)` is formed
  at `max(ℓ_T, ℓ_A)`, and the overlap checks are unchanged. CCHM puts `T`
  and `A` in one universe. With cumulativity, taking the `max` is
  equivalent. `check_glue.c` and `core.mjs` already compute a `max`, and
  under G0 it becomes a level expression.
- **Univalence.** One computable generic definition replaces the
  per-universe builtins `builtin__ua__U<n>`:

  ```text
  ua : Π (x : Uω). Π (A B : U(x)). Equiv(A, B) → Path(U(x), A, B)
  ua := λ (x : Uω). λ (A B : U(x)). λ (e : Equiv(A, B)).
          ⟨i⟩ Glue [i = 0 ↦ (A, e), i = 1 ↦ (B, idEquiv(B))] B
  ```

  It is checked once. Its Glue type lives at `max(x, x) = x`.
- **The other composition rules** cover Π, Σ, Path, `Nat`, `Unit`, sums, W,
  pushouts and Glue. Each dispatches on the head former of a small family.
  None reads a level.

**Conclusion: G0 needs no new composition rule.**

1. No family of a Kan operation is large.
2. Every composition and transport rule dispatches on the head of a small
   family and ignores levels.
3. The universe's rule is the same Glue construction at every level.
4. Levels are constant along lines.

In cubical checking, G0 changes one thing: level comparisons inside typing
become symbolic. That covers Glue's `max`, the result universe of Path, and
composition's expected types.

### 2.14 Interaction with the H stages

Every H declaration is level-generic, so H1–H4 must fit these rules.

- **Level parameters.** A signature's shared parameter telescope may begin
  with level entries `x : Uω`. The other parameters have small types.
  Generated constants (sort formers, constructors, eliminators) are
  level-abstracted over these entries. For example,
  `Trunc : Π (x : Uω). Π (A : U(x)). U(x)`.
- **A sort's level** is the `max` of the levels of the types of its data, its
  position arities and its indices. Parameters count only through those
  types. So `Trunc {x} A` lives in `U(x)`, which makes truncation
  universe-preserving. Index types must be small, and they count: a family
  indexed by `U(x)` lives in `U(x + 1)` or above. There are no large indices
  and no large parameters (Q6).
- **Eliminator motives** may land in any `U(ℓ')`, including one at a level
  variable. A motive into a large type cannot be typed, since it would need a
  sort of large types.
- **Kan structure.** Formal composition, transport along parameter lines,
  index-line matching and boundary reduction read no level. Parameter lines
  never vary a level. So H inherits "no new composition rule" from G0.
- **Soundness notes.** By the decomposition in 3.2, each H stage can argue at
  a fixed level assignment. Level parameters add no H obligation.
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
  universe obtained by Hofmann–Streicher lifting from a Grothendieck universe.
  The universe is fibrant by Glue.
- A countable hierarchy iterates this. Fix Grothendieck universes
  `V_0 ∈ V_1 ∈ …`, which ZFC with countably many inaccessibles provides, and
  let `U_n` classify `V_n`-small fibrant families. A fibration structure is
  the same data at every level, so `U_n ⊆ U_{n+1}` as presheaves. The Glue
  composition of `U_{n+1}` restricts to that of `U_n`. This models
  subsumptive cumulativity without lift terms.
- Pushouts follow Coquand–Huber–Mörtberg. W types and sums are standard.

G0 does not change this base. It adds level variables and large types on
top of it.

### 3.2 Interpretation of G0

- **Levels.** For an assignment `ρ` of numbers to level variables, a level
  denotes `⟦ℓ⟧ρ ∈ ℕ`. Lemmas 1–3 make the level rules sound and complete for
  this reading.
- **Contexts.** A level entry contributes the constant presheaf `Δℕ`, whose
  restriction maps are identities: `⟦Γ, x : Uω⟧ = ⟦Γ⟧ × Δℕ`. Term entries
  are interpreted by comprehension, as in CCHM.
- **Decomposition lemma.** `Δℕ` is discrete, and level variables depend on
  nothing. So `⟦Γ⟧ ≅ ∐_ρ ⟦Γ[ρ]⟧`, where `ρ` ranges over assignments to the
  level entries, and `Γ[ρ]` drops those entries and evaluates every level at
  `ρ`.
  - A small type over `⟦Γ⟧` is then exactly a `ρ`-indexed family of fibrant
    types over the presheaves `⟦Γ[ρ]⟧`, and a term is a `ρ`-indexed family of
    terms. CCHM's model interprets types over any presheaf, so the CCHM_ω
    rules apply at each `ρ`. When `Γ` has no entry of large type, each `Γ[ρ]`
    is an ordinary CCHM_ω context.
  - The small rules of G0 are the CCHM_ω rules applied at each `ρ`. The only
    new ingredient is that level premises are checked for all `ρ` at once,
    which is what the normal forms decide.
- **Universes.** `⟦U(ℓ)⟧` is `U_{⟦ℓ⟧ρ}` on the summand for `ρ`. It is fibrant
  because each `U_n` is. Its composition structure is defined summand by
  summand, and it is uniform because restriction maps preserve summands.
- **Large types** are dependent presheaves over `⟦Γ⟧` without fibrancy
  structure. `⟦Π (x : Uω). B⟧` is the dependent product along
  `⟦Γ⟧ × Δℕ → ⟦Γ⟧`. Since `Δℕ` is discrete, this is the pointwise countable
  product `∏_n ⟦B⟧(–, n)`. A Π with a large part is the dependent product of
  presheaves, since presheaf categories are locally cartesian closed. `∀-β`,
  `∀-η`, β and η hold there.
- **Size.** A fiber of a large type, such as `∏_n U_n(I)`, is a set in no
  `V_n`. It is still a set, because the cube category is small. So large
  types live in the ambient category of presheaves of sets, and no further
  Grothendieck universe is needed.
- **Consistency.** A closed term of `Void` in the empty context would give a
  global element of `⟦Void⟧ = ∅`. The empty context has no level entries, so
  no decomposition is involved. G0 is therefore consistent relative to the
  metatheory that models CCHM_ω, for example ZFC with countably many
  inaccessible cardinals.

### 3.3 Why `Uω` must not be a term

- **Level variables then denote natural numbers only.** Only a level
  expression can be substituted for a level variable, and every level
  expression has a finite value under every assignment. If `Uω` were a term,
  it could be passed where a universe is expected, so a level variable could
  stand for `ω`. Then `U(x) : U(x + 1)` at `x = ω` needs a universe above `ω`.
  And `Π (x : Uω). …` would quantify over a collection containing `Uω`. That
  forces either `Uω : Uω`, which is Type-in-Type and inconsistent by
  Girard's paradox (Hurkens' form), or a new universe above `Uω`. The latter
  is THTH's `UUKappa`, and the same question then recurs for it.
- **Large types are not universe elements.** If some universe contained
  `Π (x : Uω). U(x)`, it would contain every `U_n` and could be none of them.
  The model would need an internal `U_ω`, and a type for it: the tower the
  design avoids. Classified by a judgment, large types need only the ambient
  presheaf category.
- **`Uω` has no type and is never compared.** So no conversion or
  cumulativity rule involves it. The equational theory of large types is
  structural: they are Π-trees whose leaves are small types.
- **Large types stay out of small formers and Kan operations.** Consistency
  does not need this. A countable product of fibrant presheaves is fibrant,
  so `Path` over a level Π could be modelled. The restriction means G0 needs
  no composition structure for large types, and no Kan operation ever meets
  a level binder. It could be lifted later with a pointwise composition rule
  if a use appears (Q3).

### 3.4 Conservativity over templates

Call the **prenex fragment** the derivations with two properties:

- every large type is the statement of a top-level definition or
  assumption, of the form `Π (x₁ : Uω). … Π (x_k : Uω). A` with `A` small;
- every use of such a constant is instantiated at once, at `k` levels.

**Claim.** On the prenex fragment, every closed judgment at a small type is
derivable in CCHM_ω, by specializing each generic constant at the levels it
is used at. This is exactly what today's elaborator templates do.

- By Lemma 4, each specialized copy checks.
- A closed term needs finitely many copies, since each copy mentions
  finitely many instances at closed levels.

So on this fragment G0 proves nothing that templates could not. It checks
each constant once, for every level. The converse fails on purpose: a
template that checks only at particular levels is rejected by G0, and the
archive recheck lists such templates.

Higher-rank uses have no template counterpart. A parameter of large type is
an example. They rely on the model of 3.2.

### 3.5 Canonicity and computability

**Reduction is level-parametric.** No reduction rule reads a level. The
rules are:

- β and `∀-β`, δ and projections;
- eliminators on constructors, and path application at endpoints;
- composition and transport by type former (Π, Σ, Path, `Nat`, `Unit`, sums,
  W, pushouts, Glue, `U`);
- Glue and `unglue`.

The universe case builds a Glue type without inspecting its level.

**Lemma 5 (instantiation commutes with reduction).** Let `σ` be a level
substitution.

1. **Every rule is stable.** If `t ⟶ t'`, then `t[σ] ⟶ t'[σ]` by the same
   rule at the same position. A side condition that compares two subterms,
   by syntax or by conversion, still holds after `σ`.
2. **Most rules gain no redex.** For β, `∀-β`, δ, projections, eliminators on
   constructors, path application at endpoints, composition and transport by
   type former, and `unglue` of `glue`, every redex of `t[σ]` is the image of
   a redex of `t`. Their patterns mention only term formers. `σ` changes only
   level expressions, which are leaves for reduction.
3. **Comparing contractions can gain one.** A few η-contractions in the
   normalizers compare two subterms, such as surjective pairing
   `(fst p, snd q) ⟶ p` and `glue` of an `unglue`. `σ` can make two
   different levels equal: `g {x}` and `g {y}` coincide under `x, y := 0`.
   These contractions relate convertible terms.

Hence `nf(t[σ]) = nf(nf(t)[σ])`, and the outer normalization performs only
contractions of the third kind. If `nf(t)[σ]` has none, then
`nf(t[σ]) = nf(t)[σ]`. Canonical values of data types have none. So for a
generic definition `d := λ (x : Uω). t` whose instances compute to canonical
data, `nf(d {n}) = nf(t)[x := n]`. Computing the generic body once and
instantiating gives the value that each specialized copy computed before
G0. In general the two agree up to those η-contractions, and they are
always convertible.

**Canonicity.** Suppose `· ⊢ t : A`, where `A` is a closed data type as in
invariant 10 and `t` uses no assumption. Then `t` reduces to a canonical
value. The argument extends Huber's computability predicates:

- A closed large type is a finite Π-tree whose leaves are small types.
- `t` is computable at `Π (x : Uω). B` when `t {n}` is computable at
  `B[x := n]` for every numeral `n`.
- `t` is computable at `Π (a : A). B` with a large part when `t u` is
  computable at `B[u]` for every computable `u` at `A`.
- This is well founded. Substituting numerals or terms does not change the
  Π-tree, and small types use the existing predicates at level `n`, by
  induction on `n` over the hierarchy.
- The fundamental lemma gains the cases `∀-Intro`, `∀-Elim`, `∀-β` and
  `Π-Large`. Each is immediate from these definitions.

So G0 has canonicity whenever CCHM_ω has it, and in the same sense.

**Computability tracking.**

- Non-computing dependencies are computed from the term, which does not
  depend on the level. So a generic definition has the same dependencies at
  every level. `computable def` on a generic definition covers every
  instance.
- `evaluate t expecting v` requires `t` closed, including no free level
  variable.
- The canonicity fixture gains instantiated generic results (section 5.8).

### 3.6 What is proved, argued and assumed

| Claim | Status |
| --- | --- |
| Level normal forms are unique; the decision procedure is sound and complete for ℕ | Proved here (Lemmas 1–3). |
| Level substitution lemma | Proved here in outline (Lemma 4). Standard. |
| Reduction commutes with level substitution, exactly for canonical data and up to comparing η-contractions in general | Proved here (Lemma 5), given the invariant that no rule reads a level. K1.2 and K1.3 check that invariant by review and by the tests in section 5. |
| Conservativity over templates on the prenex fragment | Proved here in outline (3.4). |
| The cubical-set model of G0 with levels in ℕ | Argued from standard constructions (discrete presheaf, presheaf Π, decomposition). Not written out in full. |
| Canonicity for G0 | Argued: reduced to canonicity for CCHM_ω by extending Huber's predicates. |
| Consistency and canonicity of CCHM_ω with the kernel's formers | Assumed. This is the existing kernel's trust base: CCHM and Huber for the core, Coquand–Huber–Mörtberg for pushouts, and the standard iteration for the hierarchy. Huber treats a single universe; the hierarchy and the kernel's pushouts are not covered by a published canonicity proof that we know of. |
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
  "every `U_n` is fibrant by one construction".
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
  CSL 2022. Hierarchies over richer level structures, including first-class
  and transfinite levels. G0 stays at the simplest case: finite levels and an
  uninternalized `ω`.
- Agda user manual, *Universe Levels* and *Sort System*. `Setω` is a sort
  above every `Set ℓ` for level-quantified types. Agda later added
  `Setω₁, …` above it; G0 stops at the first step.
- de Moura, Ullrich, *The Lean 4 Theorem Prover and Programming Language*,
  CADE 2021; Carneiro, *The Type Theory of Lean*, MSc thesis, CMU, 2019.
  Prenex universe parameters with successor, `max` and `imax`, level
  equality by normalization, and a soundness proof relative to ZFC with
  inaccessible cardinals.
- Hurkens, *A Simplification of Girard's Paradox*, TLCA 1995. Why `Uω`
  cannot be an element of what it quantifies over.
- The Rust THTH kernel (`KanHarI/thth`). The project's precedent:
  `UUOmega : UUKappa`, which G0 avoids.

## 4. Implementation consequences

Both checkers implement section 2 independently. The reference checker lands
first.

### 4.1 K1.2: reference checker (`lib/cubical/core.mjs`)

**Data.**

- **Level nodes.** `{tag:"LConst", value}`, `{tag:"LSucc", level}` and
  `{tag:"LMax", left, right}`. Level variables are ordinary
  `{tag:"Var", name}` nodes in level position. This mirrors the C kernel,
  and substitution and free-variable code then covers levels.
- **Universes.** `{tag:"U", level}` takes a level node. For the many existing
  callers, `T.universe(n)` with a number builds `LConst`.
- **Level binders.** `{tag:"LPi", name, body}`, `{tag:"LLam", name, body}`
  and `{tag:"LApp", fn, level}`.
- **Level entries.** `{tag:"Omega"}` appears only as the type of a level
  entry in `verify`'s assumptions and in the checker's context map.
- **Definitions.** A definition registry: `define(name, value, type)` checks
  once, and `DefRef` infers the stored type and unfolds in `normal`. The
  reference checker has no inference rule for `DefRef` today. Without one it
  cannot test "checked once, instantiated at two levels" as the C kernel will.
- **Level module.** A new `lib/cubical/levels.mjs` provides `normalizeLevel`,
  `levelLeq`, `levelEqual`, `printLevel` and `LEVEL_MAX`. The elaborator may
  use it for display. The C kernel does not share it.

**Checks.**

- **Sizes.** `sort(t, ctx, dims)` returns `{term, level}` for a small type or
  `{term, large: true}`. It is used for binder domains, assumption types,
  definition types and expected types. `type()` stays small-only and rejects
  a large type with a specific message.
- **`infer`.** `U` checks its level and the successor bound. `Var` rejects a
  level entry ("a universe variable is not a term"). `Omega` is rejected
  everywhere. `LPi` goes through `sort` only. `LLam` and `LApp` follow 2.8.
  `Pi` and `Lam` use `sort` for the domain. `App` rejects a level Π, and
  `LApp` rejects a term Π.
- **`cumulative`.** `U` uses `levelLeq`. Add the `≤-∀` case.
- **`free`, `substitute`, `alpha`, `normal`.** These become level-aware.
  - `alpha` renders `U` and `LApp` levels as normal forms, with bound
    variables replaced by binder indices.
  - `normal` adds `∀-β`, and η-contraction of `λ (x : Uω). f {x}`, as it
    already contracts term η.
- **Small formers.** Every former other than Π keeps `type()`, which rejects a
  large type.

**Tests** (`lib/cubical/tests/levels.test.mjs` and
`lib/cubical/tests/g0.test.mjs`):

- every case of section 5, by its ID;
- a property test comparing `levelLeq` and `levelEqual` with brute-force
  evaluation over assignments up to `2·top + 2`;
- a property test for Lemma 5: for random well-typed generic terms `t` and
  numerals `n`, `nf(t[x := n])` equals `nf(nf(t)[x := n])`, and equals
  `nf(t)[x := n]` when the result is canonical data.

### 4.2 K1.3: C kernel, ABI, serialization, sanitizers

**Node kinds.** Tags 1–42 keep their numbers. The new kinds are appended:

| Tag | Kind | Payload and children |
| --- | --- | --- |
| 43 | `CC_OMEGA` | none; valid only as a level binder's child 0 or a level entry's type |
| 44 | `CC_LCONST` | payload `n` |
| 45 | `CC_LSUCC` | child 0: level |
| 46 | `CC_LMAX` | children 0 and 1: levels |
| 47 | `CC_LPI` | payload: binder symbol; child 0: `CC_OMEGA`; child 1: body |
| 48 | `CC_LLAM` | payload: binder symbol; child 0: `CC_OMEGA`; child 1: body |
| 49 | `CC_LAPP` | child 0: function; child 1: level |

- **`CC_U` changes.** Child 0 is a level node and the payload must be zero.
  Today the payload is the level. `ck_arity(CC_U)` becomes 1.
- **Level variables** are `CC_VAR` nodes bound by `CC_LPI`, `CC_LLAM` or a
  level entry.
- **Generic binder code.** `ck_term_binder` includes `CC_LPI` and `CC_LLAM`.
  Their layout matches the other binders (symbol in the payload, body in
  child 1), so substitution, free-variable computation and α-comparison
  apply unchanged.
- **ABI version.** Add `cc_kernel_abi_version()` and a matching constant in
  the JavaScript loaders, because the encoding of `CC_U` changes. The WASM
  bridge and `kernel-cli` refuse a mismatch.

**Internal functions.**

- `ck_level(k, raw, ctx, &level)` checks well-formedness and returns a
  canonical level node. `ck_level_normal`, `ck_level_leq`, `ck_level_equal`,
  `ck_level_max` and `ck_level_succ` work on a `cc_level_nf`:
  `{uint32_t constant; uint32_t count; {uint64_t key; uint32_t offset} terms[]}`,
  sorted by key.
- A key is the variable's symbol when it is free. During α-comparison it is
  the identity of the binding it resolves to, so renamed binders compare
  equal.
- `ck_type` returns a level handle instead of `uint32_t`. A new `ck_sort`
  returns either a level or "large". Binder domains, assumption types,
  definition types and expected types use `ck_sort`.
- Every site that builds `CC_U` from a computed level builds a canonical
  level node. Every `>` comparison of levels becomes `ck_level_leq`. The
  sites are:
  - `check.c` (U);
  - `check_functions.c` (Π, Σ);
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
- `cc_context` entries whose type is `CC_OMEGA` are level entries. `CC_VAR`
  inference rejects them, and `ck_level` accepts them.
- Composition, Glue and pushout computation files need no rule change. An
  audit test checks that no code outside the level functions reads a `CC_U`
  child.

**Public API.**

- `cc_kernel_check` and `cc_kernel_check_in_cube` accept level entries and
  large types in the assumption telescope, and a large `expected`.
- `cc_kernel_define` accepts a large type.
- `cc_kernel_node` exposes level nodes. Inspection functions treat malformed
  level nodes as inert syntax.

**Resources and safety.**

- Level arithmetic uses 64-bit intermediates and rejects results above
  `LEVEL_MAX`. The bound is checked for level literals, for `U-Form`, for
  instantiation results and whenever a level is normalized, including during
  conversion.
- Normal forms are heap-allocated with checked sizes.
- Deep `CC_LSUCC` chains are handled iteratively or under the recursion
  counter.
- Canonical level nodes may be interned. That is an optimization and never a
  typing certificate.

**Serialization and bridges.**

- `lib/cubical/native.mjs` gains the new kinds. `N` lines keep their format.
  An `A` line may name the `CC_OMEGA` handle as a type, and a `D` line may
  carry a large type.
- `web/cubical-syntax.mjs` and `web/cubical-kernel.mjs` encode and decode
  level nodes, and decode `CC_U` from its child.
- `cb_context_add` accepts `CC_OMEGA`.
- Every consumer of a numeric universe level moves to level expressions:
  - the renderers `web/cubical-notation.mjs` and `web/math-notation.mjs`;
  - the bridges `web/cubical-syntax.mjs` and `lib/cubical/native.mjs`;
  - `core.mjs` and `translate.mjs`.

  The template inspection in `web/cubical-program.mjs` is removed (4.3).

**Tests.**

- `kernel/tests/test_levels.c`: normal forms, order, the bound, and malformed
  nodes.
- `test_conversion.c`: α-renamed levels and level η.
- `test_kernel_api.c`: large assumptions and definitions, and the ABI
  version.
- `tests/cubical-wasm.test.mjs` runs every case of section 5 through both
  checkers and compares verdicts and normal forms.
- `make test` and `make CC=clang sanitize`, including a fuzz of random level
  nodes.

### 4.3 L1.1: language and removal of templates

**Elaboration.**

- **Parser.** `next(E)` and `max(E, F)` are new universe expressions.
  `Universe` and `U<n>` keep their spelling.
- **Scope.** `translate.mjs` gains a scope entry for universe variables,
  mapping a source name to a kernel level variable. A universe expression
  translates to a level in argument position, and to `U(level)` in term
  position.
- **Declarations.** `def d(U : Universe, …) : T` becomes one kernel
  definition, with value `λ (x : Uω). …` and type `Π (x : Uω). …`, checked
  once. A use `d(E, …)` becomes `d {ℓ_E} …`.
- **Kept.** The `typed(E, T)` ascription and explicit universe arguments.
- **Inspector.** It shows level abstractions and instantiations in source
  notation (`identity(U2, …)`), and prints levels as universe expressions
  (`max(U, U1)`).
- **Generic rules.** Rule environments, caches and goal contexts key on level
  variables instead of specializations. Rewriting with a generic rule matches
  a level argument only when the rule's level is a variable. Anything harder
  waits for milestone 5.

**Removed:**

- `UniverseSchema`, `expandUniverseBinders`, `specializeSchema` and the
  "not-translated" status of schemas;
- the per-universe builtins `builtin__ua__U<n>` and their closures;
- the per-universe keys of `libraryAssumption` (`${name}_U${level}`) in
  `web/cubical-assumptions.mjs`, and the origin kind
  `universe-specialized-assumption`;
- the template provenance panel `web/cubical-specialization.mjs`, and the
  inspector's `U0`–`U3` picker for templates;
- the migration verifier's specialization probes;
- the rule that withholds "Replace with simp only" for templates. One check
  now covers every level.

**Assumptions.** Each assumption becomes one entry with a large type and
the same content:

- `Truncate : Π (x : Uω). U(x) → U(0)` keeps the archive's resizing
  signature until H1 and G2 replace it with the universe-preserving `Trunc`
  (Q5);
- `TruncateIntro`, `TruncateProp` and `TruncateElim` follow the archive
  schema, with `A` and `P` in one universe `U(x)`;
- likewise `LEM`, `Choice`, `FunExt` and `Univalence`.

**Migration of today's templates.**

- **Dependency names.** Dependency names change from `Choice(U0)` to
  `Choice` (Q4). The migration verifier maps old per-level names to the
  generic name with a fixed table, so the rename does not count as a change
  of assumptions. The Computability examples in `web/language.html` quote
  `LEM(U0), Truncate(U0), TruncateElim(U0)`, and the reference harness
  checks those messages, so they are updated with it.
- **Archive recheck.** Elaborate each of the archive's 43 templates
  generically, together with its dependents. Record each template that fails
  in a checked-in list: the rule that failed, and the levels at which it used
  to check. Typical causes are using the universe variable as an element of
  a fixed universe (`U : U1`) and relying on `Truncate`'s resizing. Do not
  weaken a rule to accept a template.
- **Reference.** Rewrite the Universes section of `web/language.html`, and
  the paragraphs on specialization in the Axioms section.

**Sequencing.** The elaborator checks through the native kernel
(`NativeCubicalElaborator`). The reference checker is used only in tests.
So L1.1 can be developed against K1.2 in tests, but the template removal and
the archive recheck land only after K1.3.

## 5. Acceptance cases

Each case has an ID for K1.2's and K1.3's tests. "Accept" and "Reject" are
the verdicts of both checkers. `Γ` is empty unless stated. `x, y, z : Uω`
are level entries where they occur.

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

### 5.2 Placement of `Uω`

| ID | Judgment | Verdict | Reason |
| --- | --- | --- | --- |
| W1 | infer `Uω` | Reject | `Uω` is not a term. |
| W2 | `(λ (A : U(1)). A) Uω` | Reject | `Uω` as an argument. |
| W3 | `Uω : U(ℓ)` for any `ℓ` | Reject | `Uω` has no type. |
| W4 | `Σ (x : Uω). U(x)` | Reject | Σ needs a small domain; `Uω` is not a type. |
| W5 | `Path(Uω, …)` | Reject | `Uω` in a Path family. |
| W6 | `x : Uω ⊢ x : A` for any `A` | Reject | A universe variable is not a term; write `U(x)`. |
| W7 | `(λ (x : Uω). U(x)) {Nat}`; `(λ (x : Uω). U(x)) Nat` | Reject both | Instantiation needs a level; term application needs a term Π. |
| W8 | `x : Uω ⊢ U(x) : U(x + 1)` | Accept | Level entry used in a level. |
| W9 | `Π (x : Uω). Nat` | Accept (large) | A level Π whose variable is unused is still large. |
| W10 | a definition whose value is `Π (x : Uω). U(x)` | Reject | A large type has no type to register it at (Q2). |
| W11 | source: `def u = Universe;`, `f(Universe)`, `next(Nat)`, `identity(Nat, …)` | Reject | `Universe` in an expression; a non-universe where a universe is required. |

### 5.3 Large types

| ID | Judgment | Verdict | Reason |
| --- | --- | --- | --- |
| G1 | `Π (x : Uω). U(x) → U(x)` as a definition's type | Accept | Large statement. |
| G2 | `(Π (x : Uω). U(x) → U(x)) : U(ℓ)` for any `ℓ` | Reject | Large types are in no universe. |
| G3 | `Path(Π (x : Uω). U(x) → U(x), f, g)` | Reject | Large Path family. |
| G4 | `Σ (f : Π (x : Uω). U(x) → U(x)). Nat` | Reject | Large Σ domain. |
| G5 | `Glue [φ ↦ (Π (x : Uω). U(x), e)] A`; Glue with a large base | Reject | Glue needs small types. |
| G6 | `comp^i (Π (x : Uω). U(x) → U(x)) [] f` | Reject | Large composition family. |
| G7 | `Truncate {0} (Π (x : Uω). U(x))` | Reject | The argument must be in `U(0)`. |
| G8 | `λ (f : Π (x : Uω). Π (A : U(x)). A → A). f {0} Nat zero` | Accept | Parameter of large type; its type is large. |
| G9 | `Π (n : Nat). Π (x : Uω). U(x)` | Accept (large) | Small domain, large codomain. |
| G10 | `NatRec` with motive `λ n. Π (x : Uω). U(x)` | Reject | A motive must land in a universe. |
| G11 | assumption `LEM : Π (x : Uω). Π (A : U(x)). …`; a large expected type | Accept | Large telescope entries and expected types. |
| G12 | the large Π `Π (f : Π (x : Uω). U(x) → U(x)). Nat`, checked against `U(ℓ)` | Reject | Large, not small. |

### 5.4 Cumulativity

| ID | Judgment | Verdict | Reason |
| --- | --- | --- | --- |
| C1 | `x : Uω ⊢ Nat : U(x)` | Accept | `0 ≤ x`. |
| C2 | `x, y : Uω ⊢ U(x) : U(max(x + 1, y))` | Accept | `x + 1 ≤ max(x + 1, y)`. |
| C3 | `x : Uω ⊢ U(x) : U(x)` | Reject | `x + 1 ≤ x` fails. |
| C4 | `x : Uω ⊢ U(x) : U(1)` | Reject | A universe variable used at a smaller universe. Fails at `x = 1`. |
| C5 | `x : Uω, A : U(x) ⊢ A : U(0)` | Reject | Downward lifting. |
| C6 | `x : Uω, A : U(x + 1) ⊢ A : U(x)` | Reject | Downward lifting. |
| C7 | `x, y : Uω, A : U(x) ⊢ A : U(max(x, y))` | Accept | `x ≤ max(x, y)`. |
| C8 | `x, y : Uω, A : U(max(x, y)) ⊢ A : U(x)` | Reject | `y` is missing on the right. |
| C9 | `x : Uω, A : U(max(1, x)) ⊢ A : U(x + 1)`; the converse | Accept; Reject | `(1,{x↦0}) ≤ (1,{x↦1})`, but not conversely. |
| C10 | `x : Uω, B : U(x) ⊢ λ (a : Nat). B : Nat → U(x + 1)` | Accept | `≤-Π` with a symbolic level. |
| C11 | `λ (x : Uω). Nat : Π (x : Uω). U(1)`, the reduct of `(λ (A : U(1)). λ (x : Uω). A) Nat` | Accept | New `≤-∀`: the reduct infers `Π (x : Uω). U(0)` and must keep the redex's type. |
| C12 | `λ (A : U(0)). A : U(1) → U(1)` | Reject | Domains must be convertible. |
| C13 | `Π (x : Uω). U(x) ≤ Π (y : Uω). U(y + 1)` | Accept | `≤-∀` under renaming. |
| C14 | `Π (x : Uω). U(x + 1) ≤ Π (y : Uω). U(y)` | Reject | No downward lifting under a level Π. |

### 5.5 Instantiation and substitution

Let `id := λ (x : Uω). λ (A : U(x)). λ (a : A). a`.

| ID | Judgment | Verdict | Reason |
| --- | --- | --- | --- |
| S1 | `id : Π (x : Uω). Π (A : U(x)). A → A`, registered once | Accept | One check covers every level. |
| S2 | `id {0} Nat 3 : Nat` reducing to `3`, and `id {1} U(0) Nat : U(0)` reducing to `Nat` | Accept | The same definition at two levels; both compute. |
| S3 | `id {0} U(0)` | Reject | `U(0) : U(1)`, not `U(0)`. |
| S4 | `x : Uω ⊢ id {x + 1} U(x) : U(x) → U(x)` | Accept | Symbolic instantiation. |
| S5 | `y : Uω ⊢ ((λ (x : Uω). λ (y : Uω). U(max(x, y))) {y}) {0} ≡ U(y)`, and `≢ U(0)` | Accept; Reject | Capture-avoiding: the inner binder is renamed. Without renaming the result would be `U(0)`. |
| S6 | level substitution under a term binder with the same symbol (C kernel) | Accept, renamed | One name supply; term binders are renamed too. |
| S7 | `f : Π (x : Uω). U(x) → U(x) ⊢ f ≡ λ (x : Uω). f {x}` | Accept | `∀-η`. |
| S8 | `(λ (x : Uω). U(x)) {2} ≡ U(2)` | Accept | `∀-β` at the type level. |
| S9 | `(λ (x : Uω). U(x + 65000)) {1000}` | Reject | The instantiated type exceeds `LEVEL_MAX`. |
| S10 | `λ (x : Uω). λ (g : U(1) → Nat). g U(x)` | Reject | `U(x) : U(1)` needs `x + 1 ≤ 1`. The body checks only at `x = 0`: the template case G0 must reject. |
| S11 | `d {0}` vs `d {max(0, 0)}` | Accept (convertible) | `Inst` compares levels by normal form. |

### 5.6 Cubical rules at variable levels

| ID | Judgment | Verdict | Reason |
| --- | --- | --- | --- |
| K1 | `ua` of 2.13 at type `Π (x : Uω). Π (A B : U(x)). Equiv(A, B) → Path(U(x), A, B)` | Accept | Glue at `max(x, x) = x`, checked once. |
| K2 | `x, y : Uω, A : U(x), T : U(y), e : Equiv(T, A) ⊢ Glue [φ ↦ (T, e)] A : U(max(x, y))`; the same at `U(x)` | Accept; Reject | Glue lives at the `max`. |
| K3 | `x : Uω, A : U(x), E` a line in `U(x)` with `E(0) ≡ A` on `φ` `⊢ comp^i U(x) [φ ↦ E(i)] A : U(x)` | Accept | Universe composition at a variable level. The Glue reduct also checks at `U(x)`. |
| K4 | transport of `inl(tt)` along `ua {0} Two Two swap` and along `ua {1} Two Two swap`, with `Two := Unit + Unit` | Accept; both reduce to `inr(tt)` | One definition, two levels, same value (Lemma 5). |
| K5 | `x : Uω, A : U(x), a : A ⊢ Path(A, a, a) : U(x)`; `Path(U(x), A, A) : U(x + 1)`; `Path(U(x), A, A) : U(x)` | Accept; Accept; Reject | Path lives in its family's universe. |
| K6 | `f : Π (x : Uω). Nat → Nat, i : I ⊢ comp^j Nat [i = 0 ↦ f {0} zero] (f {0} zero)` | Accept | Tubes may mention a variable of large type. |
| K7 | Kan operations with a large family (G3, G6) | Reject | No composition in large types. |

### 5.7 Definitions, assumptions and dependencies

| ID | Judgment | Verdict | Reason |
| --- | --- | --- | --- |
| D1 | telescope `[Truncate : Π (x : Uω). U(x) → U(0), LEM : Π (x : Uω). Π (A : U(x)). ((A → Void) → Void) → Truncate {x} A]` | Accept | Generic assumptions are single entries. |
| D2 | telescope `[x : Uω, A : U(x), a : A]` checking `a : A` | Accept | Level entries for open goals. |
| D3 | telescope `[x : Uω, x : Nat]` | Reject | Duplicate name. |
| D4 | `computable def` using `LEM(U0, …)`; one using `ua(U0, …)` | Reject; Accept | Dependencies are unchanged by genericity. |
| D5 | the dependencies of a result using `Choice` at `U0` and at `U1` | `Choice`, listed once | One name per generic assumption (Q4). |
| D6 | `evaluate` of a term with a free level variable | Reject | Not closed. |

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
    `apply_at_nat(f : forall U : Universe, forall A : U, A -> A) = f(U0, Nat, 5)`.
    This passes a generic definition as an argument (higher rank).
- The helpers `generic_identity`, `apply_at_nat`, `Two` and `swap` live in an
  imported support module, because the harness requires every fixture
  declaration to be an `rfl` statement.
- Add `evaluate winding(concatenate(U2, S1, base, base, base, loop, loop)) expecting nonnegative(2);`,
  and raise the harness's expected evaluation count.

The test normalizes each instantiated result and compares it with the stated
value. The values are canonical data, so by Lemma 5 this equals
instantiating the generic normal form. For the kernel-level twins S2 and K4,
K1.2's test also checks `nf(d {n} …) = nf(body)[x := n] …` directly.

### 5.9 Resources and malformed input (C kernel)

| ID | Input | Verdict | Reason |
| --- | --- | --- | --- |
| R1 | a chain of 10⁶ `CC_LSUCC` nodes | Reject, no crash | Recursion or step budget; sanitizers clean. |
| R2 | `CC_LMAX` with a term child; `CC_U` with no level; `CC_LPI` whose child 0 is not `CC_OMEGA`; `CC_OMEGA` as a term | Reject; inspection stays inert | Malformed raw syntax. |
| R3 | 1,000 nested level binders, with a level mentioning all of them | Accept within budget | Heap-allocated normal forms. |
| R4 | a WASM or CLI build with a mismatched ABI version | Refused | The encoding of `CC_U` changed. |
| R5 | a deep chain of definitions whose instantiations push an intermediate level past `LEVEL_MAX` during conversion | Reject, no overflow | Checked arithmetic. The rejection point may differ between checkers, as for step budgets. |

## 6. Open questions

**Q1. Level irrelevance for neutral type formers.** `Trunc {0} A` and
`Trunc {1} A` are distinct, non-convertible types for `A : U(0)`. The same
holds for assumptions such as `Truncate`. Generic code instantiated at `U1`
then meets values built at `U0`. Coq's cumulative inductive types make such
instances convertible when the level only bounds parameters.
*Recommendation:* not in G0. The elaborator should always pick the least
level, the principal level of the argument's inferred type, so one type
appears in practice. Revisit at H1 with the rebuild's evidence. The rule
would need its own soundness argument; it is plausible because the model of
a higher inductive type does not depend on the ambient universe.

**Q2. Named large types.** Should a definition's value be allowed to be a
large type, as in `def Endo := Π (x : Uω). U(x) → U(x)`? That needs a sort
for large types to register it at: not a term, but a new judgment for
definitions. *Recommendation:* no. Source-level abbreviations can be
expanded by the elaborator. Revisit if theory declarations need named large
types.

**Q3. Σ, Path and composition for large types.** The roadmap excludes them,
and consistency does not require the exclusion (3.3). *Recommendation:*
keep the exclusion. State facts about generic functions pointwise under a
level Π, and bundle theories at a fixed universe variable, so that models
are small and live in `next(U)`.

**Q4. How dependencies name generic assumptions.** Should the dependency
list say `LEM` or `LEM(U0)`? *Recommendation:* the name only, since it is
one assumption. The inspector lists the level arguments at each use. The
error texts quoted in the reference change accordingly.

**Q5. Truncation between G0 and H1.** Should the generic `Truncate` keep the
archive's resizing signature `Π (x : Uω). U(x) → U(0)`, or become
universe-preserving now? *Recommendation:* keep the archive signature, so
that the archive recheck tests G0 alone and changes no statement. H1 and
G2's policy then replace it with `Trunc : Π (x : Uω). U(x) → U(x)`.

**Q6. Levels in H signatures.** Should parameter types count toward a sort's
level, and are large indices or large parameters allowed?
*Recommendation:*

- a sort's level is the `max` of its data, arity and index types;
- index types must be small, and they count;
- no parameter may have a large type.

This makes `Trunc` universe-preserving, as the kernel roadmap states. The H
design's sentence "the maximum of the levels of its indices, data, arities
and parameters" should drop "parameters" when H is next edited. Read
literally, it puts `Trunc(A)` in `next(U)`.

**Q7. Level constraints.** Should declarations be able to state constraints
such as `x < y`, as Coq allows? *Recommendation:* no. Unconstrained
variables with `max` and successor express every signature we know of, as
in `Group(U) : next(U)` and quotients at `max(U, V)`. Constraints would
bring in the Bezem–Coquand constraint problem and its loop checking.

**Q8. Where universe parameters may appear in source.** The kernel allows a
level binder anywhere in a telescope. *Recommendation:* in L1.1, keep
universe parameters leading in declarations, as templates require today.
Allow `forall U : Universe` anywhere in types, so that higher-rank
parameters can be written. With milestone 5, let an unbound universe name
in a declaration header become an implicit leading universe parameter, as
the H design's examples assume. The inspector shows it.

**Q9. The level bound.** `LEVEL_MAX = 65535` rejects universes the current
kernel accepts, such as `U(70000)`; today's native limit is about 2³².
*Recommendation:* accept the smaller bound. It simplifies overflow reasoning
in the C kernel, and no mathematics uses such levels.
