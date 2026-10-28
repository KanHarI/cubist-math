# Reading the cubical kernel, AST primitives, and instruction reference

The kernel checks a judgement $\Gamma; \Delta; \varphi \vdash t : A$. $\Gamma$ is an ordered telescope of typed
term and universe-level variables, $\Delta$ records interval coordinates, and $\varphi$ restricts the current cube to
a face. A successful instruction certifies the resulting judgement in the kernel's table. Allocating a
syntax node, printing a name, or requesting normalization computes on inert syntax and certifies nothing.

The browser and CLI use this C11 implementation (`kernel/`). JavaScript elaboration proposes
derivations, but cannot publish unchecked definitions in the native registry.

## Contents

1. [A reading route](#a-reading-route)
2. [Enough C to follow the rules](#enough-c-to-follow-the-rules)
3. [Arena handles and AST node layout](#arena-handles-and-ast-node-layout)
4. [Interval and face formula algebra](#interval-and-face-formula-algebra)
5. [Reference for every AST primitive (`cc_term_kind`)](#reference-for-every-ast-primitive-cc_term_kind)
   - [Universes and universe levels (G0)](#1-universes-and-universe-levels-g0)
   - [Variables and registered definitions](#2-variables-and-registered-definitions)
   - [Dependent functions ($\Pi$) and dependent pairs ($\Sigma$)](#3-dependent-functions-pi-and-dependent-pairs-sigma)
   - [Unit, Void, and disjoint sums](#4-unit-void-and-disjoint-sums)
   - [Paths, partial tubes, and cubical composition/transport](#5-paths-partial-tubes-and-cubical-compositiontransport)
   - [Glue types and terms](#6-glue-types-and-terms)
   - [Declared inductive and higher inductive types (H1)](#7-declared-inductive-and-higher-inductive-types-h1)
   - [Retired primitive tags](#8-retired-primitive-tags)
6. [Binder scopes, substitution, restriction, and comparison](#binder-scopes-substitution-restriction-and-comparison)
7. [Reference for every kernel instruction (`cc_instruction`)](#reference-for-every-kernel-instruction-cc_instruction)
   - [Context entries, judgements, and derivation sharing](#context-entries-judgements-and-derivation-sharing)
   - [1. Context entry constructors](#1-context-entry-constructors)
   - [2. Variables, endpoints, face restrictions, and definitions](#2-variables-endpoints-face-restrictions-and-definitions)
   - [3. Universes and universe-level quantification (G0)](#3-universes-and-universe-level-quantification-g0)
   - [4. Dependent functions ($\Pi$) and dependent pairs ($\Sigma$)](#4-dependent-functions-pi-and-dependent-pairs-sigma)
   - [5. Unit, Void, and disjoint sums](#5-unit-void-and-disjoint-sums)
   - [6. Paths and interval application](#6-paths-and-interval-application)
   - [7. Composition systems, `Comp`, `HComp`, and `Trans`](#7-composition-systems-comp-hcomp-and-trans)
   - [8. Glue types, Glue terms, and `Unglue`](#8-glue-types-glue-terms-and-unglue)
   - [9. Declared inductive and higher inductive types (H1)](#9-declared-inductive-and-higher-inductive-types-h1)
   - [10. Equality, conversion, cumulativity, $\eta$, `Step`, and `Replace`](#10-equality-conversion-cumulativity-eta-step-and-replace)
   - [11. Retired instruction opcodes](#11-retired-instruction-opcodes)
8. [Reduction, normalization, and elimination](#reduction-normalization-and-elimination)
9. [Cubical composition, transport, and filling computation](#cubical-composition-transport-and-filling-computation)
10. [Definitions, inspection, verification, and limits](#definitions-inspection-verification-and-limits)

---

## A reading route

1. [instructions.c](../../kernel/src/instructions.c) checks explicit typing premises for contexts, universes, functions, pairs, sums, and definition admission.
2. [instruction_paths.c](../../kernel/src/instruction_paths.c) checks paths, their boundaries, and composition (`Comp`, `HComp`, `Trans`) built one tube at a time.
3. [instruction_glue.c](../../kernel/src/instruction_glue.c) checks gluing data and equivalences through explicit piece-by-piece instructions.
4. [instruction_equality.c](../../kernel/src/instruction_equality.c) checks equality, conversion, universe lifting, $\eta$-expansion, and targeted `Step` and `Replace` rules.
5. [signatures.c](../../kernel/src/signatures.c) and [eliminators.c](../../kernel/src/eliminators.c) admit declared inductive and higher inductive types (H1), check sort instances and constructors, and check and compute dependent elimination.
6. [term_conversion.c](../../kernel/src/term_conversion.c) and [levels.c](../../kernel/src/levels.c) supply syntactic $\alpha$-equivalence modulo the interval/face algebra, universe-level normal forms, and syntactic cumulativity.
7. [term_substitution.c](../../kernel/src/term_substitution.c) handles capture-avoiding term substitution, dimension substitution, and face restriction.
8. [term_normalize.c](../../kernel/src/term_normalize.c) and [term_expose.c](../../kernel/src/term_expose.c) implement call-by-name weak-head reduction (`ck_whnf`), full normalization (`ck_normal`), the folded normal form that keeps a definition whose weak head is no data as written (`ck_normal_folded`), and compact single-step head exposure (`ck_expose`).
9. [composition_compute.c](../../kernel/src/composition_compute.c), [inductive_composition.c](../../kernel/src/inductive_composition.c), [hit_composition.c](../../kernel/src/hit_composition.c), [glue_compute.c](../../kernel/src/glue_compute.c), and [equivalence_terms.c](../../kernel/src/equivalence_terms.c) compute composition, homogeneous composition, transport, and derived filling across each type former.

The untrusted [instruction driver](../../web/cubical-instruction-driver.mjs)
chooses the derivation; each native instruction validates its own premises.
The [instruction-kernel contract](../roadmaps/kernel/kernel-instructions.md)
explains the trust boundary, and the [kernel overview](../../kernel/README.md)
maps every source file and caching invariant to its mathematical responsibility.

---

## Enough C to follow the rules

| C notation | Mathematical reading |
|---|---|
| `cc_term` | A 1-based `uint32_t` handle to an immutable syntax node in one kernel arena (`0` means absent/error) |
| `n.kind` | The node's constructor (`cc_term_kind`) |
| `n.payload` | A constructor-specific `uint32_t` parameter (variable symbol, dimension index, formula ID, definition/signature/constructor index, or level constant) |
| `n.child[0..3]` | Up to four child term handles (`a, b, c, d`); indexing starts at zero |
| `k->...` | A field of the kernel arena state (`cc_kernel`) |
| `a == b` | Equal handles (identical shared syntax node), stronger than $\alpha$-equivalence or definitional equality |
| `a && b`, `a \|\| b`, `!a` | Logical and, or, not |
| `return false` / `return 0` | Reject the proposed check or abort a computation |

---

## Arena handles and AST node layout

All AST terms live in a table `k->nodes` inside a `cc_kernel` arena ([term_internal.h](../../kernel/src/term_internal.h), [term_store.c](../../kernel/src/term_store.c)), append-only between checkpoints: `cc_kernel_rollback` truncates it to the checkpoint, and `cc_kernel_commit_checkpoint` compacts the nodes made since it, so that their handles change and must be translated with `cc_kernel_relocated` ([checkpoint.c](../../kernel/src/checkpoint.c)). Both also truncate the derivation tables of the [instruction reference](#context-entries-judgements-and-derivation-sharing) and clear the reduction caches:

```c
typedef struct {
    cc_term_kind kind;
    uint32_t payload;
    cc_term child[4];
    unsigned depth;
    bool dimensions_known;
    uint64_t symbols;
    uint64_t dims;
} cc_node;
```

- **Handles (`cc_term`):** Node `0` is the null/absent sentinel. Valid handles run from `1` to `k->count - 1`; a handle made after a checkpoint is valid until the next rollback or commit.
- **Structural sharing (`CC_SHARE_SYNTAX`):** When syntax sharing is enabled (the default), `ck_make` hash-conses `(kind, payload, child[0..3])` in the `k->interned` table so structurally identical AST nodes share a single `cc_term` handle.
- **Depth bound:** Every node records `depth = 1 + max_i(child[i].depth)`. Any construction exceeding depth `512` (a literal in `ck_make`; there is no named constant) fails with `CC_ERROR_RESOURCE`.
- **Fast dependency bitmasks:**
  - `symbols` is a 64-bit Bloom filter over the symbols of the `CC_VAR` nodes in a term, term and level variables alike (`1ULL << (s % 64)`), unioned upward from children; a binder's own name is recorded only where a variable with that name occurs under it. If a symbol's bit is clear in `n.symbols`, no variable with that symbol occurs in `n` (bound or free), allowing substitution and comparison to skip subtrees in $O(1)$ time.
  - `dims` is a 64-bit mask over the 64 interval dimensions (`0..63`). Initially it conservatively unions the dimensions of the node's formula payload, its own bound dimension if it is a dimension binder, and its children's masks; once `ck_free_dims` completes on a node, `dimensions_known` is set to `1` and `dims` holds the exact bitset of free dimensions.

---

## Interval and face formula algebra

Interval expressions and face constraints are interned in `k->formulas` and referenced by `cc_formula_id` ([cubical.h](../../kernel/include/cubical.h), [formula.c](../../kernel/src/formula.c), [interval.c](../../kernel/src/interval.c), [faces.c](../../kernel/src/faces.c)). Both sorts share the same canonical disjunctive normal form (DNF) representation—an antichain of `cc_clause` structs, kept in insertion order, compared as sets (`cc_equal`), and reduced by absorption—but their generators obey different algebraic laws:

```c
typedef struct {
    uint64_t positive;
    uint64_t negative;
} cc_clause;
```

| Sort | Meaning of bit $i$ in `positive` | Meaning of bit $i$ in `negative` | Opposite bits in one clause |
|---|---|---|---|
| `CC_INTERVAL` | Coordinate $i$ | Reversed coordinate $1 - i$ | Allowed: $i \wedge (1 - i)$ is a valid interior meet |
| `CC_FACE` | Endpoint equation $(i = 1)$ | Endpoint equation $(i = 0)$ | Impossible: $(i = 1) \wedge (i = 0) = \bot$ (clause is dropped) |

- **Constants:** The empty clause list (`length == 0`) is $\bot$ (`0`). A single clause with `positive == 0` and `negative == 0` is $\top$ (`1`). Neither has a fixed `cc_formula_id`: `ck_formula` assigns IDs in registration order from `1`, and ID `0` names no formula (`cc_kernel_get_formula` returns `NULL`, and `ck_make` rejects a `CC_PAPP`, `CC_TUBE`, or `CC_GLUE_SYSTEM` whose payload is `0`).
- **Lattice operations (`formula.c`):**
  - `cc_join(a, b)` ($a \vee b$) concatenates clauses and removes any clause $C'$ that contains another clause $C$ ($C \subseteq C' \implies C \vee C' = C$).
  - `cc_meet(a, b)` ($a \wedge b$) takes pairwise bitset unions of clauses (filtering out contradictory clauses when `sort == CC_FACE`) and applies absorption.
- **Interval operations (`interval.c`):**
  - `cc_reverse(out, r)` ($1 - r$) applies De Morgan duality by swapping meets and joins and swapping `positive` and `negative` bitsets.
  - `cc_interval_substitute(out, target, i, replacement)` computes $r[s/i]$ by replacing occurrences of $i$ in each clause with $s$ and occurrences of $1 - i$ with `cc_reverse(s)`.
- **Face operations (`faces.c`):**
  - `cc_endpoint(out, r, endpoint)` converts an interval formula $r$ into the face formula $(r = 1)$ or $(r = 0)$ using De Morgan distribution over joins and meets.
  - `cc_face_substitute(out, phi, i, r)` computes $\varphi[r/i]$ by replacing $(i = 1)$ with $(r = 1)$ and $(i = 0)$ with $(r = 0)$, both computed by `cc_endpoint`.
  - `cc_face_forall(i, phi)` computes universal quantification $\forall i.\, \varphi$ by keeping only the clauses of $\varphi$ in which neither $(i = 1)$ nor $(i = 0)$ occurs.
  - `cc_face_entails(psi, phi)` ($\psi \vdash \varphi$) holds iff for every clause $C_\psi \in \psi$, there exists a clause $C_\varphi \in \varphi$ with $C_\varphi \subseteq C_\psi$.

---

## Reference for every AST primitive (`cc_term_kind`)

Every AST node is constructed via `cc_kernel_term(k, kind, payload, a, b, c, d)` (`ck_make` in [term_store.c](../../kernel/src/term_store.c)). Below is the complete specification of every `cc_term_kind` constant in [cubical_kernel.h](../../kernel/include/cubical_kernel.h) (ABI version `3`).

Every **Composition** bullet below describes `ck_reduce_composition` ([composition_compute.c](../../kernel/src/composition_compute.c)) after its first rule, which precedes the dispatch on the family and holds for every type former: a tube on the face `1` makes `comp^i A(i) [1 ↦ u(i), …] a0` the weak head of $u(1)$ (`ck_whnf` of `ck_endpoint_term(k, u, i, 1)`), whatever `a0` and the family are. The bullets state what happens when no tube has that face.

### 1. Universes and universe levels (G0)

Universe levels denote ordinals $\omega \cdot \text{tier} + n < \omega^2$ built from constants, finite successors, binary maxima, and level variables bounded below $\omega$ ([levels.c](../../kernel/src/levels.c)). Levels are not standalone typed terms; they appear inside `CC_U`, `CC_LAPP`, and H1 `CC_SORT` level lists.

#### `CC_U` (`1`) — Universe type $\mathcal{U}(\ell)$
- **Arity:** `1` (`payload == 0`, `child[0] = level`, `child[1..3] == 0`).
- **Role:** Represents the universe type $\mathcal{U}(\ell)$ at level expression `child[0]`.
- **Instructions:** Formed by `cc_instr_universe(k, level)`, which normalizes `level` to canonical level syntax $\ell$ and certifies $\Gamma \vdash \mathcal{U}(\ell) : \mathcal{U}(\ell + 1)$.
- **Reduction & Cumulativity:** `ck_whnf` and `ck_normal` leave `CC_U(l)` as written; neither rewrites `child[0]`. Levels are put into canonical syntax by the instructions that build universes and levels (`cc_instr_universe`; `ck_level_max` in `Pi`, `Sigma`, `Sum`, and `GluePiece`; `ck_level_limit` in `LevelPi`; `cc_instr_level_apply` and `ck_level_instantiate`; `ck_instr_level` for a sort instance) and are compared by normal form in `ck_alpha_equal`. Under `cc_instr_lift`, $\mathcal{U}(\ell_1) \preceq \mathcal{U}(\ell_2)$ iff $\ell_1 \le \ell_2$ in level normal form (`ck_level_leq`).
- **Composition:** `comp^i U(l) [φ ↦ E(i)] A` reduces via `ck_universe_composition` to `Glue [φ ↦ (E(1), comp^i Equiv(E(1), E(1-i)) [] idEquiv(E(1)))] A`.

#### `CC_LBOUND` (`43`) — Level variable bound $\text{LBound}(\text{tier})$
- **Arity:** `0` (`payload = tier > 0`, `child[0..3] == 0`).
- **Role:** Binder domain marker representing the ordinal bound $\omega \cdot \text{tier}$ for a universe-level variable. Only `tier == 1` ($\ell < \omega$) occurs in checked syntax: `cc_instr_level` gives every level entry the type `CC_LBOUND(1)`, `cc_instr_signature_begin` refuses a universe parameter whose bound is any other node, and `ck_level_normal` rejects a bound where a level is expected (`"A bound is not a level."`). Stored as `child[0]` of `CC_LPI` and `CC_LLAM` and as `entry.type` of a level context entry.

#### `CC_LCONST` (`44`) — Constant universe level $\omega \cdot \text{tier} + n$
- **Arity:** `0` (`payload = (tier << 16) | n`, `child[0..3] == 0`).
- **Role:** Constant universe level with `tier = payload >> 16` ($\le \text{CC\_TIER\_MAX} = 255$) and finite offset $n = \text{payload} \mathbin{\&} \text{0xffff}$ ($\le \text{CC\_LEVEL\_MAX} = 65535$). For example, $\mathcal{U}_n$ has level `CC_LCONST` with `payload = n`, and $\mathcal{U}_\omega$ (`UU0`) has `payload = (1 << 16) | 0`.

#### `CC_LSUCC` (`45`) — Shifted universe level $\ell + k$
- **Arity:** `1` (`payload = k >= 1`, `child[0] = level`, `child[1..3] == 0`).
- **Role:** Adds a positive finite offset $k \ge 1$ to `child[0]`. Rejected if `payload == 0`. In arithmetic normal form (`ck_level_normal`), shifting a finite level increments both the constant floor $c$ and every variable offset $k_i$ by $k$; shifting a transfinite level ($\text{tier} \ge 1$) increments its constant part $c$ by $k$. Either case fails with `CC_ERROR_RESOURCE` when the new constant, or the total count of a chain of `CC_LSUCC` nodes, exceeds `CC_LEVEL_MAX`.

#### `CC_LMAX` (`46`) — Universe level maximum $\max(\ell_1, \ell_2)$
- **Arity:** `2` (`payload == 0`, `child[0] = left`, `child[1] = right`, `child[2..3] == 0`).
- **Role:** Binary supremum of two universe levels. In arithmetic normal form (`ck_level_normal`), every level expression reduces to either:
  - a **finite form** $(\text{tier} = 0,\; c,\; [(x_1, k_1), \dots, (x_m, k_m)])$ with strictly increasing symbols $x_1 < \dots < x_m$ and $k_i \le c$, denoting $\max(c, \max_i(x_i + k_i))$; or
  - a **transfinite form** $(\text{tier} \ge 1,\; c,\; [])$ denoting $\omega \cdot \text{tier} + c$, which absorbs all finite level variables ($x_i + k_i < \omega \le \omega \cdot \text{tier} + c$).
  Canonical syntax (`ck_level_build`) nests `CC_LMAX` right-associatively in symbol order, followed by `CC_LCONST(0, c)` when $c > \max_i(k_i)$ or $m = 0$.

#### `CC_LPI` (`47`) — Universe-polymorphic function type $\forall(x < \omega).\, B(x)$
- **Arity:** `2` (`payload = symbol != 0`, `child[0] = CC_LBOUND(1)`, `child[1] = codomain`, `child[2..3] == 0`).
- **Binder scope:** Binds the level variable `symbol` in `child[1]` (`ck_term_binder(CC_LPI) == true`).
- **Instructions:** Formed by `cc_instr_level_pi(k, entry, body)`, which discharges the level entry $x < \omega$ from `body` ($\Gamma, x < \omega \vdash B : \mathcal{U}(\ell)$) and places the resulting type in $\mathcal{U}(\lim_x(\ell))$, where $\lim_x(\ell) = \omega$ (`CC_LCONST(1 << 16)`) if $x$ occurs in $\text{nf}(\ell)$ and $\ell$ otherwise.
- **Cumulativity & Composition:** Covariant in `child[1]` under `ck_syntactic_cumulative`. Heterogeneous composition in `CC_LPI` reduces pointwise: `comp^i (∀(y < ω). G(i, y)) [φ ↦ u(i)] a0` $\longrightarrow \Lambda(y < \omega).\, \text{comp}^i\, G(i, y)\, [\varphi \mapsto u(i)\,\{y\}]\, (a_0\,\{y\})$.

#### `CC_LLAM` (`48`) — Universe-level abstraction $\Lambda(x < \omega).\, b(x)$
- **Arity:** `2` (`payload = symbol != 0`, `child[0] = CC_LBOUND(1)`, `child[1] = body`, `child[2..3] == 0`).
- **Binder scope:** Binds the level variable `symbol` in `child[1]`.
- **Instructions:** Introduced by `cc_instr_level_lambda(k, entry, body)`, producing $\Gamma \vdash \Lambda(x < \omega).\, b : \forall(x < \omega).\, B$.
- **Reduction ($\eta$):** In `ck_whnf`, `LLam(x, B, LApp(f, Var(x)))` contracts to $f$ when $x \notin \text{fv}(f)$. Conversely, `cc_instr_eta` expands $f : \forall(x < \omega).\, B(x)$ to $\Lambda(x < \omega).\, f\,\{x\}$.

#### `CC_LAPP` (`49`) — Universe-level application $f\,\{\ell\}$
- **Arity:** `2` (`payload == 0`, `child[0] = function`, `child[1] = level`, `child[2..3] == 0`).
- **Instructions:** Eliminated by `cc_instr_level_apply(k, function, level)` for a finite level $\ell < \omega$ (`nf.tier == 0`), storing $\text{nf}(\ell)$ in `child[1]` and instantiating the codomain via `ck_level_instantiate`.
- **Reduction ($\beta$):** `LApp(LLam(x, B, body), l)` contracts via `ck_level_instantiate(k, body, x, l)` under `Step(CC_STEP_BETA)`, `ck_whnf`, and `ck_normal` (`ck_expose` does not contract level applications).

---

### 2. Variables and registered definitions

#### `CC_VAR` (`2`) — Variable $x$
- **Arity:** `0` (`payload = symbol != 0`, `child[0..3] == 0`).
- **Role:** Represents either a term variable $x : A$ or a universe-level variable $x < \omega$, distinguished by its context entry (`entry.level_variable`).
- **Instructions:** `cc_instr_variable(k, entry)` certifies $\Gamma, x : A \vdash x : A$ for a term variable entry (and rejects level or dimension entries).
- **Substitution & Reduction:** Replaced by `ck_substitute` (or `ck_level_instantiate` inside levels) when `payload == symbol`. Irreducible in WHNF and normal form.

#### `CC_DEFREF` (`35`) — Admitted closed definition reference
- **Arity:** `0` (`payload = def_index` in `1 .. k->definition_count - 1`, `child[0..3] == 0`).
- **Role:** Folded handle to a checked, closed definition stored in `k->definitions[def_index]`.
- **Trust boundary:** Raw syntax construction (`cc_kernel_term`) accepts a `CC_DEFREF` node like any other inert syntax, and it certifies nothing. Only `cc_instr_define(k, symbol, closed)` publishes the judgement that mints a reference, and `cc_instr_lookup(k, reference)` publishes one only after checking `1 <= payload < k->definition_count`. Reducing a `CC_DEFREF` whose payload names no definition fails with `"Unknown definition reached reduction."`.
- **Reduction ($\delta$):** Kept folded by syntactic comparison (`ck_alpha_equal`) and compact head exposure (`ck_expose`). Unfolded to `k->definitions[payload].value` by `Step(CC_STEP_DELTA)`, `ck_whnf`, and `ck_normal`. `ck_normal_folded` keeps an application or projection of it as written inside the term asked for when its weak head is no data.

---

### 3. Dependent functions ($\Pi$) and dependent pairs ($\Sigma$)

#### `CC_PI` (`3`) — Dependent function type $\Pi(x : A).\, B(x)$
- **Arity:** `2` (`payload = symbol != 0`, `child[0] = domain` $A$, `child[1] = codomain` $B$, `child[2..3] == 0`).
- **Binder scope:** Binds `symbol` in `child[1]`.
- **Instructions:** Formed by `cc_instr_pi(k, entry, codomain)`, producing $\Gamma \vdash \Pi(x : A).\, B : \mathcal{U}(\max(\ell_A, \ell_B))$. Its parts can be projected by `cc_instr_domain` ($A : \mathcal{U}(\ell)$) and `cc_instr_family` ($B[a/x] : \mathcal{U}(\ell)$).
- **Cumulativity & Composition:** Invariant in `child[0]` ($A_1 \equiv_\alpha A_2$) and covariant in `child[1]` ($B_1(x) \preceq B_2(x)$) under `ck_syntactic_cumulative`. Composition `comp^i (Π(y : F(i)). G(i, y)) [φ ↦ u(i)] a0` fills backward from $x : F(1)$ along $1 - i$ (`v(i) = fill^i F(1-i) [] x (1-i)`) and returns $\lambda(x : F(1)).\, \text{comp}^i\, G(i, v(i))\, [\varphi \mapsto u(i)(v(i))]\, (a_0(v(0)))$.

#### `CC_LAM` (`4`) — Lambda abstraction $\lambda(x : A).\, b(x)$
- **Arity:** `2` (`payload = symbol != 0`, `child[0] = domain` $A$, `child[1] = body` $b$, `child[2..3] == 0`).
- **Binder scope:** Binds `symbol` in `child[1]`.
- **Instructions:** Introduced by `cc_instr_lambda(k, entry, body)`, producing $\Gamma \vdash \lambda(x : A).\, b : \Pi(x : A).\, B$.
- **Reduction ($\eta$):** In `ck_whnf`, `Lam(x, A, App(f, Var(x)))` contracts to $f$ when $x \notin \text{fv}(f)$. Conversely, `cc_instr_eta` expands $f : \Pi(x : A).\, B(x)$ to $\lambda(x : A).\, f(x)$.

#### `CC_APP` (`5`) — Application $f(a)$
- **Arity:** `2` (`payload == 0`, `child[0] = function` $f$, `child[1] = argument` $a$, `child[2..3] == 0`).
- **Role:** Applies a function, an H1 constructor spine (`CC_CON`), or an H1 eliminator (`CC_ELIM`) to a term argument.
- **Instructions:** Built by `cc_instr_apply(k, function, argument)`, which checks $f : \Pi(x : A).\, B$ and $a : A$ and produces $\Gamma \vdash f(a) : B[a/x]$.
- **Reduction ($\beta$ and H1 $\iota$):**
  - When `child[0]` is `CC_LAM(x, A, body)`, reduces to `ck_substitute(k, body, x, a)` under `Step(CC_STEP_BETA)`, `ck_expose`, `ck_whnf`, and `ck_normal`.
  - When `child[0]` is `CC_ELIM(sig, M, clauses)`, reduces via `ck_eliminate` under `Step(CC_STEP_IOTA)` (when `a` is already a constructor spine) and under `ck_whnf` / `ck_normal` (when `whnf(a)` is a constructor spine or an `hcomp`).

#### `CC_SIGMA` (`6`) — Dependent pair type $\Sigma(x : A).\, B(x)$
- **Arity:** `2` (`payload = symbol != 0`, `child[0] = domain` $A$, `child[1] = family` $B$, `child[2..3] == 0`).
- **Binder scope:** Binds `symbol` in `child[1]`.
- **Instructions:** Formed by `cc_instr_sigma(k, entry, family)`, producing $\Gamma \vdash \Sigma(x : A).\, B : \mathcal{U}(\max(\ell_A, \ell_B))$. Its parts can also be extracted via `cc_instr_domain` and `cc_instr_family`.
- **Cumulativity & Composition:** Under `ck_syntactic_cumulative`, invariant in `child[0]` ($A_1 \equiv_\alpha A_2$) and covariant in `child[1]` ($B_1(x) \preceq B_2(x)$), exactly as for `CC_PI`. Composition `comp^i (Σ(x : F(i)). G(i, x)) [φ ↦ u(i)] a0` composes the first projection $c_1 = \text{comp}^i\, F(i)\, [\varphi \mapsto \pi_1(u(i))]\, \pi_1(a_0)$, fills $v(i) = \text{fill}^i\, F(i)\, [\varphi \mapsto \pi_1(u(i))]\, \pi_1(a_0)\, i$, composes the second projection $c_2 = \text{comp}^i\, G(i, v(i))\, [\varphi \mapsto \pi_2(u(i))]\, \pi_2(a_0)$, and returns `Pair(Sigma(1), c1, c2)`.

#### `CC_PAIR` (`7`) — Dependent pair $(a, b)_{\Sigma(x:A).B(x)}$
- **Arity:** `3` (`payload == 0`, `child[0] = sigma_type`, `child[1] = first` $a$, `child[2] = second` $b$, `child[3] == 0`).
- **Instructions:** Introduced by `cc_instr_pair(k, type, first, second)`, checking $a : A$ and $b : B[a/x]$ for `type` $= \Sigma(x : A).\, B$.
- **Reduction ($\eta$):** In `ck_whnf`, `Pair(T, Fst(p), Snd(p'))` contracts to $p$ when `ck_alpha_equal(k, p, p')`. Conversely, `cc_instr_eta` expands $p : \Sigma(x : A).\, B(x)$ to `Pair(T, Fst(p), Snd(p))`.

#### `CC_FST` (`8`) and `CC_SND` (`9`) — First and second projections $\pi_1(p), \pi_2(p)$
- **Arity:** `1` (`payload == 0`, `child[0] = pair` $p$, `child[1..3] == 0`).
- **Instructions:** Eliminated by `cc_instr_first(k, pair)` ($\pi_1(p) : A$) and `cc_instr_second(k, pair)` ($\pi_2(p) : B[\pi_1(p)/x]$).
- **Reduction ($\iota$):** When `child[0]` (or its WHNF in `ck_whnf` / `ck_normal`) is `CC_PAIR(T, a, b)`, `CC_FST` contracts to `a` and `CC_SND` contracts to `b` under `Step(CC_STEP_IOTA)`, `ck_expose`, `ck_whnf`, and `ck_normal`.

---

### 4. Unit, Void, and disjoint sums

#### `CC_UNIT` (`14`) — Unit type $\mathbf{1}$
- **Arity:** `0` (`payload == 0`, `child[0..3] == 0`).
- **Instructions:** Formed by `cc_instr_unit(k)`, certifying $\vdash \mathbf{1} : \mathcal{U}_0$.
- **Composition:** When no tube has face `1` (that case comes first in `ck_reduce_composition`, for every family), `comp^i Unit [φ ↦ u(i)] a0` reduces to `CC_POINT` ($\star$) when `whnf(a0)` and the WHNF of every non-empty tube body $u(i)$ is `CC_POINT`; otherwise it remains neutral.

#### `CC_POINT` (`15`) — Unit inhabitant $\star$
- **Arity:** `0` (`payload == 0`, `child[0..3] == 0`).
- **Instructions:** Introduced by `cc_instr_point(k)`, certifying $\vdash \star : \mathbf{1}$.

#### `CC_UNITREC` (`30`) — Dependent unit recursor $\text{unitrec}(M, pt, u)$
- **Arity:** `3` (`payload == 0`, `child[0] = motive` $M$, `child[1] = point_case` $pt$, `child[2] = value` $u$, `child[3] == 0`).
- **Instructions:** Built by `cc_instr_unit_elim(k, motive, point, value)` from $M : \Pi(x : \mathbf{1}).\, \mathcal{U}(\ell)$, $pt : M(\star)$, and $u : \mathbf{1}$, producing $\text{unitrec}(M, pt, u) : M(u)$.
- **Reduction ($\iota$):** Contracts to `child[1]` ($pt$) when `child[2]` is `CC_POINT` (under `Step(CC_STEP_IOTA)`) or when `whnf(child[2]) == CC_POINT` (under `ck_whnf` and `ck_normal`).

#### `CC_VOID` (`21`) — Empty type $\mathbf{0}$
- **Arity:** `0` (`payload == 0`, `child[0..3] == 0`).
- **Instructions:** Formed by `cc_instr_void(k)`, certifying $\vdash \mathbf{0} : \mathcal{U}_0$. `CC_VOID` has no introduction rule, and composition over `CC_VOID` remains neutral unless a tube has top face `1`.

#### `CC_ABORT` (`22`) — Empty-type eliminator $\text{abort}_T(e)$
- **Arity:** `2` (`payload == 0`, `child[0] = target_type` $T$, `child[1] = impossible` $e$, `child[2..3] == 0`).
- **Instructions:** Eliminated by `cc_instr_abort(k, type, impossible)` from $T : \mathcal{U}(\ell)$ and $e : \mathbf{0}$, certifying $\text{abort}_T(e) : T$. Because $\mathbf{0}$ has no closed canonical inhabitants, `CC_ABORT` has no $\iota$-reduction rule.

#### `CC_SUM` (`26`) — Disjoint sum type $A + B$
- **Arity:** `2` (`payload == 0`, `child[0] = left_type` $A$, `child[1] = right_type` $B$, `child[2..3] == 0`).
- **Instructions:** Formed by `cc_instr_sum(k, left, right)`, certifying $\Gamma \vdash A + B : \mathcal{U}(\max(\ell_A, \ell_B))$.
- **Cumulativity & Composition:** `ck_syntactic_cumulative` has no rule for sums: $A_1 + B_1 \preceq A_2 + B_2$ only when the two types are $\alpha$-equal. In `ck_inductive_composition` ([inductive_composition.c](../../kernel/src/inductive_composition.c)), `comp^i (A(i) + B(i)) [φ ↦ u(i)] a0` reduces `a0` and every active tube body $u(i)$ to WHNF: if all are `CC_INL(_, v)` (or all are `CC_INR(_, v)`), it reduces to `Inl(A(1) + B(1), comp^i A(i) [φ ↦ v(i)] v0)` (or `Inr(A(1) + B(1), comp^i B(i) [φ ↦ v(i)] v0)`). If any head is neutral or tubes disagree on the constructor tag, the composition remains neutral (unless a tube has face `1`, which `ck_reduce_composition` takes first).

#### `CC_INL` (`27`) and `CC_INR` (`28`) — Left and right sum injections $\text{inl}_{A+B}(a), \text{inr}_{A+B}(b)$
- **Arity:** `2` (`payload == 0`, `child[0] = sum_type` $A + B$, `child[1] = value`, `child[2..3] == 0`).
- **Instructions:** Introduced by `cc_instr_inject(k, type, value, right)` (`right == false` builds `CC_INL`; `right == true` builds `CC_INR`).

#### `CC_SUMREC` (`29`) — Dependent sum recursor $\text{sumrec}(M, l, r, s)$
- **Arity:** `4` (`payload == 0`, `child[0] = motive` $M$, `child[1] = left_fn` $l$, `child[2] = right_fn` $r$, `child[3] = scrutinee` $s$).
- **Instructions:** Eliminated by `cc_instr_sum_elim(k, motive, left, right, value)` from $M : \Pi(z : A + B).\, \mathcal{U}(\ell)$, $l : \Pi(x : A).\, M(\text{inl}_{A+B}(x))$, $r : \Pi(y : B).\, M(\text{inr}_{A+B}(y))$, and $s : A + B$, producing $\text{sumrec}(M, l, r, s) : M(s)$.
- **Reduction ($\iota$):** When `child[3]` (or `whnf(child[3])` in `ck_whnf` / `ck_normal`) is `CC_INL(_, v)`, reduces to `App(l, v)`; when it is `CC_INR(_, v)`, reduces to `App(r, v)`.

---

### 5. Paths, partial tubes, and cubical composition/transport

#### `CC_PATH` (`16`) — Dependent path type $\text{Path}_i(A(i), a_0, a_1)$
- **Arity:** `3` (`payload = dim < 64`, `child[0] = family` $A(i)$, `child[1] = left` $a_0$, `child[2] = right` $a_1$, `child[3] == 0`).
- **Binder scope:** Binds interval dimension `dim` ($i$) in `child[0]` ($A(i)$) **only**; `child[1]` and `child[2]` are outside the scope of $i$.
- **Instructions:** Formed by `cc_instr_path(k, dimension, family, left, right)`, checking $A(i) : \mathcal{U}(\ell)$, $a_0 : A(0)$, and $a_1 : A(1)$, discharging $i$ from $A(i)$'s context, and certifying $\text{Path}_i(A(i), a_0, a_1) : \mathcal{U}(\ell)$.
- **Cumulativity & Composition:** `ck_syntactic_cumulative` has no rule for path types: two path types are included only when $\alpha$-equal. Composition `comp^i (Path_j(P(i, j), l(i), r(i))) [φ ↦ u(i)] a0` picks a fresh dimension $k \ne i$ and reduces to $\langle k \rangle\, \text{comp}^i\, P(i, k)\, [\varphi \mapsto u(i) \mathbin{@} k,\; (k = 0) \mapsto l(i),\; (k = 1) \mapsto r(i)]\, (a_0 \mathbin{@} k)$.

#### `CC_PLAM` (`17`) — Path abstraction $\langle i \rangle_{A(i)}\, b(i)$
- **Arity:** `2` (`payload = dim < 64`, `child[0] = family` $A(i)$, `child[1] = body` $b(i)$, `child[2..3] == 0`).
- **Binder scope:** Binds interval dimension `dim` ($i$) in **both** `child[0]` and `child[1]`.
- **Instructions:** Introduced by `cc_instr_path_lambda(k, dimension, body)` from $\Gamma, i \vdash b(i) : A(i)$, discharging $i$ and certifying $\langle i \rangle_{A(i)}\, b(i) : \text{Path}_i(A(i), b(0), b(1))$.
- **Reduction ($\eta$):** In `ck_whnf`, `PLam(i, A, PApp(i, p, _))` contracts to $p$ when $i \notin \text{fdims}(p)$. Conversely, `cc_instr_eta` expands $p : \text{Path}_i(A(i), a_0, a_1)$ to $\langle k \rangle_{A(k)}\, (p \mathbin{@}_P k)$ for a fresh dimension $k$.

#### `CC_PAPP` (`18`) — Path application $p \mathbin{@}_P r$
- **Arity:** `2` (`payload = interval_formula_id` $r$ of sort `CC_INTERVAL`, `child[0] = path` $p$, `child[1] = path_type` (optional, `0` in raw unannotated syntax), `child[2..3] == 0`).
- **Role:** Evaluates a path $p$ (or a higher inductive path constructor spine) at an interval formula $r$. When built by `cc_instr_path_apply` or `cc_instr_path_at`, `child[1]` records $p$'s path type $\text{Path}_i(A(i), a_0, a_1)$ so endpoint reductions can read $a_0$ and $a_1$ even when $p$ is neutral.
- **Comparison:** `ck_alpha_equal` compares `payload` ($r$, modulo bound dimension renaming) and `child[0]` ($p$), ignoring the optional type annotation `child[1]`.
- **Reduction:**
  1. **Endpoint boundary** (`ck_expose`, `ck_whnf`, `ck_normal`): If $r = 0$ or $r = 1$ and `child[1]` is `CC_PATH(i, A, a0, a1)`, reduces immediately to `a0` (for $r = 0$) or `a1` (for $r = 1$), without reducing $p$.
  2. **Path $\beta$** (`ck_whnf` and `ck_normal`, when the WHNF of `child[0]` is `CC_PLAM(i, A, body)`): reduces to `ck_dimension_substitute(k, body, i, r)`. `ck_expose` does not contract a path application of a path lambda.
  3. **`Step(CC_STEP_PATH)`** tries the two rules in the opposite order, both syntactically: when `child[0]` is written as `CC_PLAM(i, A, body)`, it substitutes into `body` even at $r = 0$ or $r = 1$; only otherwise does it read the endpoint from the `CC_PATH` annotation.

#### `CC_TUBE` (`20`) — Partial system tube cell $[\varphi \mapsto u, \text{next}]$
- **Arity:** `2` (`payload = face_formula_id` $\varphi$ of sort `CC_FACE`, `child[0] = partial_term` $u$, `child[1] = next_tube` (optional `CC_TUBE` or `0`), `child[2..3] == 0`).
- **Role:** Singly linked list node representing partial elements in `CC_COMP.child[1]`, `CC_HCOMP.child[1]`, `CC_TRANS.child[1]`, and `CC_GLUE_TERM.child[2]`.
- **Normalization:** During `ck_normal`, `normal_restrict` restricts `child[0]` by the intersection of endpoint equations common to all clauses of $\varphi$ before normalizing `child[0]`.

#### `CC_COMP` (`19`) — Heterogeneous composition $\text{comp}^i\, A(i)\, [\varphi \mapsto u(i)]\, a_0$
- **Arity:** `3` (`payload = dim < 64`, `child[0] = family` $A(i)$, `child[1] = tubes` (optional `CC_TUBE` list or `0`), `child[2] = base` $a_0$, `child[3] == 0`).
- **Binder scope:** Binds dimension `dim` ($i$) in `child[0]` ($A(i)$) and in the body `t.child[0]` ($u(i)$) of each `CC_TUBE` in `child[1]`. Does **not** bind $i$ in any tube face formula `t.payload` ($\varphi$) or in `child[2]` ($a_0$).
- **Instructions:** Built incrementally as a `CC_FACT_SYSTEM` judgement by `cc_instr_system`, `cc_instr_system_tube`, and `cc_instr_system_overlap`, then closed into a typing judgement $\Gamma \vdash \text{comp}^i\, A(i)\, [\varphi \mapsto u(i)]\, a_0 : A(1)$ (discharging $i$) by `cc_instr_comp`.
- **Reduction:** Under `Step(CC_STEP_FACE)`, contracts to $u(1)$ if any tube has top face $\varphi = 1$. Under `Step(CC_STEP_SPLIT)`, splits multi-clause tubes into single-clause tubes and drops `0`-face tubes. Under `ck_whnf` and `ck_normal`, dispatches to `ck_reduce_composition` (see [Cubical composition, transport, and filling computation](#cubical-composition-transport-and-filling-computation)).

#### `CC_HCOMP` (`41`) — Homogeneous composition $\text{hcomp}^i\, A\, [\varphi \mapsto u(i)]\, a_0$
- **Arity:** `3` (`payload = dim < 64`, `child[0] = type` $A$, `child[1] = tubes` (optional `CC_TUBE` list or `0`), `child[2] = base` $a_0$, `child[3] == 0`).
- **Binder scope:** Binds dimension `dim` ($i$) **only** in the body `t.child[0]` ($u(i)$) of each `CC_TUBE` in `child[1]`. Does **not** bind $i$ in `child[0]` ($A$), tube faces, or `child[2]` ($a_0$).
- **Instructions:** Closed by `cc_instr_hcomp(k, system)` from a composition system whose family $A$ does not mention $i$ and whose WHNF head is an admitted H1 higher sort.
- **Reduction:** Drops `0`-face tubes; reduces to $u(1)$ when any tube has face `1` (`Step(CC_STEP_FACE)`, `ck_expose`, `ck_hit_reduce`). When remaining tubes are non-trivial ($0 < \varphi < 1$), `CC_HCOMP` is a canonical value of the higher sort and is eliminated by H1 `CC_ELIM` (`ck_eliminate_hcomp`) and commuted with `CC_TRANS` (`transport_hcomp`).

#### `CC_TRANS` (`42`) — Higher-sort transport $\text{transp}^i\, A(i)\, \varphi\, a_0$
- **Arity:** `3` (`payload = dim < 64`, `child[0] = family` $A(i)$, `child[1] = single_tube` `CC_TUBE(face = φ, term = a0, next = 0)`, `child[2] = base` $a_0$, `child[3] == 0`).
- **Shape:** `ck_make` imposes no Trans-specific rule beyond requiring `child[1]`. The instruction `cc_instr_trans` builds `child[1]` as the single tube `CC_TUBE(φ, a0, 0)`, and every reduction reads only that tube's face $\varphi$; the base is `child[2]`.
- **Binder scope:** Binds dimension `dim` ($i$) in `child[0]` ($A(i)$) **only**.
- **Instructions:** Closed by `cc_instr_trans(k, system, face)` from a composition system over a family $A(i)$ of an admitted H1 higher sort whose tubes are $[C_m \mapsto a_0|_{C_m}]$ for the clauses $C_m$ of $\varphi$ in order.
- **Reduction:** Reduces to `a0` when $\varphi = 1$ (`Step(CC_STEP_FACE)`, `ck_expose`, `ck_hit_reduce`); otherwise dispatches to `ck_hit_reduce` to commute past `hcomp` or transport point/path constructors with boundary correction.

---

### 6. Glue types and terms

#### `CC_GLUE` (`31`) — Glue type $\text{Glue}\,[\varphi \mapsto (T, e)]\, A$
- **Arity:** `2` (`payload == 0`, `child[0] = base_type` $A$, `child[1] = system` (optional `CC_GLUE_SYSTEM` list or `0`), `child[2..3] == 0`).
- **Instructions:** Built piece-by-piece via `cc_instr_glue_base`, `cc_instr_glue_piece`, and `cc_instr_glue_overlap`, then closed into $\Gamma \vdash \text{Glue}\,[\varphi \mapsto (T, e)]\, A : \mathcal{U}(\ell)$ by `cc_instr_glue`.
- **Reduction & Composition:** In `ck_whnf`, `0`-face pieces are dropped, and if any piece has top face `1`, the `CC_GLUE` node reduces directly to that piece's partial type $T$ (`piece.child[0]`); `ck_expose` leaves Glue types untouched. Composition in a `CC_GLUE` family computes via `ck_glue_composition` ([glue_compute.c](../../kernel/src/glue_compute.c)).

#### `CC_GLUE_SYSTEM` (`32`) — Glue piece cell $[\varphi \mapsto (T, e), \text{next}]$
- **Arity:** `3` (`payload = face_formula_id` $\varphi$ of sort `CC_FACE`, `child[0] = partial_type` $T$, `child[1] = equivalence` $e$, `child[2] = next` (optional `CC_GLUE_SYSTEM` or `0`), `child[3] == 0`).
- **Role:** Linked list node in `CC_GLUE.child[1]` pairing a partial type $T$ and an equivalence $e : \text{Equiv}(T, A|_\varphi)$ on face $\varphi$. During `ck_normal`, `normal_restrict` restricts both `child[0]` ($T$) and `child[1]` ($e$) by the endpoint equations common to all clauses of $\varphi$.

#### `CC_GLUE_TERM` (`33`) — Glue element $\text{glue}_G([\varphi \mapsto t], a)$
- **Arity:** `3` (`payload == 0`, `child[0] = glue_type` $G$, `child[1] = base_val` $a$, `child[2] = tubes` (optional `CC_TUBE` list or `0`), `child[3] == 0`).
- **Instructions:** Built piece-by-piece via `cc_instr_glue_term_base`, `cc_instr_glue_term_piece`, and `cc_instr_system_overlap`, then closed into $\Gamma \vdash \text{glue}_G([\varphi \mapsto t], a) : G$ by `cc_instr_glue_term`.
- **Reduction ($\beta$ and $\eta$):**
  - Drops `0`-face tubes; if any tube has top face `1`, reduces to that tube's body $t$ (`tube.child[0]`).
  - **Syntactic Glue $\eta$ in `ck_whnf`:** If `whnf(a)` is `CC_UNGLUE(G', p)` with `ck_alpha_equal(k, G, G')` and for every non-empty tube $(\varphi \mapsto t)$ and every clause $C \in \varphi$, `ck_alpha_equal(k, t, ck_restrict(k, p, C))`, reduces to $p$.
  - **Targeted Glue $\eta$ in `Step(CC_STEP_GLUE)` (`ck_glue_step`):** Unwraps nested Glue steps on `a` to find `CC_UNGLUE(G', p)` and contracts to $p$ when $G$ and $G'$ agree (compared whole) and $t|_C$ and $p|_C$ agree on each clause $C \in \varphi$, each comparison by `normal_agree` (syntactically, by WHNF, congruently under a common head, or by full normal form).

#### `CC_UNGLUE` (`34`) — Glue base projection $\text{unglue}_G(g)$
- **Arity:** `2` (`payload == 0`, `child[0] = glue_type` $G$, `child[1] = glue_val` $g$, `child[2..3] == 0`).
- **Instructions:** Eliminated by `cc_instr_unglue(k, value)` from $g : G$, producing $\text{unglue}_G(g) : A$ where $A = G.\text{child}[0]$.
- **Reduction ($\beta$):**
  1. If $G$, which must be a `CC_GLUE` node as written (`ck_whnf` does not reduce it first), has a top-face (`1`) piece $(T, e)$, reduces to $\pi_1(e)(g)$ (`App(Fst(e), g)`).
  2. Otherwise, if `whnf(g)` is `CC_GLUE_TERM(_, base, _)`, reduces to `base`.

---

### 7. Declared inductive and higher inductive types (H1)

#### `CC_SORT` (`50`) — Declared sort instance $S\{\vec{\ell}\}(\vec{a})$
- **Arity:** `2` (`payload = sig_index >= 1`, `child[0] = params` (optional `CC_LIST` of term parameters or `0`), `child[1] = levels` (optional `CC_LIST` of recorded canonical levels or `0`), `child[2..3] == 0`).
- **Instructions:** Built by `cc_instr_sort_begin`, `cc_instr_sort_level`, and `cc_instr_sort_parameter` (and used with `child[0] == 0, child[1] == 0` as the open signature's own sort handle in `CC_FACT_SIGNATURE`).
- **Composition:**
  - If the signature is a **data sort** (`!ck_signature_higher(s)`: `modifier == CC_UNTRUNCATED` and no path constructors), `CC_SORT` composes and transports by `CC_COMP` via telescope tupling (`ck_sort_composition` in [inductive_composition.c](../../kernel/src/inductive_composition.c)).
  - If the signature is a **higher sort** (`ck_signature_higher(s)`), `CC_SORT` admits `CC_HCOMP` and `CC_TRANS`, and heterogeneous `CC_COMP` decomposes into `hcomp` and `transp` (`ck_higher_composition` in [hit_composition.c](../../kernel/src/hit_composition.c)).

#### `CC_CON` (`51`) — Declared constructor head $c_k(I)$
- **Arity:** `1` (`payload = ctor_index`, `child[0] = sort_instance` $I$ of kind `CC_SORT`, `child[1..3] == 0`).
- **Role:** Represents the $k$-th constructor of an admitted signature instantiated at sort instance $I$. Non-recursive data arguments $t_1, \dots, t_a$ and recursive arguments $q_1, \dots, q_b$ are applied to `CC_CON` using `CC_APP`; path dimensions $r_1, \dots, r_d$ are applied using `CC_PAPP`.
- **Instructions:** Introduced by `cc_instr_construct(k, instance, constructor)`, certifying $\text{Con}(k; I) : T_k[s := I, \vec{x} := \rho, \vec{p} := \vec{a}, c_m := \text{Con}(m; I)]$.
- **Boundary reduction:** When a path constructor spine $c_k(I)(\vec{t}, \vec{q}) \mathbin{@}_{P_1} r_1 \dots \mathbin{@}_{P_d} r_d$ has $r_l = 0$ or $r_l = 1$, the `CC_PAPP` node carries the instantiated path type $P_l = \text{Path}_i(B, b_{l,0}, b_{l,1})$ in `child[1]`, so `CC_STEP_PATH`, `ck_expose`, and `ck_whnf` reduce it immediately to the declared endpoint $b_{l,0}$ or $b_{l,1}$.

#### `CC_ELIM` (`52`) — Declared dependent eliminator $\text{elim}_S(M, [m_0, \dots, m_{n-1}])$
- **Arity:** `2` (`payload = sig_index >= 1`, `child[0] = motive` $M$, `child[1] = clauses` (optional `CC_LIST` of clause methods or `0`), `child[2..3] == 0`).
- **Instructions:** Opened by `cc_instr_eliminator(k, motive)`, extended one constructor clause at a time by `cc_instr_eliminator_clause(k, eliminator, clause)` (which keeps the in-progress clause list reversed in `child[1]`), and closed in forward constructor order by `cc_instr_eliminator_close(k, eliminator)` to certify $\text{Elim}(\text{sig}, M, [m_0, \dots, m_{n-1}]) : \Pi(z : I).\, M(z)$.
- **Elimination ($\iota$):** Applied to a scrutinee $s : I$ via `CC_APP(Elim(...), s)`. Reduces via `ck_eliminate` when $s$ is a constructor/path-constructor spine (under `Step(CC_STEP_IOTA)`, `ck_whnf`, and `ck_normal`) or an `hcomp` term (under `ck_whnf` and `ck_normal`).

#### `CC_LIST` (`53`) — Generic AST cons-cell `[item, next]`
- **Arity:** `2` (`payload == 0`, `child[0] = item`, `child[1] = next` (optional `CC_LIST` or `0`), `child[2..3] == 0`).
- **Role:** Immutable singly linked list spine used only inside `CC_SORT.child[0]` (term parameters), `CC_SORT.child[1]` (recorded universe levels), `CC_ELIM.child[1]` (clause methods), and `CC_FACT_INSTANCE.other` (parameter types in progress). Never typed as a standalone term.

---

### 8. Retired primitive tags

The twelve enum constants `CC_NAT` (`10`), `CC_ZERO` (`11`), `CC_SUCC` (`12`), `CC_NATREC` (`13`), `CC_W` (`23`), `CC_SUP` (`24`), `CC_WREC` (`25`), `CC_PUSHOUT` (`36`), `CC_PUSH_LEFT` (`37`), `CC_PUSH_RIGHT` (`38`), `CC_PUSH_PATH` (`39`), and `CC_PUSH_ELIM` (`40`) are preserved in `cc_term_kind` solely to keep ABI numeric constants stable. `ck_arity` assigns them sentinel arity `5` (above the 4-child maximum), so `cc_kernel_term` rejects them with `"Unknown term constructor."`

---

## Binder scopes, substitution, restriction, and comparison

### Term and dimension binder slots

Only specific child slots of binder constructors bind their `payload` symbol or dimension ([term_substitution.c](../../kernel/src/term_substitution.c)):

| Binder kind | `payload` | Bound in `child[0]` (`a`)? | Bound in `child[1]` (`b`)? | Bound in `child[2]` (`c`)? |
|---|---|---|---|---|
| `CC_PI`, `CC_LAM`, `CC_SIGMA`, `CC_LPI`, `CC_LLAM` | Term/level `symbol` | No (`a` is domain/bound) | **Yes** | — |
| `CC_PATH` | Dimension `dim` | **Yes** ($A(i)$) | No ($a_0$) | No ($a_1$) |
| `CC_PLAM` | Dimension `dim` | **Yes** ($A(i)$) | **Yes** ($t(i)$) | — |
| `CC_COMP` | Dimension `dim` | **Yes** ($A(i)$) | **Yes, in tube bodies `t.child[0]` only** (not in tube faces `t.payload`) | No ($a_0$) |
| `CC_HCOMP` | Dimension `dim` | No ($A$ is constant) | **Yes, in tube bodies `t.child[0]` only** (not in tube faces `t.payload`) | No ($a_0$) |
| `CC_TRANS` | Dimension `dim` | **Yes** ($A(i)$) | No (tube holds constant face $\varphi$ and $a_0$) | No ($a_0$) |

### Capture-avoiding substitution and face restriction

1. **Term substitution (`ck_substitute(k, target, symbol, replacement)`):**
   - Traverses `target` on an explicit worklist stack (`substitution_frame`) memoized in the shared syntax memo `k->syntax_memo` (operation `3`).
   - Fast path: if `symbol`'s bit is clear in `target.symbols`, or `!ck_term_free(k, target, symbol)`, returns `target` immediately.
   - If `target` is a term binder (`CC_PI`, `CC_LAM`, `CC_SIGMA`, `CC_LPI`, `CC_LLAM`) with `n.payload == symbol`, the variable is shadowed in `child[1]` and only `child[0]` is substituted.
   - If `n.payload != symbol` and `n.payload` occurs free in `replacement`, `ck_substitute` allocates a fresh symbol (`ck_fresh_symbol`, above every symbol any term has used), renames `n.payload` in `child[1]` first, and then substitutes `replacement`. A dimension binder whose bound dimension occurs free in `replacement` is likewise renamed to a fresh dimension first.
2. **Level instantiation (`ck_level_instantiate(k, target, symbol, level)`):**
   - Substitutes a finite level expression `level` for a level variable `symbol` across `target`, then rebuilding canonical level syntax for every `CC_U` level and `CC_LAPP` level argument (`ck_canonical_levels`); a level inside a `CC_SORT` level list is left as substituted, since comparison reads it by normal form.
3. **Dimension substitution (`ck_dimension_substitute(k, target, dim, formula)`):**
   - Replaces free occurrences of interval coordinate `dim` ($i$) with the interval formula $r$ (`formula`) using the same worklist, memoized in `k->syntax_memo` (operation `6`).
   - In `CC_PAPP`, substitutes $r$ for $i$ inside `n.payload` via `cc_interval_substitute`.
   - In `CC_TUBE` and `CC_GLUE_SYSTEM`, substitutes $r$ for $i$ inside the face formula `n.payload` via `cc_face_substitute`.
   - For a dimension binder (`CC_PATH`, `CC_PLAM`, `CC_COMP`, `CC_HCOMP`, `CC_TRANS`) whose bound dimension `n.payload` differs from `dim` and occurs in $r$, picks a fresh dimension $j \in 0..63$ (`ck_fresh_dimension` avoiding the node, $r$, and `dim`), renames `n.payload` to $j$ inside the bound slots first, and then substitutes $r$ for `dim`. A binder of `dim` itself keeps its name and shields its bound slots; substitution continues into its unbound slots (a `CC_PATH`'s endpoints, a composition's tube faces and base).
4. **Face restriction (`ck_restrict(k, term, clause)`):**
   - Simplifies `term` under a single consistent face clause $C$.
   - For each dimension $d \in 0..63$ constrained by $C$ ($(d = 0)$ in `C.negative` or $(d = 1)$ in `C.positive`), substitutes $\bot$ (`0`) or $\top$ (`1`) for $d$ via `ck_endpoint_term`; that dimension substitution also rewrites the face formulas of tubes and Glue pieces, so nothing else is done.

### Syntactic comparison and cumulativity (`term_conversion.c`)

- **`ck_alpha_equal(k, left, right)`:** Checks syntactic $\alpha$-equivalence on an explicit traversal stack (`alpha_frame`) memoized in `k->alpha_memo`:
  - Identical handles (`left == right`) with no active renamings on their free variables/dimensions succeed immediately.
  - Universe levels compare by arithmetic normal form (`level_alpha`, built on `ck_level_normal`) where the traversal reaches them: the level child of `CC_U`, the level argument of `CC_LAPP`, and the recorded levels of a `CC_SORT`, so $\mathcal{U}(\max(\ell + 1, \ell)) \equiv \mathcal{U}(\ell + 1)$ syntactically. Two level nodes compared directly (as the `cc_kernel_alpha_equal` query can) must first have the same kind, as any two nodes must: `LMax(LSucc(1, ℓ), ℓ)` and `LSucc(1, ℓ)` are then unequal, and only two `CC_LCONST`/`CC_LSUCC`/`CC_LMAX` nodes of one kind compare by normal form.
  - Term binders push `(left.payload, right.payload)` onto the active term-scope stack; dimension binders push `(left.payload, right.payload)` onto the dimension-scope stack.
  - Interval and face formula payloads on `CC_PAPP`, `CC_TUBE`, and `CC_GLUE_SYSTEM` are mapped through any active dimension renamings before comparing their canonical `cc_clause` arrays.
  - `CC_PAPP.child[1]` (the optional Path-type annotation) is ignored during syntactic comparison because `child[0]` (the path) and `payload` (the interval formula) uniquely determine the application.
- **`ck_syntactic_cumulative(k, sub_type, super_type)`:** Checks structural subtyping $A \preceq B$ for `cc_instr_lift` without reducing terms:
  - $A \equiv_\alpha B \implies A \preceq B$.
  - $\mathcal{U}(\ell_1) \preceq \mathcal{U}(\ell_2) \iff \ell_1 \le \ell_2$ (`ck_level_leq`).
  - $\Pi(x : A_1).\, B_1(x) \preceq \Pi(x : A_2).\, B_2(x) \iff A_1 \equiv_\alpha A_2 \text{ and } B_1(x) \preceq B_2(x)$.
  - $\forall(\ell < \omega).\, B_1(\ell) \preceq \forall(\ell < \omega).\, B_2(\ell) \iff B_1(\ell) \preceq B_2(\ell)$.
  - $\Sigma(x : A_1).\, B_1(x) \preceq \Sigma(x : A_2).\, B_2(x) \iff A_1 \equiv_\alpha A_2 \text{ and } B_1(x) \preceq B_2(x)$.
  - No other former is included: sums, path types, Glue types, and sort instances are included only when $\alpha$-equal.

---

## Reference for every kernel instruction (`cc_instruction`)

### Context entries, judgements, and derivation sharing

The kernel maintains three tables for derivations ([term_internal.h](../../kernel/src/term_internal.h), [instructions.c](../../kernel/src/instructions.c)), append-only between checkpoints and truncated to the checkpoint by `cc_kernel_rollback` and `cc_kernel_commit_checkpoint` (judgements from before it stay valid; a definition's `Lookup` can be issued again):

1. **Context entries (`k->entries[1 .. entry_count - 1]`, handle `cc_entry_id`):**
   Each `cc_entry` represents a single assumption in a context:
   - a **term variable entry** ($x : A$, created by `cc_instr_extend`), recording `symbol`, `type` ($A$), `level` ($\ell$ where $A : \mathcal{U}(\ell)$), `context` (the entries $A$ depends on), `scope` ($\text{context} \cup \{x\}$), and `source` (the typing judgement for $A$);
   - a **level variable entry** ($x < \omega$, created by `cc_instr_level`), recording `symbol`, `type = CC_LBOUND(1)`, `level_variable = true`, and `scope = {x}`;
   - a **dimension entry** ($i \in 0..63$, created by `cc_instr_dimension`), recording `symbol = i`, `dimension = true`, and `scope = {i}` (one canonical entry per index $0..63$);
   - a **face assumption entry** ($\varphi$, created internally by `cc_instr_restrict`), recording `face = true`, `clause` (a single consistent non-empty `cc_clause`), `context` (the dimension entries of `clause`), and `scope`.

2. **Context sets (`k->context_sets`, indexed by `uint32_t`):**
   Each judgement stores only the sorted, deduplicated set of `cc_entry_id`s it actually depends on (`set == 0` is the empty context $\varnothing$).
   - **Merging (`ck_instr_merge`):** Takes the sorted union of two context sets, rejecting if two distinct dimension entries share the same dimension index.
   - **Discharging (`ck_instr_discharge`):** Removes bound entries from a context set, rejecting if a remaining entry still depends on a removed one (`contains(e_other.context, e)`) or is a dimension entry with a removed dimension's index. `Endpoint`, `Comp`, `HComp`, `Trans`, `Replace`, and face discharge use it alone.
   - **Binding (`ck_instr_bind`):** Discharges one entry $e$ and merges $e.\text{context}$ (the dependencies of $e$'s own type) back in; the binder instructions (`Pi`, `Lambda`, `Sigma`, `LevelPi`, `LevelLambda`, `Path`, `PathLambda`) use it.
   - **Face discharge (`ck_instr_on_face`):** When a partial element is checked on a clause $C$, `ck_instr_on_face` discharges every face entry $\psi$ in the premise's context whose equations are a subset of $C$ ($C \vdash \psi$). If a remaining variable's type depends on $\psi$, discharging fails.

3. **Certified judgements (`k->facts[1 .. fact_count - 1]`, handle `cc_judgement_id`):**
   Each `cc_fact` has a `kind`, handles `term`, `other`, `type`, a `context` set ID, a `pending` bitmask/counter for multi-step builders, and the `cc_derivation` record (`rule`, `premise[0..3]`, `entry`, `operand[0..1]`, `position`, `depth`).
   - `CC_FACT_TYPING` (`1`): $\Gamma \vdash \text{term} : \text{type}$.
   - `CC_FACT_EQUALITY` (`2`): $\Gamma \vdash \text{term} \equiv \text{other} : \text{type}$.
   - `CC_FACT_SYSTEM` (`3`): open composition system, Glue type system, or Glue term system under construction (`pending` bitmask tracks unresolved overlaps with earlier tubes/pieces).
   - `CC_FACT_SIGNATURE` (`4`): open H1 signature under admission (`pending` counts constructors added so far).
   - `CC_FACT_INSTANCE` (`5`): H1 sort instance in progress (`pending` packs `level_count | (parameter_count << 32)`).
   - `CC_FACT_ELIMINATOR` (`6`): H1 eliminator in progress (`pending` counts clauses added so far).

   Stateless instructions memoize their `cc_derivation` in `k->derivations`: issuing the same instruction with identical premises, entry, operands, and position returns the existing `cc_judgement_id` in one budget step.

---

### 1. Context entry constructors

These three functions return a `cc_entry_id` (or `0` on error):

#### `cc_instr_extend(k, type, symbol)` — Term variable entry $x : A$
- **Inputs:** Typing judgement `type` ($\Gamma \vdash A : \mathcal{U}(\ell)$), fresh or matching `uint32_t symbol != 0`.
- **Checks:** `type` must be a `CC_FACT_TYPING` judgement whose type is `CC_U(l)`. If `symbol` already names an entry in `k->entry_index`, it must be a term entry with the same `source` judgement or an $\alpha$-equal type (`ck_alpha_equal(existing.type, A)`), in which case that existing `cc_entry_id` is returned; otherwise fails with `"The symbol already names a context entry."`
- **Result:** Allocates (or reuses) `cc_entry_id` for $x : A$ with `scope = Γ ∪ {x}`.

#### `cc_instr_level(k, symbol)` — Universe-level variable entry $x < \omega$
- **Inputs:** `uint32_t symbol != 0`.
- **Checks:** If `symbol` already exists in `k->entry_index`, returns the existing entry if `level_variable == true`, or fails if it names a term entry.
- **Result:** Allocates (or reuses) `cc_entry_id` with `type = CC_LBOUND(1)`, `level_variable = true`, and `scope = {x}`.

#### `cc_instr_dimension(k, index)` — Interval coordinate entry $i$
- **Inputs:** `unsigned index < 64` (`CC_DIMENSIONS`).
- **Checks:** Rejects `index >= 64` with `"Dimension outside the native range."`
- **Result:** Returns the canonical dimension entry `k->dimension_entries[index]` with `symbol = index`, `dimension = true`, and `scope = {i}`.

---

### 2. Variables, endpoints, face restrictions, and definitions

#### `CC_INSTR_VARIABLE` (`14`) — `cc_instr_variable(k, id)`
- **Inputs:** `cc_entry_id id`.
- **Checks:** `id` must be a valid term variable entry (`!dimension`, `!face`, `!level_variable`).
- **Result (`CC_FACT_TYPING`):** $\Gamma, x : A \vdash \text{Var}(x) : A$ with context `id.scope`.

#### `CC_INSTR_ENDPOINT` (`38`) — `cc_instr_endpoint(k, id, dimension, endpoint)`
- **Inputs:** Typing judgement `id` ($\Gamma \vdash t : T$), dimension entry `dimension` ($i$), `unsigned endpoint` ($\varepsilon \in \{0, 1\}$).
- **Checks:** `id` is `CC_FACT_TYPING`, `dimension` is a dimension entry, `endpoint <= 1`, and discharging $i$ from $\Gamma$ (`ck_instr_discharge`) succeeds (no remaining entry in $\Gamma$ depends on $i$).
- **Result (`CC_FACT_TYPING`):** $\Gamma \setminus \{i\} \vdash t[\varepsilon/i] : T[\varepsilon/i]$.

#### `CC_INSTR_RESTRICT` (`74`) — `cc_instr_restrict(k, id, face)`
- **Inputs:** Typing judgement `id` ($\Gamma \vdash t : T$), `cc_formula_id face` ($\varphi$).
- **Checks:** `id` is `CC_FACT_TYPING`; `face` is a registered `CC_FACE` formula with `length == 1` whose single clause $C$ is consistent (`(C.positive & C.negative) == 0`) and non-empty (`(C.positive | C.negative) != 0`).
- **Result (`CC_FACT_TYPING`):** Creates/reuses the face entry for $C$ (`ck_instr_face_entry`) and publishes $\Gamma, C \vdash \text{ck\_restrict}(t, C) : \text{ck\_restrict}(T, C)$. Unlike `Endpoint`, `Restrict` succeeds even when entries in $\Gamma$ depend on $C$'s dimensions; the added face entry $C$ is later discharged by `ck_instr_on_face` when the judgement is used inside `SystemTube`, `SystemOverlap`, `GluePiece`, `GlueOverlap`, or `GlueTermPiece`.

#### `CC_INSTR_DEFINE` (`27`) — `cc_instr_define(k, symbol, closed)`
- **Inputs:** `uint32_t symbol`, typing judgement `closed` ($\vdash t : T$).
- **Checks:** `closed` is `CC_FACT_TYPING` with empty context (`closed.context == 0`), and `symbol` is not already registered in `k->definitions`.
- **Result (`CC_FACT_TYPING`):** Registers `(symbol, t, T)` at `index = k->definition_count++`, mints `ref = CC_DEFREF(index)`, and publishes $\vdash \text{DefRef}(\text{index}) : T$ in the empty context.

#### `CC_INSTR_LOOKUP` (`28`) — `cc_instr_lookup(k, reference)`
- **Inputs:** `cc_term reference` of kind `CC_DEFREF`.
- **Checks:** `reference` is a valid `CC_DEFREF` handle with `1 <= payload < k->definition_count`.
- **Result (`CC_FACT_TYPING`):** $\vdash \text{DefRef}(\text{index}) : T$ in the empty context.

---

### 3. Universes and universe-level quantification (G0)

#### `CC_INSTR_UNIVERSE` (`1`) — `cc_instr_universe(k, level)`
- **Inputs:** `cc_term level` (a level expression).
- **Checks:** Computes arithmetic normal form `ck_level_normal(k, level, &nf)`; verifies every level variable in `nf` is a declared level entry (`level_context`) and `nf.constant < CC_LEVEL_MAX` (`65535`); builds canonical level syntax $\ell = \text{ck\_level\_build}(\text{nf})$ and $\ell' = \text{ck\_level\_build}(\text{nf} + 1)$.
- **Result (`CC_FACT_TYPING`):** $\Gamma_{\text{levels}(\ell)} \vdash \mathcal{U}(\ell) : \mathcal{U}(\ell')$.

#### `CC_INSTR_LEVEL_PI` (`61`) — `cc_instr_level_pi(k, id, body_id)`
- **Inputs:** Level entry `id` ($x < \omega$), typing judgement `body_id` ($\Gamma, x < \omega \vdash B : \mathcal{U}(\ell)$).
- **Checks:** `id` is a level entry, `body_id` is `CC_FACT_TYPING` whose type is `CC_U(l)`, and discharging `id` from `body_id.context` succeeds. Computes $\lim_x(\ell)$ (`ck_level_limit`): if $x$ occurs in $\text{nf}(\ell)$, the limit is $\omega$ (`CC_LCONST(1 << 16)`); otherwise it is $\text{nf}(\ell)$.
- **Result (`CC_FACT_TYPING`):** $\Gamma \setminus \{x\} \vdash \text{LPi}(x, \text{LBound}(1), B) : \mathcal{U}(\lim_x(\ell))$.

#### `CC_INSTR_LEVEL_LAMBDA` (`62`) — `cc_instr_level_lambda(k, id, body_id)`
- **Inputs:** Level entry `id` ($x < \omega$), typing judgement `body_id` ($\Gamma, x < \omega \vdash b : B$).
- **Checks:** `id` is a level entry, `body_id` is `CC_FACT_TYPING`, and discharging `id` from `body_id.context` succeeds.
- **Result (`CC_FACT_TYPING`):** $\Gamma \setminus \{x\} \vdash \text{LLam}(x, \text{LBound}(1), b) : \text{LPi}(x, \text{LBound}(1), B)$.

#### `CC_INSTR_LEVEL_APPLY` (`63`) — `cc_instr_level_apply(k, function, level)`
- **Inputs:** Typing judgement `function` ($\Gamma \vdash f : \forall(x < \omega).\, B$), `cc_term level` ($\ell$).
- **Checks:** `function` has type `CC_LPI(x, LBound(1), B)`; `level` normalizes to a **finite** level (`nf.tier == 0`; this instruction checks no further bound on `nf.constant`, which `ck_level_normal` has already kept at most `CC_LEVEL_MAX`) whose variables are level entries with context $\Gamma_\ell$; instantiates $B[x := \ell_{\text{canon}}]$ via `ck_level_instantiate`.
- **Result (`CC_FACT_TYPING`):** $\Gamma \cup \Gamma_\ell \vdash \text{LApp}(f, \ell_{\text{canon}}) : B[x := \ell_{\text{canon}}]$.

---

### 4. Dependent functions ($\Pi$) and dependent pairs ($\Sigma$)

#### `CC_INSTR_PI` (`15`) — `cc_instr_pi(k, id, codomain)`
- **Inputs:** Term entry `id` ($x : A$ with $A : \mathcal{U}(\ell_A)$), typing judgement `codomain` ($\Gamma, x : A \vdash B : \mathcal{U}(\ell_B)$).
- **Checks:** `id` is a term entry, `codomain` is `CC_FACT_TYPING` whose type is `CC_U(l_B)`, and `ck_instr_bind(codomain.context, id)` succeeds (discharging $x$ and merging $A$'s context).
- **Result (`CC_FACT_TYPING`):** $(\Gamma \setminus \{x\}) \cup \Gamma_A \vdash \text{Pi}(x, A, B) : \mathcal{U}(\max(\ell_A, \ell_B))$.

#### `CC_INSTR_LAMBDA` (`16`) — `cc_instr_lambda(k, id, body_id)`
- **Inputs:** Term entry `id` ($x : A$), typing judgement `body_id` ($\Gamma, x : A \vdash b : B$).
- **Checks:** `id` is a term entry, `body_id` is `CC_FACT_TYPING`, and `ck_instr_bind(body_id.context, id)` succeeds.
- **Result (`CC_FACT_TYPING`):** $(\Gamma \setminus \{x\}) \cup \Gamma_A \vdash \text{Lam}(x, A, b) : \text{Pi}(x, A, B)$.

#### `CC_INSTR_APPLY` (`17`) — `cc_instr_apply(k, function, argument)`
- **Inputs:** Typing judgements `function` ($\Gamma_1 \vdash f : \Pi(x : A).\, B$) and `argument` ($\Gamma_2 \vdash a : A'$).
- **Checks:** `function.type` has kind `CC_PI(x, A, B)`, `ck_alpha_equal(A', A)` holds, and $\Gamma_1, \Gamma_2$ merge.
- **Result (`CC_FACT_TYPING`):** $\Gamma_1 \cup \Gamma_2 \vdash \text{App}(f, a) : B[a/x]$.

#### `CC_INSTR_SIGMA` (`18`) — `cc_instr_sigma(k, id, family)`
- **Inputs:** Term entry `id` ($x : A$ with $A : \mathcal{U}(\ell_A)$), typing judgement `family` ($\Gamma, x : A \vdash B : \mathcal{U}(\ell_B)$).
- **Checks:** Same as `CC_INSTR_PI`.
- **Result (`CC_FACT_TYPING`):** $(\Gamma \setminus \{x\}) \cup \Gamma_A \vdash \text{Sigma}(x, A, B) : \mathcal{U}(\max(\ell_A, \ell_B))$.

#### `CC_INSTR_PAIR` (`19`) — `cc_instr_pair(k, type_id, first_id, second_id)`
- **Inputs:** Typing judgements `type_id` ($\Gamma_1 \vdash \Sigma(x : A).\, B : \mathcal{U}(\ell)$), `first_id` ($\Gamma_2 \vdash a : A'$), `second_id` ($\Gamma_3 \vdash b : B'$).
- **Checks:** `type_id.term` has kind `CC_SIGMA(x, A, B)`, `type_id.type` is `CC_U(l)`, $A' \equiv_\alpha A$, $B' \equiv_\alpha B[a/x]$, and $\Gamma_1, \Gamma_2, \Gamma_3$ merge.
- **Result (`CC_FACT_TYPING`):** $\Gamma_1 \cup \Gamma_2 \cup \Gamma_3 \vdash \text{Pair}(\Sigma(x:A).B, a, b) : \Sigma(x : A).\, B$.

#### `CC_INSTR_FIRST` (`20`) and `CC_INSTR_SECOND` (`21`) — `cc_instr_first(k, pair)` / `cc_instr_second(k, pair)`
- **Inputs:** Typing judgement `pair` ($\Gamma \vdash p : \Sigma(x : A).\, B$).
- **Checks:** `pair.type` has kind `CC_SIGMA(x, A, B)`.
- **Result (`CC_FACT_TYPING`):** `First` publishes $\Gamma \vdash \text{Fst}(p) : A$; `Second` publishes $\Gamma \vdash \text{Snd}(p) : B[\text{Fst}(p)/x]$.

#### `CC_INSTR_DOMAIN` (`22`) and `CC_INSTR_FAMILY` (`23`) — `cc_instr_domain(k, type_id)` / `cc_instr_family(k, type_id, argument)`
- **Inputs:** `type_id` ($\Gamma_1 \vdash F : \mathcal{U}(\ell)$ where $F$ is `CC_PI(x, A, B)` or `CC_SIGMA(x, A, B)`), and for `Family`, `argument` ($\Gamma_2 \vdash a : A'$).
- **Checks:** `type_id.type` is `CC_U(l)`, `type_id.term` is `CC_PI` or `CC_SIGMA`, and for `Family`, $A' \equiv_\alpha A$ and $\Gamma_1, \Gamma_2$ merge.
- **Result (`CC_FACT_TYPING`):** `Domain` publishes $\Gamma_1 \vdash A : \mathcal{U}(\ell)$; `Family` publishes $\Gamma_1 \cup \Gamma_2 \vdash B[a/x] : \mathcal{U}(\ell)$.

---

### 5. Unit, Void, and disjoint sums

#### `CC_INSTR_UNIT` (`6`) and `CC_INSTR_POINT` (`7`) — `cc_instr_unit(k)` / `cc_instr_point(k)`
- **Inputs:** None.
- **Result (`CC_FACT_TYPING`):** `Unit` publishes $\vdash \text{Unit} : \mathcal{U}_0$; `Point` publishes $\vdash \text{Point} : \text{Unit}$.

#### `CC_INSTR_UNIT_ELIM` (`8`) — `cc_instr_unit_elim(k, motive_id, point_id, value_id)`
- **Inputs:** Typing judgements `motive_id` ($\Gamma_1 \vdash M : \Pi(x : \mathbf{1}).\, \mathcal{U}(\ell)$), `point_id` ($\Gamma_2 \vdash b : M(\star)$), `value_id` ($\Gamma_3 \vdash u : \mathbf{1}$).
- **Checks:** `motive_id.type` is `CC_PI` from `CC_UNIT` to `CC_U`, `value_id.type` is `CC_UNIT`, `point_id.type` $\equiv_\alpha \text{App}(M, \text{Point})$, and $\Gamma_1, \Gamma_2, \Gamma_3$ merge.
- **Result (`CC_FACT_TYPING`):** $\Gamma_1 \cup \Gamma_2 \cup \Gamma_3 \vdash \text{UnitRec}(M, b, u) : \text{App}(M, u)$.

#### `CC_INSTR_VOID` (`9`) and `CC_INSTR_ABORT` (`10`) — `cc_instr_void(k)` / `cc_instr_abort(k, type_id, impossible_id)`
- **Inputs:** For `Abort`, typing judgements `type_id` ($\Gamma_1 \vdash T : \mathcal{U}(\ell)$) and `impossible_id` ($\Gamma_2 \vdash e : \mathbf{0}$).
- **Checks:** `type_id.type` is `CC_U(l)`, `impossible_id.type` is `CC_VOID`, and $\Gamma_1, \Gamma_2$ merge.
- **Result (`CC_FACT_TYPING`):** `Void` publishes $\vdash \text{Void} : \mathcal{U}_0$; `Abort` publishes $\Gamma_1 \cup \Gamma_2 \vdash \text{Abort}(T, e) : T$.

#### `CC_INSTR_SUM` (`11`) — `cc_instr_sum(k, left_id, right_id)`
- **Inputs:** Typing judgements `left_id` ($\Gamma_1 \vdash A : \mathcal{U}(\ell_A)$) and `right_id` ($\Gamma_2 \vdash B : \mathcal{U}(\ell_B)$).
- **Checks:** Both types are universes and $\Gamma_1, \Gamma_2$ merge.
- **Result (`CC_FACT_TYPING`):** $\Gamma_1 \cup \Gamma_2 \vdash \text{Sum}(A, B) : \mathcal{U}(\max(\ell_A, \ell_B))$.

#### `CC_INSTR_INJECT` (`12`) — `cc_instr_inject(k, type_id, value_id, right)`
- **Inputs:** Typing judgements `type_id` ($\Gamma_1 \vdash A + B : \mathcal{U}(\ell)$), `value_id` ($\Gamma_2 \vdash v : T$), `bool right`.
- **Checks:** `type_id.term` is `CC_SUM(A, B)`, `type_id.type` is `CC_U(l)`, $T \equiv_\alpha A$ (if `!right`) or $T \equiv_\alpha B$ (if `right`), and $\Gamma_1, \Gamma_2$ merge.
- **Result (`CC_FACT_TYPING`):** $\Gamma_1 \cup \Gamma_2 \vdash \text{Inl}(A + B, v) : A + B$ (or `Inr` when `right == true`).

#### `CC_INSTR_SUM_ELIM` (`13`) — `cc_instr_sum_elim(k, motive_id, left_id, right_id, value_id)`
- **Inputs:** Typing judgements `motive_id` ($\Gamma_1 \vdash M : \Pi(z : A + B).\, \mathcal{U}(\ell)$), `left_id` ($\Gamma_2 \vdash l : L$), `right_id` ($\Gamma_3 \vdash r : R$), `value_id` ($\Gamma_4 \vdash v : A + B$).
- **Checks:** `value_id.type` is `CC_SUM(A, B)`, `motive_id` is a motive over $A + B$, $L \equiv_\alpha \Pi(x : A).\, M(\text{Inl}(A + B, x))$, $R \equiv_\alpha \Pi(y : B).\, M(\text{Inr}(A + B, y))$, and $\Gamma_1 \dots \Gamma_4$ merge.
- **Result (`CC_FACT_TYPING`):** $\bigcup_{m=1}^4 \Gamma_m \vdash \text{SumRec}(M, l, r, v) : \text{App}(M, v)$.

---

### 6. Paths and interval application

#### `CC_INSTR_PATH` (`24`) — `cc_instr_path(k, dimension, family_id, left_id, right_id)`
- **Inputs:** Dimension entry `dimension` ($i$), typing judgements `family_id` ($\Gamma_1, i \vdash A(i) : \mathcal{U}(\ell)$), `left_id` ($\Gamma_2 \vdash a_0 : L$), `right_id` ($\Gamma_3 \vdash a_1 : R$).
- **Checks:** `dimension` is a dimension entry, `family_id.type` is `CC_U(l)`, $L \equiv_\alpha A(0)$, $R \equiv_\alpha A(1)$, discharging $i$ from $\Gamma_1$ succeeds (note that because $\mathcal{U}(\ell)$ has no free dimensions, $i$ cannot occur in $\ell$), and $(\Gamma_1 \setminus \{i\}), \Gamma_2, \Gamma_3$ merge.
- **Result (`CC_FACT_TYPING`):** $(\Gamma_1 \setminus \{i\}) \cup \Gamma_2 \cup \Gamma_3 \vdash \text{Path}(i, A(i), a_0, a_1) : \mathcal{U}(\ell)$.

#### `CC_INSTR_PATH_LAMBDA` (`25`) — `cc_instr_path_lambda(k, dimension, body_id)`
- **Inputs:** Dimension entry `dimension` ($i$), typing judgement `body_id` ($\Gamma, i \vdash b(i) : A(i)$).
- **Checks:** `dimension` is a dimension entry, `body_id` is `CC_FACT_TYPING`, and discharging $i$ from $\Gamma$ succeeds.
- **Result (`CC_FACT_TYPING`):** $\Gamma \setminus \{i\} \vdash \text{PLam}(i, A(i), b(i)) : \text{Path}(i, A(i), b(0), b(1))$.

#### `CC_INSTR_PATH_APPLY` (`26`) — `cc_instr_path_apply(k, path_id, dimension, endpoint)`
- **Inputs:** Typing judgement `path_id` ($\Gamma \vdash p : \text{Path}_i(A(i), a_0, a_1)$), dimension entry `dimension` ($j$, or `0` for an endpoint), `unsigned endpoint` ($0$ or $1$ when `dimension == 0`).
- **Checks:** `path_id.type` is `CC_PATH(i, A, a0, a1)`. If `dimension != 0`, `dimension` is a dimension entry $j$ and the interval formula is $r = j$; if `dimension == 0`, `endpoint <= 1` and the interval formula is $r = \varepsilon$.
- **Result (`CC_FACT_TYPING`):** $\Gamma \cup \{j\} \vdash \text{PApp}(r, p, \text{Path}_i(A, a_0, a_1)) : A[r/i]$.

#### `CC_INSTR_PATH_AT` (`39`) — `cc_instr_path_at(k, path_id, interval)`
- **Inputs:** Typing judgement `path_id` ($\Gamma \vdash p : \text{Path}_i(A(i), a_0, a_1)$), `cc_formula_id interval` ($r$).
- **Checks:** `path_id.type` is `CC_PATH(i, A, a0, a1)` and `interval` is a registered formula of sort `CC_INTERVAL` with dimension context $\Delta_r$.
- **Result (`CC_FACT_TYPING`):** $\Gamma \cup \Delta_r \vdash \text{PApp}(r, p, \text{Path}_i(A, a_0, a_1)) : A[r/i]$.

---

### 7. Composition systems, `Comp`, `HComp`, and `Trans`

#### `CC_INSTR_SYSTEM` (`40`) — `cc_instr_system(k, dimension, family_id, base_id)`
- **Inputs:** Dimension entry `dimension` ($i$), typing judgements `family_id` ($\Gamma_1 \vdash A(i) : \mathcal{U}(\ell)$) and `base_id` ($\Gamma_2 \vdash a_0 : A_0$).
- **Checks:** `dimension` is a dimension entry $i$, `family_id.type` is `CC_U(l)`, $A_0 \equiv_\alpha A(0)$, $i \notin \text{fdims}(a_0)$, and $\Gamma_1, \Gamma_2$ merge.
- **Result (`CC_FACT_SYSTEM`):** Publishes an open composition system with `term = CC_COMP(i, A(i), 0, a0)`, `type = A(1)`, `context = Γ₁ ∪ Γ₂`, and `pending = 0`.

#### `CC_INSTR_SYSTEM_TUBE` (`41`) — `cc_instr_system_tube(k, system_id, face, tube_id, adjacency_id)`
- **Inputs:** System judgement `system_id`, `cc_formula_id face` ($\varphi$), typing judgement `tube_id` ($\Gamma_u \vdash u : U$), equality judgement `adjacency_id` ($\Gamma_e \vdash e_0 \equiv e_1 : E$, or `0` when $\varphi = 0$).
- **Checks:**
  - `system_id` is a `CC_FACT_SYSTEM` whose `term` is `CC_COMP(i, A, tubes, a0)` and whose `pending == 0` (all overlaps of the previous tube were resolved).
  - `face` is a `CC_FACE` formula with `length <= 1`.
  - If `face` is $\bot$ (`length == 0`): `adjacency_id` must be `0`; appends `CC_TUBE(0, u)` with `pending = 0`.
  - If `face` has a single clause $C$ (`length == 1`):
    1. $C$ is consistent and does not mention $i$ (`!((C.positive | C.negative) & (1ULL << i))`).
    2. $u$ is already restricted to $C$ (`(ck_free_dims(u) & (C.positive | C.negative)) == 0`).
    3. $U \equiv_\alpha \text{ck\_restrict}(A, C)$.
    4. `adjacency_id` is a `CC_FACT_EQUALITY` with $e_0 \equiv_\alpha u[0/i]$ and $e_1 \equiv_\alpha \text{ck\_restrict}(a_0, C)$.
    5. Face entries in $\Gamma_u$ and $\Gamma_e$ entailed by $C$ are discharged via `ck_instr_on_face`.
    6. Computes the `pending` bitmask of all earlier non-empty tubes whose clause $C_k$ is compatible with $C$ (`((C.positive | C_k.positive) & (C.negative | C_k.negative)) == 0`). Positions count every earlier tube, `0`-face ones included; a compatible tube at position $64$ or above is refused with `CC_ERROR_RESOURCE` (`"A tube may overlap only the first 64 tubes of a system."`).
- **Result (`CC_FACT_SYSTEM`):** Publishes the extended `CC_COMP` system with the new tube appended to `child[1]` and `pending` set to the bitmask of overlapping earlier tubes.

#### `CC_INSTR_SYSTEM_OVERLAP` (`43`) — `cc_instr_system_overlap(k, system_id, position, agreement_id)`
- **Inputs:** System judgement `system_id` (`CC_COMP` or `CC_GLUE_TERM`), `uint32_t position < 64`, equality judgement `agreement_id` ($\Gamma_e \vdash e_0 \equiv e_1 : E$).
- **Checks:** Bit `position` is set in `system_id.pending`. Let $(C_{\text{last}}, u_{\text{last}})$ be the last tube added and $(C_{\text{pos}}, u_{\text{pos}})$ be the tube at index `position`, with overlap clause $C = C_{\text{last}} \wedge C_{\text{pos}}$. Verifies $e_0 \equiv_\alpha \text{ck\_restrict}(u_{\text{last}}, C)$ and $e_1 \equiv_\alpha \text{ck\_restrict}(u_{\text{pos}}, C)$, and discharges face entries entailed by $C$ from $\Gamma_e$ via `ck_instr_on_face`.
- **Result (`CC_FACT_SYSTEM`):** Republishes the system judgement with `pending & ~(1ULL << position)`.

#### `CC_INSTR_COMP` (`42`) — `cc_instr_comp(k, system_id)`
- **Inputs:** System judgement `system_id`.
- **Checks:** `system_id` is a `CC_FACT_SYSTEM` with `term.kind == CC_COMP(i, A, tubes, a0)`, `pending == 0`, and discharging dimension entry $i$ from `system_id.context` succeeds.
- **Result (`CC_FACT_TYPING`):** $\Gamma \setminus \{i\} \vdash \text{Comp}(i, A, \text{tubes}, a_0) : A(1)$.

#### `CC_INSTR_HCOMP` (`51`) — `cc_instr_hcomp(k, system_id)`
- **Inputs:** System judgement `system_id`.
- **Checks:** `system_id` is a `CC_FACT_SYSTEM` with `term.kind == CC_COMP(i, A, tubes, a0)` and `pending == 0`; $i \notin \text{fdims}(A)$; `whnf(A)` is an instance `CC_SORT` of an admitted **higher** sort (`ck_signature_higher`); and discharging $i$ from `system_id.context` succeeds.
- **Result (`CC_FACT_TYPING`):** $\Gamma \setminus \{i\} \vdash \text{HComp}(i, A, \text{tubes}, a_0) : A$.

#### `CC_INSTR_TRANS` (`52`) — `cc_instr_trans(k, system_id, face)`
- **Inputs:** System judgement `system_id`, `cc_formula_id face` ($\varphi$).
- **Checks:** `system_id` is a `CC_FACT_SYSTEM` with `term.kind == CC_COMP(i, A, tubes, a0)` and `pending == 0`; `face` is a `CC_FACE` formula whose clauses $C_0, \dots, C_{m-1}$ match the system's tube faces in exact order, with each tube body $\alpha$-equal to $\text{ck\_restrict}(a_0, C_k)$ (certifying that $A(i)$ is constant on $\varphi$); `whnf(A)` is an instance `CC_SORT` of an admitted **higher** sort; and discharging $i$ from `system_id.context` succeeds.
- **Result (`CC_FACT_TYPING`):** $(\Gamma \setminus \{i\}) \cup \Delta_\varphi \vdash \text{Trans}(i, A, \text{Tube}(\varphi, a_0, 0), a_0) : A(1)$.

---

### 8. Glue types, Glue terms, and `Unglue`

#### `CC_INSTR_GLUE_BASE` (`53`) — `cc_instr_glue_base(k, base_id)`
- **Inputs:** Typing judgement `base_id` ($\Gamma \vdash A : \mathcal{U}(\ell_A)$).
- **Checks:** `base_id.type` is `CC_U(l_A)`.
- **Result (`CC_FACT_SYSTEM`):** Opens a Glue type system with `term = CC_GLUE(A, 0)`, `type = U(l_A)`, `context = Γ`, `pending = 0`.

#### `CC_INSTR_GLUE_PIECE` (`54`) — `cc_instr_glue_piece(k, system_id, face, type_id, equivalence_id)`
- **Inputs:** Glue system `system_id`, `cc_formula_id face` ($\varphi$), typing judgements `type_id` ($\Gamma_T \vdash T : \mathcal{U}(\ell_T)$) and `equivalence_id` ($\Gamma_e \vdash e : E$).
- **Checks:** `system_id` is an open `CC_GLUE` system with `pending == 0`; `face` is `CC_FACE` with `length <= 1`. If `face` has a clause $C$: $C$ is consistent, $T$ and $e$ have no free dimensions in $C$, $E \equiv_\alpha \text{Equiv}(T, \text{ck\_restrict}(A, C))$, face assumptions entailed by $C$ are discharged from $\Gamma_T$ and $\Gamma_e$, and `pending` records earlier pieces whose clause overlaps $C$ (`overlapping`; an overlapping piece at position $64$ or above is refused with `CC_ERROR_RESOURCE`).
- **Result (`CC_FACT_SYSTEM`):** Appends `CC_GLUE_SYSTEM(face, T, e, 0)` to `CC_GLUE.child[1]` and updates the system's universe type to $\mathcal{U}(\max(\ell_T, \ell))$.

#### `CC_INSTR_GLUE_OVERLAP` (`55`) — `cc_instr_glue_overlap(k, system_id, position, types_id, equivalences_id)`
- **Inputs:** Glue system `system_id`, `uint32_t position < 64`, equality judgements `types_id` ($T_{\text{last}}|_C \equiv T_{\text{pos}}|_C$) and `equivalences_id` ($e_{\text{last}}|_C \equiv e_{\text{pos}}|_C$).
- **Checks:** Bit `position` is set in `system_id.pending`; verifies both equalities on the overlap clause $C = C_{\text{last}} \wedge C_{\text{pos}}$ and discharges face assumptions entailed by $C$.
- **Result (`CC_FACT_SYSTEM`):** Clears bit `position` in `pending`.

#### `CC_INSTR_GLUE` (`56`) — `cc_instr_glue(k, system_id)`
- **Inputs:** Glue system `system_id`.
- **Checks:** `system_id` is a `CC_FACT_SYSTEM` with `term.kind == CC_GLUE` and `pending == 0`.
- **Result (`CC_FACT_TYPING`):** $\Gamma \vdash \text{Glue}(A, \text{pieces}) : \mathcal{U}(\ell)$.

#### `CC_INSTR_GLUE_TERM_BASE` (`57`) — `cc_instr_glue_term_base(k, type_id, base_id)`
- **Inputs:** Typing judgements `type_id` ($\Gamma_1 \vdash G : \mathcal{U}(\ell)$ where $G = \text{Glue}(A, \text{pieces})$) and `base_id` ($\Gamma_2 \vdash a : A'$).
- **Checks:** `type_id.term` is `CC_GLUE(A, pieces)`, `type_id.type` is `CC_U(l)`, $A' \equiv_\alpha A$, and $\Gamma_1, \Gamma_2$ merge.
- **Result (`CC_FACT_SYSTEM`):** Opens a Glue term system with `term = CC_GLUE_TERM(G, a, 0)`, `type = G`, `pending = 0`.

#### `CC_INSTR_GLUE_TERM_PIECE` (`58`) — `cc_instr_glue_term_piece(k, system_id, value_id, image_id)`
- **Inputs:** Glue term system `system_id`, typing judgement `value_id` ($\Gamma_v \vdash t : T'$), equality judgement `image_id` ($\Gamma_e \vdash e_0 \equiv e_1 : E$, or `0` if the piece's face is `0`).
- **Checks:** `system_id` is an open `CC_GLUE_TERM` system with `pending == 0`. Selects the next unhandled piece $(\varphi \mapsto (T, e))$ of $G$. If $\varphi$ has clause $C$: verifies $t$ has no free dimensions in $C$, $T' \equiv_\alpha T$, $e_0 \equiv_\alpha \pi_1(e)(t)$, and $e_1 \equiv_\alpha \text{ck\_restrict}(a, C)$, discharges face entries entailed by $C$, and computes `pending` overlaps with earlier tubes (`overlapping`, with the same position bound; they are resolved using `cc_instr_system_overlap`).
- **Result (`CC_FACT_SYSTEM`):** Appends `CC_TUBE(φ, t, 0)` to `CC_GLUE_TERM.child[2]`.

#### `CC_INSTR_GLUE_TERM` (`59`) — `cc_instr_glue_term(k, system_id)`
- **Inputs:** Glue term system `system_id`.
- **Checks:** `system_id` is a `CC_FACT_SYSTEM` with `term.kind == CC_GLUE_TERM`, `pending == 0`, and its tube list has the exact same length as $G$'s piece list.
- **Result (`CC_FACT_TYPING`):** $\Gamma \vdash \text{GlueTerm}(G, a, \text{tubes}) : G$.

#### `CC_INSTR_UNGLUE` (`60`) — `cc_instr_unglue(k, value_id)`
- **Inputs:** Typing judgement `value_id` ($\Gamma \vdash g : G$).
- **Checks:** $G$ has kind `CC_GLUE(A, pieces)`.
- **Result (`CC_FACT_TYPING`):** $\Gamma \vdash \text{Unglue}(G, g) : A$.

---

### 9. Declared inductive and higher inductive types (H1)

#### `CC_INSTR_SIGNATURE_BEGIN` (`64`) — `cc_instr_signature_begin(k, former, modifier, sort_symbol, recorded)`
- **Inputs:** Closed typing judgement `former` ($\vdash F : \mathcal{U}(\dots)$), truncation `uint32_t modifier` (`CC_UNTRUNCATED == 0`, or $n + 2 \le \text{CC\_TRUNCATION\_MAX} + 2 = 16$ for $\text{trunc}(n)$ with $n \ge -1$), `uint32_t sort_symbol != 0`, bitmask `uint32_t recorded`.
- **Checks:**
  - `CC_EXTENSION_H1` is enabled (on by default).
  - `former` is a closed `CC_FACT_TYPING` judgement ($\Gamma = \varnothing$).
  - $F$ unpacks into $k \le 24$ `CC_LPI` binders $x_0, \dots, x_{k-1} < \omega$ followed by $m \le 64$ `CC_PI` binders $(p_0 : P_0) \dots (p_{m-1} : P_{m-1})$ ending in a universe $\mathcal{U}(\ell)$, with all $k + m$ parameter symbols and `sort_symbol` pairwise distinct.
  - Every unrecorded (erased) universe parameter $x_j$ (`!((recorded >> j) & 1)`) has a determining occurrence: at least one term parameter $P_i$ whose $\Pi$-codomain end is syntactically $\mathcal{U}(x_j)$.
- **Result (`CC_FACT_SIGNATURE`):** Allocates signature slot `index` and publishes a signature judgement with `term = CC_SORT(index, 0, 0)` and `type = F`.

#### `CC_INSTR_SIGNATURE_CONSTRUCTOR` (`65`) — `cc_instr_signature_constructor(k, signature_id, type_id, symbol)`
- **Inputs:** Latest open signature judgement `signature_id`, constructor type judgement `type_id` ($\Gamma \vdash T : \mathcal{U}(\ell_T)$), fresh `uint32_t symbol != 0`.
- **Checks:**
  - `signature_id` is the latest judgement for this open signature (`constructor_count < 256`).
  - `type_id.type` is `CC_U(l_T)` with $\ell_T \equiv \ell$ in level normal form (`ck_level_equal`).
  - Every entry in $\Gamma$ is one of the signature's level parameters, term parameters (at its declared type), the sort entry `sort_symbol : U(l)`, or an earlier constructor `c_m : T_m` (`admission_context`).
  - $T$ mentions no erased universe parameter (`!(recorded >> j & 1)`).
  - `constructor_shape` validates that $T$ has H1 normal form: $a$ non-recursive data arguments (not mentioning `sort_symbol`, an earlier constructor, or an earlier position), followed by $b$ strictly positive recursive position arguments $\Pi(\vec{y} : \vec{C}).\, B$ where $\vec{C}$ are data (at most `CC_CONSTRUCTOR_ARGUMENTS` $= 64$ binders per position) and $B$ is an iterated path cube over `sort_symbol` of at most `CC_CONSTRUCTOR_DIMENSIONS` $= 16$ layers ($a + b \le 64$), ending in an iterated path cube of dimension $d \le 16$ over `sort_symbol` whose endpoint boundaries are well-formed constructor expressions over the parameters, data arguments, recursive arguments, and path coordinates.
- **Result (`CC_FACT_SIGNATURE`):** Appends the constructor to the signature and publishes the next `CC_FACT_SIGNATURE` judgement with `pending = constructor_count`.

#### `CC_INSTR_SIGNATURE_CLOSE` (`66`) — `cc_instr_signature_close(k, signature_id)`
- **Inputs:** Latest open signature judgement `signature_id`.
- **Checks:** If `modifier != CC_UNTRUNCATED`, generates and validates the $(n + 2)$-step iterated path squash constructor (`squash_type`) and appends it as a `generated = true` constructor.
- **Result (`uint32_t`):** Marks `s->admitted = true` and returns the 1-based signature `index`.

#### `CC_INSTR_SORT_BEGIN` (`67`), `CC_INSTR_SORT_LEVEL` (`68`), and `CC_INSTR_SORT_PARAMETER` (`69`)
- **Signatures:**
  - `cc_instr_sort_begin(k, index)`
  - `cc_instr_sort_level(k, instance, level)`
  - `cc_instr_sort_parameter(k, instance, parameter)`
- **Checks & Multi-step Flow:**
  1. `SortBegin` checks that `index` names an admitted signature $S$.
  2. `SortLevel` supplies each recorded universe level (in parameter order) as a finite level $\ell_r < \omega$ whose normal form has a constant below `CC_LEVEL_MAX` (`ck_instr_finite_level`; unlike `LevelApply`, the constant `65535` itself is refused as a resource error), before any term parameters are given.
  3. `SortParameter` supplies each term parameter $\Gamma_i \vdash a_i : A_i$ in order.
  4. While levels or parameters remain, each step publishes a `CC_FACT_INSTANCE` judgement (`kind == 5`).
  5. Once all recorded levels and all $m$ term parameters are supplied (`complete_instance`), the kernel reads each erased universe parameter $x_j$ from the final universe of its first determining parameter's actual type $A_i$ (again a finite level with constant below `CC_LEVEL_MAX`), checks that every $A_i$ is $\alpha$-equal to the telescope type $P_i[\rho, a_0, \dots, a_{i-1}]$, takes the sort's own level $\ell[\rho]$ to normal form (of any tier, with constant below `CC_LEVEL_MAX`; `ck_instr_level`), and publishes the `CC_FACT_TYPING` judgement:
     $$\Gamma \vdash \text{Sort}(\text{index},\; [a_0, \dots, a_{m-1}],\; [\ell_{r_0}, \dots]) : \mathcal{U}(\ell[\rho])$$

#### `CC_INSTR_CONSTRUCT` (`70`) — `cc_instr_construct(k, instance, constructor)`
- **Inputs:** Complete sort instance typing judgement `instance` ($\Gamma \vdash I : \mathcal{U}(\dots)$), `uint32_t constructor` ($k < \text{constructor\_count}$).
- **Checks:** $I$ is a complete instance `CC_SORT` of an admitted signature $S$ and $k < s\text{->constructor\_count}$. Computes the simultaneously substituted constructor type $T_k[s := I,\; \vec{x} := \rho,\; \vec{p} := \vec{a},\; c_m := \text{Con}(m; I)]$.
- **Result (`CC_FACT_TYPING`):** $\Gamma \vdash \text{Con}(k, I) : T_k[s := I, \dots]$.

#### `CC_INSTR_ELIMINATOR` (`71`), `CC_INSTR_ELIMINATOR_CLAUSE` (`72`), and `CC_INSTR_ELIMINATOR_CLOSE` (`73`)
- **Signatures:**
  - `cc_instr_eliminator(k, motive_id)`
  - `cc_instr_eliminator_clause(k, eliminator, clause)`
  - `cc_instr_eliminator_close(k, eliminator)`
- **Checks & Multi-step Flow:**
  1. `Eliminator` checks that `motive_id` is a typing judgement $\Gamma_M \vdash M : \Pi(z : I).\, \mathcal{U}(\ell)$ where $I$ is a complete instance `CC_SORT` of an admitted signature $S$, and publishes a `CC_FACT_ELIMINATOR` judgement (`pending = 0`) whose `type` is the expected type of clause $0$, $\text{ClauseType}_0(M)$ (or $\Pi(z : I).\, M(z)$ at once when $S$ has no constructors, so that `EliminatorClose` then succeeds with no clause).
  2. For each constructor $k = 0 \dots n - 1$, `EliminatorClause` checks that `clause` ($\Gamma_k \vdash m_k : C_k$) has $C_k \equiv_\alpha \text{ClauseType}_k(M, m_0, \dots, m_{k-1})$ (where $\text{ClauseType}_k$ binds the constructor's data arguments, recursive position arguments $q_j$, displayed induction hypotheses $\bar{q}_j$, and path coordinates $i_1, \dots, i_d$, with displayed boundaries in which each position is shown by its displayed variable and each earlier constructor by its clause), and advances `pending` to $k + 1$ with `type` set to $\text{ClauseType}_{k+1}$ (or $\Pi(z : I).\, M(z)$ when $k + 1 = n$).
  3. `EliminatorClose` verifies `pending == s->constructor_count` (including the generated squash clause if truncated), reverses the accumulated clause list into forward constructor order, and publishes the `CC_FACT_TYPING` judgement:
     $$\Gamma \vdash \text{Elim}(\text{index},\; M,\; [m_0, \dots, m_{n-1}]) : \Pi(z : I).\, M(z)$$

---

### 10. Equality, conversion, cumulativity, $\eta$, `Step`, and `Replace`

#### `CC_INSTR_REFL` (`29`) — `cc_instr_refl(k, typing_id)`
- **Inputs:** Typing judgement `typing_id` ($\Gamma \vdash t : T$).
- **Result (`CC_FACT_EQUALITY`):** $\Gamma \vdash t \equiv t : T$.

#### `CC_INSTR_SIDE` (`33`) — `cc_instr_side(k, equality, side)`
- **Inputs:** Equality judgement `equality` ($\Gamma \vdash a \equiv b : T$), `unsigned side` (`0` or `1`).
- **Result (`CC_FACT_TYPING`):** $\Gamma \vdash a : T$ (when `side == 0`) or $\Gamma \vdash b : T$ (when `side == 1`).

#### `CC_INSTR_SYMMETRY` (`34`) — `cc_instr_symmetry(k, equality)`
- **Inputs:** Equality judgement `equality` ($\Gamma \vdash a \equiv b : T$).
- **Result (`CC_FACT_EQUALITY`):** $\Gamma \vdash b \equiv a : T$.

#### `CC_INSTR_TRANSITIVITY` (`35`) — `cc_instr_transitivity(k, first, second)`
- **Inputs:** Equality judgements `first` ($\Gamma_1 \vdash a \equiv b : T_1$) and `second` ($\Gamma_2 \vdash b' \equiv c : T_2$).
- **Checks:** $b' \equiv_\alpha b$, $T_2 \equiv_\alpha T_1$, and $\Gamma_1, \Gamma_2$ merge.
- **Result (`CC_FACT_EQUALITY`):** $\Gamma_1 \cup \Gamma_2 \vdash a \equiv c : T_1$.

#### `CC_INSTR_CONVERT` (`36`) — `cc_instr_convert(k, typing_id, equality)`
- **Inputs:** Typing judgement `typing_id` ($\Gamma_1 \vdash t : A$), equality judgement `equality` ($\Gamma_2 \vdash A' \equiv B : \mathcal{U}(\ell)$).
- **Checks:** `equality.type` is `CC_U(l)`, $A \equiv_\alpha A'$, and $\Gamma_1, \Gamma_2$ merge.
- **Result (`CC_FACT_TYPING`):** $\Gamma_1 \cup \Gamma_2 \vdash t : B$.

#### `CC_INSTR_LIFT` (`37`) — `cc_instr_lift(k, typing_id, type_id)`
- **Inputs:** Typing judgements `typing_id` ($\Gamma_1 \vdash t : A$) and `type_id` ($\Gamma_2 \vdash B : \mathcal{U}(\ell)$).
- **Checks:** `type_id.type` is `CC_U(l)`, `ck_syntactic_cumulative(k, A, B)` ($A \preceq B$) holds, and $\Gamma_1, \Gamma_2$ merge.
- **Result (`CC_FACT_TYPING`):** $\Gamma_1 \cup \Gamma_2 \vdash t : B$.

#### `CC_INSTR_ETA` (`32`) — `cc_instr_eta(k, typing_id)`
- **Inputs:** Typing judgement `typing_id` ($\Gamma \vdash t : T$).
- **Checks:** $T$ must have kind `CC_PI`, `CC_LPI`, `CC_SIGMA`, `CC_PATH`, or `CC_GLUE`.
- **Result (`CC_FACT_EQUALITY`):** Publishes $\Gamma \vdash t \equiv \eta(t) : T$, where $\eta(t)$ is:
  - for $T = \Pi(x : A).\, B$: $\lambda(z : A).\, t(z)$ (`z` fresh);
  - for $T = \forall(x < \omega).\, B$: $\Lambda(z < \omega).\, t\,\{z\}$ (`z` fresh);
  - for $T = \Sigma(x : A).\, B$: $(\pi_1(t), \pi_2(t))_T$;
  - for $T = \text{Path}_i(A(i), a_0, a_1)$: $\langle j \rangle_{A(j)}\, (t \mathbin{@}_T j)$ ($j$ fresh dimension);
  - for $T = \text{Glue}\,[\varphi_m \mapsto (T_m, e_m)]\, A$: $\text{glue}_T([\varphi_m \mapsto t],\, \text{unglue}_T(t))$.

#### `CC_INSTR_STEP` (`30`) — `cc_instr_step(k, id, side, position, depth, rule)`
- **Inputs:** Typing or equality judgement `id`, `unsigned side` (`0` = `term`/LHS, `1` = `other`/RHS of an equality, `2` = `type`), child-index path `const uint8_t *position` of length `size_t depth <= 1024`, `cc_step_rule rule`.
- **Checks:** `id` is `CC_FACT_TYPING` or `CC_FACT_EQUALITY`; `position[0..depth-1]` locates a valid subterm $s$ inside the chosen `side`; `contract(k, s, rule)` succeeds (see [Targeted single-step rules](#1-targeted-single-step-rules-cc_instr_step-in-instruction_equalityc)).
- **Result:** Republishes a judgement of the same kind (`CC_FACT_TYPING` or `CC_FACT_EQUALITY`) and context with the subterm at `position` on `side` replaced by its contractum $s'$. (To derive an equality $t \equiv t' : A$ from $t : A$, apply `Refl` first and then `Step` on `side = 1`.)

#### `CC_INSTR_REPLACE` (`31`) — `cc_instr_replace(k, id, side, position, depth, by)`
- **Inputs:** Typing or equality judgement `id`, `unsigned side` (`0`, `1`, or `2`), child-index path `position[0..depth-1]`, equality judgement `by` ($\Gamma_{\text{by}} \vdash a \equiv b : T'$).
- **Checks:**
  - `id` is `CC_FACT_TYPING` or `CC_FACT_EQUALITY`, and `by` is `CC_FACT_EQUALITY`.
  - The subterm $s$ at `position[0..depth-1]` on `side` of `id` satisfies $s \equiv_\alpha a$.
  - If `position` points to `CC_PAPP.child[1]` (the path-type annotation), $b$ must also have kind `CC_PATH`.
  - Walking outward along the binders crossed by `position`, any term/level binder $(x : D)$ or dimension binder $i$ whose bound name occurs free in $a$, $b$, or an inner discharged entry's type must match a corresponding entry in $\Gamma_{\text{by}}$ (with type $\alpha$-equal to $D$ for term binders); those entries are discharged from $\Gamma_{\text{by}}$, and replacement inside a tube body that mentions the enclosing composition's bound dimension is refused.
- **Result:** Republishes `id` in context $\Gamma_{\text{id}} \cup (\Gamma_{\text{by}} \setminus \text{discharged})$ with the subterm at `position` on `side` replaced by $b$.

---

### 11. Retired instruction opcodes

The eleven enum constants `CC_INSTR_NAT` (`2`), `CC_INSTR_ZERO` (`3`), `CC_INSTR_SUCC` (`4`), `CC_INSTR_NAT_ELIM` (`5`), `CC_INSTR_PUSHOUT` (`44`), `CC_INSTR_PUSH_POINT` (`45`), `CC_INSTR_PUSH_PATH` (`46`), `CC_INSTR_PUSH_ELIM` (`47`), `CC_INSTR_W` (`48`), `CC_INSTR_SUP` (`49`), and `CC_INSTR_W_ELIM` (`50`) remain in `cc_instruction` for ABI numbering compatibility; their C entry points have been removed in favor of H1 declared types.

---

## Reduction, normalization, and elimination

The kernel separates **trusted equality steps** (invoked explicitly by `cc_instr_step` at a chosen position), **call-by-name weak-head reduction** (`ck_whnf`), **compact single-step exposure** (`ck_expose`), and **full normalization** (`ck_normal`).

### 1. Targeted single-step rules (`CC_INSTR_STEP` in `instruction_equality.c`)

| `cc_step_rule` | Redex $s$ | Contractum $s'$ and side conditions |
|---|---|---|
| `CC_STEP_BETA` (`1`) | `App(Lam(x, A, b), a)`<br>`LApp(LLam(x, B, b), l)` | `ck_substitute(k, b, x, a)`<br>`ck_level_instantiate(k, b, x, l)` |
| `CC_STEP_DELTA` (`2`) | `DefRef(idx)` | `k->definitions[idx].value` |
| `CC_STEP_IOTA` (`3`) | `Fst(Pair(T, a, b))`<br>`Snd(Pair(T, a, b))`<br>`UnitRec(M, pt, Point)`<br>`SumRec(M, l, r, Inl(T, v))`<br>`SumRec(M, l, r, Inr(T, v))`<br>`App(Elim(sig, M, ms), c)` | `a`<br>`b`<br>`pt`<br>`App(l, v)`<br>`App(r, v)`<br>`ck_eliminate(k, Elim(sig, M, ms), c, false, &reduced)` when $c$ is already a constructor or path-applied constructor (`weak = false`): the clause method applied to the arguments and induction hypotheses, not $\beta$-reduced |
| `CC_STEP_PATH` (`4`) | `PApp(r, PLam(i, A, b), _)`<br>`PApp(0, p, Path(i, A, l, r))`<br>`PApp(1, p, Path(i, A, l, r))` | `ck_dimension_substitute(k, b, i, r)` (tried first, at any $r$)<br>`l` (uses stored Path-type annotation `child[1]`, when `p` is not written as a path lambda)<br>`r` (likewise) |
| `CC_STEP_NORMALIZE` (`5`) | Any term $s$ | `ck_normal(k, s)` |
| `CC_STEP_WHNF` (`6`) | Any term $s$ | `ck_whnf(k, s)` |
| `CC_STEP_FACE` (`7`) | `Comp(i, A, tubes, a0)` with `(1 ↦ u)` in `tubes`<br>`HComp(i, A, tubes, a0)` with `(1 ↦ u)` in `tubes`<br>`Trans(i, A, Tube(1, a0), a0)` | `ck_endpoint_term(k, u, i, 1)`<br>`ck_endpoint_term(k, u, i, 1)`<br>`a0` |
| `CC_STEP_GLUE` (`8`) | `GlueTerm(G, base, [φ ↦ t])` | Contracts via `ck_glue_step` to $b$ when `base` reduces to `Unglue(G', b)` (possibly through nested Glue steps) and $G$ and $G'$ agree (compared whole) and, for every clause $C$ of $\varphi$, $t|_C$ and $b|_C$ agree under `normal_agree` |
| `CC_STEP_SPLIT` (`9`) | `Comp` or `HComp` with multi-clause or `0`-face tubes | Splits each multi-clause tube $[\varphi_1 \vee \varphi_2 \mapsto u]$ into single-clause tubes $[\varphi_1 \mapsto u, \varphi_2 \mapsto u]$ and drops `0`-face tubes (`ck_clause_tubes`) |

### 2. Weak-head normal form (`ck_whnf` in `term_normalize.c`)

`ck_whnf(k, term)` reduces a term to its weak-head normal form by call-by-name, memoized by exact handle in `k->weak_cache`. The worker `weak` performs one head step and either returns a final head or hands back a continuation term, which the driver loop `weak_tails` reduces next; the loop records the terms it passes through, up to `WEAK_MAX_TAILS` (`16384`) of them, so that the final head is cached for all of those; later tails still reduce but are not cached. Reducing the head of an eliminated subterm (the function of `CC_APP`/`CC_LAPP`, the pair of `CC_FST`/`CC_SND`, the path of `CC_PAPP`, the scrutinee of a recursor) is a recursive `ck_whnf` call, a step of the recursion guard `ck_enter` (see [Verification and limits](#verification-and-limits)); there is no explicit stack of elimination frames:

1. **Definitions:** `CC_DEFREF(idx)` unfolds to `k->definitions[idx].value`.
2. **Eliminations:** `CC_APP(f, a)` reduces $f$ to WHNF; on `CC_LAM(x, A, body)` it continues with `ck_substitute(k, body, x, a)`, on `CC_ELIM(sig, M, clauses)` it runs `ck_eliminate(k, Elim(sig, M, clauses), a, true, &reduced)` (`weak = true`, which reduces `a` to WHNF first), and otherwise it returns the neutral application. `CC_LAPP(f, l)` reduces $f$ and, on `CC_LLAM(x, B, body)`, continues with `ck_level_instantiate(k, body, x, l)`. `CC_FST`/`CC_SND` reduce the pair and, on `CC_PAIR(T, a, b)`, continue with `a` or `b`.
3. **Path endpoints and path $\beta$:** `CC_PAPP(r, p, path_type)` with $r = 0$ or $r = 1$ and `path_type` a `CC_PATH(i, A, l, r_end)` continues with `l` or `r_end` without reducing a neutral $p$. Otherwise it reduces $p$ to WHNF and, on `CC_PLAM(i, A, body)`, continues with `ck_dimension_substitute(k, body, i, r)`. An unannotated `CC_PAPP` (raw syntax with `child[1] == 0`) reduces only when $p$'s WHNF is a path lambda; a neutral path there is an error (`"Unchecked path application reached reduction."`).
4. **Recursors:**
   - `CC_UNITREC(M, pt, v)`: reduces $v$ to WHNF; if `whnf(v) == CC_POINT`, continues with `pt`.
   - `CC_SUMREC(M, l, r, s)`: reduces $s$ to WHNF; if `whnf(s)` is `CC_INL(_, v)` or `CC_INR(_, v)`, continues with `App(l, v)` or `App(r, v)`.
5. **Glue reductions:**
   - `CC_GLUE(A, pieces)` and `CC_GLUE_TERM(G, a, tubes)`: drops any piece/tube with face `0`; if any piece/tube has top face `1`, reduces immediately to its `child[0]` ($T$ or $t$).
   - `CC_UNGLUE(G, g)`: $G$ must be a `CC_GLUE` node as written (it is not reduced); if it has a top-face (`1`) piece $(T, e)$, continues with $\pi_1(e)(g)$; otherwise reduces $g$ to WHNF, and if `whnf(g)` is `CC_GLUE_TERM(_, base, _)`, continues with `base`.
6. **Syntactic $\eta$-contractions in `ck_whnf`:**
   - `Pair(T, Fst(p), Snd(p'))` $\to p$ when `ck_alpha_equal(k, p, p')`.
   - `Lam(x, A, App(f, Var(x)))` $\to f$ when $x \notin \text{fv}(f)$.
   - `LLam(x, B, LApp(f, Var(x)))` $\to f$ when $x \notin \text{fv}(f)$.
   - `PLam(i, A, PApp(i, p, _))` $\to p$ when $i \notin \text{fdims}(p)$.
   - `GlueTerm(G, b, tubes)` $\to p$ when `whnf(b)` is `Unglue(G', p)`, `ck_alpha_equal(k, G, G')`, and every non-empty tube $(\varphi \mapsto t)$ satisfies `ck_alpha_equal(k, t, ck_restrict(k, p, C))` on each clause $C \in \varphi$.
7. **Cubical operations:** `CC_COMP` dispatches to `ck_reduce_composition`; `CC_HCOMP` and `CC_TRANS` dispatch to `ck_hit_reduce`. Each returns a head already in WHNF, or the neutral term.

### 3. Compact head exposure (`ck_expose` in `term_expose.c`)

`ck_hit_reduce`, its only caller (no instruction uses it), applies `ck_expose(k, term)` to the `HComp` or `Trans` term itself, for the top-face rule; constructor heads are found by `ck_whnf` of the base. It performs at most one of these contractions and otherwise returns the term unchanged: a top-face (`1`) tube on `Comp`/`HComp` (to $u(1)$) or on `Trans` (to its base); a `CC_PAPP` at `0` or `1` whose annotation is a `CC_PATH` (to the recorded endpoint); a `CC_APP` whose function's WHNF is a `CC_LAM` (to the substituted body); a `CC_FST`/`CC_SND` whose pair's WHNF is a `CC_PAIR` (to the component). It computes the head of the function or pair with `ck_whnf`, but it never unfolds a `CC_DEFREF` at the root, never contracts level applications, path lambdas, or Glue, and has no size bound and no arena rollback.

### 4. Full normalization (`ck_normal` in `term_normalize.c`)

`ck_normal(k, term)` computes a strong normal form under binders using an explicit worklist (`normal_stack`), memoized by exact handle in `k->normal_cache`:

1. Reduces the current node via `ck_whnf`.
2. For partial bodies (`CC_TUBE` and `CC_GLUE_SYSTEM`), `normal_restrict` computes the intersection of endpoint equations common to **all** clauses of the piece's face formula $\varphi$:
   $$\text{common\_pos} = \bigcap_{C \in \varphi} C.\text{positive}, \qquad \text{common\_neg} = \bigcap_{C \in \varphi} C.\text{negative}$$
   and restricts the partial body (`child[0]`, and `child[1]` on `CC_GLUE_SYSTEM`) by that common clause before normalizing its children.
3. Recursively normalizes all child slots (including under $\lambda$, $\Pi$, $\Sigma$, $\Lambda$, $\forall$, $\langle i \rangle$, and `Comp`/`HComp`/`Trans`).
4. On rebuilding a `CC_GLUE_TERM`, checks Glue $\eta$ (`NORMAL_GLUE`) by comparing each normalized tube body against the normalized clause-restricted candidate `ck_normal(k, ck_restrict(k, p, C))`.
5. If rebuilding a node changes any child and creates a new redex (for example, a restricted wall inside a composition became `1`, or a constructor argument simplified), `ck_normal` loops to normalize the rebuilt node.

### 5. Dependent elimination of H1 declared types (`eliminators.c`)

Let $E = \text{elim}_S(M, [m_0, \dots, m_{n-1}])$ be an admitted eliminator for signature $S$ with motive $M : \Pi(x : S(\vec{p})).\, \mathcal{U}(\ell)$. When applied to a scrutinee $s$, `ck_eliminate(k, E, s, weak, &reduced)` (reducing $s$ via `ck_whnf` first when `weak == true`) handles two cases:

1. **Constructor or path-constructor application ($s = c_k(I(\vec{p}))(t_1, \dots, t_a, q_1, \dots, q_b) \mathbin{@} r_1 \dots \mathbin{@} r_d$):**
   - Unpacks the constructor index $k$, the non-recursive arguments $t_1, \dots, t_a$, the recursive arguments $q_1, \dots, q_b$ (where $q_j : \Pi(\vec{y} : \vec{C}_j).\, B_j$), and the applied interval formulas $r_1, \dots, r_d$ ($0 \le d = \text{dimensions}$).
   - For each recursive argument $q_j$, `lifted` lifts elimination through its result cube $B_j$ to build the induction hypothesis:
     $$\bar{q}_j = \lambda(y_1 : C_{j,1}) \dots \lambda(y_r : C_{j,r}).\; \text{lift}_{B_j}\bigl(E, q_j(y_1, \dots, y_r)\bigr)$$
     At the sort instance $I$, $\text{lift}_I(E, v) = E(v)$. At a path cube $B = \text{Path}_i(B'(i), b_0, b_1)$, it chooses a fresh dimension $h$ and constructs
     $$\text{lift}_B(E, v) = \langle h \rangle\, \text{lift}_{B'(h)}(E, v \mathbin{@}_B h).$$
     The `CC_PLAM` family annotation comes from the displayed path type computed by `displayed`; nested path cubes are lifted recursively until reaching $I$. Thus a path-valued position $q : \text{Path}_i(I, a, b)$ contributes $\langle h \rangle\, E(q \mathbin{@} h)$.
   - Applies the $k$-th clause method to them, as a `CC_APP` spine $m_k(t_1, \dots, t_a, q_1, \dots, q_b, \bar{q}_1, \dots, \bar{q}_b)$: the $\bar{q}_j$ are built over fresh variables standing for the arguments, which are then substituted by the actual $t_i$ and $q_j$. The method's own $\lambda$-binders are not contracted: `Step(CC_STEP_IOTA)` returns this application, and separate $\beta$ steps (or `ck_whnf`) reduce it.
   - For each applied path coordinate $r_l$ ($1 \le l \le d$), computes the displayed path type annotation $P_l$ and applies `CC_PAPP(r_l, body, P_l)` (`ck_apply_at`).

2. **Homogeneous composition ($s = \text{hcomp}^j\, S(\vec{p})\, [\psi \mapsto w(j)]\, w_0$, when `weak == true`):**
   - Picks a fresh dimension $k \notin \text{fdims}(s) \cup \text{fdims}(E)$.
   - Forms the homogeneous fill along $k$:
     $$\text{hfill}(k) = \text{hcomp}^j\, S(\vec{p})\, \bigl[\psi \mapsto w(j \wedge k),\; (k = 0) \mapsto w_0\bigr]\, w_0$$
   - Recursively applies $E$ to each tube body $w(k)$ and to the base $w_0$, and composes in the motive family over $\text{hfill}(k)$:
     $$E\bigl(\text{hcomp}^j\, S(\vec{p})\, [\psi \mapsto w(j)]\, w_0\bigr) \;\longrightarrow\; \text{comp}^k\, M(\text{hfill}(k))\, \bigl[\psi \mapsto E(w(k))\bigr]\, E(w_0)$$

---

## Cubical composition, transport, and filling computation

### 1. Derived filling (`ck_fill` in `composition_compute.c`)

Given a heterogeneous composition problem in direction $i$ over family $A(i)$, partial tubes $[\varphi \mapsto u(i)]$, and base $a_0 : A(0)$, the open-box filler at interval coordinate $r$ is derived from `CC_COMP` by picking a fresh dimension $j$ (`ck_fresh_dimension`):

$$\text{fill}^i\, A(i)\, [\varphi \mapsto u(i)]\, a_0\, r \;:=\; \text{comp}^j\, A(r \wedge j)\, \bigl[\varphi \mapsto u(r \wedge j),\; (r = 0) \mapsto a_0\bigr]\, a_0$$

At $r = 0$, the added wall $(r = 0) \mapsto a_0$ has top face `1` and reduces immediately to $a_0$; at $r = 1$, $(r = 0)$ is `0` and $r \wedge j = j$, recovering $\text{comp}^j\, A(j)\, [\varphi \mapsto u(j)]\, a_0$.

### 2. Heterogeneous composition (`ck_reduce_composition` in `composition_compute.c`)

To compute $\text{comp}^i\, A(i)\, [\varphi \mapsto u(i)]\, a_0$, the kernel first checks whether any tube in the list has top face $\varphi = 1$; if so, it returns the weak head of $u(1)$ (`ck_whnf` of `ck_endpoint_term(k, u, i, 1)`), since `weak` takes what it returns as a finished head. Otherwise it reduces $A(i)$ to WHNF (`ck_whnf`; `ck_expose` is not used here) and dispatches on its head:

| Type family $A(i)$ | Reduction of $\text{comp}^i\, A(i)\, [\varphi \mapsto u(i)]\, a_0$ |
|---|---|
| **Unit ($\mathbf{1}$)** | Reduces to $\star$ (`CC_POINT`) when `whnf(a0)` and the WHNF of every non-empty tube body $u(i)$ is $\star$; otherwise stays neutral. |
| **Dependent pair ($\Sigma(x : F(i)).\, G(i, x)$)** | Let $c_1 = \text{comp}^i\, F(i)\, [\varphi \mapsto \pi_1(u(i))]\, \pi_1(a_0)$ and $v(i) = \text{fill}^i\, F(i)\, [\varphi \mapsto \pi_1(u(i))]\, \pi_1(a_0)\, i$. Substitute $v(i)$ for $x$ in $G(i, x)$ to form $c_2 = \text{comp}^i\, G(i, v(i))\, [\varphi \mapsto \pi_2(u(i))]\, \pi_2(a_0)$, and return $(c_1, c_2)_{\Sigma(x:F(1)).G(1,x)}$. |
| **Dependent function ($\Pi(y : F(i)).\, G(i, y)$)** | Pick a fresh variable $x : F(1)$ and fill **backward** in $F(1 - i)$ with no tubes: $v(i) = \text{fill}^i\, F(1 - i)\, [\,]\, x\, (1 - i)$. Return $\lambda(x : F(1)).\, \text{comp}^i\, G(i, v(i))\, [\varphi \mapsto u(i)(v(i))]\, (a_0(v(0)))$. |
| **Universe-polymorphic ($\forall(\ell < \omega).\, G(i, \ell)$)** | Universe levels do not vary with interval coordinates: pick fresh $\ell < \omega$ and return $\Lambda(\ell < \omega).\, \text{comp}^i\, G(i, \ell)\, [\varphi \mapsto u(i)\,\{\ell\}]\, (a_0\,\{\ell\})$. |
| **Path ($\text{Path}_j(P(i, j), l(i), r(i))$)** | Pick a fresh dimension $k \ne i$, apply `@ k` to every tube and to $a_0$, append the two endpoint tubes $(k = 0) \mapsto l(i)$ and $(k = 1) \mapsto r(i)$, and return $\langle k \rangle\, \text{comp}^i\, P(i, k)\, [\varphi \mapsto u(i) \mathbin{@} k,\; (k = 0) \mapsto l(i),\; (k = 1) \mapsto r(i)]\, (a_0 \mathbin{@} k)$. |
| **Disjoint sum ($L(i) + R(i)$)** | ([inductive_composition.c](../../kernel/src/inductive_composition.c)) Reduce $a_0$ and all non-empty tube bodies to WHNF. If all are `Inl(_, v)` (or all are `Inr(_, v)`), push composition inside the injection: $\text{inl}_{L(1)+R(1)}\bigl(\text{comp}^i\, L(i)\, [\varphi \mapsto v(i)]\, v_0\bigr)$. If any head is neutral or heads disagree, remain neutral. |
| **H1 data sort ($S(\vec{p}(i))$ with `!ck_signature_higher(s)`)** | ([inductive_composition.c](../../kernel/src/inductive_composition.c)) Reduce $a_0$ and all non-empty tube bodies to WHNF. If all are applications of the same point constructor $c_k(S(\vec{p}))(v_1, \dots, v_m)$, pack the constructor's parameter-substituted field types into a right-nested $\Sigma$-telescope $T(i) = \Sigma(x_1 : A_1(i)) \dots \Sigma(x_m : A_m(i)).\, \mathbf{1}$ (`ck_telescope`), pack each argument spine into a tuple in $T(i)$ (`ck_tuple`), compute $t_1 = \text{comp}^i\, T(i)\, [\varphi \mapsto \text{tuple}(u(i))]\, \text{tuple}(a_0)$, and reapply $c_k(S(\vec{p}(1)))$ to $\pi_1(t_1), \pi_1(\pi_2(t_1)), \dots$ (`ck_apply_components`). |
| **H1 higher sort ($S(\vec{p}(i))$ with `ck_signature_higher(s)`)** | ([hit_composition.c](../../kernel/src/hit_composition.c)) Decompose heterogeneous `Comp` into `Trans` and `HComp` at $S(\vec{p}(1))$ (`ck_higher_composition`):<br>$$\text{comp}^i\, S(\vec{p}(i))\, [\varphi \mapsto u(i)]\, u_0 \;\longrightarrow\; \text{hcomp}^i\, S(\vec{p}(1))\, \bigl[\varphi \mapsto \text{squeeze}_i(S(\vec{p}), 0, u(i))\bigr]\, \bigl(\text{transp}^i\, S(\vec{p}(i))\, 0\, u_0\bigr)$$<br>where $\text{squeeze}_i(P, \psi, u) = \text{transp}^j\, P[i \vee j / i]\, (\psi \vee (i = 1))\, u$ transports $u(i) : P(i)$ forward along $i \vee j$ to $P(1)$. |
| **Glue ($\text{Glue}\,[\psi(i) \mapsto (T(i), w(i))]\, A(i)$)** | ([glue_compute.c](../../kernel/src/glue_compute.c)) See [Glue and universe composition](#3-glue-and-universe-composition-glue_computec) below. |
| **Universe ($\mathcal{U}(\ell)$)** | ([glue_compute.c](../../kernel/src/glue_compute.c)) Reduces to a `Glue` type over the base type $a_0$: see [Glue and universe composition](#3-glue-and-universe-composition-glue_computec) below. |

### 3. Glue and universe composition (`glue_compute.c`)

- **Glue composition (`ck_glue_composition`):**
  Given $\text{comp}^i\, (\text{Glue}\,[\psi_m(i) \mapsto (T_m(i), w_m(i))]_m\, A(i))\, [\varphi \mapsto u(i)]\, u_0$:
  1. Work clause by clause: each Glue piece's face at $i = 1$ (`formula_at_one`) contributes one pick $(m, C)$ for each clause $C$ of $\psi_m(1)$. Each pick uses $T_m(1)$ and $w_m(1)$ restricted to $C$.
  2. Project the base and tubes to $A(i)$ via `unglue`: $a_0 = \text{unglue}(u_0)$ and $a(i) = \text{unglue}(u(i))$.
  3. Compose in the base type $A(i)$: $a_1' = \text{comp}^i\, A(i)\, [\varphi \mapsto a(i)]\, a_0$.
  4. For each pick $(m, C)$, `partial_fiber_points` builds a partial element of the selected fiber
     $$F_{m,C} = \Sigma(x : T_m(1)|_C).\, \text{Path}_k(A(1), a_1', (w_m(1)|_C).1(x)),$$
     in which only the pick's type and equivalence are restricted to $C$; $A(1)$ and $a_1'$ are written unrestricted, and are restricted with each partial point below, whose whole pair, type annotation included, goes through `ck_restrict`. (`ck_fiber_type` uses CCHM's orientation $\text{Fiber}_f(y) = \Sigma x.\, \text{Path}\, B\, y\, (f\,x)$.)
     - Visit **every** Glue piece $n$ and define its universal face $\delta_n = \forall i.\, \psi_n$ (`cc_face_forall`). For each clause $D$ of $\delta_n$ compatible with $C$, compose $t_n' = \text{comp}^i\, T_n(i)\, [\varphi \mapsto u(i)]\, u_0$ and use Lemma 6 (`preservation`) to build $\alpha_n : \text{Path}_k(A(1), a_1', w_n(1).1(t_n'))$. Restrict $(t_n', \alpha_n)$ to $C \wedge D$ and add it to the partial fiber system; the pieces' agreement on their overlap makes this an element of $F_{m,C}$ there.
     - Visit each composition tube and each clause $D$ of its face compatible with $C$. Add $(u(1), \langle k \rangle\, a_1')$ restricted to $C \wedge D$; on this overlap, $a_1' = a(1)$.
     - Using the contractibility proof $w_m(1).2(a_1')$ with $w_m(1)$ restricted to $C$, `extend_fiber` extends this partial element, defined on $C \wedge ((\bigvee_n \delta_n) \vee \varphi)$, to a fiber element $(t_{m,C}, \alpha_{m,C})$ on $C$.
     For example, a pick from $\psi_m = (i = 1)$ has $\delta_m = 0$, but still receives the constraint from another piece on $\psi_n = (j = 0)$, where $\delta_n = (j = 0)$.
  5. Adjust $a_1'$ in $A(1)$ along a fresh dimension $j$, using one path wall per pick and the constant path $a(1)$ on each composition tube's face:
     $$a_1 = \text{comp}^j\, A(1)\, \bigl[C \mapsto \alpha_{m,C}(j)\text{ for each pick }(m,C),\; \varphi \mapsto a(1)\bigr]\, a_1'$$
  6. Return $\text{glue}_{\text{Glue}(1)}\bigl([C \mapsto t_{m,C}]_{(m,C)},\, a_1\bigr)$.

- **Universe composition (`ck_universe_composition`):**
  Following CCHM §7.1, composition of a system of types $E(i) : \mathcal{U}(\ell)$ over a base type $A : \mathcal{U}(\ell)$ reduces to a `Glue` type by composing the identity equivalence $\text{idEquiv}(E(1))$ along the reversed line $\text{Equiv}(E(1), E(1 - i))$:
  $$\text{comp}^i\, \mathcal{U}(\ell)\, [\varphi \mapsto E(i)]\, A \;\longrightarrow\; \text{Glue}\,\Bigl[\varphi \mapsto \bigl(E(1),\; \text{comp}^i\, \text{Equiv}(E(1), E(1 - i))\, [\,]\, \text{idEquiv}(E(1))\bigr)\Bigr]\, A$$

### 4. Higher inductive `HComp` and `Trans` (`hit_composition.c`)

For a higher sort $I(i) = S(\vec{p}(i))$ (`ck_hit_reduce`):

1. **Degenerate and empty reductions:**
   - $\text{hcomp}^i\, I\, [\varphi \mapsto u(i)]\, u_0$ drops `0`-face tubes; with no tube left it is returned as it is, a canonical value of the higher sort that does not reduce to $u_0$; if any tube has face `1`, it reduces to $u(1)$.
   - $\text{transp}^i\, I(i)\, 1\, u_0 \longrightarrow u_0$.

2. **Commuting `Trans` past `HComp` (`transport_hcomp`):**
   When the base of a transport reduces to $\text{hcomp}^j\, I(0)\, [\psi \mapsto w(j)]\, w_0$ (always renaming $j$ to a fresh dimension $k$), `Trans` distributes into the `HComp` walls and base:
   $$\text{transp}^i\, I(i)\, \varphi\, \bigl(\text{hcomp}^k\, I(0)\, [\psi \mapsto w(k)]\, w_0\bigr) \;\longrightarrow\; \text{hcomp}^k\, I(1)\, \bigl[\psi \mapsto \text{transp}^i\, I(i)\, \varphi\, w(k)\bigr]\, \bigl(\text{transp}^i\, I(i)\, \varphi\, w_0\bigr)$$

3. **Transport of point and path constructors (`sort_transport`):**
   When the base reduces to a constructor application $u_0 = c_m(I(0))(a_1, \dots, a_n) \mathbin{@} r_1 \dots \mathbin{@} r_d$:
   - Pack the parameter-substituted constructor field types into a telescope $T(i) = \Sigma(x_1 : A_1(i)) \dots \mathbf{1}$ and the arguments $a_1, \dots, a_n$ into a tuple $t_0 : T(0)$.
   - Compose the argument tuple with constant tube $[\varphi \mapsto t_0]$:
     $$t_1 = \text{comp}^i\, T(i)\, [\varphi \mapsto t_0]\, t_0, \qquad \text{line}(i) = \text{fill}^i\, T(i)\, [\varphi \mapsto t_0]\, t_0\, i$$
   - Apply $c_m(I(1))$ to the components of $t_1$ and to the interval arguments $r_1, \dots, r_d$ to get $v = c_m(I(1))(\pi(t_1)) \mathbin{@} r_1 \dots \mathbin{@} r_d$.
   - **If $d = 0$ (point constructor):** return $v$ directly.
   - **If $d > 0$ (path constructor):** transporting the arguments along $i$ changes the endpoints of $v$ on the faces $(r_l = \varepsilon)$, so `hit_composition.c` wraps $v$ in an `hcomp` boundary-correction box along a fresh dimension $h$:
     $$\text{transp}^i\, I(i)\, \varphi\, u_0 \;\longrightarrow\; \text{hcomp}^h\, I(1)\, \Bigl[\,(r_l = \varepsilon) \mapsto \text{squeeze}_i\bigl(I, \varphi, b_{l,\varepsilon}(\text{line}(i))\bigr)[1 - h / i],\; \varphi \mapsto u_0\,\Bigr]\, v$$
     At $h = 0$, the squeeze term has $1 - h = 1$ and matches the endpoint $b_{l,\varepsilon}(t_1)$ of $v$; at $h = 1$, it has $1 - h = 0$ and matches $\text{transp}^i\, I(i)\, \varphi\, b_{l,\varepsilon}(t_0)$.

---

## Definitions, inspection, verification, and limits

### Definitions and inspection

`cc_instr_define` (`CC_INSTR_DEFINE`) accepts an already checked, closed typing judgement ($\Gamma = \varnothing$).
It rejects open judgements and duplicate definition symbols; only success
adds the named reference to `k->definitions` and returns a `cc_judgement_id`.
Read that judgement with `cc_kernel_judgement`; its `term` field is the
`cc_term` handle of the `CC_DEFREF` node, which can be passed to `cc_instr_lookup`.
Conversion can expose its body via `Step(Delta)` or `ck_whnf` when required, while ordinary storage keeps the compact
reference. The browser's folded view adds source labels and abbreviations;
the assembly view shows the actual native `cc_term_kind` constructors, operands, and handles.

The workbench replays source to reconstruct the checked context. A beta or delta
step must preserve definitional equality and pass checking again. Source names
are metadata, never authority to change the judgement.

### Verification and limits

`make test` runs native positive and negative regressions. `make sanitize` adds
address and undefined-behaviour sanitizers. JavaScript tests compare native
results with independent reference computations and reject malformed terms.
`npm test` also checks the source corpus once. These checks are evidence against
implementation bugs, not a machine-checked metatheoretic soundness proof.

The native interval representation uses 64 coordinate slots (`0..63`). Allocation errors,
invalid scopes, term depth above `512`, and exhausted explicitly configured budgets reject checking;
they never produce a successful judgement. `CC_ERROR_RESOURCE` (`resource` in
JavaScript) identifies allocation, depth, and representation limits separately
from mismatches, step budgets, and deadlines. Increasing the step budget does
not retry these failures. The elaborator preserves an unresolved limit through
inference and proof search, and negative-test contracts cannot count it as an
expected refusal. Bounded conversion shortcuts may still use a cheaper
alternative; a successful answer requires the ordinary checked derivation.

Native recursion is bounded by `ck_enter` (`term_store.c`). Each recursive
step of `ck_whnf`, `folding_head`, `normal`, `normal_agree` and `ck_glue_step`
(`term_normalize.c`), `canonical_traverse` (`levels.c`), `alpha`
(`term_conversion.c`) and `rebuild` (`instruction_equality.c`) is entered
through it and left through `ck_leave`. The outermost step records its frame's
address in `k->stack_base`, and `k->recursion` counts the steps entered. A
step fails with `CC_ERROR_RESOURCE` and its caller's message (`K336` for
reduction, `K337` normal forms, `K326` comparison, `K322` levels, `K207`
positions) when `CC_RECURSION_LIMIT` (`512`) steps are already entered, or when
its frame is more than `CC_STACK_BUDGET` (4 MiB) from the base. A nested step
never moves the base, and a failed step is not entered. An operation's start,
and a rollback, set `k->recursion` to `0`, so the next step records the base
again. The
bytes bound the stack the kernel runs on, whatever a cycle's frames cost: a
native main thread's 8 MiB, and the WebAssembly build's (`-sSTACK_SIZE` in the
`Makefile`). The steps bound a stack the kernel cannot measure: under
WebAssembly the engine keeps frames on its own stack, about 0.5 MiB in a
Chromium worker, and the cycles measured take 0.6 to 0.9 KiB of it a step,
so their 512 steps end before it does.

An exception out of a WebAssembly export is never the kernel's answer: the
engine's own stack ran out (a `RangeError`), or the instance trapped (a
`WebAssembly.RuntimeError`). It unwinds the kernel's frames without running
them to their end, so the instance's memory may be half changed. The
JavaScript driver therefore never enters such an instance again: `guardModule`
(`web/cubical-kernel.mjs`) wraps each export, and after the first exception
every call throws `KernelFault` (`E668`) without entering. A check on that
instance ends at its next declaration. The pages' worker
(`web/cubical-worker.mjs`) and the command line replace the instance, check
the proof again, and replay the REPL session's entries on the new one; the
workbench's worker reports the failure as fatal and closes, as for a trap.

Full cubical canonicity for every implemented constructor is not claimed by this project.
