# Reading the cubical kernel and AST reference

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
5. [AST primitives (`cc_term_kind`)](#ast-primitives-cc_term_kind)
6. [Binder scopes, substitution, restriction, and comparison](#binder-scopes-substitution-restriction-and-comparison)
7. [Judgements, contexts, and instructions](#judgements-contexts-and-instructions)
8. [Reduction, normalization, and elimination](#reduction-normalization-and-elimination)
9. [Cubical composition, transport, and filling computation](#cubical-composition-transport-and-filling-computation)
10. [Definitions, inspection, verification, and limits](#definitions-inspection-verification-and-limits)

---

## A reading route

1. [instructions.c](../../kernel/src/instructions.c) checks explicit typing premises for contexts, universes, functions, pairs, sums, and definition admission.
2. [instruction_paths.c](../../kernel/src/instruction_paths.c) checks paths, their boundaries, and composition (`Comp`, `HComp`, `Trans`) built one tube at a time.
3. [instruction_glue.c](../../kernel/src/instruction_glue.c) checks gluing data and equivalences through explicit piece-by-piece instructions.
4. [instruction_equality.c](../../kernel/src/instruction_equality.c) checks equality, conversion, universe lifting, $\eta$-laws, and targeted `Step` and `Replace` rules.
5. [signatures.c](../../kernel/src/signatures.c) and [eliminators.c](../../kernel/src/eliminators.c) admit declared inductive and higher inductive types (H1), check sort instances and constructors, and check and compute dependent elimination.
6. [term_conversion.c](../../kernel/src/term_conversion.c) and [levels.c](../../kernel/src/levels.c) supply syntactic $\alpha$-equivalence modulo the interval/face algebra, universe-level normal forms, and syntactic cumulativity.
7. [term_substitution.c](../../kernel/src/term_substitution.c) handles capture-avoiding term substitution, dimension substitution, and face restriction.
8. [term_normalize.c](../../kernel/src/term_normalize.c) and [term_expose.c](../../kernel/src/term_expose.c) implement call-by-name weak-head reduction (`ck_whnf`), full normalization (`ck_normal`), and compact single-step head exposure (`ck_expose`).
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
| `n.payload` | A constructor-specific `uint32_t` parameter (variable symbol, dimension index, formula ID, definition index, or level constant) |
| `n.child[0..3]` | Up to four child term handles (`a, b, c, d`); indexing starts at zero |
| `k->...` | A field of the kernel arena state (`cc_kernel`) |
| `a == b` | Equal handles (identical shared syntax node), stronger than $\alpha$-equivalence or definitional equality |
| `a && b`, `a \|\| b`, `!a` | Logical and, or, not |
| `return false` / `return 0` | Reject the proposed check or abort a computation |

For function application, the checker requires a checked judgement for a function of type
$\Pi(x:A).\, B(x)$ and a checked judgement for an argument of type $A$ in a compatible context, then substitutes the argument for $x$ in $B(x)$. The corresponding C code additionally manages handles, error diagnostics, arena allocation, and step budgets.

---

## Arena handles and AST node layout

All AST terms live in an append-only table `k->nodes` inside a `cc_kernel` arena ([term_internal.h](../../kernel/src/term_internal.h), [term_store.c](../../kernel/src/term_store.c)).

```c
typedef struct {
    cc_term_kind kind;
    uint32_t payload;
    cc_term child[4];
    unsigned depth;
    unsigned char dimensions_known;
    uint64_t symbols;
    uint64_t dims;
} cc_node;
```

- **Handles (`cc_term`):** Node `0` is reserved as the null/absent sentinel (`CC_TERM_INVALID`). Valid handles lie in `1 .. k->count - 1`.
- **Structural sharing (`CC_SHARE_SYNTAX`):** When syntax sharing is enabled (the default), `ck_make` hash-conses `(kind, payload, child[0..3])` in `k->syntax_buckets` so structurally identical AST nodes share a single `cc_term` handle.
- **Depth bound (`CC_MAX_TERM_DEPTH`):** Every node records `depth = 1 + max_i(child[i].depth)`. Any construction exceeding depth `512` fails with `CC_ERROR_RESOURCE`.
- **Fast dependency bitmasks:**
  - `symbols` is a 64-bit Bloom filter over variable and level symbols (`1ULL << (s % 64)`), unioned upward from children. If a symbol's bit is clear in `n.symbols`, that symbol cannot occur anywhere in `n` (bound or free), allowing substitution and comparison to skip subtrees in $O(1)$ time.
  - `dims` is a 64-bit mask over the 64 interval dimensions (`0..63`). Initially it conservatively unions the dimensions mentioned in formulas and children; once `ck_free_dims` completes on a node, `dimensions_known` is set to `1` and `dims` holds the exact bitset of free dimensions.

---

## Interval and face formula algebra

Interval expressions and face constraints are interned in `k->formulas` and referenced by `cc_formula_id` ([cubical.h](../../kernel/include/cubical.h), [formula.c](../../kernel/src/formula.c), [interval.c](../../kernel/src/interval.c), [faces.c](../../kernel/src/faces.c)). Both sorts share the same canonical disjunctive normal form (DNF) representation—an antichain of `cc_clause` structs ordered lexicographically and reduced by absorption—but their generators obey different algebraic laws:

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

- **Constants:** The empty clause list (`count == 0`) is $\bot$ (`0`, interned at ID `0`). A single clause with `positive == 0` and `negative == 0` is $\top$ (`1`, interned at ID `1`).
- **Lattice operations (`formula.c`):**
  - `cc_join(a, b)` ($a \vee b$) concatenates clauses and removes any clause $C'$ that contains another clause $C$ ($C \subseteq C' \implies C \vee C' = C$).
  - `cc_meet(a, b)` ($a \wedge b$) takes pairwise bitset unions of clauses (filtering out contradictory clauses when `sort == CC_FACE`) and applies absorption.
- **Interval operations (`interval.c`):**
  - `cc_reverse(r)` ($1 - r$) applies De Morgan duality by swapping meets and joins and swapping `positive` and `negative` bitsets.
  - `cc_subst_interval(target, i, replacement)` computes $r[s/i]$ by replacing occurrences of $i$ in each clause with $s$ and occurrences of $1 - i$ with `cc_reverse(s)`.
- **Face operations (`faces.c`):**
  - `cc_endpoint(r, is_one)` converts an interval formula $r$ into the face formula $(r = 1)$ or $(r = 0)$ using De Morgan distribution over joins and meets.
  - `cc_subst_face(phi, i, r)` computes $\varphi[r/i]$ by replacing $(i = 1)$ with `cc_endpoint(r, true)` and $(i = 0)$ with `cc_endpoint(r, false)`.
  - `cc_restrict_face(phi, psi)` simplifies $\varphi$ under the assumption $\psi$.
  - `cc_face_forall(i, phi)` computes universal quantification $\forall i.\, \varphi$ by keeping only the clauses of $\varphi$ in which neither $(i = 1)$ nor $(i = 0)$ occurs.
  - `cc_entails(psi, phi)` ($\psi \vdash \varphi$) holds iff for every clause $C_\psi \in \psi$, there exists a clause $C_\varphi \in \varphi$ with $C_\varphi \subseteq C_\psi$.

---

## AST primitives (`cc_term_kind`)

Every AST node is constructed via `cc_kernel_term(k, kind, payload, a, b, c, d)` (`ck_make` in [term_store.c](../../kernel/src/term_store.c)). The kernel enforces the exact arity of each `cc_term_kind`: unused trailing child slots must be `0`, required child slots must be non-zero valid handles, and a handful of list/annotation slots are explicitly optional (`0` when omitted).

### 1. Universes and universe levels (G0)

Universe levels denote ordinals $\omega \cdot \text{tier} + n < \omega^2$ built from constants, finite successors, binary maxima, and level variables bounded below $\omega$ ([levels.c](../../kernel/src/levels.c)).

| `cc_term_kind` | Arity | `payload` | `child[0]` (`a`) | `child[1]` (`b`) | Mathematical notation and role |
|---|---|---|---|---|---|
| `CC_U` (`1`) | 1 | `0` | `level` | — | Universe type $\mathcal{U}(\ell)$ |
| `CC_LCONST` (`32`) | 0 | `(tier << 16) \| n` | — | — | Constant level $\omega \cdot \text{tier} + n$ (`tier <= 255`, `n <= 65535`) |
| `CC_LSUCC` (`33`) | 1 | $k \ge 1$ | `level` | — | Shifted level $\ell + k$ (`k <= 65535`) |
| `CC_LMAX` (`34`) | 2 | `0` | `left` | `right` | Maximum level $\max(\ell_1, \ell_2)$ |
| `CC_LBOUND` (`35`) | 0 | `tier` (`1`) | — | — | Level bound $\text{LBound}(\text{tier})$ (admitted only for `tier == 1`, i.e., $\ell < \omega$) |
| `CC_LPI` (`36`) | 2 | `symbol` | `LBound(1)` | `codomain` | Universe-polymorphic type $\forall(\ell < \omega).\, B(\ell)$ (binds `symbol` in `b`) |
| `CC_LLAM` (`37`) | 2 | `symbol` | `LBound(1)` | `body` | Level abstraction $\Lambda(\ell < \omega).\, t(\ell)$ (binds `symbol` in `b`) |
| `CC_LAPP` (`38`) | 2 | `0` | `fn` | `level` | Level application $f\,\{\ell\}$ (`b` is stored in canonical level syntax) |

**Level normal form (`ck_level_nf`):** Every well-formed level expression reduces by arithmetic to either:
- a **finite form** $(\text{tier} = 0,\; c,\; [(x_1, k_1), \dots, (x_m, k_m)])$ with strictly increasing variable symbols $x_1 < \dots < x_m$ and offsets $k_i \le c$, representing $\max(c, \max_i(x_i + k_i))$; or
- a **transfinite form** $(\text{tier} \ge 1,\; c,\; [])$ representing $\omega \cdot \text{tier} + c$, which absorbs any finite variable $x_i + k_i < \omega$ under $\max$.

Level equality (`ck_level_equal`) and strict/non-strict ordering (`ck_level_leq`, `ck_level_lt`) compare these normal forms directly without search: $\text{nf}_1 \le \text{nf}_2$ at tier $0$ iff $c_1 \le c_2$ and every $(x_i, k_i)$ in $\text{nf}_1$ appears in $\text{nf}_2$ with offset $\ge k_i$.

### 2. Variables and registered definitions

| `cc_term_kind` | Arity | `payload` | Children | Mathematical notation and role |
|---|---|---|---|---|
| `CC_VAR` (`2`) | 0 | `symbol` (`!= 0`) | — | Term variable $x$ or level variable $\ell$ (distinguished by the typing context) |
| `CC_DEFREF` (`14`) | 0 | `def_index` | — | Folded reference to an admitted closed definition (`k->definitions[def_index]`) |

Raw syntax allocation (`cc_kernel_term`) refuses `CC_DEFREF`; a `CC_DEFREF` handle can only be minted by `CC_INSTR_DEFINE` after a closed typing judgement has been checked.

### 3. Dependent functions ($\Pi$) and dependent pairs ($\Sigma$)

| `cc_term_kind` | Arity | `payload` | `child[0]` (`a`) | `child[1]` (`b`) | `child[2]` (`c`) | Mathematical notation and role |
|---|---|---|---|---|---|---|
| `CC_PI` (`3`) | 2 | `symbol` | `domain` $A$ | `codomain` $B$ | — | Dependent function type $\Pi(x : A).\, B(x)$ (binds `symbol` in `b`) |
| `CC_LAM` (`4`) | 2 | `symbol` | `domain` $A$ | `body` $t$ | — | Lambda abstraction $\lambda(x : A).\, t(x)$ (binds `symbol` in `b`) |
| `CC_APP` (`5`) | 2 | `0` | `fn` $f$ | `arg` $u$ | — | Application $f(u)$ (also applies H1 constructors and eliminators) |
| `CC_SIGMA` (`6`) | 2 | `symbol` | `domain` $A$ | `family` $B$ | — | Dependent pair type $\Sigma(x : A).\, B(x)$ (binds `symbol` in `b`) |
| `CC_PAIR` (`7`) | 3 | `0` | `sigma_type` | `first` $u$ | `second` $v$ | Dependent pair $(u, v)_{\Sigma(x:A).B(x)}$ annotated with its $\Sigma$-type |
| `CC_FST` (`8`) | 1 | `0` | `pair` $p$ | — | — | First projection $\pi_1(p)$ |
| `CC_SND` (`9`) | 1 | `0` | `pair` $p$ | — | — | Second projection $\pi_2(p)$ |

Carrying the full $\Sigma$-type in `CC_PAIR.child[0]` ensures that pairs and their composition/normalization steps remain self-contained without needing an external typing context.

### 4. Unit, Void, and disjoint sums

| `cc_term_kind` | Arity | `payload` | `child[0]` (`a`) | `child[1]` (`b`) | `child[2]` (`c`) | `child[3]` (`d`) | Mathematical notation and role |
|---|---|---|---|---|---|---|---|
| `CC_UNIT` (`10`) | 0 | `0` | — | — | — | — | Unit type $\mathbf{1}$ |
| `CC_POINT` (`11`) | 0 | `0` | — | — | — | — | Canonical inhabitant $\star : \mathbf{1}$ |
| `CC_UNITREC` (`24`) | 3 | `0` | `motive` $M$ | `point_val` $p$ | `scrutinee` $t$ | — | Dependent recursor $\text{unitrec}(M, p, t) : M(t)$ |
| `CC_VOID` (`12`) | 0 | `0` | — | — | — | — | Empty type $\mathbf{0}$ |
| `CC_ABORT` (`13`) | 2 | `0` | `target` $A$ | `scrutinee` $v$ | — | — | Ex falso eliminator $\text{abort}_A(v) : A$ for $v : \mathbf{0}$ |
| `CC_SUM` (`25`) | 2 | `0` | `left` $A$ | `right` $B$ | — | — | Disjoint sum $A + B$ |
| `CC_INL` (`26`) | 2 | `0` | `sum_type` | `value` $a$ | — | — | Left injection $\text{inl}_{A+B}(a)$ |
| `CC_INR` (`27`) | 2 | `0` | `sum_type` | `value` $b$ | — | — | Right injection $\text{inr}_{A+B}(b)$ |
| `CC_SUMREC` (`28`) | 4 | `0` | `motive` $M$ | `left_fn` $l$ | `right_fn` $r$ | `scrutinee` $s$ | Sum recursor $\text{sumrec}(M, l, r, s) : M(s)$ |

### 5. Paths, partial tubes, and cubical composition/transport

| `cc_term_kind` | Arity | `payload` | `child[0]` (`a`) | `child[1]` (`b`) | `child[2]` (`c`) | Mathematical notation and role |
|---|---|---|---|---|---|---|
| `CC_PATH` (`15`) | 3 | `dim` $i$ | `family` $A(i)$ | `left` $a_0$ | `right` $a_1$ | Dependent path type $\text{Path}_i(A(i), a_0, a_1)$ (binds $i$ in `a` only) |
| `CC_PLAM` (`16`) | 2 | `dim` $i$ | `family` $A(i)$ | `body` $t(i)$ | — | Path abstraction $\langle i \rangle\, t(i)$ with line type $A(i)$ (binds $i$ in `a` and `b`) |
| `CC_PAPP` (`17`) | 2 (`b` opt.) | `interval_id` $r$ | `path` $p$ | `path_type` (opt.) | — | Path application $p \mathbin{@} r$ (`b` stores $\text{Path}_i(A, a_0, a_1)$ when built by instructions) |
| `CC_TUBE` (`18`) | 2 (`b` opt.) | `face_id` $\varphi$ | `partial_term` $u$ | `next_tube` (opt.) | — | Partial system node $[\varphi \mapsto u, \dots]$ (0-terminated linked list of tubes) |
| `CC_COMP` (`19`) | 3 (`b` opt.) | `dim` $i$ | `family` $A(i)$ | `tubes` $[\varphi \mapsto u(i)]$ | `base` $a_0$ | Heterogeneous composition $\text{comp}^i\, A(i)\, [\varphi \mapsto u(i)]\, a_0$ |
| `CC_HCOMP` (`43`) | 3 (`b` opt.) | `dim` $i$ | `type` $A$ | `tubes` $[\varphi \mapsto u(i)]$ | `base` $a_0$ | Homogeneous composition $\text{hcomp}^i\, A\, [\varphi \mapsto u(i)]\, a_0$ on a higher sort |
| `CC_TRANS` (`44`) | 3 | `dim` $i$ | `family` $A(i)$ | `tube` $[\varphi \mapsto a_0]$ | `base` $a_0$ | Transport $\text{transp}^i\, A(i)\, \varphi\, a_0$ on a higher sort (constant on $\varphi$) |

> [!IMPORTANT]
> **Dimension binding in `CC_COMP`, `CC_HCOMP`, and `CC_TRANS`:**
> - In `CC_COMP`, the direction `dim` ($i$) is bound in the type line `child[0]` ($A(i)$) and in the body `t.child[0]` ($u(i)$) of each `CC_TUBE` in `child[1]`, **not** in any tube's face formula `t.payload` ($\varphi$) and **not** in the base `child[2]` ($a_0$).
> - In `CC_HCOMP`, the carrier type `child[0]` ($A$) is stationary (does **not** bind $i$); $i$ is bound only in each tube body `t.child[0]` ($u(i)$).
> - In `CC_TRANS`, $i$ is bound in the type line `child[0]` ($A(i)$); `child[1]` holds a single `CC_TUBE` with constant face $\varphi$ (`i` not free in $\varphi$) and body `base` ($a_0$).

### 6. Glue types and terms

Glue types turn an equivalence $e : \text{Equiv}(T, A)$ defined on a partial face $\varphi$ into a total type that reduces to $T$ on $\varphi$ and maps into the base type $A$ everywhere ([instruction_glue.c](../../kernel/src/instruction_glue.c), [glue_compute.c](../../kernel/src/glue_compute.c), [equivalence_terms.c](../../kernel/src/equivalence_terms.c)).

| `cc_term_kind` | Arity | `payload` | `child[0]` (`a`) | `child[1]` (`b`) | `child[2]` (`c`) | Mathematical notation and role |
|---|---|---|---|---|---|---|
| `CC_GLUE` (`39`) | 2 (`b` opt.) | `0` | `base_type` $A$ | `pieces` (opt.) | — | Glue type $\text{Glue}\,[\varphi \mapsto (T, e)]\, A$ |
| `CC_GLUE_SYSTEM` (`40`) | 3 (`c` opt.) | `face_id` $\varphi$ | `partial_type` $T$ | `equiv` $e$ | `next` (opt.) | Glue system piece $(\varphi \mapsto (T, e))$, linked via `c` |
| `CC_GLUE_TERM` (`41`) | 3 (`c` opt.) | `0` | `glue_type` $G$ | `base_val` $a$ | `tubes` (opt.) | Glue element $\text{glue}_G([\varphi \mapsto t], a)$ where $f(t) = a$ on $\varphi$ (`c` is a `CC_TUBE` list) |
| `CC_UNGLUE` (`42`) | 2 | `0` | `glue_type` $G$ | `glue_val` $g$ | — | Base projection $\text{unglue}_G(g) : A$ |

An equivalence $e : \text{Equiv}(T, A)$ is represented directly as a $\Sigma$-pair $(f, c)$ where $f : T \to A$ and $c : \Pi(y : A).\, \text{IsContr}(\Sigma(x : T).\, \text{Path}_i(A, y, f(x)))$. `cc_kernel_equiv_type` in [equivalence_terms.c](../../kernel/src/equivalence_terms.c) constructs this contractible-fiber type using internal reserved symbols (`0xffff0001u..0xffff0006u`).

### 7. Declared inductive and higher inductive types (H1)

Declared data types and higher inductive types (HITs) share four AST nodes ([signatures.c](../../kernel/src/signatures.c), [eliminators.c](../../kernel/src/eliminators.c)):

| `cc_term_kind` | Arity | `payload` | `child[0]` (`a`) | `child[1]` (`b`) | Mathematical notation and role |
|---|---|---|---|---|---|
| `CC_SORT` (`45`) | 2 (both opt.) | `sig_index` | `params` (`CC_LIST`) | `levels` (`CC_LIST`) | Applied sort instance $S(p_1, \dots, p_m)$ with recorded erased universe levels |
| `CC_CON` (`46`) | 1 | `ctor_index` | `sort_instance` | — | Constructor head $c_k(S(\vec{p}))$, applied to data/recursive args via `CC_APP` and path dimensions via `CC_PAPP` |
| `CC_ELIM` (`47`) | 2 (`b` opt.) | `sig_index` | `motive` $M$ | `clauses` (`CC_LIST`) | Dependent eliminator $\text{elim}_S(M, [m_0, \dots, m_{n-1}])$, applied to a scrutinee via `CC_APP` |
| `CC_LIST` (`48`) | 2 (`b` opt.) | `0` | `item` | `next` (`CC_LIST`) | Cons-cell spine for parameter lists, recorded level lists, and eliminator method lists |

### 8. Retired primitive tags

The enum tags `CC_NAT` (`20`), `CC_ZERO` (`21`), `CC_SUCC` (`22`), `CC_NATREC` (`23`), `CC_W` (`29`), `CC_SUP` (`30`), `CC_WREC` (`31`), `CC_PUSHOUT` (`49`), `CC_PUSH_LEFT` (`50`), `CC_PUSH_RIGHT` (`51`), `CC_PUSH_PATH` (`52`), and `CC_PUSH_ELIM` (`53`) are retained in `cc_term_kind` only so ABI constants remain stable. `term_arity` assigns them sentinel arity `5`, causing `ck_make` to reject them immediately with `"Retired primitive constructor: declare an H1 inductive type"`.

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

1. **Term substitution (`ck_subst(k, target, symbol, replacement)`):**
   - Traverses `target` on an explicit worklist stack (`subst_frame`) memoized in `k->subst_memo`.
   - Fast path: if `symbol`'s bit is not set in `target.symbols`, or `!ck_mentions_free(k, target, symbol)`, returns `target` immediately.
   - If `target` is a term binder (`CC_PI`, `CC_LAM`, `CC_SIGMA`, `CC_LPI`, `CC_LLAM`) with `n.payload == symbol`, the variable is shadowed in `child[1]` and only `child[0]` is substituted.
   - If `n.payload != symbol` and `n.payload` occurs free in `replacement` while `symbol` occurs free in `child[1]`, `ck_subst` picks a fresh symbol (`ck_fresh_symbol`) not mentioned in `child[1]` or `replacement`, renames `n.payload` in `child[1]` first, and then substitutes `replacement`.
   - If `replacement` is a level expression (`ck_is_level_expr`), `ck_subst` delegates to `ck_level_instantiate`, which also re-canonicalizes affected `CC_LAPP` arguments.

2. **Dimension substitution (`ck_dim_subst(k, target, dim, formula)`):**
   - Replaces free occurrences of interval coordinate `dim` ($i$) with the interval formula $r$ (`formula`) using an explicit worklist memoized in `k->dim_subst_memo`.
   - In `CC_PAPP`, substitutes $r$ for $i$ inside `n.payload` via `cc_subst_interval`.
   - In `CC_TUBE` and `CC_GLUE_SYSTEM`, substitutes $r$ for $i$ inside the face formula `n.payload` via `cc_subst_face`.
   - For a dimension binder (`CC_PATH`, `CC_PLAM`, `CC_COMP`, `CC_HCOMP`, `CC_TRANS`) whose bound dimension `n.payload` occurs in $r$ (`(r_dims >> n.payload) & 1`), `ck_dim_subst` picks a fresh dimension $j \in 0..63$ (`ck_fresh_dim` avoiding both the node and $r$), substitutes $j$ for `n.payload` inside the bound slots first, and then substitutes $r$ for `dim`.

3. **Face restriction (`ck_restrict(k, term, face)`):**
   - Simplifies a term under a single-clause face assumption $C$.
   - For each dimension $d \in 0..63$ constrained by $C$ ($(d = 0)$ in `C.negative` or $(d = 1)$ in `C.positive`), substitutes $\bot$ (`0`) or $\top$ (`1`) for $d$ via `ck_dim_subst`, and restricts remaining face formulas via `cc_restrict_face`.

### Syntactic comparison and cumulativity (`term_conversion.c`)

- **`ck_alpha_equal(k, left, right)`:** Checks syntactic $\alpha$-equivalence on an explicit traversal stack (`cmp_frame`) memoized in `k->cmp_memo`:
  - Identical handles (`left == right`) with no active renamings on their free variables/dimensions succeed immediately.
  - Universe levels (`ck_is_level_expr`) compare by arithmetic normal form (`ck_level_equal`), so $\max(\ell + 1, \ell) \equiv \ell + 1$ syntactically.
  - Term binders push a pair of bound symbols `(left.payload, right.payload)` onto the active term-scope stack (`term_scope`); dimension binders push `(left.payload, right.payload)` onto `dim_scope`.
  - Interval and face formula payloads on `CC_PAPP`, `CC_TUBE`, and `CC_GLUE_SYSTEM` are mapped through any active dimension renamings before comparing their canonical `cc_clause` arrays.
  - `CC_PAPP.child[1]` (the optional Path-type annotation) is ignored during syntactic comparison (`arity = 1` in `push_children`) because the path term `child[0]` and interval argument `payload` uniquely determine the application.
- **`ck_syntactic_cumulative(k, sub_type, super_type)`:** Checks structural subtyping $A \preceq B$ for the `Lift` instruction without reducing terms:
  - Identical types (`ck_alpha_equal(A, B)`) always satisfy $A \preceq B$.
  - $\mathcal{U}(\ell_1) \preceq \mathcal{U}(\ell_2)$ iff `ck_level_leq(l1, l2)` ($\ell_1 \le \ell_2$ in level normal form).
  - $\Pi(x : A_1).\, B_1(x) \preceq \Pi(x : A_2).\, B_2(x)$ iff domains match ($A_1 \equiv_\alpha A_2$) and codomains are covariant ($B_1(x) \preceq B_2(x)$).
  - $\forall(\ell < \omega).\, B_1(\ell) \preceq \forall(\ell < \omega).\, B_2(\ell)$ iff $B_1(\ell) \preceq B_2(\ell)$.
  - $\Sigma(x : A_1).\, B_1(x) \preceq \Sigma(x : A_2).\, B_2(x)$ iff $A_1 \preceq A_2$ and $B_1(x) \preceq B_2(x)$.
  - $A_1 + B_1 \preceq A_2 + B_2$ iff $A_1 \preceq A_2$ and $B_1 \preceq B_2$.
  - $\text{Path}_i(A_1(i), l_1, r_1) \preceq \text{Path}_i(A_2(i), l_2, r_2)$ iff $A_1(i) \preceq A_2(i)$, $l_1 \equiv_\alpha l_2$, and $r_1 \equiv_\alpha r_2$.

---

## Judgements, contexts, and instructions

### Context entries and judgement graph

The kernel maintains two append-only arrays ([term_internal.h](../../kernel/src/term_internal.h), [instructions.c](../../kernel/src/instructions.c)):

1. **Context entries (`k->entries`, indexed by `cc_entry_id`):**
   - **Term variable (`CC_INSTR_EXTEND`):** `symbol != 0`, `type = A`, `face = 0`, `is_dim = 0`, `is_level = 0`.
   - **Dimension variable (`CC_INSTR_DIMENSION`):** `dim < 64`, `is_dim = 1`.
   - **Level variable (`CC_INSTR_LEVEL`):** `symbol != 0`, `type = LBound(1)`, `is_level = 1`.
   - **Face assumption (`CC_INSTR_RESTRICT`):** `face = phi` (`CC_FACE`), `symbol == 0`, `type == 0`. Requires $\varphi$ to be non-empty (`phi != 0`, i.e., not the contradictory face $\bot$) and all its dimensions to be declared in the parent context.

2. **Certified judgements (`k->facts`, indexed by `cc_judgement_id`, 1-based):**
   Each `cc_fact` carries a `kind`, a context `ctx` (a deduplicated list of `cc_entry_id`s), and kind-specific handles:
   - `CC_FACT_TYPING` (`1`): $\Gamma \vdash \text{term} : \text{type}$.
   - `CC_FACT_EQUALITY` (`2`): $\Gamma \vdash \text{lhs} \equiv \text{rhs} : \text{type}$.
   - `CC_FACT_SYSTEM` (`3`): partial tube system or Glue builder state (`dim`, `family`, `tubes`, `faces`).
   - `CC_FACT_SIGNATURE` (`4`): open or closed H1 inductive signature (`sig_index`, `closed`).
   - `CC_FACT_INSTANCE` (`5`): partial or complete H1 sort instance (`sig_index`, `sort_term`, `progress`, `level_progress`).
   - `CC_FACT_ELIMINATOR` (`6`): partial or closed H1 eliminator (`sig_index`, `sort_term`, `motive`, `clauses`, `progress`).

**Context compatibility and face discharge:**
- Binary rules merge two premise contexts with `ck_ctx_merge` when neither context contains a `Restrict` face entry and shared symbols/dimensions have identical entries (`ck_ctx_compatible`). If face entries are present, the two contexts must be identical (`ck_ctx_same`).
- Partial-system instructions (`SystemTube`, `SystemOverlap`, `GluePiece`, `GlueOverlap`, `GlueTermPiece`) check a premise proved under an extended context $\Gamma, \psi$ using `ck_instr_on_face(k, base_ctx, face, premise)`. That helper strips every `Restrict` entry $\psi_m$ added above `base_ctx` and verifies that their conjunction is entailed by `face` ($\varphi \vdash \bigwedge_m \psi_m$ via `cc_entails`), discharging the face assumption.

### Instruction summary by primitive family

Every instruction is submitted via `cc_kernel_instr(k, &in, &out)` ([cubical_kernel.h](../../kernel/include/cubical_kernel.h)):

| Primitive family | Formation instructions | Introduction instructions | Elimination / projection instructions |
|---|---|---|---|
| **Contexts & variables** | `Extend`, `Dimension`, `Level`, `Restrict` | `Var`, `Weaken`, `Subst`, `DimSubst`, `RestrictJudgement` | — |
| **Universes & levels** | `Universe` ($\mathcal{U}(\ell) : \mathcal{U}(\ell+1)$), `LevelPi` | `LevelLambda` | `LevelApply` ($f\,\{\ell\} : B[\ell/x]$) |
| **Definitions** | — | `Define` (admits closed $t : A$, mints `CC_DEFREF`), `Lookup` | `Step(CC_STEP_DELTA)` |
| **Functions ($\Pi$)** | `Pi` ($\Pi(x:A).B : \mathcal{U}(\max(\ell_A, \ell_B))$) | `Lambda` ($\lambda(x:A).b : \Pi(x:A).B$) | `Apply` ($f(a) : B[a/x]$) |
| **Pairs ($\Sigma$)** | `Sigma` ($\Sigma(x:A).B : \mathcal{U}(\max(\ell_A, \ell_B))$) | `Pair` ($(a, b) : \Sigma(x:A).B$ given $b : B[a/x]$) | `Fst` ($\pi_1(p) : A$), `Snd` ($\pi_2(p) : B[\pi_1(p)/x]$) |
| **Unit, Void, Sums** | `Unit` ($\mathbf{1} : \mathcal{U}_0$), `Void` ($\mathbf{0} : \mathcal{U}_0$), `Sum` ($A + B : \mathcal{U}(\max(\ell_A, \ell_B))$) | `Point` ($\star : \mathbf{1}$), `Inl`, `Inr` | `UnitRec`, `Abort`, `SumRec` |
| **Paths** | `Path` ($\text{Path}_i(A(i), a_0, a_1) : \mathcal{U}(\ell)$ when $i \notin \text{fv}(\ell)$) | `PathLambda` ($\langle i \rangle t : \text{Path}_i(A, t[0/i], t[1/i])$) | `PathApply` ($p \mathbin{@} r : A[r/i]$), `PathAt` (with endpoint equations at $r=0$ or $r=1$) |
| **Composition & transport** | `System`, `SystemTube`, `SystemOverlap` | — | `Comp` ($\text{comp}^i\, A\, [\varphi \mapsto u]\, a_0 : A[1/i]$), `HComp` ($\text{hcomp}^i\, A\, [\varphi \mapsto u]\, a_0 : A$), `Trans` ($\text{transp}^i\, A\, \varphi\, a_0 : A[1/i]$) |
| **Glue** | `GlueBase`, `GluePiece`, `GlueOverlap`, `Glue` | `GlueTermBase`, `GlueTermPiece`, `GlueTerm` | `Unglue` ($\text{unglue}_G(g) : A$) |
| **H1 declared types** | `SignatureBegin`, `SignatureConstructor`, `SignatureClose`; `SortBegin`, `SortLevel`, `SortParameter` | `Construct` ($c_k(S(\vec{p}))$) | `Eliminator`, `EliminatorClause`, `EliminatorClose` ($\text{elim}_S(M, \vec{m}) : \Pi(x:S(\vec{p})).\, M(x)$) |
| **Equality & conversion** | — | `Refl`, `Sym`, `TransEq`, `Cong`, `Replace`, `Step`, `Eta` | `Conv` (rewrites $t : A$ to $t : B$ given $A \equiv B$), `Lift` (rewrites $t : A$ to $t : B$ given $A \preceq B$) |

**Multi-step builder invariants:**
- **Composition systems (`instruction_paths.c`):** `System` initializes an empty tube list for direction $i$ and type line $A(i)$. Each `SystemTube` adds $[\varphi_m \mapsto u_m(i)]$ after checking that $i$ is not free in $\varphi_m$, $u_m(i) : A(i)$ holds on $\varphi_m$, and for every previous tube $\varphi_k$ ($k < m$), a `SystemOverlap` equality $u_k \equiv u_m : A(i)$ has been certified on $\varphi_k \wedge \varphi_m$. `Comp` and `HComp` then take a base $a_0 : A[0/i]$ accompanied by one base-compatibility equality $a_0 \equiv u_m[0/i] : A[0/i]$ on $\varphi_m$ for each tube in reverse tube list order.
- **H1 signatures and eliminators (`signatures.c`, `eliminators.c`):** `SignatureBegin` opens a signature with $m$ parameters and a sort universe specification; each `SignatureConstructor` validates strict positivity (recursive calls may occur only as targets of $\Pi$-codomains over parameters independent of the sort), path dimension declarations, and boundary faces; `SignatureClose` seals the signature (and automatically appends the 2-argument path squash constructor when `modifier == CC_PROPOSITIONAL`). `EliminatorClause` computes the expected displayed method type `ck_clause_type`—binding non-recursive arguments, recursive arguments, lifted induction hypotheses $\bar{q}_j$, and path coordinates $i_1, \dots, i_d$, and checking that on each boundary face $(i_l = \varepsilon)$ the method body agrees with the recursively eliminated boundary `ck_eval_boundary`.

---

## Reduction, normalization, and elimination

The kernel separates **trusted equality steps** (invoked explicitly by the `Step` instruction at a chosen `cc_position`), **call-by-name weak-head reduction** (`ck_whnf`), **compact single-step exposure** (`ck_expose`), and **full normalization** (`ck_normal`).

### 1. Targeted single-step rules (`CC_INSTR_STEP` in `instruction_equality.c`)

Given a typing judgement $\Gamma \vdash t : A$ and a path of child indices `k->position` pointing to a subterm $s$ (checked not to traverse inside an unbound tube face or Glue piece), `Step(rule)` contracts $s \mapsto s'$ and produces $\Gamma \vdash t[s'] \equiv t : A$:

| `cc_step_rule` | Redex $s$ | Contractum $s'$ and side conditions |
|---|---|---|
| `CC_STEP_BETA` (`1`) | `App(Lam(x, A, b), a)`<br>`LApp(LLam(x, B, b), l)` | `ck_subst(b, x, a)`<br>`ck_level_instantiate(b, x, l)` |
| `CC_STEP_DELTA` (`2`) | `DefRef(idx)` | `k->definitions[idx].value` |
| `CC_STEP_IOTA` (`3`) | `Fst(Pair(T, a, b))`<br>`Snd(Pair(T, a, b))`<br>`UnitRec(M, pt, Point)`<br>`SumRec(M, l, r, Inl(T, v))`<br>`SumRec(M, l, r, Inr(T, v))`<br>`App(Elim(sig, M, ms), c)` | `a`<br>`b`<br>`pt`<br>`App(l, v)`<br>`App(r, v)`<br>`ck_eliminate(sig, M, ms, c, false)` when $c$ is already a constructor or path-applied constructor (`weak = false`) |
| `CC_STEP_PATH` (`4`) | `PApp(r, PLam(i, A, b), _)`<br>`PApp(0, p, Path(i, A, l, r))`<br>`PApp(1, p, Path(i, A, l, r))` | `ck_dim_subst(b, i, r)`<br>`l` (uses stored Path-type annotation `child[1]`)<br>`r` (uses stored Path-type annotation `child[1]`) |
| `CC_STEP_FACE` (`5`) | `Comp(i, A, tubes, a0)` with `(1 ↦ u)` in `tubes`<br>`HComp(i, A, tubes, a0)` with `(1 ↦ u)` in `tubes`<br>`Trans(i, A, Tube(1, a0), a0)` | `ck_dim_subst(u, i, 1)`<br>`ck_dim_subst(u, i, 1)`<br>`a0` |
| `CC_STEP_GLUE` (`6`) | `GlueTerm(G, base, [φ ↦ t])` | Contracts via `ck_glue_step` to $b$ when `base` reduces to `Unglue(G', b)` (possibly through nested Glue steps) and for every clause $C$ of $\varphi$, $G|_C$ and $G'|_C$ agree and $t|_C$ and $b|_C$ agree under `normal_agree` |
| `CC_STEP_SPLIT` (`7`) | `Comp` or `HComp` with multi-clause or `0`-face tubes | Splits each multi-clause tube $[\varphi_1 \vee \varphi_2 \mapsto u]$ into single-clause tubes $[\varphi_1 \mapsto u, \varphi_2 \mapsto u]$ and drops `0`-face tubes (`ck_clause_tubes`) |
| `CC_STEP_WHNF` (`8`) | Any term $s$ | `ck_whnf(k, s)` (must differ from $s$) |
| `CC_STEP_NORMALIZE` (`9`) | Any term $s$ | `ck_normal(k, s)` (must differ from $s$) |

In addition, `CC_INSTR_ETA` certifies the five $\eta$-laws directly on a typed term:
- `CC_ETA_LAMBDA`: $\Gamma \vdash \lambda(x:A).\, f(x) \equiv f : \Pi(x:A).\, B(x)$ when $x \notin \text{fv}(f)$.
- `CC_ETA_LEVEL`: $\Gamma \vdash \Lambda(\ell < \omega).\, f\,\{\ell\} \equiv f : \forall(\ell < \omega).\, B(\ell)$ when $\ell \notin \text{fv}(f)$.
- `CC_ETA_PAIR`: $\Gamma \vdash (\pi_1(p), \pi_2(p))_{\Sigma(x:A).B} \equiv p : \Sigma(x:A).\, B(x)$.
- `CC_ETA_PATH`: $\Gamma \vdash \langle i \rangle\, (p \mathbin{@} i) \equiv p : \text{Path}_i(A(i), a_0, a_1)$ when $i \notin \text{fv}(p)$.
- `CC_ETA_UNIT`: $\Gamma \vdash t \equiv \star : \mathbf{1}$.

### 2. Weak-head normal form (`ck_whnf` in `term_normalize.c`)

`ck_whnf(k, term)` reduces a term to its weak-head normal form using a call-by-name loop with an explicit continuation stack of elimination frames (`weak_tails`: `WEAK_APP`, `WEAK_LAPP`, `WEAK_FST`, `WEAK_SND`, `WEAK_PAPP`), memoized in `k->weak_cache`:

1. **Definitions:** `CC_DEFREF(idx)` unfolds to `k->definitions[idx].value`.
2. **Elimination spine:** While the current focus is `CC_APP`, `CC_LAPP`, `CC_FST`, `CC_SND`, or `CC_PAPP` at an interior formula ($r \ne 0, 1$), `ck_whnf` pushes an elimination frame onto `weak_tails` and loops on `child[0]`.
3. **Path endpoints:** If the focus is `CC_PAPP(r, p, path_type)` with $r = 0$ or $r = 1$ and `path_type` is `CC_PATH(i, A, l, r_end)`, `ck_whnf` immediately returns `l` (for $r = 0$) or `r_end` (for $r = 1$) without needing to reduce a neutral path $p$. Otherwise it pushes `WEAK_PAPP` and reduces $p$.
4. **Recursors:**
   - `CC_UNITREC(M, pt, v)`: reduces $v$ to WHNF; if `whnf(v) == CC_POINT`, continues with `pt`.
   - `CC_SUMREC(M, l, r, s)`: reduces $s$ to WHNF; if `whnf(s)` is `CC_INL(_, v)` or `CC_INR(_, v)`, continues with `App(l, v)` or `App(r, v)`.
5. **Glue reductions:**
   - `CC_GLUE(A, pieces)` and `CC_GLUE_TERM(G, a, tubes)`: drops any piece/tube with face `0`; if any piece/tube has top face `1`, reduces immediately to its `child[0]` ($T$ or $t$).
   - `CC_UNGLUE(G, g)`: reduces $G$ to WHNF; if $G$ has a top-face (`1`) piece $(T, e)$, reduces to $\pi_1(e)(g)$; otherwise reduces $g$ to WHNF, and if `whnf(g)` is `CC_GLUE_TERM(_, base, _)`, continues with `base`.
6. **Syntactic $\eta$-contractions in `ck_whnf`:**
   - `Pair(T, Fst(p), Snd(p'))` $\to p$ when `ck_alpha_equal(p, p')`.
   - `Lam(x, A, App(f, Var(x)))` $\to f$ when $x$ is not free in $f$.
   - `LLam(x, B, LApp(f, Var(x)))` $\to f$ when $x$ is not free in $f$.
   - `PLam(i, A, PApp(i, p, _))` $\to p$ when $i$ is not free in $p$.
   - `GlueTerm(G, b, tubes)` $\to p$ when `whnf(b)` is `Unglue(G', p)`, `ck_alpha_equal(G, G')`, and every non-empty tube $(\varphi \mapsto t)$ satisfies `ck_alpha_equal(t, ck_restrict(p, C))` on each clause $C \in \varphi$.
7. **Cubical operations:** `CC_COMP` dispatches to `ck_reduce_composition`; `CC_HCOMP` and `CC_TRANS` dispatch to `ck_hit_reduce`. If those return a simplified term (`reduced != current`), `ck_whnf` continues reducing the result.
8. **Popping the continuation spine:** Once the head is in WHNF:
   - `WEAK_APP(arg)` on `CC_LAM(x, A, body)` substitutes `ck_subst(body, x, arg)` and continues.
   - `WEAK_APP(arg)` on `CC_ELIM(sig, M, clauses)` runs `ck_eliminate(k, sig, M, clauses, arg, true)` (`weak = true`, which reduces `arg` to WHNF first).
   - `WEAK_LAPP(lvl)` on `CC_LLAM(x, B, body)` instantiates `ck_level_instantiate(body, x, lvl)`.
   - `WEAK_FST` / `WEAK_SND` on `CC_PAIR(T, a, b)` selects `a` or `b`.
   - `WEAK_PAPP(r, path_type)` on `CC_PLAM(i, A, body)` substitutes `ck_dim_subst(body, i, r)`.

### 3. Compact head exposure (`ck_expose` in `term_expose.c`)

When composition rules inspect a type family or constructor head, full WHNF can inflate terms by unfolding large definitions. `ck_expose(k, term)` performs at most one structural contraction (beta, level-beta, projection, path-lambda beta, path-endpoint boundary, or top-face `1` tube on `Comp`/`HComp`/`Trans`/`Glue`) and accepts the result only if its arena node count stays within a compact growth bound (`added <= 64 + before_size`). Otherwise it rolls back the arena to a checkpoint and leaves the term unexposed.

### 4. Full normalization (`ck_normal` in `term_normalize.c`)

`ck_normal(k, term)` computes a strong normal form under binders using an explicit worklist (`normal_stack`), memoized by exact handle in `k->normal_cache`:

1. First reduces the current node via `ck_whnf`.
2. Canonicalizes universe level expressions (`ck_is_level_expr`) to canonical right-nested `CC_LMAX`/`CC_LSUCC`/`CC_LCONST` syntax via `ck_level_canonical`.
3. For partial bodies (`CC_TUBE` and `CC_GLUE_SYSTEM`), `normal_restrict` computes the intersection of endpoint equations common to **all** clauses of the piece's face formula $\varphi$:
   $$\text{common\_pos} = \bigcap_{C \in \varphi} C.\text{positive}, \qquad \text{common\_neg} = \bigcap_{C \in \varphi} C.\text{negative}$$
   and restricts the partial body (`child[0]`, and `child[1]` on `CC_GLUE_SYSTEM`) by that common clause before normalizing its children.
4. Recursively normalizes all child slots (including under $\lambda$, $\Pi$, $\Sigma$, $\Lambda$, $\forall$, $\langle i \rangle$, and `Comp`/`HComp`/`Trans`).
5. On rebuilding a `CC_GLUE_TERM`, checks Glue $\eta$ (`NORMAL_GLUE`) by comparing each normalized tube body against the normalized clause-restricted candidate `ck_normal(ck_restrict(p, C))`.
6. If rebuilding a node changes any child and creates a new redex (for example, a restricted wall inside a composition became `1`, or a constructor argument simplified), `ck_normal` loops to normalize the rebuilt node.

### 5. Dependent elimination of H1 declared types (`eliminators.c`)

Let $E = \text{elim}_S(M, [m_0, \dots, m_{n-1}])$ be an admitted eliminator for signature $S$ with motive $M : \Pi(x : S(\vec{p})).\, \mathcal{U}(\ell)$. When applied to a scrutinee $s$, `ck_eliminate(k, sig, M, clauses, s, weak)` (reducing $s$ via `ck_whnf` first when `weak == true`) handles two cases:

1. **Constructor or path-constructor application ($s = c_k(I(\vec{p}))(t_1, \dots, t_a, q_1, \dots, q_b) \mathbin{@} r_1 \dots \mathbin{@} r_d$):**
   - `parse_con_spine` unpacks the constructor index $k$, the non-recursive arguments $t_1, \dots, t_a$, the recursive arguments $q_1, \dots, q_b$ (where $q_j : \Pi(\vec{y} : \vec{C}_j).\, S(\vec{p})$), and the applied interval formulas $r_1, \dots, r_d$ ($0 \le d \le \text{dim\_count}$).
   - For each recursive argument $q_j$, `lifted` builds the induction hypothesis:
     $$\bar{q}_j = \lambda(y_1 : C_{j,1}) \dots \lambda(y_r : C_{j,r}).\; E\bigl(q_j(y_1, \dots, y_r)\bigr)$$
     (when $r = 0$, simply $\bar{q}_j = E(q_j)$).
   - Substitutes $t_1, \dots, t_a$, $q_1, \dots, q_b$, and $\bar{q}_1, \dots, \bar{q}_b$ into the $k$-th clause method $m_k$.
   - For each applied path coordinate $r_l$ ($1 \le l \le d$), computes the displayed path type annotation $P_l$ via `clause_path_type` and applies `CC_PAPP(r_l, body, P_l)`.

2. **Homogeneous composition ($s = \text{hcomp}^j\, S(\vec{p})\, [\psi \mapsto w(j)]\, w_0$):**
   - Pick a fresh dimension $k \notin \text{fv}(s) \cup \text{fv}(E)$.
   - Form the homogeneous fill along $k$:
     $$\text{hfill}(k) = \text{hcomp}^j\, S(\vec{p})\, \bigl[\psi \mapsto w(j \wedge k),\; (k = 0) \mapsto w_0\bigr]\, w_0$$
   - Recursively apply $E$ to each tube body $w(k)$ and to the base $w_0$, and compose in the motive family over $\text{hfill}(k)$:
     $$E\bigl(\text{hcomp}^j\, S(\vec{p})\, [\psi \mapsto w(j)]\, w_0\bigr) \;\longrightarrow\; \text{comp}^k\, M(\text{hfill}(k))\, \bigl[\psi \mapsto E(w(k))\bigr]\, E(w_0)$$

---

## Cubical composition, transport, and filling computation

### 1. Derived filling (`ck_fill` in `composition_compute.c`)

Given a heterogeneous composition problem in direction $i$ over family $A(i)$, partial tubes $[\varphi \mapsto u(i)]$, and base $a_0 : A(0)$, the open-box filler at interval coordinate $r$ is derived from `CC_COMP` by picking a fresh dimension $j$ (`ck_fresh_dim`):

$$\text{fill}^i\, A(i)\, [\varphi \mapsto u(i)]\, a_0\, r \;:=\; \text{comp}^j\, A(r \wedge j)\, \bigl[\varphi \mapsto u(r \wedge j),\; (r = 0) \mapsto a_0\bigr]\, a_0$$

At $r = 0$, the added wall $(r = 0) \mapsto a_0$ has top face `1` and reduces immediately to $a_0$; at $r = 1$, $(r = 0)$ is `0` and $r \wedge j = j$, recovering $\text{comp}^j\, A(j)\, [\varphi \mapsto u(j)]\, a_0$.

### 2. Heterogeneous composition (`ck_reduce_composition` in `composition_compute.c`)

To compute $\text{comp}^i\, A(i)\, [\varphi \mapsto u(i)]\, a_0$, the kernel first checks whether any tube in the list has top face $\varphi = 1$; if so, it immediately returns $u(1)$ (`ck_dim_subst(u, i, 1)`). Otherwise it inspects the head of $A(i)$ (using `ck_expose` and falling back to `ck_whnf`):

| Type family $A(i)$ | Reduction of $\text{comp}^i\, A(i)\, [\varphi \mapsto u(i)]\, a_0$ |
|---|---|
| **Unit ($\mathbf{1}$)** | Reduces to $\star$ (`CC_POINT`) when `whnf(a0)` and the WHNF of every non-empty tube body $u(i)$ is $\star$; otherwise stays neutral. |
| **Dependent pair ($\Sigma(x : F(i)).\, G(i, x)$)** | Let $c_1 = \text{comp}^i\, F(i)\, [\varphi \mapsto \pi_1(u(i))]\, \pi_1(a_0)$ and $v(i) = \text{fill}^i\, F(i)\, [\varphi \mapsto \pi_1(u(i))]\, \pi_1(a_0)\, i$. Substitute $v(i)$ for $x$ in $G(i, x)$ to form $c_2 = \text{comp}^i\, G(i, v(i))\, [\varphi \mapsto \pi_2(u(i))]\, \pi_2(a_0)$, and return $(c_1, c_2)_{\Sigma(x:F(1)).G(1,x)}$. |
| **Dependent function ($\Pi(y : F(i)).\, G(i, y)$)** | Pick a fresh variable $x : F(1)$ and fill **backward** in $F(1 - i)$ with no tubes: $v(i) = \text{fill}^i\, F(1 - i)\, [\,]\, x\, (1 - i)$. Return $\lambda(x : F(1)).\, \text{comp}^i\, G(i, v(i))\, [\varphi \mapsto u(i)(v(i))]\, (a_0(v(0)))$. |
| **Universe-polymorphic ($\forall(\ell < \omega).\, G(i, \ell)$)** | Universe levels do not vary with interval coordinates: pick fresh $\ell < \omega$ and return $\Lambda(\ell < \omega).\, \text{comp}^i\, G(i, \ell)\, [\varphi \mapsto u(i)\,\{\ell\}]\, (a_0\,\{\ell\})$. |
| **Path ($\text{Path}_j(P(i, j), l(i), r(i))$)** | Pick a fresh dimension $k \ne i$, apply `@ k` to every tube and to $a_0$, append the two endpoint tubes $(k = 0) \mapsto l(i)$ and $(k = 1) \mapsto r(i)$, and return $\langle k \rangle\, \text{comp}^i\, P(i, k)\, [\varphi \mapsto u(i) \mathbin{@} k,\; (k = 0) \mapsto l(i),\; (k = 1) \mapsto r(i)]\, (a_0 \mathbin{@} k)$. |
| **Disjoint sum ($L(i) + R(i)$)** | ([inductive_composition.c](../../kernel/src/inductive_composition.c)) Expose $a_0$ and all non-empty tube bodies. If all are `Inl(_, v)` (or all are `Inr(_, v)`), push composition inside the injection: $\text{inl}_{L(1)+R(1)}\bigl(\text{comp}^i\, L(i)\, [\varphi \mapsto v(i)]\, v_0\bigr)$. If any head is neutral or heads disagree, remain neutral. |
| **H1 data sort ($S(\vec{p}(i))$ with `data_sort == 1`)** | ([inductive_composition.c](../../kernel/src/inductive_composition.c)) Expose $a_0$ and all non-empty tube bodies. If all are applications of the same point constructor $c_k(S(\vec{p}))(v_1, \dots, v_m)$, pack the constructor's parameter-substituted field types into a right-nested $\Sigma$-telescope $T(i) = \Sigma(x_1 : A_1(i)) \dots \Sigma(x_m : A_m(i)).\, \mathbf{1}$ (`ck_telescope`), pack each argument spine into a tuple in $T(i)$ (`ck_tuple`), compute $t_1 = \text{comp}^i\, T(i)\, [\varphi \mapsto \text{tuple}(u(i))]\, \text{tuple}(a_0)$, and reapply $c_k(S(\vec{p}(1)))$ to $\pi_1(t_1), \pi_1(\pi_2(t_1)), \dots$ (`ck_apply_components`). |
| **H1 higher sort ($S(\vec{p}(i))$ with `data_sort == 0`)** | ([hit_composition.c](../../kernel/src/hit_composition.c)) Decompose heterogeneous `Comp` into `Trans` and `HComp` at $S(\vec{p}(1))$ (`ck_higher_composition`):<br>$$\text{comp}^i\, S(\vec{p}(i))\, [\varphi \mapsto u(i)]\, u_0 \;\longrightarrow\; \text{hcomp}^i\, S(\vec{p}(1))\, \bigl[\varphi \mapsto \text{squeeze}_i(S(\vec{p}), 0, u(i))\bigr]\, \bigl(\text{transp}^i\, S(\vec{p}(i))\, 0\, u_0\bigr)$$<br>where $\text{squeeze}_i(P, \psi, u) = \text{transp}^j\, P[i \vee j / i]\, (\psi \vee (i = 1))\, u$ transports $u(i) : P(i)$ forward along $i \vee j$ to $P(1)$. |
| **Glue ($\text{Glue}\,[\psi(i) \mapsto (T(i), w(i))]\, A(i)$)** | ([glue_compute.c](../../kernel/src/glue_compute.c)) See [Glue and universe composition](#3-glue-and-universe-composition-glue_computec) below. |
| **Universe ($\mathcal{U}(\ell)$)** | ([glue_compute.c](../../kernel/src/glue_compute.c)) Reduces to a `Glue` type over the base type $a_0$: see [Glue and universe composition](#3-glue-and-universe-composition-glue_computec) below. |

### 3. Glue and universe composition (`glue_compute.c`)

- **Glue composition (`ck_glue_composition`):**
  Given $\text{comp}^i\, (\text{Glue}\,[\psi(i) \mapsto (T(i), w(i))]\, A(i))\, [\varphi \mapsto u(i)]\, u_0$:
  1. Split multi-clause Glue pieces and composition tubes into single-clause pieces (`split_glue`, `ck_clause_tubes`).
  2. Project the base and tubes to $A(i)$ via `unglue`: $a_0 = \text{unglue}(u_0)$ and $a(i) = \text{unglue}(u(i))$.
  3. Compose in the base type $A(i)$: $a_1' = \text{comp}^i\, A(i)\, [\varphi \mapsto a(i)]\, a_0$.
  4. For each piece $(\psi \mapsto (T(i), w(i)))$:
     - Define the universal face $\delta = \forall i.\, \psi$ (`cc_face_forall`), on which the piece exists across the entire interval $i$.
     - On $\delta$, transport $u(0)$ along $T(i)$: $t_1' = \text{comp}^i\, T(i)\, [\varphi \mapsto u(i)]\, u_0$, and use Lemma 6 (`preservation`) to build a path $\alpha : \text{Path}_k(A(1),\, w_1.1(t_1'),\, a_1')$ agreeing with the constant path on $\varphi$.
     - On $\varphi$, the tube $u(1)$ with the constant path $\langle k \rangle\, a(1)$ already inhabits the fiber $\text{Fiber}_{w_1.1}(a_1') = \Sigma(x : T(1)).\, \text{Path}_k(A(1), w_1.1(x), a_1')$.
     - Since $w(1)$ is an equivalence, its fibers are contractible (`w_1.2(a_1')`). `extend_fiber` extends the partial fiber element defined on $\delta \vee \varphi$ to a total fiber element $(t_1, \alpha_1)$ on $\psi(1)$.
  5. Adjust $a_1'$ in $A(1)$ using the paths $\alpha_1(1 - i)$ on $\psi(1)$ and the constant path $a(1)$ on $\varphi$:
     $$a_1 = \text{comp}^i\, A(1)\, \bigl[\psi(1) \mapsto \alpha_1(1 - i),\; \varphi \mapsto a(1)\bigr]\, a_1'$$
  6. Return $\text{glue}_{\text{Glue}(1)}\bigl([\psi(1) \mapsto t_1],\, a_1\bigr)$.

- **Universe composition (`ck_universe_composition`):**
  Following CCHM §7.1, composition of a system of types $E(i) : \mathcal{U}(\ell)$ over a base type $A : \mathcal{U}(\ell)$ reduces to a `Glue` type by composing the identity equivalence $\text{idEquiv}(E(1))$ along the reversed line $\text{Equiv}(E(1), E(1 - i))$:
  $$\text{comp}^i\, \mathcal{U}(\ell)\, [\varphi \mapsto E(i)]\, A \;\longrightarrow\; \text{Glue}\,\Bigl[\varphi \mapsto \bigl(E(1),\; \text{comp}^i\, \text{Equiv}(E(1), E(1 - i))\, [\,]\, \text{idEquiv}(E(1))\bigr)\Bigr]\, A$$

### 4. Higher inductive `HComp` and `Trans` (`hit_composition.c`)

For a higher sort $I(i) = S(\vec{p}(i))$ (`ck_hit_reduce`):

1. **Degenerate and empty reductions:**
   - $\text{hcomp}^i\, I\, [\varphi \mapsto u(i)]\, u_0$ drops `0`-face tubes; if no tubes remain, it stays neutral (`CC_HCOMP` is a canonical value constructor on higher sorts); if any tube has face `1`, it reduces to $u(1)$.
   - $\text{transp}^i\, I(i)\, 1\, u_0 \longrightarrow u_0$.

2. **Commuting `Trans` past `HComp` (`transp_hcomp`):**
   When the base of a transport reduces to $\text{hcomp}^j\, I(0)\, [\psi \mapsto w(j)]\, w_0$ (renaming $j$ to a fresh dimension $k$ if $j = i$ or $j$ occurs free in $I(i)$ or $\varphi$), `Trans` distributes into the `HComp` walls and base:
   $$\text{transp}^i\, I(i)\, \varphi\, \bigl(\text{hcomp}^k\, I(0)\, [\psi \mapsto w(k)]\, w_0\bigr) \;\longrightarrow\; \text{hcomp}^k\, I(1)\, \bigl[\psi \mapsto \text{transp}^i\, I(i)\, \varphi\, w(k)\bigr]\, \bigl(\text{transp}^i\, I(i)\, \varphi\, w_0\bigr)$$

3. **Transport of point and path constructors (`transp_constructor`):**
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
adds the named reference to `k->definitions` and returns its `CC_DEFREF` handle.
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
invalid scopes, term depth above `CC_MAX_TERM_DEPTH` (`512`), and exhausted explicitly configured budgets reject checking;
they never produce a successful judgement. `CC_ERROR_RESOURCE` (`resource` in
JavaScript) identifies allocation, depth, and representation limits separately
from mismatches, step budgets, and deadlines. Increasing the step budget does
not retry these failures. The elaborator preserves an unresolved limit through
inference and proof search, and negative-test contracts cannot count it as an
expected refusal. Bounded conversion shortcuts may still use a cheaper
alternative; a successful answer requires the ordinary checked derivation.
Full cubical canonicity for every implemented constructor is not claimed by this project.
