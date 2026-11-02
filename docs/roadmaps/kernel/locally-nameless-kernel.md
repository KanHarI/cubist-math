# Variables by role: a locally nameless kernel

Proposal of 2026-11-02, against main `a933a0bf`. Design only: nothing here is
implemented. Every statement about current behavior names the C function
that enforces it; the counts in [section 1.7](#17-what-the-names-cost-measured)
and [section 6](#6-performance-expectations) come from a temporary
instrumented build of main, not committed.

**Decided by the user on 2026-11-02:**

- The kernel's syntax names a variable's role by its node kind:
  `CC_BOUND` for a bound variable, by de Bruijn index, and `CC_CONTEXT` for a
  reference to a context entry. With `CC_DEFREF`, `CC_SORT`, `CC_CON` and
  `CC_ELIM`, which already refer by index, every variable states what it is.
- `CC_CONTEXT`'s payload is the entry's global id, a `cc_entry_id`, not a
  symbol and not a position in the judgement's context.
- The ABI moves to version 4: the driver reads and builds `CC_BOUND` and
  `CC_CONTEXT` itself. No names are converted at the boundary.
- The stopgap of branch `kernel-fast-multiplication` (a node lists up to
  three free names) is not the fix.
- Checking speed has no preset threshold: PR 3 measures and reports the
  checking cost, ticks and wall time for each import closure and the archive
  audit, and the user decides then (section 6.2).
- Binder names in displays: the driver chooses them, the source's name
  where it encoded the binder itself and a generated one otherwise; the
  kernel keeps no name hints (section 5.3).
- `CC_OPENED`, an internal kind for binders the kernel opens, rather than
  temporary entries (section 3.1).
- Replace's binder entries and the signature instructions' entry operands,
  under the conditions of section 3.6.
- PR 2, the kernel primitives, is its own PR (section 7).
- Raw syntax refers to a context variable only as the `CC_CONTEXT` of an
  entry that already exists: the driver first extends the context, then
  encodes against it, and never leaves a context variable as a dangling
  index (section 5.3).
- Entries carry no names: `cc_instr_extend` and `cc_instr_level` take no
  symbol, every call makes a new entry, `find_entry` and "The symbol already
  names a context entry." go, and `cc_kernel_entry` reports no symbol for a
  term or level entry. The driver matches names to entries (section 5.3);
  signatures report entries and closed types only (section 3.4).
- Dimensions are left out for now: dimension binders stay named and the
  64-dimension cap is out of scope for this project (section 4). A later
  project could redesign formulas without the cap and move dimension
  binders to indices together.

The rest is a recommendation for the user to accept or change; section 8
keeps the one question still open, the proposal to drop every remaining
kernel symbol.

## Why

`factorial(60)` took 138,249,298 of the kernel's query ticks on main, and
136,678,663 of them (99%) were visits of `ck_term_free`, substitution's
capture check (section 1.7). The report of the stopgap
(`docs/reports/kernel-multiplication.md` on the local branch
`kernel-fast-multiplication`, not on main) found the cause. The operand
being searched is closed. Its parts mention
names only because they sit under the arithmetic definitions' own binders
(`bpositive_add`'s clauses bind `p`, `p_rec` and `b1`), and the node's
filter of mentioned names (`symbols` in `cc_node`) counts bound names too, so
the filter cannot rule the search out. In every evaluation measured below
the check found a capture zero times.

The stopgap lists up to three free names per node and brings
`factorial(100)` from 3,263,063,793 ticks to 5,210,715. It is a cap: a node
with a fourth free name is searched again, and the searches that remain on
its branch (730,051 visits in `least_divisor(44521, tt).1`) are mostly that.
The cost is not the arithmetic's but the representation's: one node kind,
`CC_VAR`, stands for both a bound variable and a context reference, so
substituting into a body must ask whether the value's free names meet the
binders on the way down. A representation that tells the two apart has no
such question to ask.

## 1. Current state, from the source

### 1.1 Three roles, one representation

| Role | Today | Bound or created by | Enforced by |
| --- | --- | --- | --- |
| Bound term variable | `CC_VAR(symbol)` under `CC_PI`, `CC_LAM`, `CC_SIGMA`, whose payload is the symbol; it binds child 1 only, never the domain | the binder instructions, from the discharged entry's symbol | `ck_term_binder`; `ck_term_free` skips child 1 when the payload is the name |
| Bound level variable | `CC_VAR(symbol)` inside a level (`U`'s child, `CC_LAPP`'s child 1, a `CC_SORT`'s recorded levels), under `CC_LPI`/`CC_LLAM` | `cc_instr_level_pi`, `cc_instr_level_lambda` | `ck_term_binder` counts `CC_LPI` and `CC_LLAM` among the term binders: level and term variables share one symbol space |
| Bound dimension | a dimension index 0..63 in formulas, under `CC_PATH` (binds the family), `CC_PLAM` (family and body), `CC_COMP` (family and tube terms, not faces or base), `CC_HCOMP` (tube terms only), `CC_TRANS` (family only) | the dimension binder instructions, from the discharged dimension entry's index | `ck_dim_binder`, `ck_free_dims`, the binding rules in `substitution`'s `SUBSTITUTE_RENAME_DIMENSION` and `SUBSTITUTE_CHILDREN` stages |
| Term context entry | `CC_VAR(symbol)`, the entry's symbol | `cc_instr_extend`: a symbol names at most one live entry; the same symbol at an alpha-equal type returns the same entry (`find_entry`) | `ck_instr_entry`, `cc_instr_variable` (`ck_var(e.symbol)`) |
| Level entry | `CC_VAR(symbol)` in a level; its type is `LBound(1)` | `cc_instr_level`, sharing the term entries' symbols | `level_context` maps each normal-form key back to an entry with `find_entry` |
| Dimension entry | the index itself; `cc_entry.symbol` is the index | `ck_instr_dimension_entry`, one per index, cached in `dimension_entries` | `ck_instr_merge` refuses two dimension entries with one index; `ck_instr_discharge` refuses a binder that would capture another dimension entry with its index |
| Face entry | no name, no type: a clause | `ck_instr_face_entry`, used by `cc_instr_restrict`; its context is its clause's dimension entries | discharged by `ck_instr_on_face` where a partial element's face implies it |
| Admission context | a signature's universe and term parameters, sort and earlier constructors, each `CC_VAR(symbol)` in constructor types | `cc_instr_signature_begin` reads the parameter symbols from the former's `CC_LPI`/`CC_PI` payloads; the sort symbol is an operand | `admission_context` matches entries to them by symbol, `reserved` forbids binders inside a constructor type to reuse them |
| Global reference | `CC_DEFREF(index)`, `CC_SORT(signature index)`, `CC_CON(constructor number; instance)`, `CC_ELIM(signature index)` | `cc_instr_define`, the signature instructions | payloads are table indices; `ck_term_free` and substitution never treat them as names (`CC_DEFREF` has arity 0, the others' payloads are not compared with names) |

So the kernel already has three kinds of reference: bound variables, context
references and global references, and the last are indices today. The first
two share `CC_VAR` and one symbol space, for terms and levels alike; for
dimensions they share the index space 0..63. That sharing is why substitution
needs a capture check: a binder's name (the discharged entry's symbol, as
`former` and `cc_instr_lambda` write `e.symbol` into the payload) and a free
name in the value are the same kind of thing, so they can collide.

The symbol space is shared with the driver: `cc_kernel_fresh_symbol` and
`ck_fresh_symbol` hand out `next_symbol`, and `ck_make` raises `next_symbol`
past any symbol a `CC_VAR` or term binder is built with, so driver names and
kernel names never meet. A rollback never lowers it.

### 1.2 The kernel's own fresh names

| Where | Function | Role the fresh name plays |
| --- | --- | --- |
| capture renaming | `substitution`, stage `SUBSTITUTE_RENAME_TERM` | a bound variable renamed so the value's free name is not captured |
| dimension capture renaming | `substitution`, `SUBSTITUTE_RENAME_DIMENSION`, with `ck_fresh_dimension` | a bound dimension renamed likewise |
| iota's display | `parts` (each constructor argument, each shown position), `arity` (a position's arity binders), `shown_positional` in `kernel/src/eliminators.c` | placeholders for bound variables of the constructor's type: opened binders, substituted away once the reduct is built (`ck_eliminate`) |
| simultaneous substitution | `apply_substitution` in `kernel/src/signatures.c` | every admission symbol first renamed to a fresh one, so the values are never substituted into: a workaround for having no simultaneous substitution |
| cumulativity | `ck_syntactic_cumulative` | one name to open two binders' bodies with, to compare them |
| new binders | `cc_instr_eta` (Π and level Π), `ck_reduce_composition` (at Π and level Π), `ck_equiv_type`, `ck_fiber_type`, `ck_contractible_type`, `ck_identity_equiv`, `expected` and `ck_clause_type` in `eliminators.c`, `squash_type`, `cc_instr_sum_elim`'s case types | the bound variable of a binder the kernel builds |
| new dimension binders | `cc_instr_eta` at a path type, `ck_fill`, path composition, `displayed`, `shown_boundary`, `ck_identity_equiv`, the Glue and higher-sort computations | the same for dimensions, chosen by `ck_fresh_dimension` below 64 |
| the generated constructor | `cc_instr_signature_close`: the squash constructor's symbol (`.symbol = ck_fresh_symbol(k)`), which `add_constructor` keeps in the signature table and `cc_kernel_signature_constructor` reports; its `.self` in the shape check; and `squash_type`'s binders `y_j`, `z_j` | a label stored outside any term, the only fresh symbol that is; the binders are bound variables |

Every kernel fresh name is a bound variable, a placeholder for one, in
`apply_substitution` a placeholder for an admission symbol about to be
replaced, or the generated constructor's label. Apart from that label, none
names anything or outlives the operation that took it except as a binder's
name. The binder names that do persist sit in judgements' terms and types:
eta's, the clause types', the eliminator's `Π (z : I). M(z)` (`expected`),
composition's in a Step's result, the equivalence types' in Glue
judgements, and capture renaming's. Besides `ck_fresh_symbol`, `next_symbol`
moves only up, in `ck_make` past a symbol a `CC_VAR` or term binder is built
with, which the entry and signature instructions use to reserve their
symbols (`ck_var` in `cc_instr_extend`, `cc_instr_level`,
`cc_instr_signature_begin` and `cc_instr_signature_constructor`).

A fresh name's cost and its effect on a result's identity differ by whether
it stays in the result:

- **Substituted away.** `apply_substitution` renames each admission symbol to
  a fresh one, then substitutes the value for it; the constructor type's own
  binders keep their names, and capture renaming touches them only when a
  value mentions a free name that one of those binders also uses. So for a
  closed instance, and for any instance whose free names avoid the
  constructor type's binder names, `ck_constructor_type` returns the same
  handle every call, by hash-consing (a review's control run: two Construct
  instructions from distinct instance judgements gave one type handle). What
  each call pays is the work: two substitution passes per admission symbol,
  each keyed in the syntax memo by a fresh symbol no earlier call used, so
  none is answered from the memo. The iota display's variables are likewise
  substituted away from the reduct.
- **Kept as a binder's name.** `ck_clause_type` (its Π binders are `parts`'s
  fresh symbols), `ck_equiv_type` and its helpers, `cc_instr_eta` and
  composition at Π and level Π return a new handle every call, the same up to
  bound names, which neither hash-consing nor the syntax memo can share.

### 1.3 Substitution and the capture check

`ck_substitute(term, name, value)` (`kernel/src/term_substitution.c`) is one
worklist, `substitution`, shared with dimension substitution:

1. `term_substitution_ready` looks the request up in the syntax memo
   (operation 3, keyed by term, name and value), takes a tick, and asks
   `ck_term_free(term, name)`: a term without the name is returned as it is.
2. At each term binder whose name is not the one substituted
   (`SUBSTITUTE_RENAME_TERM`), it asks `ck_term_free(value, binder)`. If the
   value mentions the binder's name it takes `ck_fresh_symbol`, renames the
   binder's body by a nested substitution, and continues.
3. At each dimension binder whose index the value's free dimensions contain
   (`ck_free_dims(value)`), it renames the binder to `ck_fresh_dimension`.

`ck_term_free` answers from `cc_node.symbols`, a 64-bit filter of every name
the node mentions, bound ones included (`ck_make` ORs the children's masks
and never clears a binder's bit), then from the syntax memo (operation 1),
and otherwise searches. Dimensions are exact: `ck_free_dims` computes a
node's free dimensions once, keeps them in `dims` with `dimensions_known`,
and a dimension is bit `d` itself, not `d % 64`. So the dimension capture
check costs nothing after the first scan, and the term capture check is the
one that searches.

Level substitution is term substitution: `ck_level_instantiate` is
`ck_substitute` followed by `ck_canonical_levels`.

`cc_kernel_rename` exposes free-name substitution to the driver (term or
dimension), and `cc_kernel_endpoint_term` dimension substitution.

### 1.4 Comparison up to bound names

`ck_alpha_equal` (`kernel/src/term_conversion.c`) is a worklist. A binder
pair pushes a binding (`bind`): the left and right names, a scope id interned
in `alpha_scopes` so that equal renaming chains share memo keys, and 64-bit
masks of the names renamed so far. `same_name` resolves a variable through
the chain. Results go to `alpha_memo`, keyed by both handles and both scope
ids. At a pair of which either node has depth 8 or more, `renamed_free` (via
`ck_term_free`) and `renamed_dims_free` drop a scope that neither side
mentions, so that shared subterms compare under the empty scope.
`level_alpha` compares levels by normal form, giving each bound level
variable the key `1 << 63 | scope`.
`formula_equal` compares formulas clause by clause through the dimension
scope; formulas are interned by set equality (`ck_formula` with `cc_equal`),
so with no dimension renamed equal formulas are one id. A `CC_PAPP` is
compared on its path only (arity 1 in `alpha_traverse`), not on its optional
annotation.

So "identical up to bound names", the instructions' side condition
(`ck_instr_same`), is equality up to term, level and dimension binder names,
with levels compared by normal form and formulas as clause sets, ignoring
path-application annotations.
`ck_syntactic_cumulative` opens two Π, Σ or level Π bodies with one fresh
variable and compares them again; `cc_kernel_alpha_equal` is the query.

### 1.5 Instructions that care about names

- **Extend, Level, Variable.** `cc_instr_extend` and `cc_instr_level` key
  entries by symbol (`find_entry`, `index_entry`); `cc_instr_variable`
  builds `ck_var(e.symbol)`.
- **Binders.** `former` (Pi, Sigma), `cc_instr_lambda`,
  `cc_instr_level_pi`, `cc_instr_level_lambda`, `cc_instr_path`,
  `cc_instr_path_lambda`, `cc_instr_comp`, `cc_instr_hcomp` and
  `cc_instr_trans` discharge one entry with `ck_instr_bind` or
  `ck_instr_discharge` (refused while another entry depends on it) and write
  the entry's symbol or index into the binder's payload. The body is used as
  it is: building a binder costs one node, whatever the body's size.
- **Instantiation.** `cc_instr_apply`, `cc_instr_family`, `cc_instr_pair`
  and `cc_instr_second` substitute into a Π or Σ body with `ck_substitute`;
  `cc_instr_level_apply` with `ck_level_instantiate`; `cc_instr_path_apply`
  and `cc_instr_path_at` with `ck_dimension_substitute`.
- **Contexts.** `ck_instr_merge` is a sorted union of global entry ids;
  `ck_instr_discharge` drops entries and publishes a new set; terms are never
  touched, and an entry stays in `k->entries` after it is discharged.
- **Positions through binders.** `cc_instr_step` and `cc_instr_replace`
  follow a path of child indices (`locate`), through binders too
  (`bound_under`). Step contracts the subterm found there as it is: its free
  names include the names of the binders crossed. Replace requires that,
  where the equality's sides use a name bound on the way down (`needed`, by
  `ck_term_free` or `ck_free_dims`), the replacing equality's context hold an
  entry with that name (`context_entry`, by symbol) at the binder's type,
  and discharges it; a composition's dimension is refused there.
- **Eta.** `cc_instr_eta` builds λ, level λ and path λ over fresh names.
- **Restrict, systems, Glue.** `cc_instr_restrict`, `cc_instr_system_tube`,
  `cc_instr_system_overlap`, `cc_instr_glue_piece` and
  `cc_instr_glue_term_piece` read dimension names only: faces may not use the
  composition's dimension, and a tube must be restricted already
  (`ck_free_dims(u.term) & names`). `cc_instr_glue_piece` compares with
  `ck_equiv_type`, built over fresh names each time.
- **Signatures.** `cc_instr_signature_begin` takes its parameter symbols
  from the former's binder payloads; `cc_instr_signature_constructor` checks
  the context by symbol (`admission_context`), the shape by binder payloads
  (`constructor_shape`, `positional`, `reserved`) and stores the constructor
  type over the admission symbols; `ck_constructor_type` instantiates it by
  `apply_substitution`.

### 1.6 Caches, compaction and guards

- `weak_cache`, `normal_cache` and `folded_cache` hold a completed weak head
  or normal form per handle; no context is consulted, so a handle's answer is
  global (`ck_whnf`, `normal`).
- The syntax memo (`ck_memo_get`, `ck_memo_put`, 8,192 slots) holds
  operation 1 (`ck_term_free`), 3 (term substitution), 4 (canonical levels),
  5 (`normal_agree`) and 6 (dimension substitution). The alpha memo holds
  comparisons by scope.
- `cc_kernel_rollback` truncates the arena, the definitions, the judgement
  store (facts, entries, context sets) and the signatures to the checkpoint,
  and clears every cache and memo. `cc_kernel_commit_checkpoint` keeps the
  nodes reachable from new definitions, the signatures' terms
  (`signature_terms`) and `CC_DEFREF` nodes, renumbers them, clears the
  caches, and truncates the judgement store, entries included
  (`truncate_store`); an open signature blocks it. Definitions are closed
  (`cc_instr_define` refuses a nonempty context), so no surviving definition
  mentions an entry.
- `ck_make` refuses syntax deeper than 512. `ck_enter` bounds nested
  recursion to 448 steps and 4 MiB of stack (`CC_RECURSION_LIMIT`,
  `CC_STACK_BUDGET`). Substitution, `ck_term_free`, `ck_free_dims`,
  comparison, weak-head tails and full normalization are worklists (#291,
  #292, #294, #297); the guards of #321 and #322, with their tests in
  `kernel/tests/test_normalize.c`, `kernel/tests/test_traversals.c` and
  `tests/weak-head-tail.test.mjs`, keep them so.

### 1.7 What the names cost, measured

Counts from main `a933a0bf` with temporary counters, through the REPL on the
kernel's path (each entry after its setup; ticks are deterministic query
steps):

| Entry | Ticks | `ck_term_free` visits | Capture checks at binders | Captures found | Iota steps | Nodes made by iota | Fresh symbols |
| --- | --- | --- | --- | --- | --- | --- | --- |
| `factorial(40)` | 7,764,892 | 7,201,496 (93%) | 55,006 | 0 | 10,149 | 130,468 | 43,527 |
| `factorial(60)` | 138,249,298 | 136,678,663 (99%) | 148,799 | 0 | 31,229 | 410,503 | 136,092 |
| `least_divisor(44521, tt).1` | 6,777,422 | 3,130,565 (46%) | 340,952 | 0 | 55,108 | 513,095 | 198,999 |
| `least_element(…, 1000000, tt).1` | 5,183,171 | 3,272,148 (63%) | 217,147 | 0 | 18,725 | 202,817 | 73,501 |
| Peano count of 300 | 1,908,195 | 812,440 (43%) | 128,293 | 0 | 10,412 | 104,347 | 38,526 |
| `euclid(7).1` | 1,896,001 | 838,871 (44%) | 100,171 | 0 | 15,043 | 138,519 | 53,582 |

Each iota step calls `ck_constructor_type` once and makes 9 to 13 nodes
(the report on the stopgap branch found 1,406,670 of `factorial(100)`'s
2,314,926 nodes made there).

Checking, the import closure of `binary_rationals` (the setup of
`evaluate 2/3 + 1/6`): 502,875 instructions, 11,223,319 ticks (7,521,025 in
instructions, 3,702,294 in queries), of which 2,104,442 (19%) were
`ck_term_free` visits; 581,268 capture checks found 231 captures; 4,004
dimension binders were renamed; comparison bound 18,695 term or level
binder pairs;
75,715 fresh symbols were taken. The closure of `nat` (126,148 instructions,
536,082 ticks) spent 79,204 ticks (15%) in `ck_term_free`.

## 2. The options, compared on this kernel

The question is how to represent the two roles that share `CC_VAR`. Global
references stay as they are in every option.

**(a) Locally nameless: bound variables by index, context references by
entry.** A binder has no name; `CC_BOUND(i)` refers to the `i`-th enclosing
binder; `CC_CONTEXT(e)` refers to entry `e`.

- Substitution becomes instantiation of `CC_BOUND(0)` by a value that has no
  loose indices: nothing in the value can be captured, so there is no check
  and no renaming. A node's loose-index range (one more than its greatest
  index not bound inside it) is exact and computed in `ck_make` from the
  children, so a part with no loose index is skipped in O(1), with no cap.
- Comparison of term and level binders needs no renaming: bodies compare
  directly, and alpha-equivalent terms hash-cons to one handle.
- Hash-consing shares what fresh binder names keep apart today (clause
  types, equivalence types, eta and composition at Π), and the temporary
  names whose passes cost work without changing the result
  (`ck_constructor_type`, iota's display) go.
- Context merging is unchanged: entries keep their global ids, so a merge
  touches no term (the user's point, confirmed: `ck_instr_merge` is a union
  of entry-id sets).
- Discharge (a binder instruction) now abstracts: it replaces
  `CC_CONTEXT(e)` by `CC_BOUND` at each depth. That is a traversal where
  today there is none (section 3.3 measures it).
- Replace under binders opens the target with the entries the driver names
  for the binders crossed, and abstracts them out of the replacement. Those
  entries must be fresh for the rewritten judgement (section 3.6): an entry
  that a binder's name can no longer tell apart from an ambient one would
  otherwise alias it.
- Checkpoint compaction is unchanged for definitions (closed). Signature
  constructor types must be stored closed over their admission telescope,
  since commit truncates the entries they mention today by symbol.
- Cost: working under a binder needs a variable for it, and abstracting
  again needs a traversal.

**(b) Pure de Bruijn indices for everything, context references included,
with lifting.** A judgement's context would have to be a sequence, and a
term's free variables positions in it. But contexts here are sets of global
entries that premises merge (`ck_instr_merge`), not prefixes: every
instruction with two premises would renumber both premises' terms, every
discharge of an entry that is not last would lower the later references,
and the same term in two contexts would be two nodes. Weakening, which is
free today, would be a traversal. Every computation that moves a term under a
binder would lift it. Rejected.

**(c) De Bruijn levels for context references.** A level counted in the
judgement's own context has (b)'s problem at every merge. A level counted in
one global list of entries is the entry id itself, which is (a). The
user's proposal of a position in the context list, with discharge
decrementing later references, is the per-judgement variant: considered and
rejected for the same reason (a merge would renumber terms, and a term would
mean different things in different judgements, so its weak head and normal
form could no longer be cached by handle).

**(d) Names kept, with an exact free-name set per node.** Interned,
out-of-line sets of free names (the stopgap without its cap). Substitution
keeps its capture check, answered exactly; renaming stays (it is rare: 231
in the measured closure); comparison keeps its renaming chains; hash-consing
still keeps alpha-variants apart; the kernel's fresh names stay. Sets must
be built for every new node (a union per node, quadratic in the worst case
for a term with many free names, as under many binders), stored, interned,
and rolled back and compacted with the arena. It fixes the measured cost but
keeps the conflation of roles and all the machinery that serves it.

**Recommendation: (a)**, with `CC_CONTEXT(e)` holding the global entry id.
It removes the capture check rather than answering it faster, and it is the
only option whose context handling is unchanged.

### 2.1 The starting hypothesis, checked

The proposal began as: bound variables by index, context entries by name,
because judgements keep only the entries they use and merge contexts by
entry; no capture check, exact loose-index ranges, one handle per
alpha-equivalence class; costs in opening and closing binders and at the
ABI. Against the source:

- **Confirmed:** contexts are sets of global entries merged by
  `ck_instr_merge` without touching terms, so context references must not be
  positions; instantiation needs no capture check for term and level
  binders; the loose-index range is exact and uncapped.
- **Corrected: who opens binders.** Comparison does not open them (bodies
  compare directly); the driver's decoding keeps a name stack, which is no
  kernel work; iota needs no fresh variables at all. Only normalization,
  Step at a position under binders, Glue's `parts_agree`, and
  `cc_kernel_whnf` on a term with loose indices (for the driver's guide)
  open binders, with an internal kind, not an entry (section 3.1).
- **Corrected: one handle per class** holds for term and level binder names
  only. Dimension binder names, level syntax (compared by normal form) and
  path-application annotations still differ by handle, so `ck_alpha_equal`
  stays, without term scopes.
- **Corrected: no renaming at all.** Dimension capture renaming stays, from
  exact masks.
- **Added: discharge now costs a traversal.** A binder instruction reuses
  the body as it is today; abstraction rebuilds the nodes mentioning the
  entry (section 3.3).
- **Added: commit truncates entries**, so signature constructor types must
  be stored closed (section 3.4).
- **Added: entries the driver supplies for binders must be fresh.** Today a
  binder's name picks its entry; without names, Replace, the driver's
  opening and signature admission each need a stated condition against an
  aliased entry (section 3.6).
- **Added: checking may not get faster** (section 6.2).

## 3. The proposed representation

### 3.1 Node kinds

| Kind | Payload | Children | Meaning |
| --- | --- | --- | --- |
| `CC_BOUND` (new) | de Bruijn index | none | the variable of the `i`-th enclosing term or level binder (0 the innermost) |
| `CC_CONTEXT` (new) | `cc_entry_id` | none | a term or level entry of the judgement store |
| `CC_OPENED` (new, internal) | de Bruijn level | none | a binder the kernel opened inside one operation; never in a judgement, a definition or a query's answer |
| `CC_PI`, `CC_LAM`, `CC_SIGMA`, `CC_LPI`, `CC_LLAM` | 0 (no name) | as today | binds `CC_BOUND(0)` in child 1 |
| `CC_DEFREF`, `CC_SORT`, `CC_CON`, `CC_ELIM` | as today | as today | global references |
| `CC_VAR` | retired | | its number stays reserved, as `CC_NAT`'s is |

Term and level binders form one de Bruijn chain: a level variable bound by
`CC_LPI` is `CC_BOUND` like a term variable, and a level entry is
`CC_CONTEXT` like a term entry, as they share `CC_VAR` today. A level normal
form's key becomes the reference itself: `CC_CONTEXT(e)` keys by `e`, and
`CC_BOUND(i)` and `CC_OPENED(m)` by `i` and `m` in two key ranges above every
entry id, so `ck_level_build` rebuilds the right kind and `level_context`
finds the entry without `find_entry`. `level_alpha`'s `1 << 63 | scope` keys
go: bound level variables compare by index.

**Why `CC_OPENED`.** Opening a binder to work under it needs a free variable
that is not bound. A temporary entry would be a judgement-store record with
a type judgement, a context and a scope, made by a query, and its id would be
reused after the store truncates it. So the kernel gets a third, internal
kind, numbered by de Bruijn level.

**Reserving levels.** Each operation that opens binders reserves its levels
from a counter of its own, a C local passed to the helpers it calls, never a
kernel-wide field. The counter starts above every opened level in every
operand the operation will combine with what it opens: the maximum of those
operands' `opened` fields (below). It hands out one level per binder opened
and reuses none before the operation ends. A rule local to the term being
opened is not enough: porting `parts` (a clause type's telescope) with
placeholders, for `fork : S → S → S`, opening the first argument puts
`CC_OPENED(0)` into the constructed term `fork(OPENED(0))` but not into the
rest of the telescope, `Π (y : S). S`, which still has no opened level; a
term-local rule would open `y` at 0 as well and build `M(fork(y, y))` where
`M(fork(x, y))` is meant. The operation's counter gives `y` level 1. The
start is a function of the operands, so the same operation on the same
operands opens the same binders at the same levels and makes the same
handles: caches are shared, which fresh symbols prevent today.

Closing `CC_OPENED(m)` replaces it by `CC_BOUND` at each depth, and visits
only nodes with `opened > m`. Every opener closes in the reverse order of
opening, and a nested operation closes its own levels before it returns, so
when `m` is closed no greater level is live, and those nodes are exactly the
ones containing it; closing out of order would visit more nodes, never give a
wrong answer. Every opening is closed before its operation returns;
`ck_make` refuses `CC_OPENED` from `cc_kernel_term`, and the `opened` field
lets each query and instruction check its answer in O(1).

The openers, and the operands each reserves above:

| Opener | Operands its counter starts above |
| --- | --- |
| normalization under a binder (`normal`) | the binder term being normalized; it combines with nothing else, since the parent frame receives the closed result |
| Step at a position under binders (`cc_instr_step`) | the target, whose judgement holds no opened level, so the crossed binders take 0, 1, … |
| `parts_agree` (Glue's side conditions) | both sides |
| clause and constructor types if ported with placeholders (`parts`, `arity`, `ck_clause_type`, `expected`) | the instance, the motive, the clauses given and the constructor type, and every argument opened so far, by the shared counter |
| equivalence constructions (`ck_equiv_type`, `ck_fiber_type`, `ck_contractible_type`, `ck_identity_equiv`) | their type and term operands, which may hold levels when a Glue computation runs under a normalization's opened binder; the helpers share the caller's counter |
| composition at Π and level Π (`ck_reduce_composition`) | the composition term |
| `cc_kernel_whnf` on a term with loose indices (the driver's guide, section 5.1) | the query's term, which holds no opened level |

Iota needs no opener: it instantiates the constructor's telescope by the
actual arguments, and builds each position's λ over its arity binders by
mirroring the position's own Π telescope (section 3.3). Were it ported with
placeholders instead, it would reserve above its arguments, the eliminator
and the instance, like the clause types.

The driver opens binders too, but differently: to derive a body it needs a
judgement in a context, so it makes a real entry with `cc_instr_extend`, as
today, and opens the body with it, one binder at a time
(`cc_kernel_instantiate`, section 5.1). That entry is discharged by the
binder instruction and truncated with the judgement store, as every entry
is.

A `CC_CONTEXT(e)` gives its variable's type directly, as `k->entries[e].type`;
nothing is looked up by symbol.

**Display spelling** lives in the driver, as the header already says of
names. A binder node holds no name, since a name in the node would keep
alpha-equivalent terms apart. The driver names bound variables when it
decodes, and keeps its names for entries in its scopes (section 5.3).

### 3.2 Node metadata

Today's `cc_node` is 48 bytes, natively (arm64) and under WebAssembly
(wasm32), measured with `sizeof` and `offsetof`: `kind` (the enum, 4 bytes)
at 0, `payload` at 4, `child[4]` at 8, `depth` (`unsigned`) at 24,
`dimensions_known` at 28, padding to 32, `symbols` at 32, `dims` at 40.
Adding two 32-bit counters as they stand would make it 56. Narrowing `kind`
to 8 bits (the largest kind, `CC_LIST`, is 53; three new kinds make 56) and
`depth` to 16 bits (`ck_make` bounds it by 512) keeps 48, with full 32-bit
counters; the same `sizeof` check of this layout gives 48 on both targets:

| Offset | Field | Width | Range |
| --- | --- | --- | --- |
| 0 | `kind` | 8 bits | the `cc_term_kind` values, below 256 |
| 1 | `dimensions_known` | 8 bits | as today |
| 2 | `depth` | 16 bits | 1 to 512, refused above by `ck_make` as today |
| 4 | `payload` | 32 bits | as today; for `CC_BOUND` and `CC_OPENED` below `UINT32_MAX` |
| 8 | `child[4]` | 4 × 32 bits | as today |
| 24 | `loose` | 32 bits | 0 to `UINT32_MAX` |
| 28 | `opened` | 32 bits | 0 to `UINT32_MAX` |
| 32 | `contexts` | 64 bits | the filter, replacing `symbols` |
| 40 | `dims` | 64 bits | as today |

- `loose`: one more than the greatest loose `CC_BOUND` index, 0 when the
  node is locally closed. For `CC_BOUND(i)` it is `i + 1`; for a binder, the
  larger of the domain's `loose` and the body's `loose` less one (0 when the
  body's is 0); otherwise the children's maximum. Exact.
- `opened`: one more than the greatest `CC_OPENED` level, the children's
  maximum, no binder lowering it. Exact.
- `contexts`: replaces `symbols`. A 64-bit filter of the `CC_CONTEXT` ids
  the node mentions (bit `e % 64`). Zero exactly when the node mentions no
  entry, which is the "mentions any context entry" flag; otherwise an
  over-approximation, like `symbols` today but over context references only,
  so a closed definition body or computed value is always zero.
- `dims` and `dimensions_known` as today.

The only way a counter could overflow is a leaf: `i + 1` for `CC_BOUND(i)`
with `i = UINT32_MAX` would wrap to 0 and call an open term closed, and a
binder or a parent never adds. So `ck_make` refuses `CC_BOUND` and
`CC_OPENED` with payload `UINT32_MAX` as a resource error, as it refuses a
`CC_VAR` or binder symbol of `UINT32_MAX` today ("Term symbol space
exhausted."), and refuses `CC_OPENED` from `cc_kernel_term` altogether. An
opener's counter that would reach `UINT32_MAX` fails its operation the same
way; in practice levels stay near the syntax depth. Overflow tests: a
`CC_BOUND(UINT32_MAX - 1)` leaf has `loose == UINT32_MAX` and is not closed;
`CC_BOUND(UINT32_MAX)` is refused by `cc_kernel_term`; a binder over the
largest leaf lowers it by one; and the randomized metadata test draws
indices near both ends.

### 3.3 Operations

Proposed primitives, each a worklist like `substitution`, ticking per node,
memoized in the syntax memo by their operands:

- **Instantiate** `t` at index 0 by a locally closed value `v`: visit only
  nodes with `loose > 0` that contain the index being replaced (at depth `d`,
  nodes with `loose > d`); replace `CC_BOUND(d)` by `v`. No capture check: `v`
  has no loose index to capture, and its `CC_CONTEXT` and `CC_OPENED`
  references cannot be bound by a binder of `t`. Dimension capture stays: a
  dimension binder of `t` whose index `v` mentions free is renamed as today
  (`SUBSTITUTE_RENAME_DIMENSION`; 4,004 times in the measured closure, from
  exact masks). A simultaneous form instantiates several indices in one pass
  (signatures, iota).
- **Abstract** `CC_CONTEXT(e)` in `t`: replace it by `CC_BOUND` at each depth.
  Nodes whose `contexts` is zero are skipped exactly; nodes whose filter lacks
  bit `e % 64` are skipped; others are searched, with the memo. It is used by
  the binder instructions and by Replace.
- **Open** a binder's body with `CC_OPENED(m)`, and **close** `CC_OPENED(m)`:
  instantiate and abstract with exact pruning by `loose` and `opened`.

The invariant that keeps the trusted reduction simple: **reduction,
iota, composition, Glue and the equivalence constructions only ever see
locally closed terms.** `ck_whnf` checks `loose == 0` in O(1) on entry. Then
none of them shifts an index: a locally closed part moved under a new binder
needs no lifting, and only the four primitives above touch indices.

How each piece changes:

- **Beta, Apply, Family, Pair, Second** (`weak`, `contract`,
  `cc_instr_apply`, `cc_instr_family`, `cc_instr_pair`, `projection`):
  `ck_substitute(body, payload, value)` becomes instantiate; the value is a
  judgement term or a weak head's argument, locally closed.
- **Level application** (`cc_instr_level_apply`, `CC_LAPP` in `weak`):
  instantiate, then `ck_canonical_levels`.
- **Eta at a weak head** (`weak` on `CC_LAM`, `CC_LLAM`): `λ. f (CC_BOUND 0)`
  contracts when `f.loose == 0`, which is exact and O(1); `f` is then locally
  closed and is the result. The `ck_term_free` calls go.
- **Comparison** (`ck_alpha_equal`): no term scopes, no `renamed_free`, no
  level keys by scope; binders compare their children directly. The
  dimension scopes, level normal forms, formula comparison and the
  `CC_PAPP` annotation rule stay, so the function stays, with the identical
  handle as its first exit far more often.
- **Cumulativity** (`ck_syntactic_cumulative`): compares the two bodies
  directly, no fresh variable.
- **Normalization** (`normal`): at a term or level binder, opens the body with
  `CC_OPENED(m)`, normalizes it, and closes the result. The weak, normal and
  folded caches stay keyed by handle; an opened body is a term like any
  other, and determinism lets a binder opened twice hit the cache.
  `parts_agree` (Glue's side conditions) opens a common binder before
  comparing its parts likewise.
- **Iota** (`ck_eliminate`): the display's fresh variables go; its
  construction stays. The constructor's argument telescope is instantiated
  by the actual arguments. Each position `q_j : Π (ys : As). C_j` is shown by
  its value `λ ys. elim^{C_j}(q_j(ys))`, where `elim^C`, built by `lifted`,
  is `elim(y)` when `C` is the sort and `⟨i⟩ elim^{C'}(y @ i)` when `C` is a
  path type over `C'`, each path application annotated and each path
  abstraction's family the displayed cube (`displayed`). So a path-valued
  position, such as `p` in `wrap : Path(S, base, base) → S`, is shown as
  `⟨i⟩ elim(p @ i)`, never as `elim(p)`, which would be ill-typed. The λ
  over the arity binders mirrors the position's own Π telescope, so its
  domains and the cube under it are reused with their loose indices as they
  stand, and iota opens nothing; the cube's dimension binders stay named, as
  `lifted` names them today. The reduct is the clause applied to the
  arguments and the shown positions, then applied at the constructor's own
  dimensions with its displayed result type (`ck_apply_at`).
  `ck_constructor_type` becomes one simultaneous instantiation of the
  stored, closed constructor type
  (section 3.4), with no renaming pass. Its result is already one handle per
  closed instance today (section 1.2), so memoizing it by instance and
  constructor needs no migration and could be done on main now; what the
  migration changes is the per-call work, and that open instances get one
  handle too. Skipping the display for constructors that need none, which
  every `BPositive` constructor is, is the stopgap report's "next lever"; it
  is a separate step (PR 4 below, with its exact eligibility test), not part
  of the representation change.
- **Binder instructions** (`former`, `cc_instr_lambda`,
  `cc_instr_level_pi`, `cc_instr_level_lambda`): the body, and for λ also
  its type, is abstracted over the discharged entry. `ck_level_limit` reads
  the entry's key before abstraction. The dimension binders' instructions
  (`cc_instr_path`, `cc_instr_path_lambda`, `cc_instr_comp`, `cc_instr_hcomp`,
  `cc_instr_trans`) are unchanged: they write the dimension's index into the
  payload and traverse nothing.
- **Step at a position under binders** (`cc_instr_step`): opens the target
  with one `CC_OPENED` level per binder crossed, contracts, closes, and
  rebuilds the path.
- **Replace under binders** (`cc_instr_replace`): the driver names, for each
  term or level binder crossed, the entry standing for it (0 where none is
  used), since a binder has no symbol to match. The kernel requires those
  entries to be fresh (section 3.6), checks each entry's type against the
  binder's domain opened with the outer entries (as `ck_instr_same` does
  today against the domain as written), opens the target with them, refuses
  if a loose index is left (a binder the target uses has no entry), compares
  with the equality's left side, abstracts them out of the right side, and
  discharges them from the equality's context. This is an ABI change of
  `cc_instr_replace`, and the entry vector joins its derivation's memo key
  (section 3.7).
- **Eta instruction, composition at Π and level Π, equivalence types,
  clause types, the squash** (section 1.2's "new binders"): built directly
  with `CC_BOUND`, or with `CC_OPENED` placeholders closed at the end, which
  is the mechanical port of today's fresh-symbol code. Their results become
  deterministic.
- **Queries and other entry points that take syntax**: raw syntax the
  driver builds is closed over entries (section 5.3), so the only loose
  terms that reach the kernel are subterms the driver read under binders of
  a judgement's term. One driver path asks about those: its guide compares
  two terms head by head and descends into binder bodies, asking for their
  weak heads (`guide`, `compareHeads`, `headOf`). So `cc_kernel_whnf` opens
  loose indices with `CC_OPENED` levels, computes, and closes the answer;
  comparison and dimension substitution work on loose terms as they are;
  every other entry point that would have to open a loose term refuses it
  (section 5.1 lists them all).
- **Hash-consing** (`ck_make`'s interning): unchanged code; it now identifies
  alpha-equivalent terms whose binders differ only in term or level names.
  Terms equal up to dimension binder names, level syntax or path
  annotations remain distinct handles and are still compared by
  `ck_alpha_equal`.
- **Caches and checkpoint**: unchanged. Entry ids are truncated by rollback
  and commit with the nodes made since the checkpoint, and commit keeps only
  closed definitions and the signatures' closed terms (below), so no
  surviving node mentions a truncated entry. `ck_make` refuses a
  `CC_CONTEXT` whose id is not a live term or level entry.

**Is abstraction hot?** Not in evaluation: the six entries above issue 4 to 6
binder instructions each. In checking, the `binary_rationals` closure made
35,163 abstractions (Pi, Sigma, λ and its type, level binders), which would
rebuild 346,390 nodes containing the entry; a search with no filter would
visit 1,179,595 nodes of those bodies. The `contexts` filter skips the
closed parts and most parts mentioning other entries. That is 3% to 11% of
the closure's 11.2 M ticks, against the 19% of `ck_term_free` visits removed.
The computation's hot path is instantiation, which the exact `loose` range
covers.

### 3.4 Signatures

While a signature is open, its parameters, sort and earlier constructors are
entries, referenced as `CC_CONTEXT` like any other: the constructor type's
judgement has them in its context. Since the former's binders have no names,
`cc_instr_signature_begin` takes the parameter entries (level entries and term
entries, in order) and the sort entry, and checks each entry's type against
the former's telescope opened with the earlier ones;
`cc_instr_signature_constructor` takes the constructor's entry. These entries
must be pairwise distinct (section 3.6). `admission_context` then compares
entry ids instead of symbols, and `reserved` goes (a binder has nothing to
shadow with). `constructor_shape` identifies positions by de Bruijn depth
instead of binder payloads.

On admission each constructor type is abstracted over the whole admission
telescope (levels, parameters, sort, earlier constructors) and stored closed.
Commit truncates the entries; the stored type mentions none of them. The
signature's `former`, `level` and `parameter_types` are read from the closed
former and carry loose indices relative to its prenex. `ck_constructor_type`
and `complete_instance` instantiate simultaneously, replacing
`apply_substitution`'s two passes of renaming and substitution per symbol.

What the signature reports to the driver (`cc_kernel_signature`,
`cc_kernel_signature_constructor`): its shape (levels, parameters,
constructors with their data, positions and dimensions, the modifier and
`generated`) and its closed terms, with no symbols. Entries carry no names
(decided 2026-11-02), so there are no labels to copy:
`cc_kernel_signature_symbol` and the sort and constructor symbol fields go,
and the driver keeps the names it declared. A constructor's type is
reported closed, with loose indices over the admission telescope, which the
driver decodes with its names for the telescope.

**The generated constructor.** `cc_instr_signature_close` appends the
squash with a fresh symbol today. After the change it needs neither an entry
nor a symbol. It is the last constructor, so no constructor type refers to
it, and nothing would ever open the telescope with an entry for it. Its type
is built closed directly, the sort as the `CC_BOUND` that stands for it in
the telescope and `y_j`, `z_j` as `CC_BOUND`, and checked by
`constructor_shape` as today; `.self`, which only stops a constructor from
naming itself, has nothing to compare for it. It is reported with
`generated` set and no symbol, as every constructor now is, and the driver
names it by that flag. `signatureRecord` in `web/cubical-syntax.mjs` already calls it
`squash` by the flag; `cubical-program.mjs` (`shown`) and
`tools/proof-migration.mjs` (`earlier`) read `c.symbol` for every
constructor, the squash's included, and would name it by the flag too. A
review reproduced the symbol with `inductive Tr : prop { inc; }`.

### 3.5 What happens to today's machinery

Goes: `ck_term_free`, the capture renaming of term binders, `ck_fresh_symbol`
inside the kernel, `symbols`, the term scopes of `alpha_binding`,
`renamed_free`, `bound_keys`' scope keys, `find_entry` for levels,
`apply_substitution`'s renaming, the iota display's variables. Changes:
`ck_substitute` (instantiate), `ck_level_instantiate`, `ck_alpha_equal`,
`normal`, `ck_eliminate`, the binder instructions, `cc_instr_replace`,
`cc_instr_step`, the signature instructions. Stays: dimension names and
their capture renaming, `ck_free_dims`, formulas, entries and contexts, the
judgement graph, checkpoints, the guards.

### 3.6 Entries the driver supplies: no aliasing

Today a binder's name is its entry's symbol, so the kernel finds the entry
for a binder itself (`context_entry` in `cc_instr_replace`) and a binder
cannot be confused with an ambient entry of another name. Once binders have
no names, every place where the driver hands the kernel an entry to stand
for a binder could alias an entry already in play: opening with it would
make the binder's occurrences and the ambient ones one reference, and
abstracting would then bind both. Each such place needs its own condition.

- **Replace** (`cc_instr_replace`). Without a condition it certifies a false
  equality. In `A : U0, e : A`, rewrite the body of `λ (x : A). (x, e)` by
  reflexivity at `(e, e)`, supplying `e` for the binder `x`: opening makes the
  target `(e, e)`, which is the equality's left side, the type check passes
  (`e : A`), and abstracting `e` out of the replacement `(e, e)` gives
  `λ (x : A). (x, x)`. Today's Replace refuses this: the binder's name `x` is
  not `e`'s, so the target `(x, e)` is not the left side `(e, e)` (a review's
  control run on ABI 3 confirmed it). So the kernel requires of the supplied
  entries:
  1. none is in the rewritten judgement's context, which by the
     instructions' invariant holds every entry its term, other side and type
     mention, so the opened target mentions a supplied entry only where its
     binder's variable was, and abstraction binds nothing ambient;
  2. they are pairwise distinct (as today, "One entry would be bound twice on
     the path");
  3. each is of its binder's kind (a level entry for a level binder) and has
     the type of its binder's domain, opened with the entries supplied for
     the binders outside it;
  4. after opening, the target has no loose index left (a binder it uses has
     an entry), and the same holds for each supplied entry's type;
  5. discharging them from the equality's context passes
     `ck_instr_discharge`, which refuses while a remaining entry depends on
     one of them, as today.
- **Binder instructions** (`former`, `cc_instr_lambda`, `cc_instr_level_pi`,
  `cc_instr_level_lambda`). The entry abstracted is the one the rule
  discharges, and every occurrence of it in the body is meant to become the
  bound variable, so there is no ambient occurrence to alias. The condition
  is today's: `ck_instr_bind` refuses while another entry of the body's
  context depends on it.
- **The driver's opening** (`cc_kernel_instantiate`). Its only use is to
  open a binder's body with the entry the driver has just made or reused for
  that binder, one binder at a time, while it derives under the binder
  (`deriveNode`): it replaces index 0 of the body by `CC_CONTEXT(e)`. A query:
  it certifies nothing, and the binder instruction that follows stays sound
  whatever the driver opened with. But an entry the body already mentions
  would derive another term than the one meant (`(x, e)` opened with `e`
  derives `λ. (0, 0)`), and the driver's map from name and type to entry
  (section 5.3) can hand back an entry already in scope, as for
  `λ (x : A). λ (x : A). b`. So the query refuses an entry the body already
  mentions (the `contexts` filter, then a search), and the driver reuses an
  entry only when it is not already in the scope it extends.
- **Signature admission** (`cc_instr_signature_begin`,
  `cc_instr_signature_constructor`). The parameter, sort and constructor
  entries must be pairwise distinct and of the right kind (level entries for
  universe parameters, term entries otherwise), each typed by the telescope
  opened with the ones before it. Distinctness makes abstraction over the
  telescope unambiguous. No ambient entry can alias, because
  `admission_context` allows only the admission entries in a constructor
  type's context; after abstraction the stored type's `contexts` filter must
  be zero, an O(1) check that nothing was left open.
- **The kernel's own openings** (normalization, Step under binders,
  `cc_kernel_whnf` on a loose term, constructions with `CC_OPENED`
  placeholders). A
  `CC_OPENED` level comes from the opener's counter, which starts above every
  level in every operand it combines (section 3.1), so it is fresh by that
  discipline; the condition is that each opener's operand list is complete,
  which the `fork` test of section 7.1 checks for the hardest case.

### 3.7 The new operands in the derivation memo

An instruction answers a repeated derivation from the memo before it checks
anything: `ck_instr_begin` hashes the derivation (`derivation_hash`: the
rule, `premise[4]`, `entry`, `operand[2]`, the depth and the position bytes),
looks it up, and returns the earlier judgement on a match
(`same_derivation`), and `cc_instr_replace` returns at once when it does.
Replace's derivation records its two premises, its side and its position.
With the new API, the binder entries are a further operand that changes the
result: replacing `tt` inside `λ (x : Unit). tt` by `tt ≡ (λ (z : Unit). tt) e`
with the vector `[e]` abstracts `e`, giving `λ (x : Unit). (λ (z : Unit). tt) x`
with `e` discharged, while `[0]` leaves `e` free in the result and in its
context. Under today's key the two would be one derivation, so the second
would be answered with the first's judgement and skip its own checks
(section 3.6).

So the vector is part of the derivation:

- **Storage.** A new store of `uint32_t` entry ids beside `positions`, with
  the derivation recording its offset; the count is the number of term and
  level binders the position crosses, at most the depth, which
  `ck_instr_begin` bounds by 1,024. The pending vector is kept with
  `pending_position` while the instruction runs, and the store is truncated
  at rollback and commit with the others (a sixth slot of
  `checkpoint_store`).
- **Identity.** `derivation_hash` hashes the vector after the position bytes,
  and `same_derivation` compares it entry by entry, so vectors that differ
  anywhere, `0` against an entry included, are different derivations.
- **Reading.** `cc_judgement_info` reports the vector beside the position,
  for the driver's views of a derivation.

The other instructions that gain operands are the signature instructions,
and they do not reach the memo: `cc_instr_signature_begin` and
`cc_instr_signature_constructor` start with `ck_instr_begin_stateful`, which
never answers from it, and `cc_instr_signature_close` records no derivation.
Their entry operands are still recorded with the judgement, for reading.
`cc_kernel_instantiate` is a query: if its results are memoized, the key holds
the body and the entry. Lambda, Pi, Sigma and the level binders
take no new operand (their entry is already `entry`), and Step's internal
openings are no operand.

## 4. Per binder class: what moves, and when

- **Term binders** (`CC_PI`, `CC_LAM`, `CC_SIGMA`): move. They carry the
  measured cost.
- **Level binders** (`CC_LPI`, `CC_LLAM`): move with the term binders, in
  the same change. They share `CC_VAR` and the symbol space today, and
  `ck_term_binder` and `ck_level_instantiate` treat them as term binders;
  moving them separately would keep `CC_VAR` alive for levels alone.
- **Dimension binders** (`CC_PATH`, `CC_PLAM`, `CC_COMP`, `CC_HCOMP`,
  `CC_TRANS`): stay named; left out of this project, with the cap, by the
  user's decision of 2026-11-02. A later project could redesign formulas
  without the cap and move dimension binders to indices together. Their
  "names" are not strings or symbols but bit positions
  0..63: a dimension binder's payload is its index, a formula's clause is a
  pair of 64-bit masks over those indices (`cc_clause`), and a dimension
  entry's `symbol` is the same index. Their capture check is one AND: when a
  value passes under a dimension binder, `substitution` tests
  `ck_free_dims(value) & (1 << payload)`, and `ck_free_dims` answers from
  the node's exact `dims` mask once a first scan has set `dimensions_known`.
  A capture is rare: 4,004 dimension binders were renamed in the whole
  `binary_rationals` closure (11.2 M ticks), and none in the six evaluation
  entries of section 1.7. So moving them to indices would gain nothing
  measurable in speed. It would gain uniformity: path abstractions equal up
  to their dimension's name would share one handle, `ck_alpha_equal` would
  lose its dimension scopes (`renamed_dims_free`, the dimension bindings),
  substitution its dimension renaming (`SUBSTITUTE_RENAME_DIMENSION`), and
  the driver its dimension renaming chains (`prune`, `renameBinder`). It
  would cost: formulas would mix bound dimension indices and dimension
  entries in one 64-bit mask, so the lattice library (`kernel/src/formula.c`,
  `faces.c`, `interval.c`) and every check that reads masks (tube faces,
  `ck_instr_on_face`, `ck_restrict`, endpoint substitution) would have to
  tell them apart by a partition of the bits or a tag; a formula moved under
  a dimension binder would have its bound indices shifted, and formulas are
  interned clause sets, so each shift makes a new formula; and every
  computation that builds a dimension binder around existing parts (`ck_fill`,
  composition at a path type, `displayed` and `lifted` in iota, the Glue and
  higher-sort computations, `ck_identity_equiv`) would need that shifting or
  an opening discipline for dimensions like section 3.1's. It would not lift
  the 64-dimension cap: bound dimensions and entries would still share one
  mask, which a partition splits rather than widens.
- **The 64-dimension cap** belongs to the formula representation, not to
  binders: `cc_clause`'s masks and `CC_DIMENSIONS` in `kernel/include/cubical.h`,
  the lattice operations of `kernel/src/formula.c`, `faces.c` and
  `interval.c`, `cc_node.dims`, `dimension_entries`, `ck_fresh_dimension`,
  the 64-bit check in `ck_instr_merge`, and `ck_restrict`'s and
  `clause_included`'s loops. Making dimension entries `CC_CONTEXT(entry id)`
  would not remove it, because formulas, not terms, hold dimensions; lifting
  it needs a formula representation with unbounded dimension ids. That is a
  separate project, unaffected by this one.
- **Faces and Glue** bind nothing.

## 5. The ABI boundary: version 4

### 5.1 The kernel's side

`CC_KERNEL_ABI_VERSION` becomes 4: `CC_VAR` is retired and reserved;
`CC_BOUND` and `CC_CONTEXT` are added to `cc_term_kind`; a binder's payload
must be 0; the child-order comment changes. `cc_instr_replace` takes the
entries for the binders crossed, and `cc_judgement_info` reports them
(section 3.7); `cc_instr_signature_begin` and
`cc_instr_signature_constructor` take entries instead of symbols, and
signatures report no symbols (section 3.4). `cc_instr_extend` and
`cc_instr_level` take no symbol and make a new entry on every call;
`cc_kernel_entry` reports no symbol for a term or level entry (a dimension
entry's index stays). One new query opens a binder's body with an entry, for
the driver's derivation under binders (`cc_kernel_instantiate`, a proposed
name). `cc_kernel_whnf` accepts a term with loose indices (section 3.3). The
bridge (`wasm/cubical_bridge.c`) changes with the signatures, and the
Makefile's export list gains the new query.

**Every entry point that takes or returns syntax.** The driver reads
subterms under binders (`cb_subterm`, `cb_node`), so any of them may come
back to the kernel with loose indices. The sweep below covers every
`cc_kernel_*` and `cc_instr_*` function of `kernel/include/cubical_kernel.h`
that takes a `cc_term`, and every one of the 45 bridge exports (the
`CUBICAL_EXPORTS` list of the Makefile, the same as the `cb_*` functions of
the bridge):

| Entry point (bridge export) | Takes | With loose indices |
| --- | --- | --- |
| `cc_kernel_term` (`cb_term`) | children | builds the node; a binder lowers its body's range; refuses `CC_OPENED`, an index of `UINT32_MAX` and a `CC_CONTEXT` naming no live term or level entry |
| `cc_kernel_whnf` (`cb_head`) | a term | opens each loose index with a `CC_OPENED` level, computes, and closes the answer back to the same indices: the driver's guide asks for the heads of subterms it read under binders (`headOf` through `graph.head`) |
| `cc_kernel_normalize` (`cb_normalize`), `cc_kernel_normalize_folded` (`cb_normalize_folded`) | a term | refuse it: the driver normalizes only handles an instruction derived (its `derivedHandles` guard in `web/cubical-kernel.mjs`), and a subterm under binders is normalized through Step, which opens it itself |
| `cc_kernel_equiv_type` (`cb_equiv_type`, defined in `kernel/src/instruction_glue.c`) | two types | refuses a loose operand, since its own Σ and Π binders would capture one. Its one driver caller passes judgement terms (`this.statement(type).term` in the instruction driver's Glue path), which are closed over entries, so no wrapper is needed |
| `cc_kernel_alpha_equal` (`cb_alpha_equal`) | two terms | compares them as they are, index for index |
| `cc_kernel_endpoint_term` (`cb_endpoint_term`) | a term | substitutes as it is: dimension substitution rebuilds nodes in place and never moves a part under a new term binder |
| `cc_kernel_rename` (`cb_rename`) | a term | the dimension mode as `cc_kernel_endpoint_term`. The term mode goes: its driver uses (the level-binder renaming and `freshFormer` in the instruction driver, the display renamings of `viewOfJudgement` and `nextClauseType`) all disappear with named binders and named entries |
| `cc_kernel_instantiate` (new) | a binder body, an entry | replaces its index 0 by the entry, under section 3.6's condition |
| `cc_instr_universe`, `cc_instr_level_apply`, `cc_instr_sort_level` (`cb_instr`) | a level | refuse a loose level, as `level_context` refuses an unknown variable today ("Unbound level variable.") |
| `cc_instr_lookup` (`cb_instr`), `cc_kernel_definition` (`cb_definition`) | a reference | a `CC_DEFREF`: nothing loose |
| `cc_kernel_node` (`cb_node`), `cb_subterm` | a handle | read as stored; a subterm under binders has loose indices, which the driver names by its name stack |
| `cc_kernel_relocated` (`cb_relocated`) | a handle | translates the handle; reads no syntax |
| `cc_kernel_judgement` (`cb_judgement`), `cc_kernel_entry` (`cb_entry`), `cc_kernel_mismatch` (`cb_mismatch`), `cc_kernel_signature` (`cb_signature`), `cc_kernel_signature_constructor` (`cb_signature_constructor`), `cc_kernel_definition` | return terms | judgement terms, entry types, definitions and mismatches are locally closed; a signature's former parts and constructor types carry loose indices over its prenex or admission telescope (section 3.4); no answer holds `CC_OPENED`; no symbol is reported for an entry or a signature |

The other exports take no syntax: `cb_abi_version`, `cb_new`, `cb_free`,
`cb_error`, `cb_error_kind`, `cb_optimizations`, `cb_generation`,
`cb_checkpoint`, `cb_rollback`, `cb_commit_checkpoint`, `cb_deadline_ms`,
`cb_step_budget`, `cb_work`, `cb_formula_begin`, `cb_formula_clause`,
`cb_formula_end`, `cb_formula_view`, `cb_position_clear`,
`cb_position_push`, `cb_position_set`, `cb_clear_error`, `cb_arena`,
`cb_fresh_symbol`, `cb_judgement_count`, `cb_judgement_context`,
`cb_entry_count` and `cb_extensions`. The other instructions of `cb_instr`
take judgements, entries, formulas and numbers, not raw syntax.

### 5.2 The driver's side: call sites

Two counts per module on main `a933a0bf`, leaving out
`web/cubical-runtime.mjs`, which #348 deletes. **Kernel calls**: lines
matching any of `kernel.<name>(`, `graph.<name>(` or `g.<name>(` (the
instruction graph), `.node(`, `read(` (as `levelNormal` reads nodes),
`.children[`, `.term(`, `.spine(`, `.head(`, `.symbolName(` or `_cb_`.
**Variable, binder or symbol lines**: lines naming a variable or binder kind
(`"Var"`, `"Lam"`, `"Pi"`, `"Sigma"`, `"LPi"`, `"LLam"`, `TERM_BINDERS`,
`LEVEL_BINDERS`, `termBinders`) or using symbols (`.symbol(`, `.symbol`,
`symbolName`, `.rename(`, `.extend(`, `.bind(`, `levelEntry`,
`signatureBegin`, `signatureConstructor`, `info.symbols`, `info.sort`). The
patterns are wide on purpose and overcount; the third column says what
actually changes.

| Module | Kernel calls | Variable, binder or symbol lines | What changes |
| --- | --- | --- | --- |
| `web/cubical-kernel.mjs` | 36 | 12 | the kind table `cubicalKinds`, `CUBICAL_ABI_VERSION`, `term`, `node`, `signature` (closed constructor types, no symbols), the new query |
| `web/cubical-instructions.mjs` | 24 | 11 | `extend` and `level` with no name, Replace's entries, `signatureBegin` and `signatureConstructor` taking entries, `rename` (dimension mode only) |
| `web/cubical-syntax.mjs` | 40 | 12 | `encode` and `encodeLevel` take a scope: bound names to `CC_BOUND` by depth, free names to the scope's entries, and the encoding cache keyed by the scope as it is by the dimension context (section 5.3); `decode` and `decodeLevel`: a name stack for `CC_BOUND`, the driver's names for `CC_CONTEXT`; `signatureRecord`'s names from the driver's records |
| `web/cubical-instruction-driver.mjs` | 223 | 66 | `entry` and `contextScope` keep the map from name and type to entry that `cc_instr_extend` kept (section 5.3); `deriveNode` opens binder bodies with the new or reused entry, and its renaming of a level binder whose spelling a term entry holds goes; `scopeAt` hands Replace its entries; `agree`, `guide`, `sameHead` and `levelsEqual` compare term and level binders' bodies directly, so the term renaming chains (`pruneSymbols`, the term half of `chainId` and `unrenamed`) go, while the dimension chains (`prune`) and `renameBinder`, which renames dimensions, stay; `levelsEqual`'s keys by role (below); `freeTermSymbols`, `binds` and `freshFormer` simplify or go |
| `web/cubical-elaborator.mjs` | 37 | 23 | scope first, then encoding: `derived`, `nextClauseType` and `nf` (section 5.3); the display renamings of entries (`viewOfJudgement`, `nextClauseType`) become decoder names; its `levelNormal` comparison of a level with its bound |
| `web/cubical-levels.mjs` | 5 | 5 | `levelNormal` recognizes only `Var` and throws "Expected a level" on anything else; it must read `CC_BOUND` and `CC_CONTEXT` and key them by role, so that a bound level variable and an entry with equal numbers never meet |
| `web/cubical-signatures.mjs` | 14 | 9 | admission passes entry names (`g.entry(sort).name`, `g.entry(entry).name`) to `signatureBegin` and `signatureConstructor`; it must pass the parameter, sort and constructor entries |
| `web/cubical-program.mjs` | 8 | 15 | signature display: parameter and constructor names, constructor types decoded with names for the admission telescope |
| `tools/proof-migration.mjs` | 8 | 8 | rebuilds a constructor's closed type from the signature's symbols and types: the same change as `cubical-program.mjs` |
| `web/cubical-kernel-step.mjs` | 10 | 1 | positions are unchanged; reads of binder payloads |
| `web/cubical-workbench-session.mjs`, `web/cubical-workbench-trace.mjs` | 11 | 3 | binder and variable labels in the workbench |
| `web/cubical-assembly.mjs`, `web/cubical-graph-view.mjs` | 12 | 6 | node labels; the views encode a context's types with `kernel.symbol(entry.name)`, which must use the judgement's own handles or a scope made first (section 5.3) |
| `web/translator/elaboration.mjs` | 1 | 0 | its scope's `nf` passes the scope's context to the elaborator's `nf`, which today takes none (section 5.3) |

Fourteen modules (thirteen in `web/` and one tool): about 430 kernel or
graph calls and about 170 variable, binder or symbol lines, 223 and 66 of
them in the instruction driver (the translator's `elaboration.mjs` adds one
line). Unchanged: the other translator modules
(`web/translator/evaluation.mjs`, `translate.mjs`, `match.mjs`, `hlevel.mjs`,
`inductive.mjs`), which ask for heads and spines and read signature shapes
(constructor counts, dimensions, the squash flag), and whose `"Var"` or
`"Pi"` are the translator's own syntax; `web/cubical-transaction.mjs`
(checkpoints and relocation); `web/cubical-reduction.mjs` (decodes through
`cubical-syntax.mjs`); and the probes in `tools/` that walk node children
only (`evaluation-baseline.mjs`, `runtime-repl-probe.mjs`,
`transport-normalization-probe.mjs`, `open-bnat-normalization-probe.mjs`).

**Level keys by role.** Today a level normal form's variables are keyed by
symbol on both sides of the boundary (`levelNormal`'s `offsets`, the
kernel's `cc_level_term.key`). After the switch a level variable is
`CC_BOUND(i)` or `CC_CONTEXT(e)`, and `i` and `e` are both small numbers, so
keys must carry the role (in the kernel, two key ranges, section 3.1; in the
driver, distinct keys such as a tag and the number), or a bound variable
and an entry would compare equal.

### 5.3 Three consequences for the driver

**Scope first, then syntax** (decided 2026-11-02). Today the driver encodes
a source term into kernel syntax (`encode` in `web/cubical-syntax.mjs`)
with its free variables as symbols, before any entry exists, and
`deriveNode` maps each `Var` to its entry while deriving. With
`CC_CONTEXT(entry id)` the order is the other way round: the driver first
extends the context, then encodes against it, so raw syntax refers to a
context variable only as the `CC_CONTEXT` of an entry that already exists,
and never as a dangling index. Every site that encodes in a context
changes:

- `derived` in `web/cubical-elaborator.mjs`, behind every check and
  inference of a term in a context: today the assumptions' types and the
  term are encoded first and `driver.check` or `driver.infer` makes the
  entries. Instead `contextScope` takes the assumptions as source syntax and
  builds the scope one assumption at a time, each type encoded against the
  scope of the ones before it, and the term is encoded against the whole
  scope.
- `nextClauseType`: the scope from its assumptions first, then the motive
  and the clauses encoded against it.
- The elaborator's head queries: `nf` (`web/cubical-elaborator.mjs`, called
  by the translator's scopes through `nf` in
  `web/translator/elaboration.mjs`) encodes a term with no context at all
  today and asks `kernel.head`. It is given the scope's context, extends it
  with `contextScope` (cached per context key, as `contextScopes` already
  is), and encodes against it. A context whose types cannot be derived
  makes the query fail, which is correct for an ill-formed context; where a
  caller asks before its context's types are checked, the elaborator derives
  them earlier. PR 1 finds every caller of `nf` and says which case it is.
  `derivedHead` needs nothing: it takes a handle an instruction derived,
  which already refers to existing entries.
- `differ`, which compares two closed terms, encodes against the empty
  scope; a free variable there is refused.
- Signature admission (`web/cubical-signatures.mjs`) already derives each
  parameter and constructor type in the scope of the earlier entries; it
  encodes each type against that scope instead of encoding first.
- The views (`web/cubical-assembly.mjs`, `web/cubical-graph-view.mjs`)
  encode a context's types with `kernel.symbol(entry.name)`; they take the
  judgement's own handles, or a scope made first.

The encoding cache (`this.encoded`, keyed today by the term and the
dimension context, `encode(term, dimensions, key)`) is keyed by the scope as
well. A term whose encoding mentions no entry, its `contexts` filter zero,
is cached without the scope, so closed parts are shared across scopes as
they are today. The order needs no kernel change and is adopted first, on
ABI 3, in PR 1, with symbols still standing for the entries; PR 3 then
changes only what a reference is.

`cc_kernel_instantiate` remains for one use only: `deriveNode` opens a
binder's body with the entry it has just made or reused for that binder,
one binder at a time (section 3.6 gives its condition).

**Names live in the driver** (decided 2026-11-02). Entries carry no names, so
the driver matches its names to kernel handles. `entry` in
`web/cubical-instruction-driver.mjs` keeps a map from a name and a type
handle to the entry made for them, so the same name at the same type reuses
the entry, as `cc_instr_extend`'s symbol did, and judgements derived under
the same binder are still shared by the derivation memo. After the switch
the key is exact up to term and level binder names, which no longer
distinguish types' handles. An entry is reused only when it is not already
in the scope being extended (section 3.6). The `x'1`, `x'2` variants that
`entry` makes when a name is taken at another type become the driver's
display matter only. The map is dropped at commit and rollback with the
driver's other per-declaration caches, since the entries it holds are
truncated then. A driver that fails to reuse an entry gets two distinct
variables, and terms that mention one fail to match terms that mention the
other: that is incompleteness, a check that fails, never unsoundness, since
every judgement is still checked by the kernel.

**Binder names in displays.** The kernel's normal forms no longer carry the
source's binder names (today `decode` reads them with `symbolName`, and
normal forms keep the definitions' names unless a capture renamed them).
The display naming pass (`web/display-naming.mjs`) already renames binders
apart; it would start from names the driver chooses: the source name where
the driver encoded the binder node itself (its encoding cache maps syntax to
handles), and a generated one otherwise. A normalized function shown with
`!!` or in the workbench may show `x` where the source said `p`. Decided on
2026-11-02: the driver chooses, and the kernel keeps no name hints.

### 5.4 Rejected: names at the boundary

The kernel could have kept ABI 3, abstracting on `cc_kernel_term` and
opening on `cc_kernel_node` with a display name per binder. It would make the
read path allocate and fail (`cc_kernel_node` is read-only and `const`
today), make `cb_subterm` open along its path, need a capture-free display
name per binder (a free-name test on every read) and a hint table keyed by
handle in the trusted kernel, and leave the driver's mirrored renaming
machinery in place. The user chose ABI 4.

## 6. Performance expectations

### 6.1 Evaluation

Ticks that disappear are `ck_term_free`'s visits. Ticks that appear are
none on these entries: their values have no binders to normalize under,
and they issue 4 to 6 binder instructions. So, to first order, the kernel's
path costs main's ticks minus the visits. The iota construction (ticks spent
in `ck_eliminate` after the argument's weak head, without the visits) is what
the direct iota of PR 4 can cut further, for eligible constructors only
(section 7): those of `BPositive` (`bp_even(p : BPositive)`, whose position
is the sort itself) and of `BNat` (no positions) are; a higher constructor
with a path-valued position is not.

| Entry | Main | Main minus visits (estimate) | Of which iota construction | Stopgap, three names |
| --- | --- | --- | --- | --- |
| `factorial(40)` | 7,764,892 | 563,396 | 216,972 | 596,941 |
| `factorial(60)` | 138,249,298 | 1,570,635 | 652,794 | 1,621,886 |
| `factorial(100)` | 3,263,063,793 | about 5.1 M (stopgap minus its 96,738 visits) | about 2.3 M (from the stopgap's 1,406,670 iota nodes at about 13 a step and 21 ticks a step) | 5,210,715 |
| `least_divisor(44521, tt).1` | 6,777,422 | 3,646,857 | 904,309 | 4,356,552 |
| `least_element(…, 1000000, tt).1` | 5,183,171 | 1,911,023 | 459,202 | 2,924,456 |
| Peano count of 300 | 1,908,195 | 1,095,755 | 260,224 | 1,510,081 |
| `euclid(7).1` | 1,896,001 | 1,057,130 | 251,364 | 1,249,296 |

These are estimates: instantiation takes its ticks per node as substitution
does, and deterministic constructions may hit caches more. Beyond ticks,
iota's fresh variables and displays account for most nodes made in
`factorial(100)` (1,406,670 of 2,314,926), whose time the stopgap's profile
put 43% in `ck_make` and 28% in substitution.

### 6.2 Checking

In the `binary_rationals` closure the change removes 2,104,442 `ck_term_free`
visits (19% of 11,223,319 ticks), the renaming in comparison (18,695 binder
pairs, 15,181 scope prunings), 75,715 fresh symbols and the variants they
made. It adds node rebuilds where today's code reuses the body as it is:

| Added work | Nodes |
| --- | --- |
| normalization under 58,370 binders: open | 538,900 |
| normalization under those binders: close | 844,976 |
| binder instructions' abstraction (35,163) | 346,390 |
| Step under binders (72,584 of 125,639 Steps cross 163,574 binders): open and close | 32,994 and 40,427 |

About 1.8 M node rebuilds against 2.1 M visits removed, and a rebuild
(hash-consed `ck_make`) costs more than a visit. **Checking may get no faster,
and could get slower**, where it normalizes under binders; the `nat` closure
normalized under 63 binders only. PR 3 measures it and reports the cost,
ticks and wall time for each library import closure and for the archive
audit, against main; there is no preset threshold, and the user decides
then (decided 2026-11-02). If it regresses and the user wants it back, the
lever is normalizing a body without opening it, which means
reduction on terms with loose indices and lifting wherever a computation
builds a binder around a part: the invariant of section 3.3 would no longer
hold, so it is a fallback, not the plan.

### 6.3 What to measure

On main and on each PR, each sample a new process:

- `factorial(40)`, `factorial(60)`, `factorial(100)`,
  `least_divisor(44521, tt).1`, `least_element(…, 1000000, tt).1`, the Peano
  count of 300 and `euclid(7).1`, by `node tools/runtime-repl-probe.mjs NAME
  kernel` (the probe's workloads; `factorial(60)` and `factorial(100)` are
  added as the stopgap branch added them). Ticks, time, arena growth.
- `7^60` nested to the right and to the left, and `power(7, 60)` with both
  multiplication orders, the stopgap report's controls.
- The evaluation baseline (`tools/evaluation-baseline.mjs`, recorded in
  `tests/fixtures/evaluation-baseline.json`, which
  `tests/evaluation-baseline.test.mjs` keeps in agreement with the code: every
  PR that changes ticks records it again).
- The cases of `tools/substitution-cost-probe.mjs`.
- Checking: the library's import closures (ticks, time, arena), the archive
  audit (`node tools/audit-cubical.mjs --all`), and `npm test`'s wall time.

## 7. Staged implementation

Each PR is verified locally first, opened as a draft, and keeps
`make test`, `make sanitize SANITIZERS=undefined` (ASan runs in CI) and
`npm test` green.

1. **PR 1, driver: one place for variables and binders (ABI 3, JS only).**
   Route every read and construction of binders and variables in the
   modules of section 5.2 through one small module: read a binder, open its
   body with an entry, build a binder over an entry, name a variable's role,
   decode with a name stack, key a level variable by role (`levelNormal` in
   `web/cubical-levels.mjs` and its callers, `levelsEqual` and the
   elaborator's bound check), and issue the signature admission instructions
   with entries (`web/cubical-signatures.mjs`; on ABI 3 the module passes the
   entries' symbols). It also puts the two decided disciplines of section
   5.3 in place while the kernel still takes symbols: scope first, then
   encoding, at every site listed there (`derived`, `nextClauseType`, `nf`
   with its context and every caller of `nf` sorted into "fails on an
   ill-formed context" or "derives its context earlier", `differ`,
   signature admission, the views), with the encoding cache keyed by the
   scope; and the driver's own map from name and type to entry, giving each
   new entry a new symbol so that `cc_instr_extend`'s reuse by symbol is
   never relied on. On ABI 3 it is implemented with symbols, so the kernel
   sees the same instructions: same verdicts and, but for the head queries'
   new context scopes, the same ticks. Its acceptance measures that cost,
   the derivations `contextScope` adds on the head-query path (instructions,
   ticks and wall time on the library and the archive audit, against main).
   It confines the ABI switch's driver diff: PR 3 then changes only what a
   reference is.
2. **PR 2, kernel primitives (C only, ABI unchanged).** The packed node
   layout of section 3.2 with `loose` and `opened` and their bounds (`symbols`
   stays until PR 3, where `contexts` takes its slot, so the node stays at 48
   bytes throughout), the internal kinds, and instantiate, abstract, open and
   close as worklists with ticks, the memo and the allocation-failure paths,
   with the opened-level counter of section 3.1, unused by the rules yet. C
   tests for their laws and bounds (below). Its own PR (decided
   2026-11-02).
3. **PR 3, the switch: term and level binders, ABI 4.** `CC_VAR` retired,
   `CC_BOUND` and `CC_CONTEXT` in; binders without payload; every change of
   sections 3.3 to 3.7, the freshness conditions of section 3.6 and the
   derivation identity of section 3.7 included;
   the bridge; the instruction signatures that change (`cc_instr_extend` and
   `cc_instr_level` without a symbol, `cc_instr_replace` with its entries,
   the signature instructions with entries, `cc_kernel_entry` and the
   signature readers without symbols, `cc_kernel_instantiate` new,
   `cc_kernel_rename` without its term mode); PR 1's module switched to ABI
   4, with role-distinct level keys and the signature instructions' entry
   operands, and the signature
   consumers of section 5.2 (`cubical-program.mjs`,
   `tools/proof-migration.mjs`) decoding closed constructor types; the
   kernel guide (`docs/guides/kernel.md`) and the reference chapters
   (`web/reference/kernel-terms.html`, `kernel-overview.html`,
   `kernel-instructions.html`), whose identifiers
   `tests/kernel-guide.test.mjs` checks; the evaluation baseline recorded
   again. This is the large PR. Its acceptance is the differential run below
   and the measurements of section 6.3. The checking cost is reported, ticks
   and wall time for each import closure and the archive audit against main,
   with no preset threshold: the user decides on it then.
4. **PR 4, direct iota.** For an eligible constructor, build the reduct as
   the clause applied to the arguments and then to `elim(q_j)` for each
   recursive argument `q_j`, without the display and without `ck_apply_at`.
   A constructor is eligible exactly when its result has no dimensions
   (`cc_constructor.dimensions` is 0) and every one of its positions has the
   sort itself as type: no arity binders (the position's type is no Π) and
   no cube (it is no path type). The second condition is not implied by the
   first: `cc_constructor.dimensions` counts only the result cube
   (`constructor_shape` takes it from the result; a position's cube depth is
   checked by `cube` and dropped), so `wrap : Path(S, base, base) → S` has
   0 dimensions and no arity binders yet needs `⟨i⟩ elim(p @ i)`. Admission
   computes the test once and records it with the constructor, since neither
   positions' arities nor their cube depths are stored today. Every other
   constructor, including a position `Π (ys : As). C` with arity binders, a
   path-valued one, or both, keeps the general construction of section 3.3.
   It changes how the trusted rule computes, not the rule (H1 specification
   3.7), and is reviewed as such.
5. **PR 5, driver cleanup.** Delete what ABI 4 left dead: the JS renaming
   chains, free-symbol sets and term renaming of the instruction driver.
6. **Later, if ever:** dimension binders, and the 64-dimension cap, as their
   own design.

### 7.1 Verification

- **C unit tests of the primitives** (`kernel/tests/test_substitution.c` and
  a new file if it grows): open then close is the identity; close then open
  is the identity on locally closed terms; instantiating equals opening and
  then substituting the opened variable; `loose`, `opened` and `contexts`
  agree with their definitions by recursion on 3,000 random terms over every
  binder kind, as the stopgap's randomized test checks its lists; a closed
  graph of 2^40 paths is instantiated and abstracted without being
  traversed; depth-512 chains and wide DAGs stay within the worklists, as
  `test_traversals.c` checks today; allocation faults and budget exhaustion
  leave no partial result (`substitution_allocation_fault.h`,
  `traversal_allocation_fault.h`). Mutating the binder case of `loose` must
  fail a test.
- **The existing C tests** that build variables or term and level binders
  (about 110 lines across `test_normalize.c`, `test_signatures.c`,
  `test_substitution.c`, `test_levels.c`, `test_comparison.c` and others)
  are rewritten for the new kinds. Capture tests become tests that
  instantiation under binders never touches the value; dimension capture
  tests stay as they are.
- **Adversarial instruction tests** (`kernel/tests/test_instructions.c` and
  `test_signatures.c`), one per condition of section 3.6, each refused with
  its own message, and each also run on main's ABI 3 where it can be
  expressed there, as a control that today's kernel refuses it too:
  1. Replace supplying an ambient entry for a binder: the example of
     section 3.6, `λ (x : A). (x, e)` rewritten by reflexivity at `(e, e)`
     with `e` for `x`;
  2. Replace supplying one entry for two binders;
  3. Replace supplying an entry of the wrong type, or of the wrong kind for
     a level binder, or one whose type needs an outer binder that got none;
  4. Replace giving no entry (0) for a binder the target uses;
  5. Replace whose equality keeps an entry that depends on a supplied one;
  6. accepted, with its result checked: a replacement whose right side uses
     a binder's variable that its left side does not;
  7. `cc_kernel_instantiate` with an entry the body already mentions, as the
     reused entry of `λ (x : A). λ (x : A). b` would be;
  8. SignatureBegin with a repeated parameter entry, a sort entry equal to a
     parameter entry, or a term entry for a universe parameter;
     SignatureConstructor with a constructor entry already in the telescope,
     or a type whose context holds an entry outside it.
- **Replay tests of the derivation memo** (section 3.7): the same Replace
  (premises, side, position) issued with `[e]` and then with `[0]`, the
  example there, gives two judgements with different terms and contexts,
  neither answered by the other's entry; a vector refused after an accepted
  one with the same premises and position is still refused; the same vector
  twice gives the same judgement.
- **Opened levels across operands** (section 3.1): the clause type of
  `fork : S → S → S` is `Π (x : I). Π (y : I). Π (x̄ : M(x)). Π (ȳ : M(y)).
  M(fork(x, y))`, compared with that type built by hand, the two arguments
  apart; the same for a constructor with two data arguments of one type; an
  equivalence type built under a normalization's opened binder, whose
  operands hold level 0, takes its own binders above it; `parts_agree` on
  two sides with different greatest levels.
- **Iota's cube lifting** (section 3.3): for `wrap : Path(S, base, base) → S`,
  Iota on `wrap(p)` gives the clause applied to `p` and to `⟨i⟩ elim(p @ i)`,
  a path abstraction with its displayed family, as on main (a review
  reproduced main's on WebAssembly; applying the eliminator to `p` itself is
  refused); a position with arity binders and a cube,
  `q : Π (y : A). Path(S, base, base)`, gives `λ y. ⟨i⟩ elim(q(y) @ i)`; and
  after PR 4 neither constructor is eligible for the direct iota, while
  `BPositive`'s are, with equal reducts on both paths for the eligible ones.
- **Loose terms at the boundary** (section 5.1): `cc_kernel_whnf` on a
  loose term answers with the same loose indices and no `CC_OPENED`, and
  equals the head computed by opening with an entry and abstracting it
  again; `cc_kernel_normalize`, `cc_kernel_normalize_folded` and
  `cc_kernel_equiv_type` refuse a loose term (main's control,
  `equivType(Var(A), Var(A))`, keeps `A` free without an entry); each level
  instruction refuses a loose level.
- **Raw syntax closed over entries** (section 5.3): encoding a term whose
  free variable has no entry in the scope fails in the driver; `ck_make`
  refuses a `CC_CONTEXT` naming no live entry; an `nf` query whose context
  cannot be derived fails rather than answer.
- **Names in the driver** (section 5.3): binding one name twice at one type
  in disjoint scopes reuses the entry, and a derivation repeated under it is
  answered from the memo; `λ (x : A). λ (x : A). x` derives with two
  entries, the inner `x` the inner binder's; two `cc_instr_extend` calls at
  one type give two entries.
- **Metadata bounds** (section 3.2): the overflow tests listed there.
- **The generated constructor** (section 3.4): `inductive Tr : prop { inc; }`
  admits, its squash is reported with `generated` set and no symbol, its stored type is
  closed, and an eliminator over `Tr` computes on it as today.
- **Differential run, old against new.** A temporary tool, run once with
  main's build and once with the branch's, over the library, the archive
  (`tools/audit-cubical.mjs --all`) and the `.cubist` fixtures of `tests/`:
  per declaration its verdict and rejection class, and per `evaluate` entry
  its printed value form and its folded and full normal forms decoded to
  syntax. Verdicts must agree exactly; normal forms up to alpha-equivalence
  of the decoded syntax (names are the driver's on both sides, so compare
  with a name-insensitive equality). Differences are explained, or they
  block.
- **The stopgap's tick bounds** (`tests/binary-naturals.test.mjs` on
  `kernel-fast-multiplication`: `factorial(60)` under 4,000,000 ticks,
  `factorial(100)` under 12,000,000 with its low bits checked against
  `2^97` dividing `100!`, and `7^60` nested to the right under three times
  its ticks nested to the left) come over in PR 3 unchanged, as the
  acceptance of the representation; PR 4 tightens the `factorial` bounds to
  its measured ticks with a margin. The stopgap branch is not merged.

## 8. Open questions and risks

Answered on 2026-11-02 and moved to the decisions at the top: checking
speed, binder names in displays, `CC_OPENED`, the new operands of Replace and
the signature instructions, PR 2 as its own PR, raw syntax closed over
entries (scope first), entries without names, and dimensions left out.

**Still open: drop every remaining kernel symbol?** The decision on entries
follows a principle: names live in the driver, which matches them to kernel
handles. This is the proposal that applies it to the rest. After the switch
and the decisions above, the kernel still holds symbols in these places,
each checked in the C and the driver:

| Symbol | What uses it today | Needed by the kernel? | Moves to the driver as |
| --- | --- | --- | --- |
| `cc_instr_define`'s symbol, kept in `cc_definition.symbol` | the refusal "Definition symbol is already registered." (`cc_instr_define`), the Define derivation's memo key (`operand[0]`), and `cc_kernel_definition`'s report (`definitions.c`, read by `cb_definition` field 0 and the driver's `definition(reference).name`) | No: a definition is referred to by its index (`CC_DEFREF`), `cc_instr_lookup` takes the reference, and no error message, relocation or compaction reads the symbol | the driver's maps between names and references, which exist already: `kernel.definitions` (name to `CC_DEFREF`, read by `encode` and relocated by `web/cubical-transaction.mjs`) and its inverse for `decode`; the refusal of a second definition of one name, which the program already reports as a duplicate (`gaps` with `duplicate` in `web/cubical-program.mjs`) |
| signature and constructor symbols, `cc_kernel_signature_symbol` | already gone with the entries' names (section 3.4) | No | `kernel.signatures`, the driver's record of each declaration's names |
| `cc_kernel_fresh_symbol` (`cb_fresh_symbol`), `next_symbol` | the driver's `symbol(name)` allocates its numbers there so that kernel names and its own never meet; `ck_make` raises `next_symbol` past every symbol a `CC_VAR` or binder is built with; `ck_fresh_symbol` serves the kernel's fresh names | No: after the switch no node, entry or signature holds a symbol, and the kernel's fresh names are gone (section 3.5) | the driver's own counter, or its names as strings; `symbol` and `symbolName` in `web/cubical-kernel.mjs` become driver-local |
| `cc_kernel_entry`'s symbol for a dimension entry | the index of the dimension | Yes, but it is an index, not a name | stays |

One consequence must be settled with it. Without a symbol, Define's
derivation key is its premise alone, so defining the same closed judgement
twice would answer the second time with the first definition's reference:
two names for one `CC_DEFREF`. To keep one definition per Define, as today,
`cc_instr_define` starts with `ck_instr_begin_stateful`, never answered from
the memo, like the signature instructions. Then nothing in the kernel holds a
name at all: definitions by index, signatures by index, constructors by
number, entries by id, dimensions by index. ABI 4 is the time to do it,
since every reader of these symbols changes in PR 3 anyway. Agreed?

Risks that remain:

- The checking cost of PR 3 (section 6.2) is unknown until measured; the
  fallback for normalization breaks the invariant that keeps reduction free
  of index shifting.
- PR 3 is large: it changes the kernel, the bridge and the driver together.
  PR 1's indirection and PR 2's primitives keep it to the switch itself.
- Scope first costs the head queries a context derivation each new context
  (cached per context key), and a caller of `nf` that asks before its
  context's types are checked must be found and changed; PR 1 measures the
  one and lists the other.
- The soundness of the change rests on the primitives' laws and on the
  conditions of sections 3.6 and 3.7, the places where a missing check
  would certify a false judgement rather than fail; section 7.1's
  adversarial and replay tests, and a review that targets them, are the
  guard.
