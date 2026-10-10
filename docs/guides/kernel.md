# Reading the cubical kernel

The kernel checks a judgement Γ; Δ; φ ⊢ t : A. Γ is an ordered telescope of typed
variables, Δ records interval coordinates, and φ restricts the current cube to
a face. A successful result certifies the expression and its type. Allocating a
syntax node, printing a name, or requesting normalization does not certify it.

The browser and CLI use this C implementation. JavaScript elaboration proposes
terms, but cannot publish unchecked definitions in the native registry.

## A reading route

1. [instructions.c](../../kernel/src/instructions.c) checks explicit typing premises for contexts, universes, functions, pairs and definition admission.
2. [instruction_paths.c](../../kernel/src/instruction_paths.c) checks paths, their boundaries, and composition one tube at a time.
3. [instruction_glue.c](../../kernel/src/instruction_glue.c) checks gluing data and equivalences through explicit instructions.
4. [instruction_equality.c](../../kernel/src/instruction_equality.c) checks equality, conversion and explicit reduction steps.
5. [term_conversion.c](../../kernel/src/term_conversion.c) supplies the term comparisons used by those rules.
6. [term_substitution.c](../../kernel/src/term_substitution.c) handles capture-avoiding substitution.

The untrusted [instruction driver](../../web/cubical-instruction-driver.mjs)
chooses the derivation; each native instruction validates its own premises.
The former term-checker files were retired. The [instruction-kernel contract](../roadmaps/kernel-instructions.md)
explains the trust boundary.

The [kernel overview](../../kernel/README.md) maps the remaining files to their
mathematical responsibilities. It includes storage, dimensions, and API contracts.

## Enough C to follow the rules

| C notation | Mathematical reading |
|---|---|
| `cc_term` | An integer handle to a syntax node in one kernel arena |
| `n.kind` | The node's constructor |
| `n.child[0]` | Its first operand; indexing starts at zero |
| `k->...` | A field of the kernel state |
| `a == b` | Equal handles, stronger than definitional equality |
| `a && b`, `a \|\| b`, `!a` | And, or, not |
| `&x`, `*p` | Address of a value; value at an address |
| `return false` | Reject the proposed check |

For function application, the checker establishes a dependent function type
Π(x:A). B(x), checks the argument against A, and substitutes the checked argument
into B. The corresponding code additionally manages handles, errors, allocation,
and scope. Those implementation details are part of the trusted code too.

For a path, both endpoint equations must hold in their restricted faces. Interval
expressions form a De Morgan algebra, while face formulas describe endpoint
constraints. These are different sorts: `i ∧ ¬i` need not be zero as an interval
expression, but the face `(i=0) ∧ (i=1)` is impossible.

## Definitions and inspection

`cc_instr_define` accepts an already checked, closed typing judgement.
It rejects open judgements and duplicate definition symbols; only success
adds the named reference to the registry.
Conversion can expose its body when required, but ordinary storage keeps the
reference. The browser's folded view adds source labels and abbreviations;
the assembly view shows the actual native constructors, operands, and handles.

The workbench replays source to reconstruct the checked context. A beta or delta
step must preserve definitional equality and pass checking again. Source names
are metadata, never authority to change the judgement.

## Verification and limits

`make test` runs native positive and negative regressions. `make sanitize` adds
address and undefined-behaviour sanitizers. JavaScript tests compare native
results with independent reference computations and reject malformed terms.
`npm test` also checks the source corpus once. These checks are evidence against
implementation bugs, not a machine-checked metatheoretic soundness proof.

The native interval representation uses 64 coordinate slots. Allocation errors,
invalid scopes, and exhausted explicitly configured budgets reject checking;
they never produce a successful judgement. Full cubical canonicity for every
implemented constructor is not claimed by this project.
