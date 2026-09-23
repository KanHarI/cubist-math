# Reading the cubical kernel

The kernel checks a judgement Γ; Δ; φ ⊢ t : A. Γ is an ordered telescope of typed
variables, Δ records interval coordinates, and φ restricts the current cube to
a face. A successful result certifies the expression and its type. Allocating a
syntax node, printing a name, or requesting normalization does not certify it.

The browser and CLI use this C implementation. JavaScript elaboration proposes
terms, but cannot publish unchecked definitions in the native registry.

## A reading route

1. [check.c](../../kernel/src/check.c) validates contexts, dispatches rules, and publishes results.
2. [check_functions.c](../../kernel/src/check_functions.c) implements dependent functions and pairs.
3. [check_paths.c](../../kernel/src/check_paths.c) checks interval paths and their boundaries.
4. [check_composition.c](../../kernel/src/check_composition.c) checks the base, tubes, and every required overlap.
5. [check_glue.c](../../kernel/src/check_glue.c) checks gluing data and equivalences.
6. [term_conversion.c](../../kernel/src/term_conversion.c) compares terms, unfolding only demanded heads.
7. [term_substitution.c](../../kernel/src/term_substitution.c) handles capture-avoiding substitution.

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

`cc_kernel_define` checks a closed body and optional expected type using already
checked definitions. Only success adds the named reference to the registry.
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
