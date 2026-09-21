# Live interval dimensions rather than binder depth

The browser encoder originally reserved a slot for every enclosing `Path`,
path abstraction and composition binder. A deeply nested constant equality
therefore exhausted 64 slots even if it used no interval coordinates. The
native checker separately retained the same unused interval assumptions and
freshened reused slots, so fixing only the encoder would not suffice.

## Syntax transport

`lib/cubical/dimension-slots.mjs` computes free dimension names with
the exact scope of each constructor. `bindDimensions(term,dimensions)` returns
`{dim,inner}` for a binder, preserving the live outer names in its bound
children and allocating the first other slot. It does not change typing or
remove any actual dimension occurrence.

- Path endpoints are outside the binder; only the family is inside.
- A path abstraction binds its family and body.
- Composition binds its family and tube terms; faces and base are outside.
- Homogeneous composition binds only tube terms, not its family.
- Transport binds only its family, not its face or base.

The analysis consumes immutable syntax, like the existing browser codec.
It freezes inspected nodes and formula/system arrays before caching free
names. Shared syntax DAGs are visited once rather than expanded as trees.

The 64-slot limit remains for genuinely simultaneous live coordinates. It
is not silently replaced with aliasing: a binder requiring a new slot when
all 64 outer coordinates occur in its scope still fails explicitly.

## Native checking

`c/src/dimension_scope.h` implements admissible interval-context thinning
before the Path, composition and HIT composition rules introduce a binder.
It retains every dimension free in the whole raw term **or any local term
variable's type**. The result is intersected with the original allowed cube;
an unbound dimension can never become bound through this optimization.

Retaining term-variable types matters. A point of `P(outer_i)` cannot become
a section of the varying family `P(inner_i)` merely because the raw point
variable contains no explicit interval syntax. If a reused binder slot
conflicts with that context dependency, the existing capture-avoiding
renaming still allocates a distinct live slot.

Outer tube faces also remain live. Their restrictions must not accidentally
substitute the bound composition direction. Existing free-dimension analysis
accounts for these distinct scopes before interval thinning.

## Proposed browser patch

Root owns `web/cubical-syntax.mjs`; this checkpoint does not modify it.
Add the import

```
import {bindDimensions} from "../lib/cubical/dimension-slots.mjs";
```

and replace the allocation block inside its dimension-binder case with

```
const {dim,inner} = bindDimensions(term,dimensions);
```

Keep the existing outer versus inner child encodings unchanged. Rebuild the
WASM kernel with the native checking changes before using the new allocator.
`lib/cubical/native.mjs` already uses it for independent native tests.

## Tests

`tests/dimension-slots.test.mjs` checks 100 nested constant path levels,
proper scope distinctions, truly live-coordinate exhaustion, immutable DAG
memoization, and rejection of unbound coordinate names.

`c/tests/test_dimension_scope.c` checks rejection of a captured dependent
context variable, acceptance of the corresponding constant line with its
outer dependency intact, preservation of an outer composition face while
renaming a same-slot tube binder, rejection of unbound coordinates, and
acceptance of a closed line in an otherwise full unused outer cube.

These changes do not expand the native formula bitset or alter cubical
computation equations. They prevent unused lexical nesting from masquerading
as geometric dimension usage.
