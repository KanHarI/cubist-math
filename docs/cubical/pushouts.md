# Computational pushouts

This extension follows Coquand, Huber, and Mörtberg,
[On Higher Inductive Types in Cubical Type Theory](https://simhu.github.io/papers/hitcubical.pdf),
§§3.2 and 3.3.5. A pushout joins arbitrary span maps `C -> A` and `C -> B`.
Suspension is the library construction `Pushout(A, Unit, Unit, const(tt), const(tt))`.
No suspension axiom or suspension-specific kernel constructor is added.

## Checked constructors and elimination

Native C and the reference checker support:

- `Pushout(center,left,right,maps)`, with maps an ordinary checked dependent pair
  of functions, preserving the maximum universe level of the three carriers.
- `PushLeft(P,a)` and `PushRight(P,b)`.
- `PushPath(P,c,r)`, with judgmental endpoints `PushLeft(P,f(c))` and
  `PushRight(P,g(c))`.
- `PushElim(motive,left,right,bridge)`, a function on the pushout. The bridge
  case is a dependent path over `PushPath(P,c,r)`, with endpoints given by the
  two point cases. Application computes on all three constructors.

The append-only native tags are 36–40 respectively. The raw `T.pushout` builder
accepts the packed maps as its fourth argument. The five-argument `pushout`
helper and derived suspension operations live in `lib/cubical/pushouts.mjs`.

## Composition and transport

Tags 41 and 42 add `HComp` and `Trans`. Both are currently checked only for
pushout types; unsupported families are rejected explicitly. Ordinary `Comp`
at a pushout reduces to transported tubes and a canonical homogeneous box.
The dependent eliminator maps such a box to composition in the motive along
its homogeneous filling.

`HComp(i,P,system,base)` binds `i` in tube terms only: `P`, faces, and the base
are in the outer cube. `Trans(i,P,phi,base)` binds `i` in `P` only. The checker
requires `P` to be constant on `phi`, and transport restricts to `base` there.
Its C face descriptor is one existing `Tube`; only its face is read from raw
input, and its term is rebuilt from the checked base. No new face sort is added.

Transport on a bridge uses the parameter's ordinary composition/filling,
followed by a homogeneous correction at each endpoint. This matters even when
the three carrier types stay fixed: changing either span map changes the
bridge endpoints. It also works when the carriers vary along a Glue universe
path. These are computation rules implemented independently in C and the
reference checker, not additional axioms.

The code is split into `check_pushout.c`, `pushout_compute.c`,
`check_hit_composition.c`, and `hit_composition.c`. Existing shared substitution,
face restriction, and composition checking are reused. An audit test also
ensures that free dimensions in face formulas are never accidentally hidden
by a composition direction with the same numeric name.

## Validation and remaining migration

Tests cover genuinely dependent motives, nonidentity span maps, both meridian
endpoints, nonempty homogeneous boxes, eliminator computation on boxes,
changing maps, changing carriers through a checked nonidentity Glue
equivalence, and a nontrivial constant face. Incorrect bridge cases, incorrect
box boundaries, falsely claimed constant faces, and malformed span maps are
rejected. Both native and reference normal forms are rechecked where practical;
the carrier-change case registers the actual checked universe path and avoids
strongly normalizing its full proof body.

This supplies computational pushouts and derived suspension. It does not yet
port the existing circle proof, construct propositional truncation, or provide
a general HIT schema. The source language's transport-based dependent-path
premise still needs a derived conversion to the native dependent Path premise.
