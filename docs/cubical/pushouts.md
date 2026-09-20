# Computational pushouts

This extension follows Coquand, Huber, and Mörtberg,
[On Higher Inductive Types in Cubical Type Theory](https://simhu.github.io/papers/hitcubical.pdf),
§§3.2 and 3.3.5. A pushout joins arbitrary span maps `C -> A` and `C -> B`.
Suspension is the library construction `Pushout(A, Unit, Unit, const(tt), const(tt))`.
No suspension axiom or suspension-specific kernel constructor is added.

## Point and path checkpoint

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
helper and derived suspension operations live in `experiments/cubical/pushouts.mjs`.

Tests independently check dependent identity-path families, nonidentity span
maps, meridian endpoints, and rejection of an incorrect bridge case. The
100-test experimental suite and the new tests under native UBSan pass.

## Remaining before full support

The next increment supplies canonical homogeneous composition and transport,
including the endpoint correction for transporting a pushout bridge. Ordinary
composition at a pushout currently remains neutral; this checkpoint must not be
presented as complete computational HIT support or a completed circle migration.
The source language's transport-based dependent-path premise will also need a
derived conversion to the native dependent Path premise.
