# FG3 universes of generated telescopes

G2 is an active regression. Generated model types, Hom and Iso now infer
their result universes by ordinary elaboration of their complete dependent
field telescopes. Fixed operation domains, dependent arguments, family
indices, carrier evidence and preservation/round-trip fields contribute
through the existing Pi/Sigma universe rules. There is no new universe
formula or large fallback level.

The base model type also needs this treatment: an operation accepting
`A : U1` cannot fit the previous annotation `next(U)` for arbitrary carrier
universe `U`. Its full telescope determines that contribution before a
morphism is requested. The generated declaration builder uses the parser's
existing inferred-value form, with complete grouped parameter lambdas and
`valueParameters`; it does not send a missing type to proof checking.

The policy for which universe parameters are shared is unchanged. Fixed
domains mentioning a theory's universe require both models to share it;
otherwise independent model universes remain independent. Inferred levels
use the existing finite/tiered solver and public binder labels. For example,
a carrier in `U` and a fixed domain `A : V` give Hom a level
`max(U,next(V))`, rather than `next(max(U,V))`. Independent client annotations
check that least justified level, and lower annotations are refused.

Hom, its constructor/projections, identity and composition still use one
analyzed field telescope. Iso uses checked Hom and its own full round-trip
telescope. They elaborate inside FG1's publication groups: a universe or
other checking failure cannot publish a partial family. Syntax support
remains conditional until these ordinary checking obligations succeed.
The kernel, budgets and initial/free capability boundary are unchanged.

## Producer and consumer audit

| Boundary | Evidence |
| --- | --- |
| Model-type builder | Uses the existing `value`/`valueParameters` representation with scope-aware grouped lambdas; no new syntax kind. Generated public universe labels and implicit parameter metadata remain separate. |
| Hom/Iso source templates | Remove only the guessed result annotation. Structured payload holes and references still pass through the same capture and lowering paths. |
| Ordinary elaboration and publication | Existing inference checks the entire telescope in its header context; dependent declarations consume the checked inferred signatures inside the publication group. FG1 rollback tests still pass. |
| Signatures and inspection | Independent source clients state expected universe types and preservation types, check computations and assumption sets, and reject actual lowering. Existing headerless-label, named-argument, import and browser tests cover inferred-declaration consumers. |

`frontend-universes.test.mjs` covers fixed domains at U0/U1 with dependent
proof arguments, both direct and imported/inherited theories; generic
shared universes and incompatible model universes; multiple header universes;
and dependent family indices at U1. Clients check Hom identity/composition,
preservation fields, Iso inverse computations, public types and absence of
new assumptions. Universe lowering remains E606. Related integration tests
pass 103/103, including initial/free generation, capture, publication and
source observations. Full-suite, browser and resource results follow below.
