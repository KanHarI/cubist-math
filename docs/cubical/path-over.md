# Dependent paths and equality after transport

`experiments/cubical/path-over.mjs` derives the equivalence

```
PathP (i ↦ Aᵢ) a b  ≃  Path A₁ (transport A a) b.
```

Here `a : A₀`, `b : A₁`, and `transport A a` means ordinary cubical composition
in `A` with an empty tube system. This is useful when a source eliminator states
its coherence as equality after transport, while a cubical higher inductive
eliminator expects a dependent path. In particular, the pushout bridge case
(and therefore the derived suspension meridian case) can use this conversion.

There are no additional trusted rules or axioms. The module constructs inert
terms from existing paths, composition, and the derived filling operation.
The independent native C checker certifies the resulting terms.

## API

Each helper takes `(dimensionName, family, left, right)`. The named dimension
binds only `family`, just as in `T.path`. The maps and laws returned are ordinary
functions; apply them with `T.app`.

- `dependentPathToTransport`: dependent path → equality after transport.
- `transportToDependentPath`: equality after transport → dependent path.
- `dependentPathTransportSection`: backward(forward(p)) = p.
- `dependentPathTransportRetraction`: forward(backward(q)) = q.
- `dependentPathTransportEquivalence`: the forward map together with a checked
  proof that all its fibers are contractible.

Fresh names avoid all names already present in the inputs. Native `Ref` and
browser `DefRef` nodes are preserved exactly. As with every syntax builder,
producing a term is not a checking certificate.

## The filling squares

Write `F(i)` for the canonical filling of `a` along `A`, so `F(0)=a` and
`F(1)=transport A a`. For a dependent path `p`, its forward image is

```
forward(p)(j) = comp i Aᵢ [j=0 ↦ F(i), j=1 ↦ p(i)] a.
```

Both walls matter: the first fixes the transport endpoint explicitly. For a
path `q` from the transported endpoint to `b`, the backward image is

```
backward(q)(i) = comp j Aᵢ [i=0 ↦ a, i=1 ↦ q(j)] F(i).
```

For the first inverse law, fill the first composition to a square `Q(i,j)`.
Its four boundaries are `F(i)`, `p(i)`, `a`, and `forward(p)(j)`. Add `k=1 ↦ Q`
to the backward composition. Varying `k` gives the desired path from
`backward(forward(p))` to `p`, keeping the dependent endpoints fixed.

For the second law, fill the backward composition to a square `R(i,j)`.
Its four boundaries are `F(i)`, `backward(q)(i)`, `a`, and `q(j)`. Add
`k=1 ↦ R` to the forward composition to obtain the other inverse homotopy.

The established quasi-inverse-to-equivalence theorem packages these laws into
contractible fibers. It is applied under lambda-bound maps and inverse laws,
rather than duplicating all filling squares throughout its contraction proof.

## Validation and limits

`tests/path-over.test.mjs` checks both maps and both inverse laws independently
with the JS reference checker and native C checker at U0 and U2. The packaged
equivalence also checks. A nonconstant family from the product-swap Glue
universe path is tested with actual closed checked definitions, and a false
endpoint is rejected. Name-collision and reference-preservation tests exercise
syntax hygiene. A checked endpoint denoting 2²² stays compact: the packaged
equivalence uses fewer than 15,000 arena nodes and 100,000 reduction steps,
without materializing that unary numeral.

The bridge does not assert judgmental regularity of transport, or identify
cubical paths with a separate strict identity type. The comparison is a proved
equivalence with inverse paths, exactly as the cubical rules support.

A remaining native conversion incompleteness was encountered when fully
inlining the four filling proofs directly into the quasi-inverse contraction:
the reference checker accepts this expanded term, but native checking reports
an overlap disagreement. The modular theorem application used here checks in
both implementations and does not rely on that expanded form. No checking
rule was relaxed to accept the bridge.
