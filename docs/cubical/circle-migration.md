# Circle encode–decode in the native cubical checker

`web/proofs/circle.cubist` preserves the original integer cover,
encode–decode construction, winding number, addition compatibility, loop-group
laws, and final multiplication-preserving integer isomorphism. Its imports use
the native cubical source loader. The legacy source remains unchanged.

Four former strict computation assumptions need explicit proofs:

- Transport along the lower meridian ends with `transport_constant` after the
  recursor beta path. The previous native edition already contained this fix.
- The zero case of `action_positive` uses `transport_constant` for an arbitrary
  integer, rather than requiring constant-family composition on a neutral sum
  element to be judgmentally the identity.
- The left unit in `loop_group` uses the checked cubical `left_unit` path.
- `addition_left_zero` composes `integer_loop_add` with that left-unit path before
  reflecting equality through winding.

No declaration's statement or assumption set is strengthened. Univalence is
provided by the checked Glue construction; it is not a new circle axiom.

## Dependent suspension branch correction

A suspension is `Pushout(A, Unit, Unit, const(tt), const(tt))`. Consequently the
pushout eliminator's left branch has type `Πu:Unit. motive(push_left(u))`. A value
at the north pole has type `motive(push_left(tt))`. A constant lambda cannot
provide the branch for an arbitrary dependent motive: neutral `u` is not
judgmentally `tt`.

The Cubist suspension elaborator must construct each point branch with Unit
elimination:

```js
const branch = (constructor, value) => T.lam(u, T.unit, T.unitrec(
  T.lam(point, T.unit, T.app(motive, constructor(type.domain, T.variable(point)))),
  value,
  T.variable(u)
));
```

Apply this to `T.pushLeft` and `T.pushRight`; keep the checked transport-to-PathP
bridge unchanged. The point branches still compute to their supplied values at
`tt`. This correction is required for `decode`, whose motive is nonconstant.

`tests/suspension-dependent.test.mjs` checks the general dependent construction
in JS and native C at U0 and U2, verifies both point computations, and rejects
the former constant-lambda construction. The UBSan build passes the same tests.

The circle's complete import graph checks in the main WASM/source frontend with
the native circle file supplied by an isolated loader: **188 declarations,
0 failures, 0 gaps**. This includes `fundamental_group_of_circle`. The separate
`circle_group_identity` result additionally imports the general group-univalence
development; its independent migration status must be reported separately.
