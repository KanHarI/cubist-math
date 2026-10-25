# PR #312: display follow-up

Found while fixing #312's round-12 review finding (a function's domain read
through a motive's head redex). This is outside #312's change and remains
unfixed here.

- [ ] An eliminator taken as a function, whose motive is a variable, is
  shown as an untyped lambda that does not read back where nothing gives
  it an expected type. With `inductive B(A : U0) { b; }` and
  `def g := fun (P : B(Unit) -> U0) => fun (h : P(b)) => fun (x : B(Unit)) => match x as z return P(z) { b => h; };`,
  `evaluate !!g` shows `fun (P : B(Unit) -> U0, h : P(b)) => fun x => match x as z return P(z) { b => h; }`
  on #312 and on its base #311, and `refl(…)` of it fails with E346. Main
  at `8beac486` shows `fun (P : B(Unit) -> U0, h : P(b)) => B.elim(P, h)`,
  which fails with E343. The folded normal form eta-reduces the motive `λ z. P(z)` to `P`,
  and spelledOut's domain recovery (`domainOf` in
  `web/display-naming.mjs`) reads domains off syntax alone: a lambda, a
  definition's type, an eliminator's motive, after contracting head
  redexes. A variable's domain is in the type of the binder that binds it,
  which spelledOut does not track; shared syntax is spelled once per place,
  so tracking it needs binder types keyed by scope, not by node.
