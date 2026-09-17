import assert from "node:assert/strict";

// Independent boundary checks for the definitions used by the theorem.
// In particular, excluding 0 and 1 guards against a vacuous "prime" predicate.
export function checkPrimes(a) {
  const {
    b,
    app,
    N,
    Z,
    V,
    tt,
    S,
    one,
    two,
    lam,
    pi,
    arr,
    eq,
    refl,
    sigma,
    pair,
    split,
    and,
    both,
    add,
    mul,
    le,
    lt,
    fact,
    prime,
    div,
    zeroSucc,
    inj,
    inv,
    transport,
  } = a;
  const numerals = [Z];
  for (let n = 1; n <= 24; n++) numerals.push(S(numerals.at(-1)));
  const same = (actual, expected) =>
    assert.equal(b.view(b.norm(actual), 0), b.view(b.norm(expected), 0));
  for (const [x, y] of [
    [0, 0],
    [0, 3],
    [3, 0],
    [1, 4],
    [2, 3],
    [4, 4],
  ]) {
    same(add(numerals[x], numerals[y]), numerals[x + y]);
    same(mul(numerals[x], numerals[y]), numerals[x * y]);
    same(le(numerals[x], numerals[y]), x <= y ? a.T : V);
    same(lt(numerals[x], numerals[y]), x < y ? a.T : V);
  }
  for (const [n, f] of [
    [0, 1],
    [1, 1],
    [2, 2],
    [3, 6],
    [4, 24],
  ])
    same(fact(numerals[n]), numerals[f]);
  const excluded = (p, i) =>
    pi(N, (j) => arr(lt(j, i), arr(div(S(S(j)), p), V)));
  const body = (p, i) => and(eq(p, S(S(i))), excluded(p, i));
  const primalityTwo = pair(
    N,
    (i) => body(two, i),
    Z,
    both(
      eq(two, two),
      excluded(two, Z),
      refl(two),
      lam(N, (j) => lam(V, (empty) => lam(div(S(S(j)), two), () => empty))),
    ),
  );
  assert.equal(b.k.verify(prime(two), primalityTwo), true);
  for (const n of [0, 1, 4]) {
    const p = numerals[n];
    const composite = lam(prime(p), (assumption) =>
      split(
        N,
        (i) => body(p, i),
        assumption,
        V,
        (i, data) =>
          split(
            eq(p, S(S(i))),
            () => excluded(p, i),
            data,
            V,
            (e, noDivisor) => {
              if (n === 0) return app(zeroSucc, S(i), e);
              if (n === 1) return app(zeroSucc, i, app(inj, Z, S(i), e));
              const indexEq = app(inj, two, i, app(inj, numerals[3], S(i), e));
              const exclusion = transport(
                N,
                (k) => excluded(p, k),
                i,
                two,
                inv(two, i, indexEq),
                noDivisor,
              );
              const divisor = pair(N, (q) => eq(mul(q, two), p), two, refl(p));
              return app(exclusion, Z, tt, divisor);
            },
          ),
      ),
    );
    assert.equal(b.k.verify(arr(prime(p), V), composite), true);
  }
  console.log(
    "Arithmetic examples and checked proofs: 2 is prime; 0, 1, and 4 are not prime.",
  );
}
