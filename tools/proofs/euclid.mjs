import { numberTheory } from "./number_theory.mjs";

// Euclid's constructive argument: a least nontrivial divisor of n!+1 is
// prime, and cannot be at most n because it would then divide n! as well.
export function euclid(module) {
  const a = numberTheory(module);
  const {
    b,
    op,
    norm,
    app,
    N,
    Z,
    U,
    V,
    T,
    tt,
    S,
    one,
    two,
    lam,
    pi,
    arr,
    eq,
    refl,
    not,
    sum,
    L,
    R,
    absurd,
    cases,
    sigma,
    pair,
    split,
    and,
    both,
    ind,
    rec,
    J,
    transport,
    def,
    inv,
    cat,
    map,
    succ,
    add,
    mul,
    le,
    lt,
    zeroSucc,
    inj,
    snz,
    addZero,
    addSucc,
    addAssoc,
    addComm,
    natCase,
    leRefl,
    leZero,
    leStep,
    leTrans,
    leTotal,
    leSplit,
    leAdd,
    eqDec,
    addCancel,
    mulZero,
    mulSucc,
    mulComm,
    mulAdd,
    mulAssoc,
    mulBound,
    below,
    payload,
    minimum,
    none,
    result,
    decidable,
    pack,
    unpack,
    search,
    least,
    div,
    divDec,
  } = a;
  const divTrans = def(
    "divides_transitive",
    lam(N, (d) =>
      lam(N, (m) =>
        lam(N, (n) =>
          lam(div(d, m), (dm) =>
            lam(div(m, n), (mn) => {
              const C = div(d, n);
              return split(
                N,
                (k) => eq(mul(k, d), m),
                dm,
                C,
                (k, pk) =>
                  split(
                    N,
                    (l) => eq(mul(l, m), n),
                    mn,
                    C,
                    (l, pl) => {
                      const q = mul(l, k),
                        qd = mul(q, d),
                        lkd = mul(l, mul(k, d)),
                        lm = mul(l, m);
                      return pair(
                        N,
                        (q) => eq(mul(q, d), n),
                        q,
                        cat(
                          qd,
                          lkd,
                          n,
                          app(mulAssoc, l, k, d),
                          cat(
                            lkd,
                            lm,
                            n,
                            map(
                              lam(N, (x) => mul(l, x)),
                              mul(k, d),
                              m,
                              pk,
                            ),
                            pl,
                          ),
                        ),
                      );
                    },
                  ),
              );
            }),
          ),
        ),
      ),
    ),
  );
  const noAdjacent = def(
    "multiples_not_adjacent",
    lam(N, (d) => {
      const D = S(S(d));
      const C = (k, l) => not(eq(mul(l, D), S(mul(k, D))));
      const base = lam(N, (l) =>
        natCase(
          (l) => C(Z, l),
          app(zeroSucc, Z),
          (l) =>
            lam(eq(mul(S(l), D), one), (p) =>
              snz(add(d, mul(l, D)), app(inj, S(add(d, mul(l, D))), Z, p)),
            ),
          l,
        ),
      );
      return lam(N, (k) =>
        ind(
          (k) => pi(N, (l) => C(k, l)),
          base,
          (k, ih) =>
            lam(N, (l) =>
              natCase(
                (l) => C(S(k), l),
                app(zeroSucc, mul(S(k), D)),
                (l) =>
                  lam(eq(mul(S(l), D), S(mul(S(k), D))), (p) => {
                    const left = mul(l, D),
                      right = mul(k, D);
                    const aligned = cat(
                      add(D, left),
                      S(add(D, right)),
                      add(D, S(right)),
                      p,
                      inv(
                        add(D, S(right)),
                        S(add(D, right)),
                        app(addSucc, D, right),
                      ),
                    );
                    return app(
                      ih,
                      l,
                      app(addCancel, D, left, S(right), aligned),
                    );
                  }),
                l,
              ),
            ),
          k,
        ),
      );
    }),
  );
  const consecutive = def(
    "nontrivial_divisor_not_consecutive",
    lam(N, (d) =>
      lam(N, (n) => {
        const D = S(S(d));
        return lam(div(D, n), (dn) =>
          lam(div(D, S(n)), (dsn) =>
            split(
              N,
              (k) => eq(mul(k, D), n),
              dn,
              V,
              (k, pk) =>
                split(
                  N,
                  (l) => eq(mul(l, D), S(n)),
                  dsn,
                  V,
                  (l, pl) =>
                    app(
                      noAdjacent,
                      d,
                      k,
                      l,
                      cat(
                        mul(l, D),
                        S(n),
                        S(mul(k, D)),
                        pl,
                        inv(S(mul(k, D)), S(n), map(succ, mul(k, D), n, pk)),
                      ),
                    ),
                ),
            ),
          ),
        );
      }),
    ),
  );
  const factorial = lam(N, (n) => rec(N, one, (k, h) => mul(S(k), h), n));
  b.named(factorial, "nat_factorial");
  const fact = (n) => app(factorial, n);
  const addPositive = def(
    "nat_add_positive",
    lam(N, (x) =>
      natCase(
        (x) => pi(N, (y) => arr(le(one, x), le(one, add(x, y)))),
        lam(N, (y) => lam(V, (v) => absurd(le(one, y), v))),
        (x) => lam(N, (y) => lam(T, () => tt)),
        x,
      ),
    ),
  );
  const factPositive = def(
    "factorial_positive",
    lam(N, (n) =>
      ind(
        (n) => le(one, fact(n)),
        tt,
        (n, h) => app(addPositive, fact(n), mul(n, fact(n)), h),
        n,
      ),
    ),
  );
  const factDiv = def(
    "bounded_divisor_of_factorial",
    lam(N, (d) => {
      const D = S(S(d));
      return lam(N, (n) =>
        ind(
          (n) => arr(le(D, n), div(D, fact(n))),
          lam(V, (v) => absurd(div(D, one), v)),
          (n, ih) =>
            lam(le(D, S(n)), (bound) =>
              cases(
                le(D, n),
                eq(D, S(n)),
                app(leSplit, D, n, bound),
                div(D, fact(S(n))),
                (small) =>
                  app(
                    divTrans,
                    D,
                    fact(n),
                    fact(S(n)),
                    app(ih, small),
                    pair(
                      N,
                      (k) => eq(mul(k, fact(n)), fact(S(n))),
                      S(n),
                      refl(fact(S(n))),
                    ),
                  ),
                (same) =>
                  pair(
                    N,
                    (k) => eq(mul(k, D), fact(S(n))),
                    fact(n),
                    cat(
                      mul(fact(n), D),
                      mul(fact(n), S(n)),
                      fact(S(n)),
                      map(
                        lam(N, (x) => mul(fact(n), x)),
                        D,
                        S(n),
                        same,
                      ),
                      app(mulComm, fact(n), S(n)),
                    ),
                  ),
              ),
            ),
          n,
        ),
      );
    }),
  );
  // p is prime iff p = 2+i and none of 2, ..., p-1 divides p.
  const prime = (p) =>
    sigma(N, (i) =>
      and(
        eq(p, S(S(i))),
        pi(N, (j) => arr(lt(j, i), not(div(S(S(j)), p)))),
      ),
    );
  b.named(lam(N, prime), "Prime");
  const factor = (n) => sigma(N, (i) => and(prime(S(S(i))), div(S(S(i)), n)));
  const primeFactor = def(
    "prime_divisor_exists",
    lam(N, (n) =>
      natCase(
        (n) => arr(le(two, n), factor(n)),
        lam(V, (v) => absurd(factor(Z), v)),
        (k) =>
          natCase(
            (k) => arr(le(two, S(k)), factor(S(k))),
            lam(V, (v) => absurd(factor(one), v)),
            (x) =>
              lam(T, () => {
                const M = S(S(x)),
                  P = lam(N, (i) => div(S(S(i)), M)),
                  dec = lam(N, (i) => app(divDec, i, M));
                const self = pair(
                  N,
                  (k) => eq(mul(k, M), M),
                  one,
                  app(addZero, M),
                );
                return unpack(
                  P,
                  x,
                  app(least, P, dec, x, self),
                  factor(M),
                  (i, _, w, minimal) => {
                    const p = S(S(i));
                    const exclusion = lam(N, (j) =>
                      lam(lt(j, i), (smaller) =>
                        lam(div(S(S(j)), p), (dp) =>
                          app(
                            minimal,
                            j,
                            smaller,
                            app(divTrans, S(S(j)), p, M, dp, w),
                          ),
                        ),
                      ),
                    );
                    const primality = pair(
                      N,
                      (k) =>
                        and(
                          eq(p, S(S(k))),
                          pi(N, (j) => arr(lt(j, k), not(div(S(S(j)), p)))),
                        ),
                      i,
                      both(
                        eq(p, p),
                        pi(N, (j) => arr(lt(j, i), not(div(S(S(j)), p)))),
                        refl(p),
                        exclusion,
                      ),
                    );
                    return pair(
                      N,
                      (i) => and(prime(S(S(i))), div(S(S(i)), M)),
                      i,
                      both(prime(p), div(p, M), primality, w),
                    );
                  },
                );
              }),
            k,
          ),
        n,
      ),
    ),
  );
  const beyond = (n) => sigma(N, (p) => and(prime(p), lt(n, p)));
  const statement = b.named(pi(N, beyond), "InfinitelyManyPrimes");
  const proof = b.named(
    lam(N, (n) => {
      const M = S(fact(n));
      return split(
        N,
        (i) => and(prime(S(S(i))), div(S(S(i)), M)),
        app(primeFactor, M, app(factPositive, n)),
        beyond(n),
        (i, data) => {
          const p = S(S(i));
          return split(
            prime(p),
            () => div(p, M),
            data,
            beyond(n),
            (primality, w) => {
              const greater = cases(
                le(p, n),
                lt(n, p),
                app(leTotal, p, n),
                lt(n, p),
                (bounded) =>
                  absurd(
                    lt(n, p),
                    app(
                      consecutive,
                      i,
                      fact(n),
                      app(factDiv, i, n, bounded),
                      w,
                    ),
                  ),
                (greater) => greater,
              );
              return pair(
                N,
                (p) => and(prime(p), lt(n, p)),
                p,
                both(prime(p), lt(n, p), primality, greater),
              );
            },
          );
        },
      );
    }),
    "infinitely_many_primes",
  );
  if (!b.k.verify(statement, proof))
    throw new Error("Infinitude of primes did not verify");
  console.log("VERIFIED EUCLID", b.k.steps.length, b.k.stats());
  return {
    ...a,
    prime,
    divTrans,
    noAdjacent,
    consecutive,
    factorial,
    fact,
    factPositive,
    factDiv,
    primeFactor,
    statement,
    proof,
  };
}
