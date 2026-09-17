import { arithmetic } from "./arithmetic.mjs";

export function numberTheory(module) {
  const a = arithmetic(module);
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
  } = a;
  const value = (P, n) => app(P, n);
  const below = (P, i) => pi(N, (j) => arr(lt(j, i), not(value(P, j))));
  const payload = (P, n, i) => and(le(i, n), and(value(P, i), below(P, i)));
  const minimum = (P, n) => sigma(N, (i) => payload(P, n, i));
  const none = (P, n) => pi(N, (j) => arr(le(j, n), not(value(P, j))));
  const result = (P, n) => sum(minimum(P, n), none(P, n));
  const decidable = (P) => pi(N, (n) => sum(value(P, n), not(value(P, n))));
  function pack(P, n, i, bound, proof, minimal) {
    return pair(
      N,
      (i) => payload(P, n, i),
      i,
      both(
        le(i, n),
        and(value(P, i), below(P, i)),
        bound,
        both(value(P, i), below(P, i), proof, minimal),
      ),
    );
  }
  function unpack(P, n, p, C, fn) {
    return split(
      N,
      (i) => payload(P, n, i),
      p,
      C,
      (i, data) =>
        split(
          le(i, n),
          () => and(value(P, i), below(P, i)),
          data,
          C,
          (bound, rest) =>
            split(
              value(P, i),
              () => below(P, i),
              rest,
              C,
              (proof, minimal) => fn(i, bound, proof, minimal),
            ),
        ),
    );
  }
  // The search result carries either the least witness or a refutation of
  // every candidate through the inclusive bound. Both branches are constructive.
  const search = def(
    "bounded_least_search",
    lam(arr(N, U), (P) =>
      lam(decidable(P), (dec) =>
        lam(N, (n) => {
          const base = cases(
            value(P, Z),
            not(value(P, Z)),
            app(dec, Z),
            result(P, Z),
            (p) =>
              L(
                minimum(P, Z),
                none(P, Z),
                pack(
                  P,
                  Z,
                  Z,
                  tt,
                  p,
                  lam(N, (j) =>
                    lam(lt(j, Z), (impossible) =>
                      lam(value(P, j), () => impossible),
                    ),
                  ),
                ),
              ),
            (np) =>
              R(
                minimum(P, Z),
                none(P, Z),
                lam(N, (j) =>
                  lam(le(j, Z), (bound) =>
                    lam(value(P, j), (p) =>
                      app(
                        np,
                        transport(
                          N,
                          (k) => value(P, k),
                          j,
                          Z,
                          app(leZero, j, bound),
                          p,
                        ),
                      ),
                    ),
                  ),
                ),
              ),
          );
          return ind(
            (n) => result(P, n),
            base,
            (n, ih) =>
              cases(
                minimum(P, n),
                none(P, n),
                ih,
                result(P, S(n)),
                (witness) =>
                  unpack(
                    P,
                    n,
                    witness,
                    result(P, S(n)),
                    (i, bound, p, minimal) =>
                      L(
                        minimum(P, S(n)),
                        none(P, S(n)),
                        pack(P, S(n), i, app(leStep, i, n, bound), p, minimal),
                      ),
                  ),
                (oldNone) =>
                  cases(
                    value(P, S(n)),
                    not(value(P, S(n))),
                    app(dec, S(n)),
                    result(P, S(n)),
                    (p) =>
                      L(
                        minimum(P, S(n)),
                        none(P, S(n)),
                        pack(P, S(n), S(n), app(leRefl, S(n)), p, oldNone),
                      ),
                    (np) =>
                      R(
                        minimum(P, S(n)),
                        none(P, S(n)),
                        lam(N, (j) =>
                          lam(le(j, S(n)), (bound) =>
                            lam(value(P, j), (p) =>
                              cases(
                                le(j, n),
                                eq(j, S(n)),
                                app(leSplit, j, n, bound),
                                V,
                                (small) => app(oldNone, j, small, p),
                                (same) =>
                                  app(
                                    np,
                                    transport(
                                      N,
                                      (k) => value(P, k),
                                      j,
                                      S(n),
                                      same,
                                      p,
                                    ),
                                  ),
                              ),
                            ),
                          ),
                        ),
                      ),
                  ),
              ),
            n,
          );
        }),
      ),
    ),
  );
  const least = def(
    "least_bounded_witness",
    lam(arr(N, U), (P) =>
      lam(decidable(P), (dec) =>
        lam(N, (n) =>
          lam(value(P, n), (pn) =>
            cases(
              minimum(P, n),
              none(P, n),
              app(search, P, dec, n),
              minimum(P, n),
              (witness) => witness,
              (empty) =>
                absurd(minimum(P, n), app(empty, n, app(leRefl, n), pn)),
            ),
          ),
        ),
      ),
    ),
  );
  const div = (d, n) => sigma(N, (q) => eq(mul(q, d), n));
  b.named(
    lam(N, (d) => lam(N, (n) => div(d, n))),
    "Divides",
  );
  const divDec = def(
    "nontrivial_divisibility_decidable",
    lam(N, (d) =>
      lam(N, (n) => {
        const divisor = S(S(d)),
          P = lam(N, (q) => eq(mul(q, divisor), n));
        const dec = lam(N, (q) => app(eqDec, mul(q, divisor), n));
        const C = sum(div(divisor, n), not(div(divisor, n)));
        return cases(
          minimum(P, n),
          none(P, n),
          app(search, P, dec, n),
          C,
          (witness) =>
            unpack(P, n, witness, C, (q, _, p) =>
              L(
                div(divisor, n),
                not(div(divisor, n)),
                pair(N, (q) => eq(mul(q, divisor), n), q, p),
              ),
            ),
          (empty) =>
            R(
              div(divisor, n),
              not(div(divisor, n)),
              lam(div(divisor, n), (w) =>
                split(
                  N,
                  (q) => eq(mul(q, divisor), n),
                  w,
                  V,
                  (q, p) =>
                    app(
                      empty,
                      q,
                      transport(
                        N,
                        (m) => le(q, m),
                        mul(q, divisor),
                        n,
                        p,
                        app(mulBound, d, q),
                      ),
                      p,
                    ),
                ),
              ),
            ),
        );
      }),
    ),
  );
  return {
    ...a,
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
  };
}
