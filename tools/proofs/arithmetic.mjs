// Proof-producing natural-number arithmetic. All terms and conversions are
// emitted through the checked instruction API; no arithmetic facts are axioms.
import { Builder } from "./builder.mjs";
export function arithmetic(module) {
  const b = new Builder(module, { loadLibrary: false });
  b.opaque = true;
  const op = (...a) => b.emit(...a),
    norm = (a) => b.norm(a),
    app = (...a) => b.app(...a);
  const N = op("NatForm"),
    Z = op("NatIntroZ"),
    U = op("UIntro0"),
    V = op("VoidForm"),
    T = op("UnitForm"),
    tt = op("UnitIntro");
  const S = (n) => op("NatIntroS", [n]),
    one = S(Z),
    two = S(one);
  const lam = (A, f) => b.lam(A, f),
    pi = (A, f) => b.pi(A, f),
    arr = (A, B) => b.arrow(A, B),
    eq = (x, y) => b.eq(N, x, y),
    refl = (x) => b.refl(x);
  const not = (A) => arr(A, V),
    sum = (A, B) => op("SumForm", [A, B]);
  const L = (A, B, x) => op("SumIntroL", [A, B, b.coerce(x, A)]),
    R = (A, B, x) => op("SumIntroR", [A, B, b.coerce(x, B)]);
  const absurd = (A, v) => op("VoidElim", [A, v], [null]);
  function cases(A, B, v, C, left, right) {
    const x = b.fresh(A),
      y = b.fresh(B);
    return norm(
      op(
        "SumElim",
        [C, b.coerce(left(x.v), C), b.coerce(right(y.v), C), v],
        [null, x.c, y.c],
      ),
    );
  }
  function sigma(A, B) {
    const x = b.fresh(A);
    return op("SigmaForm", [A, B(x.v)], [x.c]);
  }
  function pair(A, B, a, v) {
    const x = b.fresh(A),
      C = B(x.v);
    return op("SigmaIntro", [a, C, b.coerce(v, b.subst(C, x, a))], [x.c]);
  }
  function split(A, B, p, C, fn) {
    const x = b.fresh(A),
      y = b.fresh(B(x.v));
    return norm(
      op("SigmaElim", [C, b.coerce(fn(x.v, y.v), C), p], [null, x.c, y.c]),
    );
  }
  const and = (A, B) => sigma(A, () => B),
    both = (A, B, a, c) => pair(A, () => B, a, c);
  function ind(C, base, step, n) {
    const z = b.fresh(N),
      k = b.fresh(N),
      m = C(z.v),
      h = b.fresh(b.subst(m, z, k.v));
    return norm(
      op(
        "NatElim",
        [
          m,
          b.coerce(base, b.subst(m, z, Z)),
          b.coerce(step(k.v, h.v), b.subst(m, z, S(k.v))),
          n,
        ],
        [z.c, k.c, h.c],
      ),
    );
  }
  const rec = (A, base, step, n) => ind(() => A, base, step, n);
  function specialize(body, vars, values) {
    let f = body;
    for (const x of [...vars].reverse()) f = op("PiIntro", [x.A, f], [x.c]);
    for (const v of values)
      f = op("UnHigh", [
        op("BetaReducePointed", [op("HighExp", [op("PiElim", [f, v])])]),
      ]);
    return f;
  }
  function J(A, C, base, a, c, p) {
    const x = b.fresh(A),
      y = b.fresh(A),
      q = b.fresh(b.eq(A, x.v, y.v)),
      z = b.fresh(A),
      m = C(x.v, y.v, q.v);
    const d = b.coerce(
      base(z.v),
      specialize(m, [x, y, q], [z.v, z.v, refl(z.v)]),
    );
    return norm(op("EqElim", [m, d, a, c, p], [x.c, y.c, q.c, z.c]));
  }
  function transport(A, C, x, y, p, t) {
    return app(
      J(
        A,
        (x, y) => arr(C(x), C(y)),
        (x) => lam(C(x), (t) => t),
        x,
        y,
        p,
      ),
      t,
    );
  }
  function def(name, body) {
    const r = op("DefEqExtL", [op("Def", [body])]);
    const named = b.named(r, name);
    console.log("Proved", name, b.k.steps.length, b.k.stats().nodes);
    return named;
  }
  const sym = def(
    "nat_eq_sym",
    lam(N, (x) =>
      lam(N, (y) =>
        lam(eq(x, y), (p) => J(N, (x, y) => eq(y, x), refl, x, y, p)),
      ),
    ),
  );
  const trans = def(
    "nat_eq_trans",
    lam(N, (x) =>
      lam(N, (y) =>
        lam(N, (z) =>
          lam(eq(x, y), (p) =>
            lam(eq(y, z), (q) => transport(N, (z) => eq(x, z), y, z, q, p)),
          ),
        ),
      ),
    ),
  );
  const ap = def(
    "nat_congruence",
    lam(arr(N, N), (f) =>
      lam(N, (x) =>
        lam(N, (y) =>
          lam(eq(x, y), (p) =>
            J(
              N,
              (x, y) => eq(app(f, x), app(f, y)),
              (x) => refl(app(f, x)),
              x,
              y,
              p,
            ),
          ),
        ),
      ),
    ),
  );
  const inv = (x, y, p) => app(sym, x, y, p),
    cat = (x, y, z, p, q) => app(trans, x, y, z, p, q),
    map = (f, x, y, p) => app(ap, f, x, y, p);
  const succ = lam(N, S);
  const addF = lam(N, (x) => lam(N, (y) => rec(N, y, (k, h) => S(h), x)));
  const add = (x, y) => app(addF, x, y);
  b.named(addF, "nat_add");
  const mulF = lam(N, (x) => lam(N, (y) => rec(N, Z, (k, h) => add(y, h), x)));
  const mul = (x, y) => app(mulF, x, y);
  b.named(mulF, "nat_mul");
  const leF = lam(N, (x) =>
    rec(
      arr(N, U),
      lam(N, () => T),
      (k, h) => lam(N, (y) => rec(U, V, (j, _) => app(h, j), y)),
      x,
    ),
  );
  const le = (x, y) => app(leF, x, y),
    lt = (x, y) => le(S(x), y);
  b.named(leF, "nat_le");
  const isZero = lam(N, (n) => rec(U, T, () => V, n));
  const zeroSucc = def(
    "nat_zero_ne_succ",
    lam(N, (n) =>
      lam(eq(Z, S(n)), (p) =>
        transport(N, (x) => app(isZero, x), Z, S(n), p, tt),
      ),
    ),
  );
  const pred = lam(N, (n) => rec(N, Z, (k, _) => k, n));
  const inj = def(
    "nat_succ_injective",
    lam(N, (x) =>
      lam(N, (y) => lam(eq(S(x), S(y)), (p) => map(pred, S(x), S(y), p))),
    ),
  );
  const snz = (n, p) => app(zeroSucc, n, inv(S(n), Z, p));
  const addZero = def(
    "nat_add_zero",
    lam(N, (x) =>
      ind(
        (x) => eq(add(x, Z), x),
        refl(Z),
        (k, h) => map(succ, add(k, Z), k, h),
        x,
      ),
    ),
  );
  const addSucc = def(
    "nat_add_succ",
    lam(N, (x) =>
      ind(
        (x) => pi(N, (y) => eq(add(x, S(y)), S(add(x, y)))),
        lam(N, (y) => refl(S(y))),
        (k, h) =>
          lam(N, (y) => map(succ, add(k, S(y)), S(add(k, y)), app(h, y))),
        x,
      ),
    ),
  );
  const addAssoc = def(
    "nat_add_assoc",
    lam(N, (x) =>
      ind(
        (x) =>
          pi(N, (y) => pi(N, (z) => eq(add(add(x, y), z), add(x, add(y, z))))),
        lam(N, (y) => lam(N, (z) => refl(add(y, z)))),
        (k, h) =>
          lam(N, (y) =>
            lam(N, (z) =>
              map(succ, add(add(k, y), z), add(k, add(y, z)), app(h, y, z)),
            ),
          ),
        x,
      ),
    ),
  );
  const addComm = def(
    "nat_add_comm",
    lam(N, (x) =>
      ind(
        (x) => pi(N, (y) => eq(add(x, y), add(y, x))),
        lam(N, (y) => inv(add(y, Z), y, app(addZero, y))),
        (k, h) =>
          lam(N, (y) =>
            cat(
              S(add(k, y)),
              S(add(y, k)),
              add(y, S(k)),
              map(succ, add(k, y), add(y, k), app(h, y)),
              inv(add(y, S(k)), S(add(y, k)), app(addSucc, y, k)),
            ),
          ),
        x,
      ),
    ),
  );
  const natCase = (C, z, s, n) => ind(C, z, (k, _) => s(k), n);
  const leRefl = def(
    "nat_le_refl",
    lam(N, (n) =>
      ind(
        (n) => le(n, n),
        tt,
        (k, h) => h,
        n,
      ),
    ),
  );
  const leZero = def(
    "nat_le_zero",
    lam(N, (n) =>
      ind(
        (n) => arr(le(n, Z), eq(n, Z)),
        lam(T, () => refl(Z)),
        (k, _) => lam(V, (h) => absurd(eq(S(k), Z), h)),
        n,
      ),
    ),
  );
  const leStep = def(
    "nat_le_step",
    lam(N, (a) =>
      ind(
        (a) => pi(N, (c) => arr(le(a, c), le(a, S(c)))),
        lam(N, (c) => lam(T, () => tt)),
        (a, h) =>
          lam(N, (c) =>
            natCase(
              (c) => arr(le(S(a), c), le(S(a), S(c))),
              lam(V, (v) => absurd(le(S(a), one), v)),
              (c) => lam(le(a, c), (v) => app(h, c, v)),
              c,
            ),
          ),
        a,
      ),
    ),
  );
  const leTrans = def(
    "nat_le_trans",
    lam(N, (a) =>
      ind(
        (a) =>
          pi(N, (c) => pi(N, (d) => arr(le(a, c), arr(le(c, d), le(a, d))))),
        lam(N, (c) => lam(N, (d) => lam(T, () => lam(le(c, d), () => tt)))),
        (a, h) =>
          lam(N, (c) =>
            natCase(
              (c) => pi(N, (d) => arr(le(S(a), c), arr(le(c, d), le(S(a), d)))),
              lam(N, (d) =>
                lam(V, (v) => lam(T, () => absurd(le(S(a), d), v))),
              ),
              (c) =>
                lam(N, (d) =>
                  natCase(
                    (d) => arr(le(a, c), arr(le(S(c), d), le(S(a), d))),
                    lam(le(a, c), () => lam(V, (v) => absurd(le(S(a), Z), v))),
                    (d) =>
                      lam(le(a, c), (ac) =>
                        lam(le(c, d), (cd) => app(h, c, d, ac, cd)),
                      ),
                    d,
                  ),
                ),
              c,
            ),
          ),
        a,
      ),
    ),
  );
  const leTotal = def(
    "nat_le_total",
    lam(N, (a) =>
      ind(
        (a) => pi(N, (c) => sum(le(a, c), lt(c, a))),
        lam(N, (c) => L(le(Z, c), lt(c, Z), tt)),
        (a, h) =>
          lam(N, (c) =>
            natCase(
              (c) => sum(le(S(a), c), lt(c, S(a))),
              R(le(S(a), Z), lt(Z, S(a)), tt),
              (c) => app(h, c),
              c,
            ),
          ),
        a,
      ),
    ),
  );
  const leSplit = def(
    "nat_le_succ_split",
    lam(N, (a) =>
      ind(
        (a) => pi(N, (c) => arr(le(a, S(c)), sum(le(a, c), eq(a, S(c))))),
        lam(N, (c) => lam(T, () => L(le(Z, c), eq(Z, S(c)), tt))),
        (a, h) =>
          lam(N, (c) =>
            natCase(
              (c) => arr(le(S(a), S(c)), sum(le(S(a), c), eq(S(a), S(c)))),
              lam(le(a, Z), (v) =>
                R(
                  le(S(a), Z),
                  eq(S(a), one),
                  map(succ, a, Z, app(leZero, a, v)),
                ),
              ),
              (c) =>
                lam(le(a, S(c)), (v) =>
                  cases(
                    le(a, c),
                    eq(a, S(c)),
                    app(h, c, v),
                    sum(le(S(a), S(c)), eq(S(a), S(S(c)))),
                    (ac) => L(le(S(a), S(c)), eq(S(a), S(S(c))), ac),
                    (ac) =>
                      R(
                        le(S(a), S(c)),
                        eq(S(a), S(S(c))),
                        map(succ, a, S(c), ac),
                      ),
                  ),
                ),
              c,
            ),
          ),
        a,
      ),
    ),
  );
  const leAdd = def(
    "nat_le_add",
    lam(N, (a) =>
      ind(
        (a) => pi(N, (c) => le(c, add(a, c))),
        lam(N, (c) => app(leRefl, c)),
        (a, h) => lam(N, (c) => app(leStep, c, add(a, c), app(h, c))),
        a,
      ),
    ),
  );
  const eqDec = def(
    "nat_eq_decidable",
    lam(N, (a) =>
      ind(
        (a) => pi(N, (c) => sum(eq(a, c), not(eq(a, c)))),
        lam(N, (c) =>
          natCase(
            (c) => sum(eq(Z, c), not(eq(Z, c))),
            L(eq(Z, Z), not(eq(Z, Z)), refl(Z)),
            (c) => R(eq(Z, S(c)), not(eq(Z, S(c))), app(zeroSucc, c)),
            c,
          ),
        ),
        (a, h) =>
          lam(N, (c) =>
            natCase(
              (c) => sum(eq(S(a), c), not(eq(S(a), c))),
              R(
                eq(S(a), Z),
                not(eq(S(a), Z)),
                lam(eq(S(a), Z), (p) => snz(a, p)),
              ),
              (c) =>
                cases(
                  eq(a, c),
                  not(eq(a, c)),
                  app(h, c),
                  sum(eq(S(a), S(c)), not(eq(S(a), S(c)))),
                  (p) =>
                    L(eq(S(a), S(c)), not(eq(S(a), S(c))), map(succ, a, c, p)),
                  (np) =>
                    R(
                      eq(S(a), S(c)),
                      not(eq(S(a), S(c))),
                      lam(eq(S(a), S(c)), (p) => app(np, app(inj, a, c, p))),
                    ),
                ),
              c,
            ),
          ),
        a,
      ),
    ),
  );
  const addCancel = def(
    "nat_add_cancel",
    lam(N, (a) =>
      ind(
        (a) =>
          pi(N, (c) => pi(N, (d) => arr(eq(add(a, c), add(a, d)), eq(c, d)))),
        lam(N, (c) => lam(N, (d) => lam(eq(c, d), (p) => p))),
        (a, h) =>
          lam(N, (c) =>
            lam(N, (d) =>
              lam(eq(S(add(a, c)), S(add(a, d))), (p) =>
                app(h, c, d, app(inj, add(a, c), add(a, d), p)),
              ),
            ),
          ),
        a,
      ),
    ),
  );
  const mulZero = def(
    "nat_mul_zero",
    lam(N, (a) =>
      ind(
        (a) => eq(mul(a, Z), Z),
        refl(Z),
        (a, h) => h,
        a,
      ),
    ),
  );
  const addShuffle = def(
    "nat_add_shuffle",
    lam(N, (a) =>
      lam(N, (c) =>
        lam(N, (d) =>
          cat(
            add(a, add(c, d)),
            add(add(a, c), d),
            add(c, add(a, d)),
            inv(add(add(a, c), d), add(a, add(c, d)), app(addAssoc, a, c, d)),
            cat(
              add(add(a, c), d),
              add(add(c, a), d),
              add(c, add(a, d)),
              map(
                lam(N, (x) => add(x, d)),
                add(a, c),
                add(c, a),
                app(addComm, a, c),
              ),
              app(addAssoc, c, a, d),
            ),
          ),
        ),
      ),
    ),
  );
  const mulSucc = def(
    "nat_mul_succ",
    lam(N, (a) =>
      ind(
        (a) => pi(N, (c) => eq(mul(a, S(c)), add(a, mul(a, c)))),
        lam(N, (c) => refl(Z)),
        (a, h) =>
          lam(N, (c) =>
            map(
              succ,
              add(c, mul(a, S(c))),
              add(a, add(c, mul(a, c))),
              cat(
                add(c, mul(a, S(c))),
                add(c, add(a, mul(a, c))),
                add(a, add(c, mul(a, c))),
                map(
                  lam(N, (x) => add(c, x)),
                  mul(a, S(c)),
                  add(a, mul(a, c)),
                  app(h, c),
                ),
                app(addShuffle, c, a, mul(a, c)),
              ),
            ),
          ),
        a,
      ),
    ),
  );
  const mulComm = def(
    "nat_mul_comm",
    lam(N, (a) =>
      ind(
        (a) => pi(N, (c) => eq(mul(a, c), mul(c, a))),
        lam(N, (c) => inv(mul(c, Z), Z, app(mulZero, c))),
        (a, h) =>
          lam(N, (c) =>
            cat(
              add(c, mul(a, c)),
              add(c, mul(c, a)),
              mul(c, S(a)),
              map(
                lam(N, (x) => add(c, x)),
                mul(a, c),
                mul(c, a),
                app(h, c),
              ),
              inv(mul(c, S(a)), add(c, mul(c, a)), app(mulSucc, c, a)),
            ),
          ),
        a,
      ),
    ),
  );
  const mulAdd = def(
    "nat_mul_add",
    lam(N, (a) =>
      ind(
        (a) =>
          pi(N, (c) =>
            pi(N, (d) => eq(mul(add(a, c), d), add(mul(a, d), mul(c, d)))),
          ),
        lam(N, (c) => lam(N, (d) => refl(mul(c, d)))),
        (a, h) =>
          lam(N, (c) =>
            lam(N, (d) =>
              cat(
                add(d, mul(add(a, c), d)),
                add(d, add(mul(a, d), mul(c, d))),
                add(add(d, mul(a, d)), mul(c, d)),
                map(
                  lam(N, (x) => add(d, x)),
                  mul(add(a, c), d),
                  add(mul(a, d), mul(c, d)),
                  app(h, c, d),
                ),
                inv(
                  add(add(d, mul(a, d)), mul(c, d)),
                  add(d, add(mul(a, d), mul(c, d))),
                  app(addAssoc, d, mul(a, d), mul(c, d)),
                ),
              ),
            ),
          ),
        a,
      ),
    ),
  );
  const mulAssoc = def(
    "nat_mul_assoc",
    lam(N, (a) =>
      ind(
        (a) =>
          pi(N, (c) => pi(N, (d) => eq(mul(mul(a, c), d), mul(a, mul(c, d))))),
        lam(N, (c) => lam(N, (d) => refl(Z))),
        (a, h) =>
          lam(N, (c) =>
            lam(N, (d) =>
              cat(
                mul(add(c, mul(a, c)), d),
                add(mul(c, d), mul(mul(a, c), d)),
                add(mul(c, d), mul(a, mul(c, d))),
                app(mulAdd, c, mul(a, c), d),
                map(
                  lam(N, (x) => add(mul(c, d), x)),
                  mul(mul(a, c), d),
                  mul(a, mul(c, d)),
                  app(h, c, d),
                ),
              ),
            ),
          ),
        a,
      ),
    ),
  );
  const mulBound = def(
    "nat_quotient_bound",
    lam(N, (d) =>
      lam(N, (q) =>
        ind(
          (q) => le(q, mul(q, S(S(d)))),
          tt,
          (q, h) => {
            const product = mul(q, S(S(d)));
            return app(
              leTrans,
              q,
              product,
              S(add(d, product)),
              h,
              app(leStep, product, add(d, product), app(leAdd, d, product)),
            );
          },
          q,
        ),
      ),
    ),
  );

  return {
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
  };
}
