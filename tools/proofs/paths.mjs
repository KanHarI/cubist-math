// Path algebra derived only with equality induction. Concatenation eliminates
// its second path, so p · refl computes to p; left units are proved explicitly.
export function paths(b, U0omega, apDefinition = "lib_ap") {
  const op = (...xs) => b.emit(...xs),
    app = (...xs) => b.app(...xs),
    norm = (x) => b.norm(x);
  const eq = (A, x, y) => b.eq(A, x, y),
    refl = (x) => b.refl(x);
  const cache = new Map();
  function specialize(body, vars, values) {
    let f = body;
    for (const x of [...vars].reverse()) f = op("PiIntro", [x.A, f], [x.c]);
    for (const v of values)
      f = op("UnHigh", [
        op("BetaReducePointed", [op("HighExp", [op("PiElim", [f, v])])]),
      ]);
    return f;
  }
  function J(A, motive, base, a, c, p) {
    const x = b.fresh(A),
      y = b.fresh(A),
      q = b.fresh(eq(A, x.v, y.v)),
      z = b.fresh(A);
    const C = motive(x.v, y.v, q.v);
    const d = b.coerce(
      base(z.v),
      specialize(C, [x, y, q], [z.v, z.v, refl(z.v)]),
    );
    return norm(op("EqElim", [C, d, a, c, p], [x.c, y.c, q.c, z.c]));
  }
  const ap = (A, C, f, x, y, p) => app(apDefinition, U0omega, A, C, f, x, y, p);
  function cached(tag, A, build) {
    const key = tag + ":" + b.view(A, 0);
    if (!cache.has(key)) cache.set(key, build());
    return cache.get(key);
  }
  function cat(A, x, y, z, p, q) {
    const fn = cached("cat", A, () =>
      b.lam(A, (y) =>
        b.lam(A, (z) =>
          b.lam(eq(A, y, z), (q) =>
            J(
              A,
              (y, z) => b.pi(A, (x) => b.arrow(eq(A, x, y), eq(A, x, z))),
              (y) => b.lam(A, (x) => b.lam(eq(A, x, y), (p) => p)),
              y,
              z,
              q,
            ),
          ),
        ),
      ),
    );
    return app(fn, y, z, q, x, p);
  }
  function inv(A, x, y, p) {
    const fn = cached("inv", A, () =>
      b.lam(A, (x) =>
        b.lam(A, (y) =>
          b.lam(eq(A, x, y), (p) =>
            J(
              A,
              (x, y) => eq(A, y, x),
              (x) => refl(x),
              x,
              y,
              p,
            ),
          ),
        ),
      ),
    );
    return app(fn, x, y, p);
  }
  function leftUnit(A, x, y, p) {
    const fn = cached("lu", A, () =>
      b.lam(A, (x) =>
        b.lam(A, (y) =>
          b.lam(eq(A, x, y), (p) =>
            J(
              A,
              (x, y, p) => eq(eq(A, x, y), cat(A, x, x, y, refl(x), p), p),
              (x) => refl(refl(x)),
              x,
              y,
              p,
            ),
          ),
        ),
      ),
    );
    return app(fn, x, y, p);
  }
  // Naturality of H : k ~ id: ap(k,p) · H(y) = H(x) · p.
  function natural(A, k, H, x, y, p) {
    return J(
      A,
      (x, y, p) =>
        eq(
          eq(A, app(k, x), y),
          cat(A, app(k, x), app(k, y), y, ap(A, A, k, x, y, p), app(H, y)),
          cat(A, app(k, x), x, y, app(H, x), p),
        ),
      (x) => leftUnit(A, app(k, x), x, app(H, x)),
      x,
      y,
      p,
    );
  }
  function cancelRight(A, x, y, z, p, q, r, h) {
    const lemma = J(
      A,
      (y, z, r) =>
        b.pi(A, (x) =>
          b.pi(eq(A, x, y), (p) =>
            b.pi(eq(A, x, y), (q) =>
              b.arrow(
                eq(eq(A, x, z), cat(A, x, y, z, p, r), cat(A, x, y, z, q, r)),
                eq(eq(A, x, y), p, q),
              ),
            ),
          ),
        ),
      (y) =>
        b.lam(A, (x) =>
          b.lam(eq(A, x, y), (p) =>
            b.lam(eq(A, x, y), (q) => b.lam(eq(eq(A, x, y), p, q), (h) => h)),
          ),
        ),
      y,
      z,
      r,
    );
    return app(lemma, x, p, q, h);
  }
  function commute(A, k, H, x) {
    const kx = app(k, x),
      kkx = app(k, kx),
      hx = app(H, x),
      hkx = app(H, kx);
    const mapped = ap(A, A, k, kx, x, hx);
    const h = natural(A, k, H, kx, x, hx);
    return cancelRight(A, kkx, kx, x, mapped, hkx, hx, h); // ap k (H x) = H(k x)
  }
  function apCompose(A, B, C, f, g, x, y, p) {
    const gf = b.lam(A, (a) => app(g, app(f, a)));
    return J(
      A,
      (x, y, p) =>
        eq(
          eq(C, app(g, app(f, x)), app(g, app(f, y))),
          ap(B, C, g, app(f, x), app(f, y), ap(A, B, f, x, y, p)),
          ap(A, C, gf, x, y, p),
        ),
      (x) => refl(refl(app(g, app(f, x)))),
      x,
      y,
      p,
    );
  }
  function cancelLeft(A, x, y, z, p, q) {
    const lemma = J(
      A,
      (x, y, p) =>
        b.pi(A, (z) =>
          b.pi(eq(A, y, z), (q) =>
            eq(
              eq(A, y, z),
              cat(A, y, x, z, inv(A, x, y, p), cat(A, x, y, z, p, q)),
              q,
            ),
          ),
        ),
      (x) =>
        b.lam(A, (z) =>
          b.lam(eq(A, x, z), (q) => {
            const rq = cat(A, x, x, z, refl(x), q),
              rrq = cat(A, x, x, z, refl(x), rq),
              T = eq(A, x, z);
            return cat(
              T,
              rrq,
              rq,
              q,
              leftUnit(A, x, z, rq),
              leftUnit(A, x, z, q),
            );
          }),
        ),
      x,
      y,
      p,
    );
    return app(lemma, z, q);
  }
  return {
    J,
    eq,
    refl,
    ap,
    cat,
    inv,
    leftUnit,
    natural,
    cancelRight,
    commute,
    apCompose,
    cancelLeft,
  };
}
