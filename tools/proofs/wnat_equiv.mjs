import { writeFile } from "node:fs/promises";
import { Session } from "../../web/session.mjs";
import { formatStep } from "../../web/language.mjs";
import catalogue from "../../web/proofs/catalogue.mjs";
import createKernel from "../../web/dist/kernel.mjs";
import { Builder } from "./builder.mjs";
import { paths } from "./paths.mjs";
const module = await createKernel();
const b = new Builder(module);
const op = (...xs) => b.emit(...xs),
  norm = (x) => b.norm(x),
  app = (...xs) => b.app(...xs);
const Unit = op("UnitForm"),
  star = op("UnitIntro"),
  Void = op("VoidForm"),
  U0 = op("UIntro0");
const U1 = op("UIntro", [U0]),
  U1omega = op("UCumulOmega", [U1]);
const Two = norm("lib_Two"),
  W = norm("lib_UNat"),
  Nat = op("NatForm"),
  zero = op("NatIntroZ");
const label0 = op("SumIntroL", [Unit, Unit, star]),
  label1 = op("SumIntroR", [Unit, Unit, star]);
const arity = app(
  "lib_ind2",
  U1omega,
  b.lam(Two, () => U0),
  Void,
  Unit,
);
const B = (a) => app(arity, a);
const wz = norm("lib_zeroU"),
  ws = norm("lib_succU");
function twoElim(motive, left, right, value) {
  const z = b.fresh(Two),
    u = b.fresh(Unit),
    v = b.fresh(Unit);
  const mz = motive(z.v);
  const il = op("SumIntroL", [Unit, Unit, u.v]),
    ir = op("SumIntroR", [Unit, Unit, v.v]);
  const ml = b.subst(mz, z, il),
    mr = b.subst(mz, z, ir);
  const lc = op(
    "UnitElim",
    [ml, b.coerce(left, b.subst(ml, u, star)), u.v],
    [u.c],
  );
  const rc = op(
    "UnitElim",
    [mr, b.coerce(right, b.subst(mr, v, star)), v.v],
    [v.c],
  );
  return norm(op("SumElim", [mz, lc, rc, value], [z.c, u.c, v.c]));
}
const n = b.fresh(Nat),
  ih = b.fresh(W);
const g = b.named(
  b.emit(
    "PiIntro",
    [Nat, op("NatElim", [W, wz, app(ws, ih.v), n.v], [null, null, ih.c])],
    [n.c],
  ),
  "nat_to_wnat",
);
const motive = (a) =>
  b.arrow(b.arrow(B(a), W), b.arrow(b.arrow(B(a), Nat), Nat));
const left = b.lam(b.arrow(Void, W), () =>
  b.lam(b.arrow(Void, Nat), () => zero),
);
const right = b.lam(b.arrow(Unit, W), () =>
  b.lam(b.arrow(Unit, Nat), (h) => op("NatIntroS", [app(h, star)])),
);
const a = b.fresh(Two),
  children = b.fresh(b.arrow(B(a.v), W));
const branch = app(twoElim(motive, left, right, a.v), children.v);
const w = b.fresh(W);
const f = b.named(
  op(
    "PiIntro",
    [W, op("WElim", [Nat, branch, w.v], [null, a.c, children.c])],
    [w.c],
  ),
  "wnat_to_nat",
);
console.log("Maps constructed", b.k.steps.length, b.k.stats());
for (
  let i = 0, numeral = zero;
  i < 4;
  i++, numeral = op("NatIntroS", [numeral])
) {
  const roundtrip = app(f, app(g, numeral));
  if (b.view(roundtrip, 0) !== b.view(numeral, 0))
    throw new Error("Numeral round trip failed " + i);
}
console.log("Numeral round trips checked");

const U0omega = op("UCumulOmega", [U0]);
const succ = b.lam(Nat, (n) => op("NatIntroS", [n]));
const eq = (A, x, y) => b.eq(A, x, y),
  refl = (x) => b.refl(x);
const ap = (A, C, h, x, y, p) => app("lib_ap", U0omega, A, C, h, x, y, p);
function natInd(motive, base, step, value) {
  const z = b.fresh(Nat),
    n = b.fresh(Nat),
    C = motive(z.v);
  const ih = b.fresh(b.subst(C, z, n.v));
  const branch = b.coerce(
    step(n.v, ih.v),
    b.subst(C, z, op("NatIntroS", [n.v])),
  );
  const baseExact = b.coerce(base, b.subst(C, z, zero));
  return norm(op("NatElim", [C, baseExact, branch, value], [z.c, n.c, ih.c]));
}
const epsilonMotive = (n) => eq(Nat, app(f, app(g, n)), n);
const epsilon = b.named(
  b.lam(Nat, (n) =>
    natInd(
      epsilonMotive,
      refl(zero),
      (k, ih) => ap(Nat, Nat, succ, app(f, app(g, k)), k, ih),
      n,
    ),
  ),
  "nat_roundtrip",
);
console.log("Nat round trip proved", b.k.steps.length);
const arityLabel = b.fresh(Two),
  arityBody = B(arityLabel.v);
function sup(a, t) {
  const childrenType = b.arrow(b.subst(arityBody, arityLabel, a), W);
  return norm(
    op("WIntro", [a, arityBody, b.coerce(t, childrenType)], [arityLabel.c]),
  );
}
const funext = (A, C, left, right, h) =>
  app(
    "lib_funext",
    U0omega,
    A,
    b.lam(A, () => C),
    left,
    right,
    h,
  );
const etaMotive = (w) => eq(W, app(g, app(f, w)), w);
const childIH = (A, t) => b.pi(A, (x) => etaMotive(app(t, x)));
function etaCase(A, label, isZero) {
  return b.lam(b.arrow(A, W), (t) =>
    b.lam(childIH(A, t), (ih) => {
      const rebuilt = isZero
        ? b.lam(Void, (v) => op("VoidElim", [W, v], [null]))
        : b.lam(Unit, () => app(g, app(f, app(t, star))));
      let homotopy;
      if (isZero) {
        homotopy = b.lam(Void, (v) =>
          op("VoidElim", [eq(W, app(rebuilt, v), app(t, v)), v], [null]),
        );
      } else {
        const u = b.fresh(Unit),
          C = eq(W, app(g, app(f, app(t, star))), app(t, u.v));
        const base = b.coerce(app(ih, star), b.subst(C, u, star));
        homotopy = b.lam(Unit, (v) => op("UnitElim", [C, base, v], [u.c]));
      }
      const childrenEq = funext(A, W, rebuilt, t, homotopy);
      const constructor = b.lam(b.arrow(A, W), (child) => sup(label, child));
      return ap(b.arrow(A, W), W, constructor, rebuilt, t, childrenEq);
    }),
  );
}
for (const [label, A, term] of [
  ["nat", Nat, (n) => op("PiElim", [g, op("NatIntroS", [n])])],
  ["w", b.arrow(Unit, W), (t) => op("PiElim", [f, sup(label1, t)])],
  [
    "composed",
    b.arrow(Unit, W),
    (t) => op("PiElim", [g, op("PiElim", [f, sup(label1, t)])]),
  ],
]) {
  const x = b.fresh(A),
    raw = term(x.v);
  const before = norm(op("PiIntro", [A, raw], [x.c]));
  const after = op("PiIntro", [A, norm(raw)], [x.c]);
  if (b.view(before, 0) !== b.view(after, 0))
    throw new Error(`Reduction does not commute with abstraction: ${label}`);
}
const etaLeft = etaCase(Void, label0, true),
  etaRight = etaCase(Unit, label1, false);
const etaBranchType = (a) =>
  b.pi(b.arrow(B(a), W), (t) =>
    b.arrow(childIH(B(a), t), etaMotive(sup(a, t))),
  );
const etaLabel = b.fresh(Two),
  etaChildren = b.fresh(b.arrow(B(etaLabel.v), W));
const etaZ = b.fresh(W),
  etaC = etaMotive(etaZ.v);
const etaBranchExpected = b.arrow(
  b.pi(B(etaLabel.v), (x) => b.subst(etaC, etaZ, app(etaChildren.v, x))),
  b.subst(etaC, etaZ, sup(etaLabel.v, etaChildren.v)),
);
const etaBranch = b.coerce(
  app(twoElim(etaBranchType, etaLeft, etaRight, etaLabel.v), etaChildren.v),
  etaBranchExpected,
);
const eta = b.named(
  b.lam(W, (w) => {
    return norm(
      op("WElim", [etaC, etaBranch, w], [etaZ.c, etaLabel.c, etaChildren.c]),
    );
  }),
  "wnat_roundtrip",
);
console.log("WNat round trip proved", b.k.steps.length, b.k.stats());

// Keep the proved round trips opaque during path algebra: their checked
// definitions remain in the replay, but normalization need not duplicate them.
const rawAp = norm("lib_ap"),
  rawIsEquiv = norm("lib_isEquiv");
const etaOpaque = op("DefEqExtL", [op("Def", [eta])]);
const epsilonOpaque = op("DefEqExtL", [op("Def", [epsilon])]);
b.opaque = true;
// Resolve the polymorphic ap definition once; all subsequent conversion is beta.
b.normal.set(`beta:${b.k.bindings.get("lib_ap").id}`, rawAp);
const P = paths(b, U0omega);
const k = b.lam(W, (x) => app(g, app(f, x))),
  l = b.lam(Nat, (y) => app(f, app(g, y)));
const epsilonAdjusted = b.named(
  b.lam(Nat, (y) => {
    const gy = app(g, y),
      fgy = app(f, gy),
      fgfgy = app(l, fgy);
    const s = app(epsilonOpaque, fgy),
      q = P.ap(W, Nat, f, app(k, gy), gy, app(etaOpaque, gy)),
      r = app(epsilonOpaque, y);
    return P.cat(
      Nat,
      fgy,
      fgfgy,
      y,
      P.inv(Nat, fgfgy, fgy, s),
      P.cat(Nat, fgfgy, fgy, y, q, r),
    );
  }),
  "nat_roundtrip_coherent",
);
console.log("Adjusted epsilon constructed", b.k.steps.length);
// Adjointification (HoTT Book, Theorem 4.2.3):
// eps'(y) = inverse(eps(f(g(y)))) · (ap(f, eta(g(y))) · eps(y)).
// Naturality and cancellation prove ap(f, eta(x)) = eps'(f(x)).
// https://github.com/HoTT/book/blob/master/equivalences.tex
const coherence = b.named(
  b.lam(W, (x) => {
    const kx = app(k, x),
      kkx = app(k, kx),
      fx = app(f, x),
      fkx = app(f, kx),
      fkkx = app(f, kkx);
    const hx = app(etaOpaque, x),
      hkx = app(etaOpaque, kx);
    const p = P.ap(W, Nat, f, kx, x, hx),
      q = P.ap(W, Nat, f, kkx, kx, hkx);
    const r = app(epsilonOpaque, fx),
      s = app(epsilonOpaque, fkx);
    const apk = P.ap(W, W, k, kx, x, hx);
    const commuting = P.commute(W, k, etaOpaque, x); // ap k eta(x) = eta(k x)
    const pathW = eq(W, kkx, kx),
      pathN = eq(Nat, fkkx, fkx);
    const mapF = b.lam(pathW, (h) => P.ap(W, Nat, f, kkx, kx, h));
    const a = P.ap(pathW, pathN, mapF, apk, hkx, commuting);
    const fapk = P.ap(W, Nat, f, kkx, kx, apk);
    const c1 = P.apCompose(W, W, Nat, k, f, kx, x, hx);
    const lfP = P.ap(Nat, Nat, l, fkx, fx, p);
    const c2 = P.apCompose(W, Nat, Nat, f, l, kx, x, hx);
    const common = P.ap(
      W,
      Nat,
      b.lam(W, (z) => app(f, app(k, z))),
      kx,
      x,
      hx,
    );
    const qToCommon = P.cat(
      pathN,
      q,
      fapk,
      common,
      P.inv(pathN, fapk, q, a),
      c1,
    );
    const qToLf = P.cat(
      pathN,
      q,
      common,
      lfP,
      qToCommon,
      P.inv(pathN, lfP, common, c2),
    );
    const outer = eq(Nat, fkkx, fx),
      qr = P.cat(Nat, fkkx, fkx, fx, q, r),
      lpr = P.cat(Nat, fkkx, fkx, fx, lfP, r),
      sp = P.cat(Nat, fkkx, fkx, fx, s, p);
    const postR = b.lam(pathN, (h) => P.cat(Nat, fkkx, fkx, fx, h, r));
    const qrToLpr = P.ap(pathN, outer, postR, q, lfP, qToLf);
    const natural = P.natural(Nat, l, epsilonOpaque, fkx, fx, p);
    const qrToSp = P.cat(outer, qr, lpr, sp, qrToLpr, natural);
    const invS = P.inv(Nat, fkkx, fkx, s),
      finalType = eq(Nat, fkx, fx);
    const prefix = b.lam(outer, (h) => P.cat(Nat, fkx, fkkx, fx, invS, h));
    const adjusted = P.cat(Nat, fkx, fkkx, fx, invS, qr),
      cancelTerm = P.cat(Nat, fkx, fkkx, fx, invS, sp);
    const prefixed = P.ap(outer, finalType, prefix, qr, sp, qrToSp);
    const canceled = P.cancelLeft(Nat, fkkx, fkx, fx, s, p);
    const adjustedToP = P.cat(
      finalType,
      adjusted,
      cancelTerm,
      p,
      prefixed,
      canceled,
    );
    return P.inv(finalType, adjusted, p, adjustedToP);
  }),
  "wnat_nat_coherence",
);
console.log("Coherence proved", b.k.steps.length, b.k.stats());

function sigma(A, body) {
  const x = b.fresh(A);
  return op("SigmaForm", [A, body(x.v)], [x.c]);
}
function pair(A, body, value, tail) {
  const x = b.fresh(A),
    C = body(x.v),
    v = b.coerce(value, A);
  return op("SigmaIntro", [v, C, b.coerce(tail, b.subst(C, x, v))], [x.c]);
}
const etaType = (gg) => b.pi(W, (x) => eq(W, app(gg, app(f, x)), x));
const epsType = (gg) => b.pi(Nat, (y) => eq(Nat, app(f, app(gg, y)), y));
const tauType = (gg, ee, eps) =>
  b.pi(W, (x) => {
    const gfx = app(gg, app(f, x)),
      fgfx = app(f, gfx),
      fx = app(f, x);
    return eq(
      eq(Nat, fgfx, fx),
      P.ap(W, Nat, f, gfx, x, app(ee, x)),
      app(eps, fx),
    );
  });
const epsPair = pair(
  epsType(g),
  (eps) => tauType(g, etaOpaque, eps),
  epsilonAdjusted,
  coherence,
);
const etaPair = pair(
  etaType(g),
  (ee) => sigma(epsType(g), (eps) => tauType(g, ee, eps)),
  etaOpaque,
  epsPair,
);
const fullPair = pair(
  b.arrow(Nat, W),
  (gg) =>
    sigma(etaType(gg), (ee) =>
      sigma(epsType(gg), (eps) => tauType(gg, ee, eps)),
    ),
  g,
  etaPair,
);
const proposition = b.named(
  app(rawIsEquiv, U0omega, W, Nat, f),
  "WNatToNat_isEquiv",
);
const proof = b.named(b.coerce(fullPair, proposition), "wnat_to_nat_isEquiv");
if (!b.k.verify(proposition, proof))
  throw new Error("Final isEquiv verification failed");
console.log("VERIFIED isEquiv(WNat -> Nat)", b.k.steps.length, b.k.stats());
console.log(
  "Sizes",
  b.k.node(b.view(proof, 0)).size,
  b.k.node(b.view(proposition, 0)).size,
);

// Remove unused construction attempts and identical checked judgements. This is
// an untrusted size optimization: a fresh engine replays the emitted program.
const exports = [
  f,
  g,
  eta,
  epsilon,
  epsilonAdjusted,
  coherence,
  "lib_UNat",
  proposition,
  proof,
];
const roots = new Set(exports),
  canonical = new Map(),
  first = new Map(),
  candidates = [];
for (const step of b.k.steps) {
  const binding = b.k.bindings.get(step.name),
    key = binding.kind + ":" + binding.id;
  if (first.has(key) && !roots.has(step.name)) {
    canonical.set(step.name, first.get(key));
    continue;
  }
  canonical.set(step.name, step.name);
  if (!first.has(key)) first.set(key, step.name);
  const resolve = (x) => (x === null ? null : canonical.get(x));
  candidates.push({
    ...step,
    args: step.args.map(resolve),
    context: resolve(step.context),
    free: step.free.map(resolve),
    hidden: !roots.has(step.name),
  });
}
const byName = new Map(candidates.map((s) => [s.name, s])),
  needed = new Set();
function visit(name) {
  if (!name || needed.has(name)) return;
  needed.add(name);
  const s = byName.get(name);
  if (!s) throw new Error("Missing replay dependency " + name);
  for (const ref of [...s.args, s.context, ...s.free]) visit(ref);
}
for (const name of roots) visit(name);
const steps = candidates.filter((s) => needed.has(s.name));
const document = {
  format: "thth-workbench",
  version: 1,
  policy: { allowAxioms: true },
  steps,
};
const replay = new Session(module, true);
replay.import(document);
if (!replay.verify(proposition, proof))
  throw new Error("Saved proof did not verify");
const axioms = steps.filter((s) => s.op === "Axiom").map((s) => s.name);
console.log("Replay verified", steps.length, "instructions; axioms:", axioms);
if (
  axioms.length !== 1 ||
  b.k.bindings.get(axioms[0]).id !== b.k.bindings.get("lib_funext").id
)
  throw new Error("Expected only the existing function-extensionality axiom");
await writeFile(
  new URL("../../web/proofs/wnat_equiv.thth.json", import.meta.url),
  JSON.stringify(document, null, 2) + "\n",
);
await writeFile(
  new URL("../../web/proofs/wnat_equiv.math", import.meta.url),
  "# WNat to Nat: a half-adjoint equivalence. Requires function extensionality only.\n" +
    steps.map(formatStep).join("\n") +
    "\n",
);
const entry = {
  id: "wnat_equiv",
  title: "WNat ≃ Nat (isEquiv)",
  file: "wnat_equiv.thth.json",
  source: "tools/proofs/wnat_equiv.mjs",
  steps: steps.length,
  allowAxioms: true,
  exports,
  verify: [proposition, proof],
  axioms: ["function extensionality"],
};
await writeFile(
  new URL("../../web/proofs/wnat_equiv_entry.json", import.meta.url),
  JSON.stringify(entry, null, 2) + "\n",
);
await writeFile(
  new URL("../../web/proofs/catalogue.mjs", import.meta.url),
  "// Generated by tools/export_workbench.py and tools/proofs/wnat_equiv.mjs.\nexport default " +
    JSON.stringify(
      [...catalogue.filter((p) => p.id !== entry.id), entry],
      null,
      2,
    ) +
    ";\n",
);
replay.dispose();
b.k.dispose();
