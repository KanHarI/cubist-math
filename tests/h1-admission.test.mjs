// Declared types (H1), families F1, F2, F3, F5 and F6, through the WASM bridge:
// the extension gate, admission one constructor at a time, the generated
// squash, instances, their constructors and boundaries, eliminators, and
// refusals reported as kernel errors. The C tests in
// kernel/tests/test_signatures.c cover the acceptance cases in full.
import test from "node:test";
import assert from "node:assert/strict";
import createCubical from "../web/dist/cubical.mjs";
import { CubicalKernel, CUBICAL_ABI_VERSION } from "../web/cubical-kernel.mjs";
import { CubicalSyntax } from "../web/cubical-syntax.mjs";
import { InstructionGraph } from "../web/cubical-instructions.mjs";

const module = await createCubical();
function session(t) {
  const kernel = new CubicalKernel(module);
  t.after(() => kernel.dispose());
  return { kernel, syntax: new CubicalSyntax(kernel), g: new InstructionGraph(kernel) };
}

test("the ABI version is 3, with the declared-type kinds", () => {
  assert.equal(CUBICAL_ABI_VERSION, 3);
  assert.equal(module._cb_abi_version(), 3);
});

test("SignatureBegin is refused until the H1 extension is enabled", t => {
  const { kernel, syntax, g } = session(t);
  const u0 = g.universe(syntax.encodeLevel(0));
  assert.throws(() => g.signatureBegin(u0, 0, "N"), /kernel extension under review/);
  kernel.setExtensions({ h1: true });
  assert.ok(g.signatureBegin(u0, 0, "N") > 0);
});

test("natural numbers and the circle are admitted one constructor at a time", t => {
  const { kernel, syntax, g } = session(t);
  kernel.setExtensions({ h1: true });
  const u0 = g.universe(syntax.encodeLevel(0));
  // inductive N { zero; succ(n : N); }
  let sig = g.signatureBegin(u0, 0, "N");
  assert.equal(g.judgement(sig).kind, "signature");
  const s = g.extend(u0, "N");
  sig = g.signatureConstructor(sig, g.variable(s), "zero");
  g.extend(g.variable(s), "zero");
  const n = g.extend(g.variable(s), "n");
  sig = g.signatureConstructor(sig, g.pi(n, g.variable(s)), "succ");
  const nat = kernel.signature(g.signatureClose(sig));
  assert.equal(nat.admitted, true);
  assert.equal(nat.experimental, true);
  assert.deepEqual(nat.constructors.map(c => [c.data, c.positions, c.dimensions]), [[0, 0, 0], [0, 1, 0]]);
  assert.throws(() => g.signatureClose(sig), /already admitted/);
  // inductive Circle { base; loop : base = base; }
  let circle = g.signatureBegin(u0, 0, "Circle");
  const c = g.extend(u0, "Circle");
  circle = g.signatureConstructor(circle, g.variable(c), "base");
  const base = g.extend(g.variable(c), "base");
  const loopType = g.path(g.dimension(0), g.variable(c), g.variable(base), g.variable(base));
  circle = g.signatureConstructor(circle, loopType, "loop");
  const s1 = kernel.signature(g.signatureClose(circle));
  assert.equal(s1.constructors[1].dimensions, 1);
});

test("a truncation gets the generated squash, and an erased parameter stays out of constructor types", t => {
  const { kernel, syntax, g } = session(t);
  kernel.setExtensions({ h1: true });
  // Trunc(U < UU0, A : U) : prop { point(a : A); }
  const x = g.level("x"), ux = g.universe(syntax.encodeLevel({ tag: "Var", name: "x" }));
  const a = g.extend(ux, "A");
  const former = g.levelPi(x, g.pi(a, ux));
  let trunc = g.signatureBegin(former, 1, "Trunc");
  const s = g.extend(ux, "Trunc");
  const point = g.extend(g.variable(a), "a");
  trunc = g.signatureConstructor(trunc, g.pi(point, g.variable(s)), "point");
  const info = kernel.signature(g.signatureClose(trunc));
  assert.equal(info.recorded, 0);
  assert.equal(info.levels, 1);
  assert.equal(info.parameters, 1);
  const squash = info.constructors[1];
  assert.deepEqual([squash.generated, squash.positions, squash.dimensions], [true, 2, 1]);
  // Holder(U < UU0, A : U) : next(U) { hold(B : U); }, with U proposed erased.
  const next = g.universe(syntax.encodeLevel({ tag: "LSucc", count: 1, level: { tag: "Var", name: "x" } }));
  const holder = g.signatureBegin(g.levelPi(x, g.pi(a, next)), 0, "Holder");
  const h = g.extend(next, "Holder"), b = g.extend(ux, "B");
  assert.throws(() => g.signatureConstructor(holder, g.pi(b, g.variable(h)), "hold"), /erased universe parameter/);
});

test("instances of admitted signatures give their constructors", t => {
  const { kernel, syntax, g } = session(t);
  kernel.setExtensions({ h1: true });
  const u0 = g.universe(syntax.encodeLevel(0));
  // inductive N { zero; succ(n : N); }: with no parameters, SortBegin completes it.
  let sig = g.signatureBegin(u0, 0, "N");
  const s = g.extend(u0, "N");
  sig = g.signatureConstructor(sig, g.variable(s), "zero");
  sig = g.signatureConstructor(sig, g.pi(g.extend(g.variable(s), "n"), g.variable(s)), "succ");
  const n = g.sortBegin(g.signatureClose(sig));
  assert.equal(g.judgement(n).kind, "typing");
  const one = g.apply(g.construct(n, 1), g.construct(n, 0));
  assert.equal(g.judgement(one).type, g.judgement(n).term);
  assert.throws(() => g.construct(n, 2), /no such constructor/);
  // Trunc(U < UU0, A : U) : prop { point(a : A); } at Nat: in progress, then complete.
  const x = g.level("x"), ux = g.universe(syntax.encodeLevel({ tag: "Var", name: "x" }));
  const a = g.extend(ux, "A");
  let trunc = g.signatureBegin(g.levelPi(x, g.pi(a, ux)), 1, "Trunc");
  const ts = g.extend(ux, "Trunc");
  trunc = g.signatureConstructor(trunc, g.pi(g.extend(g.variable(a), "a"), g.variable(ts)), "point");
  const started = g.sortBegin(g.signatureClose(trunc));
  assert.equal(g.judgement(started).kind, "instance");
  assert.throws(() => g.construct(started, 0), /Expected a typing judgement/);
  assert.throws(() => g.step(started, "term", [], "whnf"), /not rewritten/);
  const truncNat = g.sortParameter(started, g.nat());
  assert.equal(g.judgement(truncNat).type, g.judgement(u0).term);
  assert.equal(g.judgement(g.apply(g.construct(truncNat, 0), g.zero())).type, g.judgement(truncNat).term);
  // Pointed(U < UU0) : next(U) { pt(X : U, x : X); }: its level is recorded.
  const y = g.level("y"), uy = g.universe(syntax.encodeLevel({ tag: "Var", name: "y" }));
  const next = g.universe(syntax.encodeLevel({ tag: "LSucc", count: 1, level: { tag: "Var", name: "y" } }));
  let pointed = g.signatureBegin(g.levelPi(y, next), 0, "Pointed", 1);
  const ps = g.extend(next, "Pointed"), carrier = g.extend(uy, "X");
  pointed = g.signatureConstructor(pointed, g.pi(carrier, g.pi(g.extend(g.variable(carrier), "element"), g.variable(ps))), "pt");
  const p0 = g.sortLevel(g.sortBegin(g.signatureClose(pointed)), syntax.encodeLevel(0));
  assert.equal(g.judgement(p0).type, g.judgement(g.universe(syntax.encodeLevel(1))).term);
  assert.equal(g.judgement(g.construct(p0, 0)).rule, "construct");
});

test("a constructor at an endpoint steps to its boundary", t => {
  const { kernel, syntax, g } = session(t);
  kernel.setExtensions({ h1: true });
  const u0 = g.universe(syntax.encodeLevel(0));
  // inductive Circle { base; loop : base = base; }
  let sig = g.signatureBegin(u0, 0, "Circle");
  const c = g.extend(u0, "Circle");
  sig = g.signatureConstructor(sig, g.variable(c), "base");
  const base = g.extend(g.variable(c), "base");
  sig = g.signatureConstructor(sig, g.path(g.dimension(0), g.variable(c), g.variable(base), g.variable(base)), "loop");
  const circle = g.sortBegin(g.signatureClose(sig));
  const point = g.judgement(g.construct(circle, 0)).term;
  for (const endpoint of [0, 1])
    for (const rule of ["path", "whnf", "normalize"]) {
      const stepped = g.step(g.refl(g.pathApply(g.construct(circle, 1), 0, endpoint)), "other", [], rule);
      assert.equal(g.judgement(stepped).other, point);
    }
});

test("an eliminator takes a clause per constructor and computes by Iota", t => {
  const { kernel, syntax, g } = session(t);
  kernel.setExtensions({ h1: true });
  const u0 = g.universe(syntax.encodeLevel(0));
  let sig = g.signatureBegin(u0, 0, "N");
  const s = g.extend(u0, "N");
  sig = g.signatureConstructor(sig, g.variable(s), "zero");
  sig = g.signatureConstructor(sig, g.pi(g.extend(g.variable(s), "n"), g.variable(s)), "succ");
  const n = g.sortBegin(g.signatureClose(sig));
  const zero = g.construct(n, 0), succ = g.construct(n, 1);
  // A motive P : N -> U0, and clauses pz : P(zero), ps : Π (m : N). P(m) -> P(succ(m)).
  const P = g.extend(g.pi(g.extend(n, "z"), u0), "P");
  const at = t => g.apply(g.variable(P), t);
  let elim = g.eliminator(g.variable(P));
  assert.equal(g.judgement(elim).kind, "eliminator");
  assert.equal(g.judgement(elim).type, g.judgement(at(zero)).term);
  assert.throws(() => g.eliminatorClose(elim), /lacks a clause/);
  const pz = g.extend(at(zero), "pz");
  elim = g.eliminatorClause(elim, g.variable(pz));
  const m = g.extend(n, "m"), h = g.extend(at(g.variable(m)), "h");
  const ps = g.extend(g.pi(m, g.pi(h, at(g.apply(succ, g.variable(m))))), "ps");
  const closed = g.eliminatorClose(g.eliminatorClause(elim, g.variable(ps)));
  assert.equal(g.judgement(closed).kind, "typing");
  const stepped = g.step(g.refl(g.apply(closed, zero)), "other", [], "iota");
  assert.equal(g.judgement(stepped).other, g.judgement(g.variable(pz)).term);
});
