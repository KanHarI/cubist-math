// Declared types (H1), families F1 and F6, through the WASM bridge: the
// extension gate, admission one constructor at a time, the generated squash,
// and refusals reported as kernel errors. The C tests in
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
