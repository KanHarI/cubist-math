import test from "node:test";
import assert from "node:assert/strict";
import createKernel from "../web/dist/kernel.mjs";
import { compile } from "../web/mathscript/compiler.mjs";
import { Builder } from "../web/mathscript/builder.mjs";
import { Kernel } from "../web/kernel.mjs";

const module = await createKernel();
const configurations = [
  { normalForms: false, instructions: false },
  { normalForms: true, instructions: false }, { normalForms: false, instructions: true },
  { normalForms: true, instructions: true },
];
const source = `
  opaque def Box = Nat;
  opaque def next(n : Nat) = succ(n);
  def boxed : Box { exact 2; }
  def twice(f : Nat -> Nat, n : Nat) = f(f(n));
  theorem converted : next(1) = 2 { exact refl(2); }
  theorem repeated : twice(succ, 0) = 2 { exact refl(2); }
  theorem duplicate(A : Type, x : A) = typed(A and A, (x, x));
`;

test("independent compiler optimizations reduce instructions and retain replayable checked proofs", () => {
  let baseline;
  for (const optimizations of configurations) {
    const c = compile(module, source, {}, { optimizations });
    const replay = new Kernel(module, c.allowAxioms);
    try {
      for (const step of c.kernel.steps) replay.apply(step);
      for (const output of c.outputs) {
        assert.ok(c.kernel.verify(output.proposition, output.binding));
        assert.ok(replay.verify(output.proposition, output.binding));
        assert.deepEqual(replay.axiomsFor(output.binding), []);
      }
      if (!baseline) baseline = c.instructionCount;
      else assert.ok(c.instructionCount < baseline, JSON.stringify(optimizations));
      assert.deepEqual(c.optimizations, {
        normalForms: optimizations.normalForms === true,
        instructions: optimizations.instructions === true,
        freshContexts: true,
      });
    } finally { replay.dispose(); c.kernel.dispose(); }
  }
});

test("cached instructions retain distinct binders, highlights, names, and axiom provenance", () => {
  const b = new Builder(module, { loadLibrary: false, allowAxioms: true,
    optimizations: { normalForms: true, instructions: true } });
  try {
    b.opaque = true;
    const unit = b.emit("UnitForm"), tt = b.emit("UnitIntro");
    const p = b.emit("Axiom", [unit]), q = b.emit("Axiom", [unit]);
    assert.notEqual(p, q);
    assert.notEqual(b.emit("Def", [tt]), b.emit("Def", [tt]));
    const x = b.fresh(unit), y = b.fresh(unit);
    assert.notEqual(x.c, y.c);
    assert.notEqual(x.v, y.v);
    assert.notEqual(b.named(tt, "first"), b.named(tt, "second"));
    assert.equal(b.emit("EqIntro", [p]), b.emit("EqIntro", [p]));
    assert.deepEqual(b.k.axiomsFor(b.emit("EqIntro", [p])), [p]);
    assert.deepEqual(b.k.axiomDependencies.get(b.emit("EqIntro", [q])), [q]);
    const axiomType = b.emit("UnHigh", [b.emit("HighType", [p])]);
    assert.deepEqual(b.k.axiomsFor(b.norm(axiomType)), [p]);
    assert.deepEqual(b.k.axiomsFor(b.norm(unit)), []);
    const eq = b.emit("DefEqRefl", [tt]);
    assert.notEqual(b.emit("HighExp", [eq]), b.emit("HighType", [eq]));
    const normal = b.norm(tt), count = b.k.steps.length;
    assert.equal(b.norm(normal), normal);
    assert.equal(b.k.steps.length, count);
  } finally { b.k.dispose(); }
});

test("all optimization combinations reject invalid dependent proofs and opaque conversions", () => {
  for (const optimizations of configurations) {
    assert.throws(() => compile(module,
      "theorem bad(A : Type, B : Type, x : A) : B { exact x; }", {}, { optimizations }), /Expected/);
    assert.throws(() => compile(module,
      "opaque def Box = Nat; theorem bad : Box { exact tt; }", {}, { optimizations }), /Expected/);
  }
});

test("optimization options reject unknown keys and non-Boolean values", () => {
  for (const optimizations of [null, [], { normalForms: "false" }, { unknown: true }])
    assert.throws(() => compile(module, source, {}, { optimizations }), /Boolean/);

});


test("mathematical compilation defaults to both optimizations with independent opt-outs", () => {
  for (const [options, expected] of [
    [undefined, { normalForms: true, instructions: true, freshContexts: true }],
    [{ optimizations: { normalForms: false } }, { normalForms: false, instructions: true, freshContexts: true }],
    [{ optimizations: { instructions: false } }, { normalForms: true, instructions: false, freshContexts: true }],
    [{ optimizations: { freshContexts: false } }, { normalForms: true, instructions: true, freshContexts: false }],
  ]) {
    const c = compile(module, source, {}, options);
    try { assert.deepEqual(c.optimizations, expected); }
    finally { c.kernel.dispose(); }
  }
});

test("construction instructions remain unchanged with default and explicit optimization settings", () => {
  let baseline;
  for (const options of [undefined, { optimizations: { normalForms: true, instructions: true } },
    { optimizations: { normalForms: false, instructions: false } }]) {
    const c = compile(module, "construction example { export unit = unit_value(); }", {}, options);
    try {
      assert.deepEqual(c.optimizations, { normalForms: false, instructions: false, freshContexts: false });
      if (baseline) assert.deepEqual(c.kernel.steps, baseline);
      else baseline = c.kernel.steps;
    } finally { c.kernel.dispose(); }
  }
});

test("fresh-context indexing preserves the entire checked instruction trace", () => {
  const baseline = compile(module, source, {}, { optimizations: { freshContexts: false } });
  const indexed = compile(module, source, {}, { optimizations: { freshContexts: true } });
  try { assert.deepEqual(indexed.kernel.steps, baseline.kernel.steps); }
  finally { baseline.kernel.dispose(); indexed.kernel.dispose(); }
});

test("fresh-context indexing tracks manual contexts, counter ties, and distinct dependent types", () => {
  const run = freshContexts => {
    const b = new Builder(module, { loadLibrary: false, optimizations: { freshContexts } });
    try {
      const unit = b.emit("UnitForm"), nat = b.emit("NatForm");
      const first = b.fresh(unit, "first");
      b.k.apply({ name: "same_counter", op: "CtxExt", args: [unit], free: [null] });
      const second = b.fresh(unit, "second");
      assert.equal(b.k.steps.find(s => s.name === second.c).free[0], first.c);
      b.k.apply({ name: "manual_successor", op: "CtxExt", args: [unit], free: [second.c] });
      b.k.apply({ name: "manual_reset", op: "CtxExt", args: [unit], free: [null] });
      const third = b.fresh(unit, "third");
      assert.equal(b.k.steps.find(s => s.name === third.c).free[0], "manual_successor");
      b.k.apply({ name: "manual_fresh", op: "CtxExt", args: [unit], free: [null], fresh: true });
      const fourth = b.fresh(unit, "fourth");
      assert.equal(b.k.steps.find(s => s.name === fourth.c).free[0], "manual_fresh");
      const n = b.fresh(nat, "n"), m = b.fresh(nat, "m");
      assert.equal(b.k.steps.find(s => s.name === n.c).free[0], null);
      const tn = b.eq(nat, n.v, n.v), tm = b.eq(nat, m.v, m.v);
      const pn = b.fresh(tn, "pn"), pm = b.fresh(tm, "pm"), qn = b.fresh(tn, "qn");
      assert.equal(b.k.steps.find(s => s.name === pm.c).free[0], null);
      assert.equal(b.k.steps.find(s => s.name === qn.c).free[0], pn.c);
      return b.k.steps;
    } finally { b.k.dispose(); }
  };
  assert.deepEqual(run(true), run(false));
});
