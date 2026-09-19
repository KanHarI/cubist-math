import test from "node:test";
import assert from "node:assert/strict";
import createKernel from "../web/dist/kernel.mjs";
import { compile } from "../web/mathscript/compiler.mjs";
import { loadProof } from "../tools/test-selection.mjs";
import { checkedFoldedView, exportInspection } from "../web/mathscript/kernel-folding.mjs";
import { kernelMathTree } from "../web/math-notation.mjs";
import { Kernel } from "../web/kernel.mjs";
import { Session } from "../web/session.mjs";
import { layout, pathFromMarked } from "../web/expressions.mjs";

const module = await createKernel();
test("checked inspector metadata preserves definition bodies, named theorem types, and imported syntax", async () => {
  const { source, sources } = await loadProof(new URL("../web/proofs/euclid.proof", import.meta.url).pathname);
  const c = compile(module, source, sources);
  try {
    const concept = c.outputs.find(o => o.name === "InfinitelyManyPrimes");
    assert.equal(concept.mathscript.expression, "forall n : Nat, exists p : Nat, Prime(p) and n < p");
    assert.equal(concept.mathscript.type, "Type");
    const theorem = c.outputs.find(o => o.name === "euclid");
    assert.equal(theorem.mathscript.expression, "euclid");
    assert.equal(theorem.mathscript.type, "InfinitelyManyPrimes");
    const prime = c.imports.find(o => o.name === "Prime");
    assert.match(prime.mathscript.expression, /^fun \(p : Nat\) => .*Divides/);
    for (const output of [concept, theorem, prime])
      assert.ok(c.kernel.verify(output.proposition, output.binding));
    const snapshot = structuredClone(concept.mathscript);
    assert.throws(() => compile(module, source.replace("exact (p, (hp, bigger));", "exact tt;"), sources), /Expected/);
    assert.deepEqual(concept.mathscript, snapshot);
  } finally { c.kernel.dispose(); }
});

test("source projection handles parameterized lambdas and typed definition blocks without guessing aliases", () => {
  const c = compile(module, `
    def identity(A : Type, x : A) = x;
    def lambda = fun (x : Nat) => x;
    def block : Nat { exact 0; }
    theorem reference : Nat { exact 0; }
  `);
  try {
    assert.equal(c.outputs[0].mathscript.expression, "fun (A : Type) => fun (x : A) => x");
    assert.equal(c.outputs[1].mathscript.expression, "fun (x : Nat) => x");
    assert.equal(c.outputs[2].mathscript.expression, "def block : Nat { exact 0; }");
    assert.equal(c.outputs[2].mathscript.expressionKind, "declaration");
    assert.equal(c.outputs[3].mathscript.expression, "reference");
  } finally { c.kernel.dispose(); }
});

test("folded inspector terms have replayable kernel equality certificates and named definition references", async () => {
  const { source, sources } = await loadProof(new URL("../web/proofs/euclid.proof", import.meta.url).pathname);
  const c = compile(module, source, sources);
  try {
    const originalCount = c.kernel.steps.length, originalStats = c.kernel.stats();
    const f = checkedFoldedView(c, "InfinitelyManyPrimes", { certificate: true });
    assert.deepEqual(f.failures, {});
    assert.equal(f.expression.kind, "Pi");
    assert.equal(f.expression.children[1].kind, "Sigma");
    assert.equal(f.expression.children[1].children[1].kind, "Sigma");
    const expression = kernelMathTree(f.expression, f.references);
    assert.equal(expression.name, "n");
    assert.equal(expression.body.name, "p");
    assert.equal(expression.body.body.kind, "Product");
    assert.equal(expression.body.body.left.fn.name, "Prime");
    assert.equal(expression.body.body.left.fn.binding, "Prime");
    assert.deepEqual(expression.body.body.left.args.map(a => a.name), ["p"]);
    assert.equal(expression.body.body.right.fn.name, "isLt");
    assert.deepEqual(expression.body.body.right.args.map(a => a.name), ["n", "p"]);
    assert.ok(f.expression.size < 20, "the displayed kernel term stays folded");

    const replay = new Kernel(module, f.certificate.policy.allowAxioms);
    try {
      for (const step of f.certificate.steps) replay.apply(step);
      const expr = name => module._wb_view(replay.handle, 0, replay.bindings.get(name).id, 0);
      for (const evidence of Object.values(f.verified)) {
        const equality = replay.node(expr(evidence.witness));
        assert.equal(equality.kind, "DefEq");
        assert.deepEqual(equality.children, [expr(evidence.candidate), expr(evidence.original)]);
        assert.deepEqual(replay.axiomsFor(evidence.witness), []);
      }
      for (const [id, reference] of Object.entries(f.references)) {
        const node = replay.node(Number(id));
        assert.equal(node.kind, "DRef");
        assert.equal(module._wb_view(replay.handle, 0, node.parameter, 0), expr(reference.binding));
      }
    } finally { replay.dispose(); }
    assert.equal(c.kernel.steps.length, originalCount);
    assert.deepEqual(c.kernel.stats(), originalStats);
    // Raw rendering must account for the hidden eliminator binders too.
    const raw = layout(c.kernel.inspect("euclid", { expand: ["type"] }).type);
    assert.doesNotMatch(raw.text, /#\d/);
    assert.match(raw.text, /nat\.elim \[x\d+, x\d+\]/);
    const variable = raw.spans.find(s => s.node.kind === "VRef");
    const marked = raw.text.slice(0, variable.start) + "[[" + raw.text.slice(variable.start, variable.end) + "]]" + raw.text.slice(variable.end);
    assert.deepEqual(pathFromMarked(c.kernel.inspect("euclid", { expand: ["type"] }).type, marked), variable.path);

    const exported = exportInspection(c, "euclid", "expression");
    const workbench = new Session(module, false);
    try {
      workbench.import(exported.document, true);
      const view = workbench.inspect(exported.selection.name);
      assert.equal(view.type.kind, "DRef");
      assert.equal(view.declarations[view.type.id], "InfinitelyManyPrimes");
    } finally { workbench.dispose(); }
  } finally { c.kernel.dispose(); }
});

test("the kernel rejects incorrect folding proposals instead of displaying source-shaped claims", async () => {
  const { source, sources } = await loadProof(new URL("../web/proofs/euclid.proof", import.meta.url).pathname);
  const c = compile(module, source, sources);
  try {
    const output = c.outputs.find(o => o.name === "InfinitelyManyPrimes");
    output.mathscript.foldingPlan.expression.body.kind = "Pi";
    const rejected = checkedFoldedView(c, output.binding);
    assert.equal(rejected.expression, null);
    assert.match(rejected.failures.expression, /not definitionally equal/);
    assert.ok(!rejected.verified.expression);
    assert.ok(rejected.verified.type);
  } finally { c.kernel.dispose(); }
});

test("folded dependent domains follow the kernel binder convention and local names are not definition links", () => {
  const c = compile(module, "def family = forall A : Type, forall x : A, exists y : A, x = y;");
  try {
    const f = checkedFoldedView(c, "family");
    assert.deepEqual(f.failures, {});
    const display = kernelMathTree(f.expression, f.references);
    assert.equal(display.body.domain.name, "A");
    assert.equal(display.body.body.domain.name, "A");
    assert.equal(display.body.body.body.kind, "Identity");
    assert.equal(display.body.body.body.carrier.name, "A");
    assert.equal(display.body.body.body.left.name, "x");
    assert.equal(display.body.body.body.right.name, "y");
    assert.equal(display.body.body.body.left.local, true);
    assert.equal(display.body.body.body.left.binding, undefined);
  } finally { c.kernel.dispose(); }
});

test("expression and type exports replay in the workbench with their dependencies and axiom policy", () => {
  const c = compile(module, "axiom witness : Nat; def proposition = witness = witness;");
  try {
    for (const side of ["expression", "type"]) for (const folded of [false, true]) {
      const exported = exportInspection(c, "proposition", side, folded);
      const session = new Session(module, false);
      try {
        session.import(exported.document, true);
        const view = session.inspect(exported.selection.name);
        assert.equal(exported.selection.side, folded ? "expression" : side);
        assert.equal(view[exported.selection.side].kind, side === "type" ? "U" : "Eq");
        assert.equal(session.allowAxioms, true);
        if (side === "expression") assert.deepEqual(view.axioms, ["witness"]);
        if (folded) assert.ok(session.snapshot().bindings.some(o => o.name.endsWith("folding_equality") && !o.hidden));
      } finally { session.dispose(); }
    }
    assert.throws(() => exportInspection(c, "proposition", "bogus"), /Unknown inspection side/);
  } finally { c.kernel.dispose(); }
});

test("classical complex inverse has a certified folded dependent type including the nonzero equality carrier", async () => {
  const { source, sources } = await loadProof(new URL("../web/proofs/classical_complex_inverses.proof", import.meta.url).pathname);
  const c = compile(module, source, sources);
  try {
    const f = checkedFoldedView(c, "classical_complex_nonzero_inverse");
    assert.deepEqual(f.failures, {});
    assert.ok(f.verified.type);
    let type = kernelMathTree(f.type, f.references);
    const binders = new Map();
    while (type.kind === "Pi") { binders.set(type.name, type.domain); type = type.body; }
    assert.equal(binders.size, 13);
    assert.equal(binders.get("z").fn.binding, "Complex");
    const nonzero = binders.get("nonzero");
    assert.equal(nonzero.kind, "Arrow");
    assert.equal(nonzero.left.kind, "Identity");
    assert.equal(nonzero.left.carrier.fn.binding, "Complex");
    assert.equal(nonzero.left.left.name, "z");
    assert.equal(nonzero.left.right.fn.binding, "complex_zero");
    assert.equal(type.fn.binding, "ComplexUnit");
  } finally { c.kernel.dispose(); }
});

test("inferred induction types use substituted parameters and factorial has a certified folded eliminator", async () => {
  const { source, sources } = await loadProof(new URL("../web/proofs/euclid.proof", import.meta.url).pathname);
  const c = compile(module, source, sources);
  try {
    for (const name of ["nat_le_total", "prime_divisor_exists", "factorial"]) {
      const f = checkedFoldedView(c, name, { certificate: true });
      assert.deepEqual(f.failures, {}, name);
      const replay = new Kernel(module, f.certificate.policy.allowAxioms);
      try {
        for (const step of f.certificate.steps) replay.apply(step);
        const expr = binding => module._wb_view(replay.handle, 0, replay.bindings.get(binding).id, 0);
        for (const evidence of Object.values(f.verified)) {
          const witness = replay.node(expr(evidence.witness));
          assert.equal(witness.kind, "DefEq");
          assert.deepEqual(witness.children, [expr(evidence.candidate), expr(evidence.original)]);
        }
      } finally { replay.dispose(); }
      const type = kernelMathTree(f.type, f.references);
      assert.doesNotMatch(JSON.stringify(type), /"name":"(?:a2|k|#\d+)"/);
      if (name === "nat_le_total") {
        assert.equal(type.name, "a");
        assert.deepEqual(type.body.body.left.args.map(a => a.name), ["a", "c"]);
      } else if (name === "prime_divisor_exists") {
        assert.equal(type.body.right.body.right.fn.name, "Divides");
        assert.equal(type.body.right.body.right.args[1].name, "n");
      } else {
        const expression = kernelMathTree(f.expression, f.references);
        assert.equal(expression.name, "n");
        assert.equal(expression.body.kind, "NatElim");
        assert.deepEqual(expression.body.names, ["k", "h"]);
        assert.deepEqual(expression.body.args[0], { kind: "Number", value: 1 });
        assert.equal(expression.body.args[1].fn.binding, "mul");
        assert.equal(expression.body.args[1].args[0].args[0].name, "k");
        assert.equal(expression.body.args[1].args[1].name, "h");
        assert.equal(expression.body.args[2].name, "n");
        assert.ok(f.expression.size < 25);
      }
    }
    const plan = c.imports.find(o => o.name === "factorial").mathscript.foldingPlan.expression;
    plan.body.step.fn.binding = "add";
    const rejected = checkedFoldedView(c, "factorial");
    assert.equal(rejected.expression, null);
    assert.match(rejected.failures.expression, /not definitionally equal/);
  } finally { c.kernel.dispose(); }
});

test("local folding preserves checked assumptions and uses source labels for context references", async () => {
  const { source, sources } = await loadProof(new URL("../web/proofs/euclid.proof", import.meta.url).pathname);
  const c = compile(module, source, sources);
  const replay = new Kernel(module, false);
  try {
    const before = c.kernel.steps.length;
    const local = c.localViews.find(local => local.name === "bounded");
    const folded = checkedFoldedView(c, local.binding, { certificate: true });
    assert.deepEqual(folded.failures, {});
    assert.deepEqual(kernelMathTree(folded.expression, folded.references, folded.contextNames),
      { kind: "Name", name: "bounded", local: true });
    const type = kernelMathTree(folded.type, folded.references, folded.contextNames);
    assert.equal(type.fn.name, "le");
    assert.equal(type.args[0].args[0].args[0].name, "i");
    assert.equal(type.args[1].name, "n");
    for (const step of folded.certificate.steps) replay.apply(step);
    for (const side of ["expression", "type"]) {
      const evidence = folded.verified[side];
      const witness = replay.inspect(evidence.witness);
      const original = replay.inspect(evidence.original);
      if (side === "type") assert.equal(original.expression.id, replay.inspect(local.binding).type.id);
      assert.equal(witness.expression.kind, "DefEq");
      assert.deepEqual(witness.assumptions.map(a => a.id), original.assumptions.map(a => a.id));
      assert.deepEqual(evidence.assumptions, original.assumptions.map(a => a.id));
    }
    assert.equal(folded.verified.expression.assumptions.length, 3);
    assert.equal(folded.verified.type.assumptions.length, 2);
    assert.equal(c.kernel.steps.length, before);
    for (const side of ["expression", "type"]) {
      const exported = exportInspection(c, local.binding, side);
      const session = new Session(module, false);
      try {
        session.import(exported.document, true);
        const view = session.inspect(exported.selection.name);
        assert.equal(view.assumptions.length, side === "expression" ? 3 : 2);
        assert.equal(view.expression.kind, side === "expression" ? "CRef" : "Ap");
        assert.equal(session.allowAxioms, false);
      } finally { session.dispose(); }
    }
    const original = structuredClone(local.mathscript.foldingPlan.type);
    local.mathscript.foldingPlan.type.args.reverse();
    const wrong = checkedFoldedView(c, local.binding);
    assert.equal(wrong.type, null);
    assert.match(wrong.failures.type, /not definitionally equal/);
    local.mathscript.foldingPlan.type = original;

    // A beta-equivalent proposal must still not acquire an extra assumption.
    const n = c.localViews.find(local => local.name === "n");
    const i = c.localViews.find(local => local.name === "i");
    const typeTarget = local.proposition;
    local.proposition = n.proposition;
    const wrongTarget = checkedFoldedView(c, local.binding);
    assert.equal(wrongTarget.type, null);
    assert.match(wrongTarget.failures.type, /not the inspected judgement's stored type/);
    local.proposition = typeTarget;
    n.mathscript.foldingPlan.expression = { kind: "Call", fn: { kind: "Lambda", name: "extra",
      domain: { kind: "Name", name: "Nat" }, body: { kind: "Name", name: "n", binding: n.binding } },
      args: [{ kind: "Name", name: "i", binding: i.binding }] };
    const extra = checkedFoldedView(c, n.binding);
    assert.equal(extra.expression, null);
    assert.match(extra.failures.expression, /changes the original assumptions/);
  } finally { replay.dispose(); c.kernel.dispose(); }
});
