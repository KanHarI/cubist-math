import test from "node:test";
import assert from "node:assert/strict";
import createKernel from "../web/dist/kernel.mjs";
import { compile } from "../web/mathscript/compiler.mjs";
import { loadProof } from "../tools/test-selection.mjs";
import { checkedFoldedView } from "../web/mathscript/kernel-folding.mjs";
import { kernelMathTree } from "../web/math-notation.mjs";
import { Kernel } from "../web/kernel.mjs";

const module = await createKernel();
const loaded = await loadProof("web/proofs/f4_galois_group.proof");
const constructive = ["lib_funext", "lib_univalence"];

test("the Galois group inspector keeps a certified application instead of expanding proof bodies", () => {
  const c = compile(module, loaded.source, loaded.sources);
  try {
    const f = checkedFoldedView(c, "F4GaloisGroup", { certificate: true });
    assert.deepEqual(f.failures, {});
    assert.equal(f.expression.size, 5);
    const expression = kernelMathTree(f.expression, f.references);
    assert.equal(expression.fn.name, "GaloisGroup");
    assert.deepEqual(expression.args.map(a => a.name), ["F2", "F4OverF2"]);
    assert.equal(kernelMathTree(f.type, f.references).name, "Group");
    const replay = new Kernel(module, f.certificate.policy.allowAxioms);
    try {
      for (const step of f.certificate.steps) replay.apply(step);
      for (const side of ["expression", "type"]) {
        const evidence = f.verified[side];
        const expr = name => replay.module._wb_view(replay.handle, 0, replay.bindings.get(name).id, 0);
        const equality = replay.node(expr(evidence.witness));
        assert.equal(equality.kind, "DefEq");
        assert.deepEqual(equality.children, [expr(evidence.candidate), expr(evidence.original)]);
      }
    } finally { replay.dispose(); }
  } finally { c.kernel.dispose(); }
});

test("field automorphisms are loops, with transport, composition and the complete F4/F2 example", () => {
  const c = compile(module, loaded.source, loaded.sources);
  try {
    for (const name of [
      "field_structure_identity", "extension_structure_identity",
      "extension_iso_roundtrip", "extension_path_roundtrip",
      "galois_automorphisms_are_loops", "galois_loop_action",
      "galois_composition_is_concatenation", "galois_group_laws",
      "f2_laws", "f4_laws", "f4_frobenius_automorphism",
      "f4_loop_exchanges_roots", "f4_loop_nontrivial", "f4_loop_twice",
      "f4_galois_has_two_elements", "f4_galois_is_cyclic_two", "f4_galois_group_equality",
    ]) {
      assert.ok(c.kernel.verify(name + "_type", name), name);
      assert.ok(c.kernel.axiomsFor(name).every(a => constructive.includes(a)), name);
    }
    for (const name of ["f2_laws", "f4_laws", "f4_frobenius_automorphism"])
      assert.deepEqual(c.kernel.axiomsFor(name), [], name);
    for (const name of ["extension_structure_identity", "galois_automorphisms_are_loops", "f4_loop_nontrivial"])
      assert.deepEqual(c.kernel.axiomsFor(name).sort(), constructive, name);
    assert.ok(!c.kernel.bindings.has("AOC"));
    assert.ok(!c.kernel.bindings.has("LEM"));
    assert.match(c.outputs.find(o => o.name === "f4_galois_group_equality").type, /=\[Group\]/);
    for (const name of ["structured_sets", "algebraic_fields", "field_extensions", "galois_paths", "finite_fields", "f4_galois"])
      assert.doesNotMatch(loaded.sources[name], /\baxiom\s|\bpostulate\s*\(/);
    assert.doesNotMatch(loaded.source, /\baxiom\s|\bpostulate\s*\(/);
  } finally { c.kernel.dispose(); }
});

test("Unit computation preserves enclosing variables in the WASM kernel", () => {
  const c = compile(module, `
    def first(a : Nat, b : Nat) = unit_induction((fun (u : Unit) => Nat), a, tt);
    def second(a : Nat, b : Nat) = unit_induction((fun (u : Unit) => Nat), b, tt);
    theorem keeps_outer(a : Nat, b : Nat) : first(a, b) = a { exact refl(a); }
    theorem keeps_inner(a : Nat, b : Nat) : second(a, b) = b { exact refl(b); }
  `);
  try { assert.equal(c.axiomCount, 0); }
  finally { c.kernel.dispose(); }
  assert.throws(() => compile(module, `
    def first(a : Nat, b : Nat) = unit_induction((fun (u : Unit) => Nat), a, tt);
    theorem bad(a : Nat, b : Nat) : first(a, b) = b { exact refl(b); }
  `), /Expected|differ/);
});

test("the finite field laws reject a corrupted multiplication table", () => {
  const original = loaded.sources.finite_fields;
  const mutated = original.replace(
    "f4_0, f4_2, f4_3, f4_1, y)",
    "f4_0, f4_2, f4_2, f4_1, y)",
  );
  assert.notEqual(mutated, original);
  assert.throws(() => compile(module, loaded.source, { ...loaded.sources, finite_fields: mutated }), /Expected|differ/);
});

test("the root-exchanging loop cannot be replaced with the identity symmetry", () => {
  const original = loaded.sources.f4_galois;
  const mutated = original.replace("def f4_frobenius(x : F4Carrier) = f4_mul(x, x);", "def f4_frobenius(x : F4Carrier) = x;");
  assert.notEqual(mutated, original);
  assert.throws(() => compile(module, loaded.source, { ...loaded.sources, f4_galois: mutated }), /Expected|differ/);
});

test("an extension's inclusion must be a field embedding", () => {
  const original = loaded.sources.f4_galois;
  const mutated = original.replace("=> F4Carrier), f4_0, f4_1, x);", "=> F4Carrier), f4_0, f4_0, x);");
  assert.notEqual(mutated, original);
  assert.throws(() => compile(module, loaded.source, { ...loaded.sources, f4_galois: mutated }), /Expected|differ/);
});
