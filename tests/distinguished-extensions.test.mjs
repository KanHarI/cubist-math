import test, { after } from "node:test";
import assert from "node:assert/strict";
import createKernel from "../web/dist/kernel.mjs";
import { compile } from "../web/mathscript/compiler.mjs";
import { Kernel } from "../web/kernel.mjs";
import { checkedFoldedView } from "../web/mathscript/kernel-folding.mjs";
import { loadProof } from "../tools/test-selection.mjs";
import { replaceSyntax } from "./source-edit.mjs";

const module = await createKernel();
const classes = await loadProof("web/proofs/distinguished_extensions.proof");
const example = await loadProof("web/proofs/f4_embedded_composita.proof");
const source = "import distinguished_extensions;\n" + example.source;
const sources = { ...classes.sources, ...example.sources,
  distinguished_extensions: classes.source, f4_embedded_composita: example.source };
const c = compile(module, source, sources);
after(() => c.kernel.dispose());
const truncation = ["lib_Trunc", "lib_trunc_elim", "lib_trunc_intro", "lib_trunc_is_trunc"];
const extensional = [...truncation, "lib_funext"].sort();
const univalent = [...extensional, "lib_univalence"].sort();
function check(name, axioms) {
  assert.ok(c.kernel.verify(name + "_type", name), name);
  assert.deepEqual(c.kernel.axiomsFor(name).sort(), axioms, name);
}

test("embedded composita have checked factors, compatible base maps and leastness", () => {
  for (const name of ["embedded_compositum_left_lands", "embedded_compositum_right_lands", "embedded_compositum_factor"])
    check(name, truncation);
  for (const name of ["embedded_compositum_left_triangle", "embedded_compositum_right_triangle",
    "embedded_compositum_base_agreement", "embedded_compositum_base_triangle", "embedded_compositum_factor_triangle"])
    check(name, extensional);
  check("embedded_compositum_least", ["lib_Trunc", "lib_trunc_elim"]);
  check("embedded_compositum_commutative", univalent);
});

test("Lang's third clause follows from tower and base change and isomorphism invariance uses transport", () => {
  for (const name of ["ExtensionClass", "ExtensionClassProp"]) check(name, []);
  check("Distinguished", truncation);
  for (const name of ["distinguished_composita_from_tower_base_change", "distinguished_from_tower_base_change"])
    check(name, extensional);
  for (const name of ["extension_class_iso", "extension_class_iso_iff"])
    check(name, ["lib_funext", "lib_univalence"]);
  assert.ok(!c.kernel.bindings.has("LEM"));
  assert.ok(!c.kernel.bindings.has("AOC"));
});

test("two embedded copies of F2 generate a field equal to F2 inside F4", () => {
  check("f2_embedded_compositum_is_f2", univalent);
  check("f2_embedded_compositum_triangle", extensional);
  check("f2_embedded_compositum_base_agreement", extensional);
});

test("common-base equality retains a folded kernel type with a replayable conversion certificate", () => {
  const count = c.kernel.steps.length;
  const folded = checkedFoldedView(c, "embedded_compositum_base_agreement", { certificate: true });
  assert.deepEqual(folded.failures, {});
  assert.ok(folded.verified.type);
  assert.ok(Object.values(folded.references).some(ref => ref.name === "EmbeddedCompositum"));
  const replay = new Kernel(module, folded.certificate.policy.allowAxioms);
  try {
    for (const step of folded.certificate.steps) replay.apply(step);
    const expression = name => module._wb_view(replay.handle, 0, replay.bindings.get(name).id, 0);
    const evidence = folded.verified.type;
    const equality = replay.node(expression(evidence.witness));
    assert.equal(equality.kind, "DefEq");
    assert.deepEqual(equality.children, [expression(evidence.candidate), expression(evidence.original)]);
  } finally { replay.dispose(); }
  assert.equal(c.kernel.steps.length, count, "inspection must not modify the mathematical proof");
});

test("common-base agreement cannot discard the second commuting triangle", () => {
  const changed = replaceSyntax(sources.embedded_composita,
    "sym(cong((fun (e : FieldEmbedding(B, O)) => field_embedding_map(B, O, e, x)), rightTower))",
    "refl(field_embedding_map(B, O, bo, x))");
  assert.throws(() => compile(module, source, { ...sources, embedded_composita: changed }), /Expected|differ/);
});

test("compositum closure needs membership of both original extensions", () => {
  const changed = replaceSyntax(classes.source, "(inL, inLM)", "(inK, inLM)");
  assert.throws(() => compile(module, source, { ...sources, distinguished_extensions: changed }), /Expected|differ/);
});

test("a generated compositum is not automatically the entire ambient field", () => {
  assert.throws(() => compile(module, source + `
    theorem false_ambient_compositum :
      EmbeddedCompositum(F2, F2, F4, f2_f4_embedding, f2_f4_embedding) =[AlgebraicField] F4 {
      exact f2_embedded_compositum_is_f2;
    }
  `, sources), /Expected|differ/);
});

test("class membership must be propositional, not arbitrary chosen witness data", () => {
  assert.throws(() => compile(module, source + `
    def WitnessClass(K : AlgebraicField, E : FieldExt(K)) = typed(U1, Unit or Unit);
    theorem false_class_prop : ExtensionClassProp(WitnessClass) {
      intro K; intro E; intro p; intro q;
      exact refl(p);
    }
  `, sources), /Expected|differ/);
});
