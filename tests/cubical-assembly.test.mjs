import test from "node:test";
import assert from "node:assert/strict";
import createCubical from "../web/dist/cubical.mjs";
import { CubicalProgram } from "../web/cubical-program.mjs";
import { kernelAssembly, assemblyText } from "../web/cubical-assembly.mjs";

const module = await createCubical();
async function fixture(t) {
  const program = new CubicalProgram(module, async () => ""); t.after(() => program.dispose());
  const result = await program.check(`def N := Nat; def id(n : Nat) := n;
    def twice := id(id(0)); def annotated := typed(N, 0);
    def along(A : U0, x : A, y : A, p : x = y) :=
      path(fun (i : Interval) => A, fun (i : Interval) => at(p, i));`, "assembly");
  assert.equal(result.complete, true);
  return program;
}
function checkedView(program, binding) {
  const view = program.inspect(binding);
  const checked = program.checker.syntax.check(view.expression, view.type,
    view.context.map(entry => [entry.name, entry.type]), new Map(view.dimensions));
  return { view, checked };
}

test("assembly rows expose actual C opcodes, payloads, and all four operand slots", async t => {
  const program = await fixture(t), { view, checked } = checkedView(program, "assembly__twice");
  const listing = kernelAssembly(program, view, checked);
  assert.equal(listing.roots[0].handle, checked.expression);
  assert.equal(listing.nodes[0].mnemonic, "CC_APP");
  assert.equal(listing.nodes[0].opcode, 5);
  assert.equal(new Set(listing.nodes.map(node => node.id)).size, listing.nodes.length);
  for (const node of listing.nodes) {
    const native = program.kernel.node(node.id);
    assert.equal(node.opcode, module._cb_node(program.kernel.handle, node.id, 0));
    assert.equal(node.payload, native.payload);
    assert.deepEqual(node.operands.map(operand => operand.handle), native.children);
  }
  const ref = listing.nodes.find(node => node.kind === "DefRef");
  assert.ok(ref.annotation.includes("assembly__id"));
  assert.equal(listing.nodes.some(node => node.id === ref.definition.value), false);
  const expanded = kernelAssembly(program, view, checked, { expanded: [ref.id] });
  assert.equal(expanded.nodes.some(node => node.id === ref.definition.value), true);
  assert.match(assemblyText(expanded), /CC_LAM \[4\]/);
  assert.equal(program.inspect("assembly__twice").expression.tag, "App", "reading assembly must not normalize");
});

test("the listing keeps checked type and inferred type roots distinct", async t => {
  const program = await fixture(t), { view, checked } = checkedView(program, "assembly__annotated");
  const reducedTypeView = { ...view, type: { tag: "Nat" } };
  const result = program.checker.syntax.check(view.expression, reducedTypeView.type);
  const listing = kernelAssembly(program, reducedTypeView, result);
  assert.equal(program.kernel.node(listing.roots.find(root => root.label === "Checked type").handle).kind, "Nat");
  assert.equal(program.kernel.node(listing.roots.find(root => root.label === "Inferred type").handle).kind, "DefRef");
});

test("bounded listings retain navigable roots and can prioritize an omitted operand", async t => {
  const program = await fixture(t), { view, checked } = checkedView(program, "assembly__twice");
  const partial = kernelAssembly(program, view, checked, { limit: 1 });
  assert.equal(partial.nodes.length, 1); assert.ok(partial.pending > 0);
  assert.match(assemblyText(partial), /Partial listing/);
  const operand = partial.nodes[0].operands[0].handle;
  const focused = kernelAssembly(program, view, checked, { limit: 1, focus: [operand] });
  assert.equal(focused.nodes[0].id, operand);
});

test("open interval contexts and full 64-bit formula masks survive assembly inspection", async t => {
  const program = await fixture(t);
  const pType = { tag: "Path", dim: "j", family: { tag: "Nat" }, left: { tag: "Zero" }, right: { tag: "Zero" } };
  const view = { expression: { tag: "PApp", path: { tag: "Var", name: "p" }, arg: [["i:1"]] },
    type: { tag: "Nat" }, context: [{ name: "p", label: "path", type: pType }], dimensions: [["i", 63]], symbols: {} };
  const checked = program.checker.syntax.check(view.expression, view.type, [["p", pType]], new Map(view.dimensions));
  const listing = kernelAssembly(program, view, checked);
  assert.equal(listing.context[0].label, "path");
  assert.deepEqual(listing.dimensions, [["i", 63]]);
  assert.equal(listing.formulas.find(formula => formula.sort === "interval").clauses[0].positive, "0x8000000000000000");
  assert.match(assemblyText(listing), /Interval i: dimension #63/);
});

test("universe axiom specialization records provenance without inventing a kernel application", async t => {
  const program = new CubicalProgram(module, async () => ""); t.after(() => program.dispose());
  const result = await program.check(`def choice0 := Choice(U0); def choice1 := Choice(U1);
    def truncate1 := Truncate(U1); def identity(n : Nat) := n;`, "specialization");
  assert.equal(result.complete, true);
  for (const level of [0, 1]) {
    const binding = `__assumption_Choice_U${level}`;
    const { view, checked } = checkedView(program, binding);
    assert.equal(view.expression.tag, "Var");
    assert.equal(view.specialization.schema, "Choice");
    assert.equal(view.specialization.universe, `U${level}`);
    assert.deepEqual(view.specialization.mentions.map(use => use.declaration), [`choice${level}`]);
    assert.equal(view.specialization.schemaType.domain.tag, "Var");
    assert.equal(view.specialization.schemaType.domain.name, "U");
    assert.equal(view.type.domain.tag, "U");
    assert.equal(view.type.domain.level, level);
    const listing = kernelAssembly(program, view, checked);
    assert.equal(program.kernel.node(listing.roots[0].handle).kind, "Var");
    assert.match(assemblyText(listing), new RegExp(`Elaborator specialization: Choice\\(U\\), U := U${level}`));
    assert.match(assemblyText(listing), /No universe-generic kernel term or CC_APP/);
    assert.equal(program.kernel.node(listing.roots.find(root => root.label === "Checked type").handle).kind, "Pi");
  }
  const truncation = program.inspect("__assumption_Truncate_U1");
  assert.equal(truncation.specialization.schemaType.body.tag, "U");
  assert.equal(truncation.specialization.schemaType.body.level, 0, "schema display preserves fixed codomain");
  assert.equal(truncation.type.body.level, 0);
  assert.equal(program.inspect("specialization__identity").specialization, undefined);
  const { view, checked } = checkedView(program, "__assumption_Choice_U0");
  const edited = { ...view, expression: { tag: "Nat" } };
  const editedCheck = program.checker.syntax.check(edited.expression);
  assert.equal(kernelAssembly(program, edited, editedCheck).specialization, null, "edits must not inherit stale axiom origin");
});
