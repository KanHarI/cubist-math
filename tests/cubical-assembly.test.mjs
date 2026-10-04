import "./fresh-build.mjs";
import {naturalSort, numeral} from "../web/translator/numerals.mjs";
import test from "node:test";
import assert from "node:assert/strict";
import createCubical from "../web/dist/cubical.mjs";
import { checkTestModule } from "./check-program.mjs";
import { kernelAssembly, assemblyText } from "../web/cubical-assembly.mjs";

const module = await createCubical();
// The declarations are cubist-tests/assembly_*.cubist.
async function fixture(t) {
  return (await checkTestModule(t, "assembly_fixture", { module })).program;
}
function checkedView(program, binding) {
  const view = program.inspect(binding);
  const checked = program.checker.checkView(view.expression, view.type,
    view.context.map(entry => [entry.name, entry.type]), new Map(view.dimensions));
  return { view, checked };
}

test("assembly rows expose actual C opcodes, payloads, and all four operand slots", async t => {
  const program = await fixture(t), { view, checked } = checkedView(program, "assembly_fixture__twice");
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
  assert.ok(ref.annotation.includes("assembly_fixture__id"));
  assert.equal(listing.nodes.some(node => node.id === ref.definition.value), false);
  const expanded = kernelAssembly(program, view, checked, { expanded: [ref.id] });
  assert.equal(expanded.nodes.some(node => node.id === ref.definition.value), true);
  assert.match(assemblyText(expanded), /CC_LAM \[4\]/);
  assert.equal(program.inspect("assembly_fixture__twice").expression.tag, "App", "reading assembly must not normalize");
});

test("the listing keeps checked type and inferred type roots distinct", async t => {
  const program = await fixture(t), { view, checked } = checkedView(program, "assembly_fixture__annotated");
  const reducedTypeView = { ...view, type: naturalSort };
  program.checker.checkView(view.expression, reducedTypeView.type);
  const result = checked;
  const listing = kernelAssembly(program, reducedTypeView, result);
  assert.equal(program.kernel.node(listing.roots.find(root => root.label === "Checked type").handle).kind, "Sort");
  assert.equal(program.kernel.node(listing.roots.find(root => root.label === "Inferred type").handle).kind, "DefRef");
});

test("bounded listings retain navigable roots and can prioritize an omitted operand", async t => {
  const program = await fixture(t), { view, checked } = checkedView(program, "assembly_fixture__twice");
  const partial = kernelAssembly(program, view, checked, { limit: 1 });
  assert.equal(partial.nodes.length, 1); assert.ok(partial.pending > 0);
  assert.match(assemblyText(partial), /Partial listing/);
  const operand = partial.nodes[0].operands[0].handle;
  const focused = kernelAssembly(program, view, checked, { limit: 1, focus: [operand] });
  assert.equal(focused.nodes[0].id, operand);
});

test("open interval contexts and full 64-bit formula masks survive assembly inspection", async t => {
  const program = await fixture(t);
  const pType = { tag: "Path", dim: "j", family: naturalSort, left: numeral(0), right: numeral(0) };
  const view = { expression: { tag: "PApp", path: { tag: "Var", name: "p" }, arg: [["i:1"]] },
    type: naturalSort, context: [{ name: "p", label: "path", type: pType }], dimensions: [["i", 63]], symbols: {} };
  const checked = program.checker.checkView(view.expression, view.type, [["p", pType]], new Map(view.dimensions));
  const listing = kernelAssembly(program, view, checked);
  assert.equal(listing.context[0].label, "path");
  assert.deepEqual(listing.dimensions, [["i", 63]]);
  assert.equal(listing.formulas.find(formula => formula.sort === "interval").clauses[0].positive, "0x8000000000000000");
  assert.match(assemblyText(listing), /Interval i: dimension #63/);
});

test("a generic assumption is one kernel entry, and each use is a level application", async t => {
  const { program } = await checkTestModule(t, "assembly_generic_assumptions", { module });
  // The command line and the workbench check through the instruction kernel;
  // the term checker has no level rules.
  const view = program.inspect("__assumption_Choice");
  const checked = program.checker.checkView(view.expression, view.type, view.context.map(entry => [entry.name, entry.type]), new Map(view.dimensions));
  assert.equal(view.expression.tag, "Var");
  assert.equal(view.type.tag, "LPi");
  const listing = kernelAssembly(program, view, checked);
  assert.equal(program.kernel.node(listing.roots[0].handle).kind, "Var");
  assert.equal(program.kernel.node(listing.roots.find(root => root.label === "Checked type").handle).kind, "LPi");
  for (const level of [0, 1]) {
    const use = program.inspect(`assembly_generic_assumptions__choice${level}`).expression;
    assert.equal(use.tag, "LApp");
    assert.deepEqual([use.fn, use.level], [{ tag: "Var", name: "__assumption_Choice" }, level]);
  }
  // One assumption, whatever levels it is used at (G0 Q4).
  // Choice's statement mentions Truncate.
  const labels = name => program.symbols[name].axioms.map(id => program.checker.assumptionLabels.get(id)).sort();
  assert.deepEqual(labels("assembly_generic_assumptions__choice0"), ["Choice", "Truncate"]);
  assert.deepEqual(labels("assembly_generic_assumptions__choice1"), ["Choice", "Truncate"]);
  // Truncate keeps the archive's resizing signature until H1 (G0 Q5): the
  // module prints its type.
});
