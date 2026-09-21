import test from "node:test";
import assert from "node:assert/strict";
import { splitInspectionContext } from "../web/cubical-context.mjs";

test("inspection separates checked axioms from locals without changing the kernel context", () => {
  const axiom = { name: "__assumption_Choice_U0", binding: "__assumption_Choice_U0", label: "Choice(U0)", type: { tag: "U", level: 1 } };
  const local = { name: "Choice42", binding: "test__local_12", label: "Choice(U0)", type: { tag: "Nat" } };
  const view = { context: [axiom, local], axioms: [axiom.name], symbols: {} };
  assert.deepEqual(splitInspectionContext(view), { context: [local], axioms: [axiom] });
  assert.deepEqual(view.context, [axiom, local]);
  const folded = view.context.map(entry => ({ ...entry, type: { tag: "DefRef", name: "NamedType" } }));
  const result = splitInspectionContext(view, folded);
  assert.equal(result.axioms[0], folded[0]);
  assert.equal(result.context[0], folded[1]);
});

test("axiom symbol metadata remains usable when a workbench view has no dependency list", () => {
  const axiom = { name: "__assumption_Choice_U1", binding: "__assumption_Choice_U1" };
  assert.deepEqual(splitInspectionContext({ context: [axiom], symbols: { [axiom.binding]: { kind: "axiom" } } }),
    { context: [], axioms: [axiom] });
  assert.deepEqual(splitInspectionContext({}), { context: [], axioms: [] });
});
