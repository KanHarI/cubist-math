import "./fresh-build.mjs";
import test from "node:test";
import assert from "node:assert/strict";
import createCubical from "../web/dist/cubical.mjs";
import { CubicalProgram } from "../web/cubical-program.mjs";
import { sourceReader } from "../tools/module-sources.mjs";

const literal = n => `0b${n.toString(2)}`;

test("binary arithmetic and comparison agree with independent integer results", async t => {
  const program = new CubicalProgram(await createCubical(), sourceReader(), { collectReferences: false });
  t.after(() => program.dispose());
  const pairs = [];
  for (let a = 0n; a < 8n; a++) for (let b = 0n; b < 8n; b++) pairs.push([a, b]);
  for (const bits of [31n, 32n, 63n, 64n, 65n]) {
    const n = 1n << bits;
    pairs.push([n - 1n, 1n], [n, n + 1n], [n + 1n, n - 1n]);
  }
  const proofs = [];
  for (const [i, [a, b]] of pairs.entries()) {
    const x = literal(a), y = literal(b);
    const equations = {
      add: `${x} + ${y} = ${literal(a + b)}`,
      mul: `${x} * ${y} = ${literal(a * b)}`,
      order: `bnat_compare(${x}, ${y}) = ${a < b ? "b_less" : a === b ? "b_equal" : "b_greater"}`,
      equal: `bnat_equal(${x}, ${y}) = ${a === b ? "Unit" : "Void"}`,
      le: `bnat_le(${x}, ${y}) = ${a <= b ? "Unit" : "Void"}`,
      lt: `bnat_lt(${x}, ${y}) = ${a < b ? "Unit" : "Void"}`,
      pred: `bnat_pred(${x}) = ${literal(a ? a - 1n : 0n)}`,
      succ: `bnat_succ(${x}) = ${literal(a + 1n)}`,
    };
    for (const [operation, equation] of Object.entries(equations))
      proofs.push(`def case_${i}_${operation} : ${equation} { rfl; }`);
  }
  const result = await program.check(`import bnat_notation; use bnat;\n${proofs.join("\n")}`, "binary_differential");
  assert.ok(result.complete, JSON.stringify(result.gaps));
  assert.equal(result.outputs.length, proofs.length);
  assert.ok(result.outputs.every(output => output.verified && !output.axioms.length));
});

test("binary arithmetic's checked definitions have no unary carrier dependency", async t => {
  const program = new CubicalProgram(await createCubical(), sourceReader(), { collectReferences: false });
  t.after(() => program.dispose());
  const result = await program.check("import bnat; def probe := bnat_add;", "binary_dependencies");
  assert.ok(result.complete, JSON.stringify(result.gaps));
  const kernel = program.kernel, unary = kernel.signatures.get("nat__Nat").index;
  const visited = new Set();
  const visit = term => {
    if (!term || visited.has(term)) return;
    visited.add(term);
    const node = kernel.node(term);
    assert.ok(node.kind !== "Sort" || node.payload !== unary, "binary arithmetic reached the unary natural carrier");
    if (node.kind === "DefRef") {
      const definition = kernel.definition(term);
      visit(definition.value); visit(definition.type);
    }
    for (const child of node.children) visit(child);
  };
  for (const name of ["bnat_succ", "bnat_pred", "bnat_add", "bnat_mul", "bnat_compare", "bnat_equal", "bnat_le", "bnat_lt"]) {
    const reference = kernel.definitions.get(`bnat__${name}`);
    assert.ok(reference, name);
    const { value, type } = kernel.definition(reference);
    visit(value); visit(type);
  }
});
