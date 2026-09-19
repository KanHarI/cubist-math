import test from "node:test";
import assert from "node:assert/strict";
import createKernel from "../web/dist/kernel.mjs";
import { compile } from "../web/mathscript/compiler.mjs";
import { loadProof } from "../tools/test-selection.mjs";

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
