import test, { after } from "node:test";
import assert from "node:assert/strict";
import createKernel from "../web/dist/kernel.mjs";
import { compile } from "../web/mathscript/compiler.mjs";
import { checkedFoldedView } from "../web/mathscript/kernel-folding.mjs";
import { loadProof } from "../tools/test-selection.mjs";

const module = await createKernel();
const loaded = await loadProof("web/proofs/radix_univalence_transfer.proof");
const c = compile(module, loaded.source, loaded.sources);
after(() => c.kernel.dispose());

test("binary, every radix, and unary Nat have actual checked equivalences", () => {
  for (const name of ["binary_nat_equiv", "nat_binary_equiv", "radix_nat_equiv", "nat_radix_equiv", "radix_binary_equiv", "binary_radix_equiv"]) {
    assert.ok(c.kernel.verify(name + "_type", name), name);
    assert.deepEqual(c.kernel.axiomsFor(name), ["lib_funext"], name);
  }
});

test("existing addition, multiplication and factorial are preserved, not redefined", () => {
  for (const name of ["binary_decode_add", "binary_decode_mul", "binary_factorial_correct",
    "radix_decode_add", "radix_decode_mul", "radix_factorial_correct", "factorial_ten_from_binary"]) {
    assert.ok(c.kernel.verify(name + "_type", name), name);
    assert.deepEqual(c.kernel.axiomsFor(name), ["lib_funext"], name);
  }
});

test("all four requested directions use explicit HoTT univalence transport", () => {
  for (const name of ["factorial_ten_via_univalence", "factorial_ten_binary_to_radix", "factorial_ten_radix_to_binary",
    "factorial_ten_radix_to_nat", "factorial_ten_from_base_two", "factorial_ten_from_base_ten",
    "factorial_ten_base_two_to_binary", "factorial_ten_base_ten_to_binary", "factorial_ten_binary_to_base_two", "factorial_ten_binary_to_base_ten"]) {
    assert.ok(c.kernel.verify(name + "_type", name), name);
    assert.deepEqual(c.kernel.axiomsFor(name).sort(), ["lib_funext", "lib_univalence"], name);
  }
  // These are intentionally not labelled native cubical checks. That backend
  // must derive Glue/univalence before it can remove the above assumptions.
});

test("transport to Nat never constructs the millions of unary successors", () => {
  const stats = c.kernel.stats();
  assert.ok(stats.nodes < 500000, JSON.stringify(stats));
  assert.ok(stats.bytes < 100 * 1024 * 1024, JSON.stringify(stats));
  const lengths = new Map();
  let maximum = 0;
  for (let id = 1; id <= stats.nodes; id++) {
    const n = c.kernel.node(id);
    if (n.kind === "ZN") lengths.set(id, 0);
    if (n.kind === "SN" && lengths.has(n.children[0])) {
      const length = lengths.get(n.children[0]) + 1;
      lengths.set(id, length);
      maximum = Math.max(maximum, length);
    }
  }
  assert.equal(maximum, 10);
});

test("the numeral conversions are separate checked certificates", () => {
  for (const name of ["base_two_3628800_to_binary", "base_ten_3628800_to_binary"]) {
    assert.ok(c.kernel.verify(name + "_type", name));
    assert.deepEqual(c.kernel.axiomsFor(name), ["lib_funext"]);
  }
});

test("transported factorial statements retain certified readable folded types", () => {
  for (const name of ["factorial_ten_binary_to_base_two", "factorial_ten_binary_to_base_ten", "factorial_ten_from_base_ten"]) {
    const view = checkedFoldedView(c, name);
    assert.deepEqual(view.failures, {}, name);
    assert.ok(view.verified.type, name);
  }
});
