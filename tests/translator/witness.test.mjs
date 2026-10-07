// witnessOf (web/translator/evaluation.mjs, L2.9b) reads a closed
// truncation's witness. Its refusal of a base built in another type (E481)
// is defensive: H1's closed normal forms reach point(w), so no source reaches
// it (cubist-tests/truncation_readout.cubist checks the readouts that do).
// Here a scope stands for the kernel, so that the two answers of its check
// can be given: whether the constructor's value is accepted at the requested
// type decides, not whether its inferred type equals that type.
import test from "node:test";
import assert from "node:assert/strict";
import { witnessOf } from "../../web/translator/evaluation.mjs";

const unit = { tag: "Unit" }, tt = { tag: "tt", type: unit };
const requested = { tag: "Sort", signature: "Trunc", parameters: [{ tag: "A" }] };
// point(tt), built in Trunc(Unit): another type than the requested one by
// equality, whether the kernel accepts it at that type or not.
const point = { tag: "App", fn: { tag: "Con", index: 0 }, arg: tt, type: { tag: "Sort", signature: "Trunc", parameters: [unit] } };
const kernel = accepted => ({
  nf: term => term,
  infer: term => ({ type: term.type }),
  equal: () => false,
  accepts: (term, type) => accepted(term, type),
  checker: { kernel: { signatures: new Map([["Trunc", { index: 0 }]]), signature: () => ({ modifier: true, constructors: [{}] }) } },
});
const show = term => term.tag === "Sort" ? `Trunc(${term.parameters[0].tag})` : term.tag;

test("a witness is read where the kernel accepts its constructor at the requested type, its inferred type aside", () => {
  const { witness, type } = witnessOf({ tag: "Trans", base: point }, requested, kernel(() => true), show);
  assert.equal(witness, tt);
  // The truncated type as written, which the kernel accepts the witness at.
  assert.equal(type, requested.parameters[0]);
});

test("a base the kernel refuses at the requested type is no witness of it (E481)", () => {
  assert.throws(() => witnessOf({ tag: "Trans", base: point }, requested, kernel(() => false), show),
    /^Error: The truncation's witness lies under a composition whose type changes: it is built in Trunc\(Unit\), not Trunc\(A\)\.$/);
});
