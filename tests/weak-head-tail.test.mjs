import "./fresh-build.mjs";
import test from "node:test";
import assert from "node:assert/strict";
import createCubical from "../web/dist/cubical.mjs";
import { CubicalKernel } from "../web/cubical-kernel.mjs";
import { InstructionGraph } from "../web/cubical-instructions.mjs";

test("checked alias chains reduce within the ordinary WASM stack", async () => {
  const module = await createCubical();
  for (const shareSyntax of [true, false]) {
    for (const mode of ["head", "normalize"]) {
      const kernel = new CubicalKernel(module);
      try {
        kernel.setOptimizations({ shareSyntax });
        const graph = new InstructionGraph(kernel);
        let value = graph.point();
        const point = graph.judgement(value).term;
        for (let i = 0; i < 4096; i++) value = graph.define(`alias${i}`, value);
        const source = graph.judgement(value).term;
        if (mode === "head") {
          assert.equal(graph.head(source, 200n), 0, "bounded interruption");
          const before = kernel.work().querySteps;
          assert.equal(graph.head(source, 10000n), point);
          assert.equal(kernel.work().querySteps - before, 4097);
          const warm = kernel.work().querySteps;
          assert.equal(graph.head(source, 10000n), point);
          assert.equal(kernel.work().querySteps - warm, 1);
        } else {
          // A fresh kernel requests full normalization through an instruction,
          // so neither a preceding head query nor a raw result supplies evidence.
          const equality = graph.step(graph.refl(value), "other", [], "normalize");
          const result = graph.judgement(equality);
          assert.equal(result.kind, "equality");
          assert.deepEqual(result.context, []);
          assert.equal(kernel.node(result.other).kind, "Point");
        }
      } finally { kernel.dispose(); }
    }
  }
});

test("nested prerequisite heads retain a controlled WASM recursion failure", async () => {
  const module = await createCubical();
  for (const shareSyntax of [true, false]) {
    const kernel = new CubicalKernel(module);
    try {
      kernel.setOptimizations({ shareSyntax });
      const graph = new InstructionGraph(kernel), point = graph.point();
      const unit = graph.unit(), entry = graph.extend(unit, "value");
      const motive = graph.lambda(entry, unit);
      const pointType = graph.step(graph.refl(graph.apply(motive, point)), "term", [], "beta");
      const pointCase = graph.convert(point, pointType);
      let value = point;
      for (let i = 0; i < 1100; i++) {
        const result = graph.unitElim(motive, pointCase, value);
        const type = graph.step(graph.refl(graph.apply(motive, value)), "other", [], "beta");
        value = graph.define(`nested${i}`, graph.convert(result, type));
      }
      assert.throws(() => kernel.head(graph.judgement(value).term),
        error => error.kind === "resource" && error.message === "Native reduction recursion depth exceeded.");
      assert.equal(kernel.head(graph.judgement(point).term), graph.judgement(point).term);
    } finally { kernel.dispose(); }
  }
});
