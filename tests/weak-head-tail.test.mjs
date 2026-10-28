import "./fresh-build.mjs";
import test from "node:test";
import assert from "node:assert/strict";
import { readFile } from "node:fs/promises";
import createCubical from "../web/dist/cubical.mjs";
import { CubicalKernel } from "../web/cubical-kernel.mjs";
import { InstructionGraph } from "../web/cubical-instructions.mjs";
import { checkProgram } from "./check-program.mjs";

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

// A declared type's eliminator nested in itself takes about 3.7 KiB of the
// WASM stack a level. On a 2 MiB stack placed after the static data, 600
// levels ran past its end without a trap and overwrote the session table:
// the declaration, and every later one, failed with "Invalid cubical session.".
test("nested declared eliminators reach the recursion guard within the WASM stack", async t => {
  const { verdicts } = await checkProgram(t, `import unat;
use unat;
inductive Lamp { dark; lit; }
def toggle(f : Lamp) : Lamp := match f { dark => lit; lit => dark; };
def parity(n : UNat) : Lamp := match n { zero => dark; succ(m) => toggle(parity(m)); };
def deep : parity(5 * 200) = dark := refl(dark);
def past_the_guard : parity(10 * 200) = dark := refl(dark);
def after : toggle(dark) = lit := refl(lit);
`);
  assert.deepEqual(verdicts.deep, true);
  assert.match(verdicts.past_the_guard, /Native reduction recursion depth exceeded/);
  assert.deepEqual(verdicts.after, true);
});

// The stack lies below the static data (the Makefile's --stack-first), so an
// overflow runs below address 0 and traps rather than overwriting that data:
// a static string of the bridge lies past the whole stack.
test("the WASM stack lies below the static data", async () => {
  const module = await createCubical();
  const makefile = await readFile(new URL("../Makefile", import.meta.url), "utf8");
  const stack = Number(makefile.match(/-sSTACK_SIZE=(\d+)/)[1]);
  assert.ok(module._cb_error(0) >= stack, `"Invalid cubical session." at ${module._cb_error(0)}, below the stack's end at ${stack}`);
});
