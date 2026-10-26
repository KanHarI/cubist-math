// A kernel instance that fails is never entered again (guardModule in
// web/cubical-kernel.mjs), and the command line replaces it: the session's
// entries are checked again on a new instance, and the next entry works.
import "./fresh-build.mjs";
import test from "node:test";
import assert from "node:assert/strict";
import { mkdtemp, writeFile, rm } from "node:fs/promises";
import { tmpdir } from "node:os";
import { join } from "node:path";
import { spawnSync } from "node:child_process";
import { fileURLToPath } from "node:url";
import createCubical from "../web/dist/cubical.mjs";
import { CubicalKernel, KernelFault, moduleFault } from "../web/cubical-kernel.mjs";
import { InstructionGraph } from "../web/cubical-instructions.mjs";

// Unit eliminations nested through definitions: a head query recurses once
// a level, so near the end of the engine's stack it overflows inside the
// instance.
function nested(kernel, depth) {
  const graph = new InstructionGraph(kernel), point = graph.point();
  const unit = graph.unit(), entry = graph.extend(unit, "value");
  const motive = graph.lambda(entry, unit);
  const pointType = graph.step(graph.refl(graph.apply(motive, point)), "term", [], "beta");
  const pointCase = graph.convert(point, pointType);
  let value = point;
  for (let i = 0; i < depth; i++) {
    const result = graph.unitElim(motive, pointCase, value);
    const type = graph.step(graph.refl(graph.apply(motive, value)), "other", [], "beta");
    value = graph.define(`nested${i}`, graph.convert(result, type));
  }
  return { deep: graph.judgement(value).term, point: graph.judgement(point).term };
}

// Calls f with the engine's stack all but used up: each frame that catches
// the overflow tries f again, one frame higher, until f returns or throws
// something else.
const nearTheEnd = f => { try { return nearTheEnd(f); } catch (error) { if (error instanceof RangeError) return f(); throw error; } };

test("an engine error out of an export ends the instance: no later call enters it", async () => {
  const module = await createCubical(), entered = new Map();
  for (const name of ["_cb_head", "_cb_free"]) {
    const call = module[name];
    module[name] = (...args) => { entered.set(name, (entered.get(name) ?? 0) + 1); return call(...args); };
  }
  const kernel = new CubicalKernel(module), { deep, point } = nested(kernel, 300);
  assert.equal(moduleFault(module), null);
  assert.throws(() => nearTheEnd(() => kernel.head(deep)), error => error instanceof KernelFault
    && error.kind === "fault" && error.cause instanceof RangeError
    && /^The kernel's WebAssembly instance failed \(Maximum call stack size exceeded\)/.test(error.message));
  assert.ok(moduleFault(module) instanceof KernelFault);
  const heads = entered.get("_cb_head");
  assert.throws(() => kernel.head(point), KernelFault);
  assert.throws(() => new CubicalKernel(module), KernelFault);
  kernel.dispose();
  assert.equal(entered.get("_cb_head"), heads);
  assert.equal(entered.get("_cb_free"), undefined);
  // A new instance computes what the failed one was asked.
  const fresh = new CubicalKernel(await createCubical()), again = nested(fresh, 300);
  assert.equal(fresh.head(again.deep), again.point);
  fresh.dispose();
});

// The engine's stack is made smaller than the kernel's recursion guard
// assumes (--stack-size), so nested eliminators overflow it inside the
// instance: a genuine engine error, in a REPL entry over a checked file.
test("the command line replaces a failed instance and checks the source and the session again", async t => {
  const directory = await mkdtemp(join(tmpdir(), "cubist-fault-"));
  t.after(() => rm(directory, { recursive: true, force: true }));
  await writeFile(join(directory, "lamps.cubist"), `import unat;
use unat;
inductive Lamp { dark; lit; }
def toggle(f : Lamp) : Lamp := match f { dark => lit; lit => dark; };
def parity(n : UNat) : Lamp := match n { zero => dark; succ(m) => toggle(parity(m)); };
`);
  const cli = fileURLToPath(new URL("../cli/repl.mjs", import.meta.url));
  const input = ["check lamps.cubist", "let bright := toggle(dark);",
    // The overflow ends the entry: the statement after it is not checked.
    "def deep : parity(2 * 200 + 100) = dark := refl(dark); def unchecked : bright = lit := refl(lit);",
    "def again : bright = lit := refl(lit);", "evaluate toggle(bright);", "quit"].join("\n") + "\n";
  const run = spawnSync(process.execPath, ["--stack-size=350", cli], { cwd: directory, input, encoding: "utf8", timeout: 120000 });
  assert.equal(run.status, 0, run.stderr);
  assert.match(run.stderr, /^E666: The kernel's WebAssembly instance failed \(Maximum call stack size exceeded\), and is not used again: nothing computed after the failure is kept\.$/m);
  assert.match(run.stderr, /^The kernel was restarted: the last source checked, and the session's entries, were checked again\.$/m);
  assert.doesNotMatch(run.stdout + run.stderr, /deep :|unchecked/);
  assert.match(run.stdout, /^bright : Lamp\n[\s\S]*^again : bright = lit\ndark$/m);
});
