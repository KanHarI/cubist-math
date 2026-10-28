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
import { CubicalProgram } from "../web/cubical-program.mjs";
import { ReplSession, restartNote } from "../web/repl-session.mjs";
import { RuntimeQuery } from "../web/cubical-runtime.mjs";
import { sourceReader } from "../tools/module-sources.mjs";

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

// A REPL value form computes in the runtime (web/cubical-runtime.mjs), whose
// snapshot reads the checked term from the kernel. An engine error out of
// one of those reads ends the entry at that statement, as anywhere else, and
// a session rebased on a new instance replays the entries that extended it.
// The error is injected beneath the guard, as the engine's RangeError, at
// the first export the snapshot calls.
const stackOf = () => {
  const limit = Error.stackTraceLimit;
  Error.stackTraceLimit = 100;
  try { return new Error().stack; } finally { Error.stackTraceLimit = limit; }
};
test("a failure in a runtime value form's kernel reads ends the entry, and a rebased session goes on", async () => {
  const module = await createCubical();
  let armed = false, injectedIn = null;
  for (const name of Object.keys(module).filter(name => name.startsWith("_cb_"))) {
    const call = module[name];
    module[name] = (...args) => {
      if (armed && /\bat snapshot\b/.test(stackOf())) {
        armed = false; injectedIn = name;
        throw new RangeError("Maximum call stack size exceeded");
      }
      return call(...args);
    };
  }
  const session = new ReplSession(new CubicalProgram(module, sourceReader(), { collectReferences: false }));
  await session.run("import unat; use unat; let x := 7;");
  armed = true;
  assert.deepEqual(await session.run("evaluate x + 1; let y := 2;"), [{ kind: "error", text: "E668: The kernel's WebAssembly "
    + "instance failed (Maximum call stack size exceeded), and is not used again: nothing computed after the failure is kept." }]);
  assert.ok(injectedIn && session.faulted && moduleFault(module));
  const rebased = await session.rebase(new CubicalProgram(await createCubical(), sourceReader(), { collectReferences: false }));
  assert.deepEqual(await rebased.run("evaluate x + 1; typeof x; typeof y;"),
    [{ kind: "value", text: "8" }, { kind: "type", text: "UNat" }, { kind: "error", text: "E343: Untranslated name: y" }]);
  assert.equal(rebased.faulted, false);
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
  // A query before a declaration is not replayed, yet a later entry names
  // the declaration's entry, repl_2: the replay keeps that name.
  const input = ["check lamps.cubist", "typeof tt;", "def Pointed := axiom Unit;", "let saved := repl_2::Pointed;",
    "let bright := toggle(dark);",
    // The overflow ends the entry: the statement after it is not checked.
    "def deep : parity(2 * 200 + 100) = dark := refl(dark); def unchecked : bright = lit := refl(lit);",
    "typeof saved;", "def again : bright = lit := refl(lit);", "evaluate toggle(bright);", "quit"].join("\n") + "\n";
  const run = spawnSync(process.execPath, ["--stack-size=350", cli], { cwd: directory, input, encoding: "utf8", timeout: 120000 });
  assert.equal(run.status, 0, run.stderr);
  assert.match(run.stderr, /^E668: The kernel's WebAssembly instance failed \(Maximum call stack size exceeded\), and is not used again: nothing computed after the failure is kept\.$/m);
  assert.match(run.stderr, /^The kernel was restarted: the last source checked was checked again; the session's entries were checked again\.$/m);
  assert.doesNotMatch(run.stdout + run.stderr, /deep :|unchecked|E343/);
  assert.match(run.stdout, /^saved : Unit\nsaved assumes repl_2::Pointed\nbright : Lamp\nUnit\nassumes repl_2::Pointed\nagain : bright = lit\ndark$/m);
});

// A rebase replays each statement as the entry it was, repl_N, though the
// queries between them are not run again; and what it cannot replay, here
// a module that is no longer there, it lists in `lost`, which the owner's
// note says (restartNote) rather than that everything was restored.
test("a rebased session keeps its entries' names and lists those it could not replay", async t => {
  const directory = await mkdtemp(join(tmpdir(), "cubist-rebase-"));
  t.after(() => rm(directory, { recursive: true, force: true }));
  await writeFile(join(directory, "helper.cubist"), "def h : Unit := tt;\n");
  const files = new Map([["library/helper", join(directory, "helper.cubist")]]);
  const session = new ReplSession(new CubicalProgram(await createCubical(), sourceReader({ files }), { collectReferences: false }));
  await session.run("typeof tt; let x := tt; let saved := repl_2::x; import helper; let k := h; let m := tt;");
  assert.equal(session.count, 6);
  const rebased = await session.rebase(new CubicalProgram(await createCubical(), sourceReader(), { collectReferences: false }));
  assert.deepEqual(rebased.lost, ["import helper;", "let k := h;"]);
  assert.deepEqual(rebased.accepted.map(({ entry }) => entry), [2, 3, 6]);
  assert.equal(rebased.count, 6);
  assert.deepEqual(await rebased.run("typeof saved; typeof m; typeof k;"),
    [{ kind: "type", text: "Unit" }, { kind: "type", text: "Unit" }, { kind: "error", text: "E343: Untranslated name: k" }]);
  assert.equal(restartNote({ source: "the proof", rechecked: true, replayed: true, session: rebased }),
    "The kernel was restarted: the proof was checked again; these entries could not be checked again, and what they defined is gone: import helper; let k := h;");
  assert.equal(restartNote({ replayed: true, session: await session.rebase(new CubicalProgram(await createCubical(), sourceReader({ files }))) }),
    "The kernel was restarted: the session's entries were checked again.");
  assert.equal(restartNote({ source: "the proof", replayed: true }),
    "The kernel was restarted: the proof could not be checked again: check it again to continue; the session's entries could not be checked again, and what they defined is gone.");
});

// An argument the engine cannot convert, as a BigInt for a 32-bit integer,
// is refused before the instance is entered, and ends nothing; an exception
// from a call whose arguments convert, as a trap, ends the instance.
test("an unconvertible argument is refused before entry; a trap ends the instance", async () => {
  const module = await createCubical(), trap = module._cb_arena;
  let trapping = false;
  module._cb_arena = (...args) => {
    if (trapping) throw new WebAssembly.RuntimeError("unreachable");
    return trap(...args);
  };
  const kernel = new CubicalKernel(module), graph = new InstructionGraph(kernel), point = graph.point();
  assert.throws(() => graph.judgement(1n), error => error instanceof TypeError && !(error instanceof KernelFault));
  assert.throws(() => module._cb_arena(kernel.handle, Symbol("field")), TypeError);
  assert.throws(() => module._cb_arena(kernel.handle, { valueOf() { throw new Error("converted"); } }), TypeError);
  assert.equal(moduleFault(module), null);
  assert.equal(graph.judgement(point).kind, "typing");
  trapping = true;
  assert.throws(() => kernel.arena(), error => error instanceof KernelFault && error.cause instanceof WebAssembly.RuntimeError);
  assert.throws(() => graph.judgement(point), KernelFault);
});

// A runtime query retained across operations publishes nothing once its
// instance has failed: neither an observation pending when it failed nor a
// later one, though its snapshot was copied before.
test("a runtime query publishes nothing after its kernel instance fails", async () => {
  const module = await createCubical(), arena = module._cb_arena;
  let failing = false;
  module._cb_arena = (...args) => {
    if (failing) throw new RangeError("Maximum call stack size exceeded");
    return arena(...args);
  };
  const kernel = new CubicalKernel(module), graph = new InstructionGraph(kernel);
  const query = new RuntimeQuery(kernel, graph.point(), { slice: 1 });
  assert.equal(query.observeNow().kind, "Point");
  const pending = query.observe();
  failing = true;
  assert.throws(() => kernel.arena(), KernelFault);
  await assert.rejects(pending, KernelFault);
  assert.throws(() => query.observeNow(), KernelFault);
  query.dispose();
});
