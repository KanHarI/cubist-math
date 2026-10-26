import "./fresh-build.mjs";
import test from "node:test";
import assert from "node:assert/strict";
import { mkdtemp, readFile, rm, writeFile } from "node:fs/promises";
import { tmpdir } from "node:os";
import { join } from "node:path";
import { spawnSync } from "node:child_process";
import { fileURLToPath } from "node:url";
import createCubical from "../web/dist/cubical.mjs";
import { CubicalProgram } from "../web/cubical-program.mjs";
import { ReplSession } from "../web/repl-session.mjs";
import { ContextualSession } from "../web/contextual-session.mjs";
import { WorkbenchSession } from "../web/cubical-workbench-session.mjs";
import { sourceReader } from "../tools/module-sources.mjs";

// An assumption's kernel name carries a mark (web/translator/names.mjs,
// assumptionMark), and an axiom's identity is module__Name: neither is
// anything a person reads. Over a program whose axioms depend on one
// another, every surface shows each assumption by its label, module::Name:
// the command line's check, inspect, assembly and entries, a REPL session,
// the workspace's check result, which the pages and the reference render,
// its inspector's views, the console under a proof and the workbench
// (#317's review round 4, finding 3).
const source = "def A := axiom U0;\ndef B := axiom A;\ndef C := axiom (B = B);\ndef use_ : B = B := C;\n"
  + "def f(h : B = B) : B = B { exact h; }\nprint(typeof(C));\nprint(inspect(use_));\n";
// A kernel name with the mark, as sweep__A#, or an axiom's identity; the
// assembly numbers its symbols #1, #2, …, which name nothing.
const raw = /\w#|\b(?:sweep|repl_\d+)__[A-E]\b/;
const clean = (surface, texts) => {
  for (const text of texts) assert.doesNotMatch(String(text), raw, `${surface}: ${text}`);
};

test("no surface shows an assumption's kernel name or an axiom's identity", async t => {
  const module = await createCubical();
  const program = new CubicalProgram(module, sourceReader(), { collectScopes: true });
  t.after(() => program.dispose());
  const result = await program.check(source, "sweep");
  assert.equal(result.complete, true, JSON.stringify(program.gaps));
  // The check result: declarations, symbols, prints and labels.
  clean("check", [...result.outputs.flatMap(output => [output.name, output.type]),
    ...result.symbols.flatMap(symbol => [symbol.name, symbol.type]), ...result.prints.map(print => print.text),
    ...Object.values(result.assumptionLabels)]);
  assert.equal(result.outputs.find(output => output.name === "B").type, "sweep::A");
  // The inspector's views, each with its symbols and context.
  for (const binding of ["sweep__A", "sweep__B", "sweep__C", "sweep__use_", "sweep__f"]) {
    const view = program.inspect(binding);
    clean(`inspect ${binding}`, [view.expressionText, view.typeText, ...Object.values(view.symbols).map(symbol => symbol.name),
      ...view.context.map(entry => entry.label ?? entry.name).filter(label => !/^h$/.test(label))]);
  }
  // A REPL session over the check, with an axiom of its own.
  const repl = new ReplSession(program, { base: "sweep" });
  for (const entry of ["typeof C;", "print(typeof(B));", "print(inspect(C));", "let x := C;", "def D := axiom (x = x);", "typeof D;", "D"])
    clean(`repl ${entry}`, (await repl.run(entry)).map(line => line.text));
  // The console under the proof of f.
  const start = source.indexOf("exact h;");
  const point = [...program.scopePoints.values()].find(point => point.origin.module === "sweep" && point.origin.start === start && point.phase === "before");
  const session = new ContextualSession(program, point.id);
  t.after(() => session.dispose());
  for (const entry of ["/goal", "/locals", "typeof h", "inspect h", "let k := h", "/prove { exact C; }"])
    clean(`console ${entry}`, (await session.run(entry)).map(line => line.text));
  // The workbench, from the declaration's transfer.
  const workbench = new WorkbenchSession(module);
  t.after(() => workbench.dispose());
  const loaded = await workbench.load(program.export("sweep__use_"));
  clean("workbench", [loaded.view.expressionText, loaded.view.typeText, ...Object.values(loaded.view.symbols).map(symbol => symbol.name)]);
  // The command line: check, inspect, assembly and entries. inspect heads
  // its view with the declaration's binding, the form a name is typed in
  // when it is ambiguous (web/reference/checking.html), which is no
  // assumption's.
  const directory = await mkdtemp(join(tmpdir(), "cubist-display-"));
  t.after(() => rm(directory, { recursive: true, force: true }));
  await writeFile(join(directory, "sweep.cubist"), source);
  const cli = fileURLToPath(new URL("../cli/repl.mjs", import.meta.url));
  const shell = spawnSync(process.execPath, [cli], { cwd: directory, encoding: "utf8", timeout: 60000,
    input: "check sweep.cubist\ninspect B\ninspect use_\nassembly B\ntypeof C;\nprint(typeof(B));\ndef E := axiom A;\nquit\n" });
  assert.equal(shell.status, 0, shell.stderr);
  assert.match(shell.stdout, /^E : sweep::A$/m);
  clean("command line", shell.stdout.split("\n").filter(line => !/^sweep__\w+$/.test(line)));
});
