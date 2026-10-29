import "./fresh-build.mjs";
import {sourceReader} from "../tools/module-sources.mjs";
import test from "node:test";
import assert from "node:assert/strict";
import {readFile, mkdtemp, rm, writeFile} from "node:fs/promises";
import { tmpdir } from "node:os";
import { join } from "node:path";
import { execFileSync } from "node:child_process";
import { createHash } from "node:crypto";
import { fileURLToPath } from "node:url";
import createCubical from "../web/dist/cubical.mjs";
import { CubicalKernel } from "../web/cubical-kernel.mjs";
import { InstructionGraph } from "../web/cubical-instructions.mjs";
import { benchmark, benchmarkAreas, category } from "../web/benchmark-runner.mjs";
import { areaLabels, savedReport, declarationLink, repository } from "../web/benchmark-areas.mjs";
import { parse } from "../web/cubist/parser.mjs";
import { diagnosticCode } from "../web/diagnostics.mjs";
import { InstructionDriver } from "../web/cubical-instruction-driver.mjs";
import { budget } from "./timing.mjs";
import { committedSource, pinnedSources } from "../tools/benchmark-cubical.mjs";

const checkout = fileURLToPath(new URL("../", import.meta.url));

// A kernel session with its instruction graph, and a definition of tt : Unit
// admitted by Define, recorded under its name as the elaborator records one.
async function session(t) {
  const module = await createCubical(), kernel = new CubicalKernel(module), graph = new InstructionGraph(kernel);
  t.after(() => kernel.dispose());
  const define = (name, value = graph.point()) => {
    const reference = graph.judgement(graph.define(name, value)).term;
    kernel.definitions.set(name, reference);
    return reference;
  };
  return { module, kernel, graph, define, typeOf: reference => kernel.node(graph.judgement(graph.lookup(reference)).type).kind };
}

test("benchmark distinguishes invalid proofs, blocked uses, and independent checked declarations", async () => {
  const report = await benchmark({ modules: ["sample"], readSource: async name => name === "sample" ?
    "import unat; use unat; def good := 0; def bad : 0 = 1 { exact refl(0); } def dependent := bad; def independent := 2;" : sourceReader()(name) });
  assert.deepEqual(report.declarations.filter(d=>d.module === "sample").map(d => d.category), ["checked", "failed", "blocked", "checked"]);
  assert.equal(report.declarations.find(d=>d.name === "dependent").rootBlocker, "sample__bad");
  for(const row of report.declarations.filter(d=>d.module === "sample")) {
    assert.ok(Number.isSafeInteger(row.nativeCheckingSteps)&&row.nativeCheckingSteps>=0);
    assert.deepEqual(row.rewriteWork,{traversals:0,candidateVisits:0,eligibleMatches:0,
      successfulRewrites:0,premiseAttempts:0,premiseProofs:0,premiseRewriteSteps:0});
    if(row.category==="checked") {
      assert.ok(row.finalCheckArenaNodes>0);
      assert.ok(row.finalCheckArenaBytes>0);
    } else {
      assert.equal(row.finalCheckArenaNodes,null);
      assert.equal(row.finalCheckArenaBytes,null);
    }
  }
  assert.equal(report.importErrors.length, 0);
});

test("the native deadline rejects work, then recovers", async t => {
  const { module, kernel, graph } = await session(t);
  graph.point();
  // Set C's deadline directly so this exercises C, not the JS preflight guard.
  module._cb_deadline_ms(kernel.handle, .01);
  const until = performance.now() + 2;
  while (performance.now() < until) { /* let the native deadline expire */ }
  assert.throws(() => graph.unit(), /Declaration time limit exceeded/);
  module._cb_deadline_ms(kernel.handle, 0);
  assert.equal(kernel.node(graph.judgement(graph.unit()).term).kind, "Unit");
});

test("rollback discards definitions and cached reductions from a rejected attempt", async t => {
  const { module, kernel, graph, define, typeOf } = await session(t);
  const before = define("before");
  module._cb_checkpoint(kernel.handle);
  const late = define("late");
  kernel.head(late);
  module._cb_rollback(kernel.handle);
  kernel.definitions.delete("late");
  assert.throws(() => graph.lookup(late));
  assert.equal(typeOf(before), "Unit");
});

test("a timeout remains a speed failure", () => {
  assert.equal(category({ status: "checked-native-cubical" }, 1000.01, 1000), "optimize");
  assert.equal(category({ failure: "deadline", reason: "Declaration time limit exceeded." }, 1000, 1000), "optimize");
});

test("successful compaction retains definitions and translates references", async t => {
  const { module, kernel, graph, define, typeOf } = await session(t);
  module._cb_checkpoint(kernel.handle);
  for (let i = 0; i < 300; i++) kernel.term("Var", kernel.symbol(`unused${i}`));
  const reference = define("retained");
  kernel.head(reference);
  assert.equal(module._cb_commit_checkpoint(kernel.handle), 1);
  const moved = module._cb_relocated(kernel.handle, reference);
  assert.ok(moved < reference);
  kernel.definitions.set("retained", moved);
  assert.equal(kernel.node(kernel.head(moved)).kind, "Point");
  assert.equal(typeOf(moved), "Unit");
  module._cb_checkpoint(kernel.handle);
  const later = define("later", graph.lookup(moved));
  assert.equal(typeOf(later), "Unit");
});

test("benchmark reports the selected deadline and optimizations and rejects invalid deadlines", async () => {
  const optimizations = { shareSyntax: false, reuseChecks: false, compactPaths: false };
  const report = await benchmark({ modules: ["sample"], limitMs: 250, optimizations, readSource: async name => name === "sample" ? "def one := tt;" : sourceReader()(name) });
  assert.equal(report.limitMs, 250);
  assert.deepEqual(report.optimizations, optimizations);
  assert.equal(report.counts.checked, 1);
  for (const limitMs of [0, -1, NaN, Infinity]) await assert.rejects(benchmark({ limitMs }), /positive number/);
});

test("benchmark measures an area, the library, the archive or the Cubist tests, as its modules import", async () => {
  // The page names each area and finds its saved report.
  assert.deepEqual(Object.keys(benchmarkAreas), ["library", "archive", "tests"]);
  assert.deepEqual(Object.keys(areaLabels), Object.keys(benchmarkAreas));
  // The benchmark imports each of an area's modules, so each has a name an
  // import can write: none is a keyword, as a test named induction was.
  for (const [area, modules] of Object.entries(benchmarkAreas))
    for (const name of modules) assert.doesNotThrow(() => parse(`import ${name};`), `${area}: ${name}`);
  assert.deepEqual(Object.keys(benchmarkAreas).map(savedReport),
    ["benchmark-results-library.json", "benchmark-results.json", "benchmark-results-tests.json"]);
  // A Cubist test is checked from cubist-tests/, importing the library.
  const readSource = sourceReader();
  readSource.place("benchmark", "tests");
  const report = await benchmark({ area: "tests", modules: ["let_statements"], limitMs: budget(10000), readSource });
  assert.equal(report.area, "tests");
  assert.ok(report.declarations.some(d => d.module === "let_statements" && d.category === "checked"));
  await assert.rejects(benchmark({ area: "elsewhere" }), /library, archive or tests, not elsewhere/);
});

// The benchmark page links a row of a saved report to its declaration's
// source at the revision the report measured (declarationLink), not to
// today's workspace, where a declaration measured then may be gone or
// changed; and only where that source is the one measured: a saved report
// pins a module (tools/benchmark-cubical.mjs's pinnedSources) with the
// SHA-256 of the text it measured, which is the file's at the revision, and
// a report measured on a clean tree pins every module. A row of a module it
// does not pin has no link. A run in the browser opens its rows in the
// workspace.
test("every link from a saved benchmark opens the source it measured, at the revision it measured", async () => {
  for (const area of Object.keys(benchmarkAreas)) {
    const report = JSON.parse(await readFile(new URL(`../web/${savedReport(area)}`, import.meta.url), "utf8"));
    assert.ok(report.revision, `${area}: the report records its revision`);
    const modules = [...new Set(report.declarations.map(row => row.module))];
    if (!report.dirty) assert.deepEqual(modules.filter(name => !report.sources?.[name]), [], `${area}: a clean report pins every module`);
    const pinned = Object.entries(report.sources ?? {});
    // Every pinned file at that revision, read in one batch: a header, then its text.
    const batch = execFileSync("git", ["cat-file", "--batch"], { cwd: checkout, maxBuffer: 1 << 28,
      input: pinned.map(([, { path }]) => `${report.revision}:${path}\n`).join("") });
    const lines = new Map();
    for (let at = 0, i = 0; i < pinned.length; i++) {
      const [name, { path, sha256 }] = pinned[i], end = batch.indexOf(10, at), header = batch.subarray(at, end).toString();
      const size = Number(/^\w+ blob (\d+)$/.exec(header)?.[1]);
      assert.ok(Number.isInteger(size), `${area}: ${path} at ${report.revision}: ${header}`);
      const text = batch.subarray(end + 1, end + 1 + size);
      assert.equal(createHash("sha256").update(text).digest("hex"), sha256, `${area}: ${name} is pinned to the text it measured`);
      lines.set(name, text.toString().split("\n").length);
      at = end + 1 + size + 1;
    }
    for (const row of report.declarations) {
      const source = report.sources?.[row.module], label = `${area}: ${row.module}.${row.name}`;
      assert.equal(declarationLink(report, row), source ? `${repository}/blob/${report.revision}/${source.path}#L${row.line}` : null, label);
      if (source) assert.ok(row.line >= 1 && row.line <= lines.get(row.module), label);
    }
  }
  assert.equal(declarationLink({ declarations: [] }, { module: "nat", name: "nat_add", line: 3 }), "proof.html?proof=nat&name=nat_add");
});

// A report measured with working changes pins only the modules whose measured
// text is the committed one, byte for byte: a declaration added in memory to
// nat, at a line past the committed file's end, gets no link into the
// committed nat; nor does a file that is not valid UTF-8, whose byte 0xff and
// any other invalid byte both decode to U+FFFD.
test("a saved benchmark pins no source it did not measure", async t => {
  const revision = execFileSync("git", ["rev-parse", "HEAD"], { cwd: checkout, encoding: "utf8" }).trim();
  const committed = path => committedSource(revision, path, checkout);
  const nat = committed("library/nat.cubist").toString(), lists = committed("library/lists.cubist").toString();
  const edited = `${nat}\ncomputable def added_in_memory : Nat := 0;\n`;
  // A repository whose one file has the byte 0xff in a comment; the working
  // tree's 0xfe there decodes as it does.
  const scratch = await mkdtemp(join(tmpdir(), "cubist-pins-"));
  t.after(() => rm(scratch, { recursive: true, force: true }));
  // The scratch repository ignores the caller's Git: no inherited GIT_*
  // variable (GIT_DIR or GIT_INDEX_FILE would send writes elsewhere), and a
  // home of its own and no system files, so no settings, ignore or attribute
  // files, commit signing, hooks, templates or identity of theirs.
  const inherited = Object.entries(process.env).filter(([name]) => !name.startsWith("GIT_"));
  const isolated = { ...Object.fromEntries(inherited), HOME: scratch, XDG_CONFIG_HOME: scratch,
    GIT_CONFIG_NOSYSTEM: "1", GIT_ATTR_NOSYSTEM: "1",
    GIT_AUTHOR_NAME: "test", GIT_AUTHOR_EMAIL: "test@example.com",
    GIT_COMMITTER_NAME: "test", GIT_COMMITTER_EMAIL: "test@example.com" };
  const git = args => execFileSync("git", ["-c", "commit.gpgsign=false", "-c", "core.hooksPath=/dev/null", ...args],
    { cwd: scratch, encoding: "utf8", env: isolated });
  const bytes = byte => Buffer.from(`// ${byte}\ncomputable def odd : Unit := tt;\n`, "latin1");
  git(["init", "-q", "--template="]);
  await writeFile(join(scratch, "invalid.cubist"), bytes("\xff"));
  git(["add", "invalid.cubist"]);
  git(["commit", "-q", "-m", "invalid UTF-8"]);
  const scratchRevision = git(["rev-parse", "HEAD"]).trim(), invalid = bytes("\xfe").toString();
  const scratchCommitted = path => committedSource(scratchRevision, path, scratch, isolated);
  assert.equal(invalid, bytes("\xff").toString(), "both bytes decode to U+FFFD");
  assert.deepEqual(scratchCommitted("invalid.cubist"), bytes("\xff"), "the committed bytes are read back");
  assert.deepEqual(pinnedSources([{ name: "invalid", path: "invalid.cubist", text: invalid }], scratchCommitted), {});
  const sources = pinnedSources([
    { name: "nat", path: "library/nat.cubist", text: edited },
    { name: "lists", path: "library/lists.cubist", text: lists },
    { name: "uncommitted", path: "library/uncommitted.cubist", text: "computable def fresh : Unit := tt;\n" },
  ], committed);
  assert.deepEqual(Object.keys(sources), ["lists"]);
  assert.equal(sources.lists.sha256, createHash("sha256").update(committed("library/lists.cubist")).digest("hex"));
  const report = { revision, dirty: true, sources, declarations: [] }, line = edited.split("\n").length - 1;
  assert.ok(line > nat.split("\n").length - 1, "the added declaration lies past the committed file");
  assert.equal(declarationLink(report, { module: "nat", name: "added_in_memory", line }), null);
  assert.equal(declarationLink(report, { module: "uncommitted", name: "fresh", line: 1 }), null);
  assert.equal(declarationLink(report, { module: "lists", name: "List", line: 4 }), `${repository}/blob/${revision}/library/lists.cubist#L4`);
});

test("benchmark lists a failure or block its source's comment states as intended, not as one to fix", async () => {
  const body = "import unat;\ndef bad : 0 = 1 { exact refl(0); }\ndef dependent := bad;\ndef other : 0 = 1 { exact refl(0); }\n";
  const read = source => async name => name === "sample" ? source : sourceReader()(name);
  const first = await benchmark({ modules: ["sample"], readSource: read(body) });
  // Each comment as tools/inline-errors.mjs writes it: the code and the
  // reason without its position.
  const stated = name => {
    const reason = first.declarations.find(d => d.name === name).reason.replace(/ at \d+:\d+$/, "");
    return `// Error: ${diagnosticCode(reason)}: ${reason}\n`;
  };
  const commented = body.replace("def bad", `${stated("bad")}def bad`).replace("def dependent", `${stated("dependent")}def dependent`)
    .replace("def other", "// Error: E606: Type mismatch: found something else.\ndef other");
  const report = await benchmark({ modules: ["sample"], readSource: read(commented) });
  const category = name => report.declarations.find(d => d.name === name).category;
  // A failure otherwise than its comment states still needs fixing.
  assert.deepEqual(["bad", "dependent", "other"].map(category), ["intended", "intended", "failed"]);
  assert.equal(report.counts.intended, 2);
});

test("benchmark checks local simp witnesses without collecting inspector references",async()=>{
  const report=await benchmark({modules:["ergonomics_registered"],limitMs:budget(10000),
    readSource:async name=>{
      const source=await readFile(name==="ergonomics_registered"
        ? new URL("../docs/examples/proof-ergonomics/implemented/registered-simp.cubist",import.meta.url)
        : new URL(`../archive/first-library/${name}.cubist`,import.meta.url),"utf8");
      return name==="ergonomics_registered"?`${source}
        def folded(n : UNat) := n + 0;
        def twice(n : UNat) := folded(n);
        def inner(n : UNat, h : n + 0 = n) : folded(n) = n { exact h; }
        def outer(n : UNat, h : folded(n) = n) : twice(n) = n { exact h; }
        def nested(n : UNat) : twice(n) = n { simp only [outer, inner, unat_add_zero]; }
      `:source;
    }});
  assert.equal(report.counts.failed,0,JSON.stringify(report.declarations.filter(d=>d.category==="failed")));
  for(const name of ["simplified_copy","conditional_rewrite","recursive_premise","nested"])
    assert.equal(report.declarations.find(d=>d.name===name)?.category,"checked",name);
  const work=report.declarations.find(d=>d.name==="nested").rewriteWork;
  assert.ok(work.candidateVisits>0&&work.premiseAttempts>=2&&work.premiseProofs>=2);
});

test("the instruction kernel admits each declaration the benchmark counts", async () => {
  const readSource = async name => name === "sample" ? "import unat; use unat; def good := 0; def uses := good;" : sourceReader()(name);
  const report = await benchmark({ modules: ["sample"], readSource });
  for (const row of report.declarations.filter(d=>d.module === "sample")) {
    assert.equal(row.category, "checked");
    assert.ok(row.instructionJudgements > 0 && row.instructionMs >= 0, row.binding);
    // The kernel's share: the admission, and the elaborator's derivations.
    assert.ok(row.kernelMs >= row.instructionMs && row.kernelJudgements >= row.instructionJudgements, row.binding);
    assert.ok(row.elapsedMs >= row.kernelMs);
  }
  // What the instruction kernel cannot derive fails, and blocks what uses it.
  const check = InstructionDriver.prototype.check;
  InstructionDriver.prototype.check = function (value, type, context) {
    if (this.kernel.node(value).kind === "Con") throw new Error("No rule for this yet.");
    return check.call(this, value, type, context);
  };
  try {
    const failing = await benchmark({ modules: ["sample"], readSource });
    assert.deepEqual(failing.declarations.filter(d=>d.module === "sample").map(d => d.category), ["failed", "blocked"]);
    // A declaration not admitted still has the derivations it needed.
    assert.ok(failing.declarations.filter(d=>d.module === "sample").every(d => d.instructionMs === null && d.kernelMs >= 0 && d.kernelJudgements >= 0));
    assert.match(failing.declarations.find(d=>d.name === "good").reason, /^Instruction kernel: No rule for this yet/);
    assert.equal(failing.declarations.find(d=>d.name === "uses").rootBlocker, "sample__good");
  } finally { InstructionDriver.prototype.check = check; }
});


test("benchmark shares source contracts without hiding invalid contracts or unrelated failures",async()=>{
  const sources={valid:"# test(refusal) # expect_error(E606) def bad : Void := tt;",
    invalid:"# test(wrong_contract) # expect_error(E343) def bad : Void := tt;",
    assumption:"# test(assumption) # expect_axioms([]) def x := axiom Unit;",
    unrelated:"def bad : Void := tt;"};
  const report=await benchmark({area:"tests",modules:Object.keys(sources),limitMs:budget(10000),readSource:async name=>sources[name]});
  assert.deepEqual(report.declarations.map(row=>[row.module,row.category]),
    [["valid","intended"],["invalid","failed"],["assumption","checked"],["unrelated","failed"]]);
  assert.ok(report.testFailures.some(message=>message.startsWith("wrong_contract:")));
  assert.ok(report.testFailures.some(message=>message.startsWith("assumption:")));
  assert.ok(!report.testFailures.some(message=>message.startsWith("refusal:")));
  const ordinary=await benchmark({area:"library",modules:["valid"],readSource:async()=>sources.valid});
  assert.equal(ordinary.declarations.length,0);
  assert.match(ordinary.importErrors[0].reason,/explicit test mode/);
});


test("benchmark resource failures cannot become expected refusals or semantic contract failures",async()=>{
  const report=await benchmark({area:"tests",modules:["timed"],limitMs:0.000001,
    readSource:async()=>"# test(timed) # expect_error(E629) def value : Unit := tt;"});
  assert.equal(report.declarations[0].category,"optimize");
  assert.equal(report.counts.intended,0);
  assert.equal(report.testFailures,undefined);
});
