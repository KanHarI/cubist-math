#!/usr/bin/env node
// The runtime evaluation baseline (EVAL0 of
// docs/roadmaps/runtime-evaluation-roadmap.md): what evaluating the fixed
// archive workloads costs today, phase by phase, with failures counted as
// well as successes.
//   node tools/evaluation-baseline.mjs [--samples=N] [--warm=N] [--only=ID,…] [--no-depth] [--write]
// Each sample of a workload is a new Node process: it loads the kernel,
// runs the workload's setup entries (its imports) and then its entry once,
// cold, and --warm more times in the same session. Entries run as the CLI
// REPL runs them (web/repl-session.mjs). One more process times the cold
// entry with no phase observed, and another, unless --no-depth, measures
// the syntax depth its normalizations, comparisons and checks reach, its
// times discarded. The report goes to
// build/evaluation-baseline.json; --write, over every workload, records it
// in tests/fixtures/evaluation-baseline.json, whose outcomes and counters
// tests/evaluation-baseline.test.mjs keeps in agreement with the code.
//
// Counters are deterministic: the kernel's work (cc_kernel_work), the
// arena's growth and each phase's calls and failures. A workload whose cold
// samples disagree on them is reported as not deterministic. Times, memory
// and the warm runs are one machine's observations, never test thresholds.
//
// The "scratch" series runs the versioned closure experiment
// (tools/closure-evaluation-experiment.mjs) on the same checked definitions.
// Its results are untrusted values of a demanded natural, not normal forms,
// and are reported apart from the kernel series.
import { spawnSync, execFileSync } from "node:child_process";
import { readFileSync, writeFileSync, mkdirSync } from "node:fs";
import { createHash } from "node:crypto";
import os from "node:os";
import { fileURLToPath, pathToFileURL } from "node:url";
import createCubical from "../web/dist/cubical.mjs";
import { CubicalProgram } from "../web/cubical-program.mjs";
import { ReplSession } from "../web/repl-session.mjs";
import { Translator } from "../web/translator/translate.mjs";
import { sourceReader } from "./module-sources.mjs";
import { assertFreshBuild } from "./build-stamp.mjs";
import { closureEvaluator } from "./closure-evaluation-experiment.mjs";

const root = new URL("../", import.meta.url);
export const fixture = new URL("tests/fixtures/evaluation-baseline.json", root);
// Bumped when a workload, a phase or the report's meaning changes: a
// recorded baseline of another version is not comparable.
export const version = 2;

const euclid = "import euclid; use nat;", circle = "import circle; use nat;";
// The archived Euclid construction and its prerequisites stay fixed for
// evaluator comparisons (archive/first-library/euclid.cubist, primes.cubist):
// a change to their algorithm starts a separate series.
export const workloads = [
  // Full results: the REPL checks the normal form against itself, print does not.
  { id: "euclid-3", setup: euclid, entry: "evaluate euclid(3);" },
  { id: "euclid-3-print", setup: euclid, entry: "print(evaluate(euclid(3)));" },
  { id: "euclid-4", setup: euclid, entry: "evaluate euclid(4);" },
  // An expected-value pattern matches the full normal form: its hole saves nothing.
  { id: "euclid-4-pattern", setup: euclid, entry: "evaluate euclid(4) expecting (5, _);" },
  // Prime projections.
  { id: "euclid-3-prime", setup: euclid, entry: "evaluate euclid(3).1;" },
  { id: "euclid-3-prime-expected", setup: euclid, entry: "evaluate euclid(3).1 expecting 7;" },
  { id: "euclid-4-prime", setup: euclid, entry: "evaluate euclid(4).1;" },
  { id: "euclid-4-prime-print", setup: euclid, entry: "print(evaluate(euclid(4).1));" },
  { id: "euclid-5-prime", setup: euclid, entry: "evaluate euclid(5).1;" },
  // Factorial, the construction's growth factor.
  { id: "factorial-4", setup: euclid, entry: "evaluate factorial(4);" },
  { id: "factorial-5-print", setup: euclid, entry: "print(evaluate(factorial(5)));" },
  // Divisibility decisions: whether 3, 4 and 5 divide 6, 6 and 121.
  { id: "divides-3-6", setup: euclid, entry: "evaluate nontrivial_divisibility_decidable(1, 6);" },
  { id: "divides-4-6", setup: euclid, entry: "evaluate nontrivial_divisibility_decidable(2, 6);" },
  { id: "divides-5-121", setup: euclid, entry: "evaluate nontrivial_divisibility_decidable(3, 121);" },
  // Ordinary data recursion, and the syntax depth of a unary result.
  { id: "multiply-12-12", setup: euclid, entry: "evaluate 12 * 12;" },
  { id: "multiply-2-254", setup: euclid, entry: "evaluate 2 * 254;" },
  { id: "multiply-2-255", setup: euclid, entry: "evaluate 2 * 255;" },
  { id: "multiply-2-255-print", setup: euclid, entry: "print(evaluate(2 * 255));" },
  { id: "multiply-2-256-print", setup: euclid, entry: "print(evaluate(2 * 256));" },
  // Cubical terms (docs/examples/hott-automation/canonicity.cubist):
  // transport along a closed path, and winding numbers through Glue and the
  // circle's declared pushout.
  { id: "transport-closed", setup: circle, entry: "evaluate transport(fun (n : Nat) => Nat, 3 + 0, 3, nat_add_zero(3), 5);" },
  { id: "winding-2", setup: circle, entry: "evaluate winding(concatenate(U1, S1, base, base, base, loop, loop));" },
  { id: "winding-minus-2", setup: circle, entry: "evaluate winding(integer_loop(negative(2)));" },
  // The closure experiment's prime projections, the roadmap's preliminary
  // series, on the definition `probe := euclid(n)` the kernel checked.
  ...[3, 4, 5, 6].map(n => ({ id: `scratch-euclid-${n}-prime`, series: "scratch", setup: euclid, entry: `def probe := euclid(${n});` })),
];

// What each workload's result is, and what it promises.
export const contracts = {
  repl: "REPL evaluate: the full normal form, checked equal to itself (evaluate e expecting e)",
  print: "print(evaluate(e)): the full normal form, printed",
  expected: "evaluate e expecting v: the full normal form, compared with v's",
  pattern: "evaluate e expecting p, p with holes: the full normal form, matched part by part",
  scratch: "closure experiment: the demanded natural only; untrusted, certifies nothing",
};
export const contractOf = workload => workload.series === "scratch" ? "scratch"
  : /^print\s*\(/.test(workload.entry) ? "print"
  : !/\bexpecting\b/.test(workload.entry) ? "repl"
  : /\bexpecting\b[\s\S]*\b_\b/.test(workload.entry) ? "pattern" : "expected";

// Where an entry's time and work go. Each phase is a boundary of the code
// that runs it, observed by wrapping that method of the session's program;
// a call nested in another phase belongs to the outer one, unless named
// here, and a phase's figures are its own, without those nested in it.
export const phases = {
  elaborate: "Translator.term: elaborating source terms, with the kernel queries elaboration asks",
  check: "checker.checkSyntax, inside verify: checking the elaborated term",
  normalize: "kernel.normalize, wherever it is asked: the kernel's normalization, whose result is syntax (no separate readback)",
  decode: "checker.syntax.decode of a normal form, inside verify: kernel syntax into terms",
  inventory: "checker.verify's own work: the closedness, assumption and kernel-extension inventory",
  compare: "checker.equal, outside other phases: comparing types, normal forms and patterns' parts",
  render: "checker.displayText, outside other phases: printing a value or message",
  other: "the rest of the entry: parsing, module and session bookkeeping, transactions",
  execute: "scratch: forcing the definition to a pair",
  readback: "scratch: forcing the pair's first component to a number; laziness defers most computation here",
};

const workFields = ["instructions", "rejected", "instructionSteps", "queries", "failedQueries", "querySteps", "exhausted", "deadlines"];
// A reading of the clock, the kernel's cumulative work and the arena.
const reading = kernel => {
  const work = kernel.work(), arena = kernel.arena();
  return { ms: performance.now(), ...Object.fromEntries(workFields.map(field => [field, work[field]])), nodes: arena.nodes, bytes: arena.bytes };
};
const keys = ["ms", ...workFields, "nodes"];
const minus = (a, b) => Object.fromEntries(keys.map(key => [key, a[key] - b[key]]));
const plus = (a, b) => Object.fromEntries(keys.map(key => [key, a[key] + b[key]]));
const zero = Object.fromEntries(keys.map(key => [key, 0]));

// The depth of each node an operation allocated, and the deepest chain: the
// kernel refuses syntax deeper than 512 (K344, kernel/src/term_store.c).
function syntaxDepth(kernel, first, last) {
  const depths = new Map(), via = new Map();
  const depth = id => {
    if (!id) return 0;
    if (depths.has(id)) return depths.get(id);
    let most = 0, through = 0;
    for (const child of kernel.node(id).children) { const d = depth(child); if (d > most) { most = d; through = child; } }
    depths.set(id, most + 1); via.set(id, through);
    return most + 1;
  };
  let deepest = 0;
  const kinds = new Map();
  for (let id = first; id <= last; id++) {
    if (depth(id) > depth(deepest)) deepest = id;
    kinds.set(kernel.node(id).kind, (kinds.get(kernel.node(id).kind) ?? 0) + 1);
  }
  // Its kinds from the root, each with the child it continues through, runs of one counted.
  const chain = [];
  for (let id = deepest; id; id = via.get(id)) {
    const node = kernel.node(id), step = `${node.kind}${via.get(id) ? `.${node.children.indexOf(via.get(id))}` : ""}`;
    if (chain.at(-1)?.step === step) chain.at(-1).count++; else chain.push({ step, count: 1 });
  }
  return { depth: depth(deepest), allocated: last - first + 1, chain: chain.slice(0, 16).map(({ step, count }) => count > 1 ? `${step} ×${count}` : step),
    kinds: Object.fromEntries([...kinds].sort((a, b) => b[1] - a[1]).slice(0, 8)) };
}

// A digest of a normal form as checker.verify decodes it
// (web/cubical-syntax.mjs): the whole term, where a display is cut at 1000
// characters. Bound variables and dimensions are numbered by binding depth,
// so renaming them leaves it unchanged, and a formula's clauses are sorted.
const termBinders = new Set(["Pi", "Lam", "Sigma", "LPi", "LLam"]);
// The fields a dimension binder binds; a composition's system binds its
// tubes' terms, not their faces.
const dimensionBinders = { Path: ["family"], PLam: ["family", "body"], Trans: ["family"], Comp: ["family", "system"], HComp: ["system"] };
export function normalDigest(term) {
  const hash = createHash("sha256"), parts = [], terms = { names: new Map(), depth: 0 }, dims = { names: new Map(), depth: 0 };
  const write = part => { parts.push(part); if (parts.length >= 65536) hash.update(`${parts.splice(0).join("\0")}\0`); };
  // `visit` under a binder of `name`, numbered by the binders of its sort around it.
  const under = (scope, name, visit) => {
    const had = scope.names.has(name), outer = scope.names.get(name);
    scope.names.set(name, scope.depth++);
    visit();
    scope.depth--;
    if (had) scope.names.set(name, outer); else scope.names.delete(name);
  };
  const named = (scope, name) => scope.names.has(name) ? `#${scope.names.get(name)}` : `free ${JSON.stringify(name)}`;
  const literal = text => { const at = text.lastIndexOf(":"); return `${named(dims, text.slice(0, at))}:${text.slice(at + 1)}`; };
  const walk = value => {
    if (value === null || typeof value !== "object") return write(JSON.stringify(value) ?? "undefined");
    if (Array.isArray(value)) {
      // A formula: clauses of literals such as `d3:1`.
      if (value.length && value.every(Array.isArray))
        return write(`formula ${value.map(clause => clause.map(literal).sort().join("&")).sort().join("|")}`);
      write("[");
      value.forEach(walk);
      return write("]");
    }
    // A level variable decodes as a term variable does.
    if (value.tag === "Var") return write(`Var ${named(terms, value.name)}`);
    const binds = termBinders.has(value.tag) ? ["body"] : dimensionBinders[value.tag] ?? [];
    const binder = termBinders.has(value.tag) ? "name" : binds.length ? "dim" : null;
    write(`{${value.tag ?? ""}`);
    for (const [key, item] of Object.entries(value)) {
      if (key === "tag" || key === binder) continue;
      write(key);
      if (!binds.includes(key)) walk(item);
      else if (binder === "name") under(terms, value.name, () => walk(item));
      else if (key !== "system") under(dims, value.dim, () => walk(item));
      else {
        write("[");
        for (const tube of item) { write("face"); walk(tube.face); write("term"); under(dims, value.dim, () => walk(tube.term)); }
        write("]");
      }
    }
    write("}");
  };
  walk(term);
  hash.update(parts.join("\0"));
  return hash.digest("hex").slice(0, 16);
}

// Observe a program's phases while `run` runs: each phase's own calls,
// failures, time, kernel work and arena growth, the run's peak arena, and
// the normal form of the term it evaluated: the first verified at the
// entry's top level, before any expected value or pattern.
async function profiled(program, run, { depth = false } = {}) {
  const kernel = program.kernel, checker = program.checker, totals = {}, stack = [], restore = [], depths = {};
  let peakNodes = 0, peakBytes = 0, normal = null, evaluated = null;
  const read = () => { const r = reading(kernel); peakNodes = Math.max(peakNodes, r.nodes); peakBytes = Math.max(peakBytes, r.bytes); return r; };
  const open = name => { const frame = { name, start: read(), inner: zero }; stack.push(frame); return frame; };
  const close = (frame, failed) => {
    const end = read(), inclusive = minus(end, frame.start);
    stack.pop();
    const total = totals[frame.name] ??= { calls: 0, failures: 0, ...zero };
    Object.assign(total, plus(total, minus(inclusive, frame.inner)), { calls: total.calls + 1, failures: total.failures + (failed ? 1 : 0) });
    if (stack.length) stack.at(-1).inner = plus(stack.at(-1).inner, inclusive);
    // Analysed before a rollback could free the nodes, outside any timing kept.
    if (depth && ["normalize", "compare", "check"].includes(frame.name) && end.nodes > frame.start.nodes) {
      const found = syntaxDepth(kernel, frame.start.nodes + 1, end.nodes);
      if (!depths[frame.name] || found.depth > depths[frame.name].depth) depths[frame.name] = found;
    }
  };
  const top = () => stack.at(-1)?.name;
  // A missing boundary is an error: the phases would silently go elsewhere.
  const wrap = (owner, method, name, opens, after = () => {}) => {
    const original = owner[method];
    if (typeof original !== "function") throw new Error(`The phase boundary ${method} (${name}) no longer exists.`);
    const own = Object.hasOwn(owner, method);
    owner[method] = function (...args) {
      if (!opens(...args)) return original.apply(this, args);
      const frame = open(name);
      let result;
      try { result = original.apply(this, args); }
      catch (error) { close(frame, true); throw error; }
      close(frame, false);
      after(result);
      return result;
    };
    restore.push(() => { if (own) owner[method] = original; else delete owner[method]; });
  };
  wrap(Translator.prototype, "term", "elaborate", () => top() === "other");
  wrap(checker, "verify", "inventory", () => true, result => { if (!evaluated && top() === "other") evaluated = result.normal; });
  wrap(checker, "checkSyntax", "check", () => top() === "inventory");
  wrap(kernel, "normalize", "normalize", () => top() !== "normalize", result => { normal = result; });
  wrap(checker.syntax, "decode", "decode", id => top() === "inventory" && id === normal);
  wrap(checker, "equal", "compare", () => top() === "other");
  wrap(checker, "displayText", "render", () => top() === "other");
  const frame = open("other");
  try { return { result: await run(), ...finish() }; }
  catch (error) { return { error, ...finish() }; }
  function finish() {
    if (stack.at(-1) === frame) close(frame, false);
    for (const undo of restore.reverse()) undo();
    restore.length = 0;
    const entry = Object.values(totals).reduce((sum, total) => plus(sum, total), zero);
    return { totals, entry, peakNodes, peakBytes, evaluated, ...(depth ? { depths } : {}) };
  }
}

// An outcome: a value or an error, with its code; its text, a preview past
// 160 characters, with the whole text's length and hash; and the digest of
// the normal form evaluated, when the entry reached one. The REPL displays
// at most 1000 characters of a value, so only the digest covers a large one.
const outcomeFor = (failed, text, normal = null) => ({ status: failed ? "error" : "value",
  ...(failed ? { code: /^([EKW]\d+):/.exec(text)?.[1] ?? null } : {}),
  text: text.length > 160 ? `${text.slice(0, 159)}…` : text, length: text.length,
  sha256: createHash("sha256").update(text).digest("hex").slice(0, 16), ...(normal ? { normal: normalDigest(normal) } : {}) });
// What an entry gave: its values, or its first error.
const outcomeOf = (results, normal = null) => {
  const error = results.find(result => result.kind === "error");
  return outcomeFor(Boolean(error), error ? error.text : results.map(result => result.text).join("\n"), normal);
};
const rounded = run => Object.fromEntries(Object.entries(run).map(([key, value]) =>
  [key, typeof value === "number" && key === "ms" ? Number(value.toFixed(3)) : value]));

// One run of an entry in the session: its outcome, and its phases, or the
// scratch evaluator's.
async function runEntry(program, session, workload, { depth = false } = {}) {
  const measured = await profiled(program, () => session.run(workload.entry), { depth });
  if (measured.error) throw measured.error;
  const run = { outcome: outcomeOf(measured.result, measured.evaluated), phases: Object.fromEntries(Object.entries(measured.totals).map(([name, total]) => [name, rounded(total)])),
    entry: rounded(measured.entry), peakNodes: measured.peakNodes, peakBytes: measured.peakBytes, ...(depth ? { depths: measured.depths } : {}) };
  if (workload.series !== "scratch") return run;
  if (run.outcome.status === "error") throw new Error(`${workload.id}: ${run.outcome.text}`);
  // The definition the entry checked, evaluated by the experiment.
  const reference = program.kernel.definitions.get(`repl_${session.count}__probe`);
  if (!reference) throw new Error(`${workload.id}: the entry defined no probe.`);
  const evaluator = closureEvaluator(program.kernel), before = reading(program.kernel);
  const scratch = { definition: run };
  let pair, value, failure = null, stage = "execute";
  const started = performance.now();
  try {
    pair = evaluator.force(evaluator.delay(reference));
    if (pair.tag !== "Pair") throw new Error("Expected result pair");
    scratch.executeMs = performance.now() - started;
    stage = "readback";
    value = evaluator.natural(pair.first);
  } catch (error) { failure = error; }
  const end = reading(program.kernel), ms = end.ms - started;
  scratch.executeMs ??= ms;
  Object.assign(scratch, { readbackMs: ms - scratch.executeMs, stage,
    outcome: failure ? outcomeFor(true, failure.message) : outcomeFor(false, String(value)),
    stats: { ...evaluator.stats }, kernel: rounded(minus(end, before)) });
  scratch.executeMs = Number(scratch.executeMs.toFixed(3)); scratch.readbackMs = Number(scratch.readbackMs.toFixed(3));
  return scratch;
}

// A workload in this process: a new program over `module`, its setup, then
// the entry once cold and `warm` times more. Unobserved, the cold entry is
// only timed, with no phase wrapped: the observation's own cost.
export async function measureWorkload(module, workload, { warm = 0, depth = false, observe = true } = {}) {
  const program = new CubicalProgram(module, sourceReader());
  try {
    const session = new ReplSession(program);
    const started = performance.now(), before = reading(program.kernel);
    const setup = await session.run(workload.setup);
    const failed = setup.find(result => result.kind === "error");
    if (failed) throw new Error(`${workload.id}: its setup failed: ${failed.text}`);
    const imported = rounded({ ...minus(reading(program.kernel), before), ms: performance.now() - started });
    if (!observe) {
      const start = performance.now(), outcome = outcomeOf(await session.run(workload.entry));
      return { import: imported, cold: { outcome, ms: Number((performance.now() - start).toFixed(3)) } };
    }
    const cold = await runEntry(program, session, workload, { depth });
    const warmRuns = [];
    for (let i = 0; i < warm; i++) warmRuns.push(await runEntry(program, session, workload));
    return { import: imported, cold, warm: warmRuns };
  } finally { program.dispose(); }
}

// Figures without their time.
const strip = figures => Object.fromEntries(Object.entries(figures).filter(([key]) => key !== "ms"));
// A run's deterministic part: everything but times and the depth analysis.
// Where the experiment overflows the host's stack depends on how far the JIT
// has compiled it, so a failed scratch run's counts are observations.
export function deterministic(run) {
  if (run.definition) return { definition: deterministic(run.definition), outcome: run.outcome, stage: run.stage,
    ...(run.outcome.status === "value" ? { stats: run.stats, kernel: strip(run.kernel) } : {}) };
  return { outcome: run.outcome, entry: strip(run.entry), peakNodes: run.peakNodes,
    phases: Object.fromEntries(Object.entries(run.phases).map(([name, figures]) => [name, strip(figures)])) };
}

const statistics = values => {
  const sorted = values.filter(value => typeof value === "number").sort((a, b) => a - b);
  if (!sorted.length) return null;
  const middle = sorted.length >> 1, median = sorted.length % 2 ? sorted[middle] : (sorted[middle - 1] + sorted[middle]) / 2;
  return { median: Number(median.toFixed(3)), min: sorted[0], max: sorted.at(-1), samples: sorted.length };
};

// One sample in a new process, so that each is cold and has its own peak memory.
function child(workload, { warm = 0, depth = false, observe = true }) {
  const script = fileURLToPath(import.meta.url);
  const run = spawnSync(process.execPath, [script, `--child=${workload.id}`, `--warm=${warm}`, ...(depth ? ["--depth"] : []), ...(observe ? [] : ["--unobserved"])],
    { encoding: "utf8", maxBuffer: 1 << 28 });
  if (run.status !== 0) throw new Error(`${workload.id}: the sample process failed:\n${run.stderr}`);
  return JSON.parse(run.stdout);
}

// Figures as the report shows them: no time, and no counter that is zero.
const sparse = figures => Object.fromEntries(Object.entries(figures).filter(([key, value]) => key !== "ms" && (value !== 0 || key === "calls")));
const median = values => statistics(values)?.median ?? null;

// Summarize a workload's samples: their common outcome and counters, and
// the spread of their times. A phase's line holds its counters, sparse, and
// its median times cold and warm.
export function summarize(workload, samples, { depthSample = null, unobserved = null } = {}) {
  const cold = samples.map(sample => sample.cold), warm = samples.flatMap(sample => sample.warm), first = cold[0];
  const variants = new Set(cold.map(run => JSON.stringify(deterministic(run))));
  const series = workload.series ?? "kernel";
  const summary = { id: workload.id, series, contract: contractOf(workload), setup: workload.setup, entry: workload.entry,
    outcome: first.outcome, deterministic: variants.size === 1,
    import: { ...sparse(samples[0].import), ms: statistics(samples.map(sample => sample.import.ms)) } };
  if (series === "scratch") {
    Object.assign(summary, { stage: first.stage, stats: first.stats, kernel: sparse(first.kernel),
      definition: { ...sparse(first.definition.entry), ms: statistics(cold.map(run => run.definition.entry.ms)) },
      ms: { execute: statistics(cold.map(run => run.executeMs)), readback: statistics(cold.map(run => run.readbackMs)),
        warmExecute: median(warm.map(run => run.executeMs)), warmReadback: median(warm.map(run => run.readbackMs)) } });
  } else {
    if (unobserved && unobserved.cold.outcome.sha256 !== first.outcome.sha256) throw new Error(`${workload.id}: unobserved, the entry gave another outcome.`);
    Object.assign(summary, {
      total: { ...sparse(first.entry), peakNodes: first.peakNodes, peakBytes: first.peakBytes },
      ms: { cold: statistics(cold.map(run => run.entry.ms)), unobserved: unobserved?.cold.ms ?? null,
        warm: statistics(warm.map(run => run.entry.ms)) },
      phases: Object.fromEntries(Object.keys(first.phases).map(name => [name, { ...sparse(first.phases[name]),
        coldMs: median(cold.map(run => run.phases[name]?.ms ?? 0)), warmMs: median(warm.map(run => run.phases[name]?.ms ?? 0)) }])),
      ...(depthSample ? { depth: depthSample.cold.depths ?? {} } : {}) });
  }
  summary.maxRssMiB = statistics(samples.map(sample => sample.maxRssMiB));
  return summary;
}

// JSON with each record of scalars on one line, when it fits: a report to read.
export function reportText(value, indent = "") {
  const flat = JSON.stringify(value);
  if (value === null || typeof value !== "object" || flat.length <= 150 - indent.length
    && Object.values(value).every(item => item === null || typeof item !== "object" || JSON.stringify(item).length <= 80)) return flat;
  const inner = `${indent}  `, items = Array.isArray(value) ? value.map(item => reportText(item, inner))
    : Object.entries(value).map(([key, item]) => `${JSON.stringify(key)}: ${reportText(item, inner)}`);
  const [open, close] = Array.isArray(value) ? ["[", "]"] : ["{", "}"];
  return items.length ? `${open}\n${items.map(item => `${inner}${item}`).join(",\n")}\n${indent}${close}` : `${open}${close}`;
}

const git = args => { try { return execFileSync("git", args, { cwd: fileURLToPath(root), encoding: "utf8" }).trim(); } catch { return null; } };

if (process.argv[1] && import.meta.url === pathToFileURL(process.argv[1]).href) {
  // A stale WASM kernel would run code it does not contain.
  assertFreshBuild();
  const args = process.argv.slice(2), option = name => args.find(arg => arg.startsWith(`--${name}=`))?.slice(name.length + 3);
  const known = /^--(samples=\d+|warm=\d+|only=.+|child=.+|depth|no-depth|unobserved|write)$/;
  for (const arg of args) if (!known.test(arg)) throw new Error(`Unknown option: ${arg}`);
  const byId = id => workloads.find(workload => workload.id === id) ?? (() => { throw new Error(`Unknown workload: ${id}`); })();
  if (option("child")) {
    // A sample: the result as JSON on stdout, with this process's peak memory.
    const sample = await measureWorkload(await createCubical(), byId(option("child")),
      { warm: Number(option("warm") ?? 0), depth: args.includes("--depth"), observe: !args.includes("--unobserved") });
    sample.maxRssMiB = Number((process.resourceUsage().maxRSS / 1024).toFixed(1));
    process.stdout.write(JSON.stringify(sample));
  } else {
    const samples = Number(option("samples") ?? 5), warm = Number(option("warm") ?? 3);
    const selected = option("only") ? option("only").split(",").map(byId) : workloads;
    if (args.includes("--write") && selected !== workloads) throw new Error("--write records every workload: drop --only.");
    if (samples < 1) throw new Error("--samples must be at least 1.");
    const stamp = JSON.parse(readFileSync(new URL("web/dist/build-stamp.json", root), "utf8")).kernel;
    const report = {
      version, generatedAt: new Date().toISOString(),
      revision: git(["rev-parse", "HEAD"]), modified: git(["status", "--porcelain", "--untracked-files=no"]) !== "",
      build: { kernelSources: stamp.sources, kernelOutputs: stamp.outputs },
      machine: { node: process.version, platform: `${os.platform()} ${os.arch()}`, cpu: os.cpus()[0]?.model ?? null, cpus: os.cpus().length },
      settings: { samples, warm, depth: !args.includes("--no-depth"), optimizations: "the CLI's defaults", stack: "Node's default" },
      method: "Each sample is a new Node process that loads the kernel, runs the workload's setup entries in a new REPL session "
        + "(web/repl-session.mjs, as the CLI does) and its entry once cold, then the warm runs in the same session. A further "
        + "process times the cold entry with no phase observed, for the observation's cost. An outcome's text is a preview past 160 "
        + "characters, with the whole text's length and hash; the REPL displays at most 1000 characters of a value, so a kernel "
        + "outcome also digests the whole normal form evaluated, its bound variables and dimensions numbered by binding depth. "
        + "Phases are observed by wrapping the methods named in `phases`; a phase's figures exclude the "
        + "phases nested in it. Counters are the kernel's cumulative work and the arena's net growth, compared across the cold "
        + "samples; times are medians over samples on this machine, and include the observation's wrappers. Failed entries count "
        + "the work and time spent before they failed. The depth sample repeats the cold entry, measuring the syntax depth "
        + "of the nodes each normalization, comparison and check allocated, its times discarded.",
      contracts, phases, workloads: [],
    };
    for (const workload of selected) {
      const runs = Array.from({ length: samples }, () => child(workload, { warm }));
      const kernelSeries = workload.series !== "scratch";
      const summary = summarize(workload, runs, { depthSample: report.settings.depth && kernelSeries ? child(workload, { depth: true }) : null,
        unobserved: kernelSeries ? child(workload, { observe: false }) : null });
      report.workloads.push(summary);
      const ms = summary.ms.cold?.median ?? summary.ms.execute.median + summary.ms.readback.median;
      console.log(`${workload.id.padEnd(26)} ${summary.outcome.status.padEnd(5)} ${(summary.outcome.code ?? summary.outcome.text.slice(0, 24)).padEnd(24)}`
        + ` ${String(summary.phases?.normalize?.calls ?? "-").padStart(2)} nf  ${ms.toFixed(1).padStart(9)} ms`
        + `${summary.deterministic ? "" : "  NOT DETERMINISTIC"}`);
    }
    mkdirSync(new URL("build/", root), { recursive: true });
    writeFileSync(new URL("build/evaluation-baseline.json", root), `${reportText(report)}\n`);
    if (args.includes("--write")) writeFileSync(fixture, `${reportText(report)}\n`);
    if (report.workloads.some(workload => !workload.deterministic)) process.exitCode = 1;
  }
}
