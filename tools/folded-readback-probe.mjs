// M3 of typed readback (docs/roadmaps/runtime/typed-readback.md, section 9):
// a printed normal form, `print(evaluate(!!e));` or the REPL's
// `evaluate !!e;`, computed as W3 would compute it, against the kernel's own.
//   kernel   the kernel's folded normal form of e, as today;
//   runtime  the runtime's data, walked as the value form walks it, by a
//            query that keeps origins; R(root), read back with them; and
//            the kernel's folded normal form of R(root). A value the
//            runtime cannot compute, a demand it refuses, a stop at its
//            limits or a readback past the kernel's syntax depth (K344),
//            keeps today's path, whose work the sample then includes.
// Each sample, one print by one path, is a fresh process: the print's
// setup is checked first, and the print runs in a declaration transaction
// of its own, which finds the kernel's caches cleared by the end of the
// one before. The workloads are the note's and the contracts' `!!_` terms,
// each as a REPL entry, and every printed `!!` of the Cubist test modules
// and of the language reference's examples, in its own module or session.
// Ticks are the kernel's query steps (cc_kernel_work), steps the runtime's;
// times and the process's peak memory are one machine's observations.
// Neither path's answer is evidence.
//   node tools/folded-readback-probe.mjs               every workload, both paths
//   node tools/folded-readback-probe.mjs NAME[,NAME] [kernel|runtime]
import { execFileSync } from "node:child_process";
import { readFileSync, readdirSync } from "node:fs";
import { createHash } from "node:crypto";
import { fileURLToPath } from "node:url";
import createCubical from "../web/dist/cubical.mjs";
import { CubicalProgram } from "../web/cubical-program.mjs";
import { ReplSession, replTranscript } from "../web/repl-session.mjs";
import { Translator } from "../web/translator/translate.mjs";
import { valueForm } from "../web/translator/evaluation.mjs";
import { RuntimeQuery, RuntimeError } from "../web/cubical-runtime.mjs";
import { KernelError } from "../web/cubical-kernel.mjs";
import { cubistTestModules } from "../web/cubist/modules.mjs";
import { parse } from "../web/cubist/parser.mjs";
import { checkedModule } from "./inline-errors.mjs";
import { sourceReader } from "./module-sources.mjs";
import { referenceExamples } from "../tests/reference-pages.mjs";
import { assertFreshBuild } from "./build-stamp.mjs";

const euclid = "import euclid; use nat;", rationals = "import binary_rationals; use binary_rationals;";
const integers = "import binary_integers; use binary_integers;", numbers = "import rationals; use nat;";
const counting = "import unat; use unat; def count_into(n, total : UNat) : UNat := match n { zero => total; succ(k) => count_into(k, succ(total)); };";
const wide = "340282366920938463463374607431768211455";
// The note's workloads, the library Euclid in place of the archive's, and
// the terms the contracts check under `!!_` (tests/fixtures/contracts/).
const entries = {
  "euclid-0": [euclid, "euclid(0)"], "euclid-3": [euclid, "euclid(3)"], "euclid-4": [euclid, "euclid(4)"],
  "euclid-5": [euclid, "euclid(5)"], "euclid-6": [euclid, "euclid(6)"], "euclid-7": [euclid, "euclid(7)"],
  "euclid-10": [euclid, "euclid(10)"],
  "count-into-508": [counting, "count_into(2 * 254, 0)"], "count-into-510": [counting, "count_into(2 * 255, 0)"],
  "binary-factorial-40": ["import nat; use nat;", "factorial(40)"],
  "binary-product": ["import nat; use nat;", "12345678901234567890 * 98765432109876543210"],
  "binary-rational": [rationals, "2/3 + 1/6"],
  "binary-rational-wide-inverse": [rationals, `bq_inv(-${wide}/18446744073709551615)`],
  "binary-rational-distinct": [rationals, "bq_decide(1/2, 2/3)"],
  "binary-rational-equal": [rationals, "bq_decide(1/2 + 1/3, 5/6)"],
  "binary-integer-wide-product": [integers, `${wide} * ${wide}`],
  "binary-integer-distinct": [integers, `bint_decide(${wide}, -1)`],
  "contract-euclid-5-certificates": [euclid, "euclid(5).2"],
  "contract-divmod-certificate": [`${euclid} computable def positive_bits(n : Nat) : BPositive := match n { b_zero => bp_one; b_positive(p) => p; };`,
    "bnat_divmod_correct(121, positive_bits(11))"],
  "contract-least-divisor-121": [euclid, "least_divisor(121, tt).2.2.1"],
  "contract-bq-wide-fraction": [rationals, `typed(BQ, 18446744073709551615/${wide})`],
  "contract-bq-wide-decimal": [rationals, "typed(BQ, 18446744073709551615.125)"],
  "contract-integers-wide": [numbers, `integers.(-${wide})`],
  "contract-rat-constructor": [numbers, "rat(int(2, 0), 2)"],
  "contract-rationals-wide-fraction": [numbers, `rationals.(18446744073709551615/${wide})`],
  "contract-rat-inv-wide": [numbers, `rat_inv(rationals.(-${wide}/18446744073709551615))`],
};
const root = fileURLToPath(new URL("..", import.meta.url));
const printsFolded = source => (parse(source).directives ?? []).filter(d => d.kind === "print" && d.show === "evaluate" && d.mark === "!!").length;
// Each printed !! of the corpora, by its module or example and its place
// among the !! prints there.
const corpus = [
  ...cubistTestModules.flatMap(name => Array.from({ length: printsFolded(readFileSync(`${root}cubist-tests/${name}.cubist`, "utf8")) },
    (_, k) => `cubist-tests/${name}#${k}`)),
  ...readdirSync(`${root}web/reference`).filter(file => file.endsWith(".html")).sort().flatMap(file =>
    referenceExamples(`reference/${file}`, readFileSync(`${root}web/reference/${file}`, "utf8")).flatMap(example =>
      Array.from(example.text.matchAll(/evaluate\s*\(?\s*!!(?!!)/g), (_, k) => `${example.label}#${k}`))),
];
const workloads = [...Object.keys(entries), ...corpus];

// The kernel's refusal of a term deeper than its syntax allows (K344).
const deep = error => error instanceof KernelError && error.message === "Native prototype syntax depth exceeds 512.";
// The !! print the sample measures, by either path, with the work, time
// and text of its normal form: the `index`-th of the module whose source is
// `source`, or of any module.
function measuring(path, index = 0, source = null) {
  const records = [], printed = Translator.prototype.printed;
  let seen = 0;
  Translator.prototype.printed = function (d, scope) {
    if (d.show !== "evaluate" || d.mark !== "!!" || source !== null && scope.unit.source !== source || seen++ !== index)
      return printed.call(this, d, scope);
    scope.spend("queries");
    const checker = this.checker, kernel = checker.kernel, result = checker.evaluated(this.term(d.value, scope));
    if (result.native.axioms.length) return printed.call(this, d, scope);
    const record = { path }, ticks = () => Number(kernel.work().querySteps), started = performance.now(), before = ticks();
    records.push(record);
    let normal = null;
    try {
      if (path === "runtime") {
        let query = null;
        try {
          query = new RuntimeQuery(kernel, result.judgement, { ...checker.runtimeLimits(), origins: true });
          // The value form's walk, which spends no query of the directive's fuel.
          valueForm(query.root, this.runtimeQueries({ spend() {} }, query, this.demandQueries(scope, () => "")), d.value);
          const walked = performance.now(), walkSteps = query.stats.steps;
          const term = query.readback(query.root, { origins: true }), read = performance.now(), atRead = ticks();
          normal = checker.normalForm(term);
          Object.assign(record, { by: "runtime", walkSteps, walkMs: walked - started, readbackSteps: query.stats.steps - walkSteps,
            readbackMs: read - walked, normalizeTicks: ticks() - atRead, normalizeMs: performance.now() - read });
        } catch (error) {
          if (!(error instanceof RuntimeError) && !deep(error)) throw error;
          Object.assign(record, { fallback: error.message, walkSteps: query?.stats.steps ?? 0 });
        } finally { query?.dispose(); }
      }
      if (!normal) {
        const at = ticks(), kernelStarted = performance.now();
        try { normal = checker.normalForm(result.expression); record.by ??= "kernel"; }
        catch (error) { record.error = error.message; throw error; }
        finally { Object.assign(record, { kernelTicks: ticks() - at, kernelMs: performance.now() - kernelStarted }); }
      }
    } finally { Object.assign(record, { ticks: ticks() - before, milliseconds: performance.now() - started }); }
    record.text = this.shownIn(normal, scope);
    return { text: record.text, axioms: [] };
  };
  return { records, restore() { Translator.prototype.printed = printed; } };
}

// A sample: the setup checked, then the measured print.
async function sample(name, path) {
  const module = await createCubical();
  if (entries[name]) {
    const [setup, entry] = entries[name], program = new CubicalProgram(module, sourceReader(), { collectReferences: false });
    try {
      const session = new ReplSession(program);
      for (const line of await session.run(setup)) if (line.kind === "error") throw new Error(line.text);
      const watched = measuring(path);
      try { await session.run(`evaluate !!${entry};`); } finally { watched.restore(); }
      return watched.records;
    } finally { program.dispose(); }
  }
  const [, place, line, at] = name.match(/^(.*?)(?::(\d+))?#(\d+)$/), index = Number(at);
  if (place.startsWith("cubist-tests/")) {
    const watched = measuring(path, index, readFileSync(`${root}${place}.cubist`, "utf8"));
    try { await checkedModule(place.slice("cubist-tests/".length), module); } finally { watched.restore(); }
    return watched.records;
  }
  // A reference example, as tests/reference-examples.test.mjs checks it: an
  // accepted one as a module, a REPL transcript on the accepted example
  // before it, and a command-line session's entries in a fresh REPL.
  const examples = referenceExamples(place, readFileSync(`${root}web/${place}`, "utf8"));
  const position = examples.findIndex(example => example.label === `${place}:${line}`), example = examples[position];
  const kind = example.attrs["data-check"], program = new CubicalProgram(module, sourceReader(), { collectReferences: false });
  try {
    if (kind === "accept") {
      const watched = measuring(path, index, example.text);
      try { await program.check(example.text, "reference_example"); } finally { watched.restore(); }
      return watched.records;
    }
    let session = new ReplSession(program);
    if (kind === "repl" && example.attrs["data-base"] !== "none") {
      await program.check(examples.slice(0, position).filter(e => e.attrs["data-check"] === "accept").at(-1).text, "example");
      session = new ReplSession(program, { base: "example" });
    }
    const inputs = kind === "repl" ? replTranscript(example.text).map(({ input }) => input)
      : example.text.split("\n").filter(text => text.startsWith("> ")).map(text => text.slice(2));
    const watched = measuring(path, index);
    try { for (const input of inputs) await session.run(input); } finally { watched.restore(); }
    return watched.records;
  } finally { program.dispose(); }
}

assertFreshBuild();
const args = process.argv.slice(2), child = args[0] === "--child";
const [names, only] = child ? args.slice(1) : args;
const selected = (names ? names.split(",") : workloads).flatMap(name => (only ? [only] : ["kernel", "runtime"]).map(path => {
  if (!workloads.includes(name) || !["kernel", "runtime"].includes(path)) throw new Error(`Unknown workload or path: ${name} ${path}`);
  return [name, path];
}));
if (!child) {
  for (const [name, path] of selected) execFileSync(process.execPath, [fileURLToPath(import.meta.url), "--child", name, path], { stdio: "inherit" });
} else {
  const [[name, path]] = selected, records = await sample(name, path);
  if (records.length !== 1) throw new Error(`${name}: ${records.length} prints measured, not one.`);
  const { text, ...record } = records[0], round = value => typeof value === "number" ? Math.round(value * 10) / 10 : value;
  console.log(JSON.stringify({ workload: name, ...Object.fromEntries(Object.entries(record).map(([key, value]) => [key, round(value)])),
    textLength: text?.length, textSha256: text === undefined ? null : createHash("sha256").update(text).digest("hex").slice(0, 16),
    text: text?.length > 120 ? `${text.slice(0, 120)}…` : text, maxRssMiB: Math.round(process.resourceUsage().maxRSS / 1024),
    revision: execFileSync("git", ["rev-parse", "--short", "HEAD"], { cwd: root, encoding: "utf8" }).trim(),
    modified: execFileSync("git", ["status", "--porcelain", "--untracked-files=normal"], { cwd: root, encoding: "utf8" }).trim() !== "",
    node: process.version, platform: `${process.platform}/${process.arch}` }));
}
