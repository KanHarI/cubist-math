// The acceptance measurements of the evaluation demand marks (DM5 of the note
// beside this directory). Each case runs in a fresh program, through the REPL
// as the CLI runs it (web/repl-session.mjs), with the probe's fixed query
// budget. For each it records the entry's first result and its SHA-256, the
// query ticks and queries the entry alone spent, and, where the entry
// normalized a term, how many times and how many of those failed, and for
// the last normalization, the whole value's under `!!_` after any its
// elaboration asked for, its ticks alone and either its failure or the
// distinct objects of the normal form's decoding and its digest
// (tools/evaluation-baseline.mjs's sharedNormalDigest, which compares as its
// normalDigest does).
// Usage: node report.mjs [--root=CHECKOUT] [budget] [case ...]. --root
// measures another checkout, as main, with the spelling each case had there
// before the marks (`expecting _` for `expecting !!_`); a case with no such
// spelling is skipped. Named cases run alone. Results are JSON lines.
import { createHash } from "node:crypto";
import { pathToFileURL } from "node:url";
import { sources } from "./probe-sources.mjs";
import { sharedNormalDigest } from "../../../../tools/evaluation-baseline.mjs";

const option = process.argv.find(arg => arg.startsWith("--root="));
const root = option ? pathToFileURL(`${option.slice("--root=".length).replace(/\/$/, "")}/`) : new URL("../../../../", import.meta.url);
const args = process.argv.slice(2).filter(arg => !arg.startsWith("--"));
const budget = BigInt(args.find(arg => /^\d+$/.test(arg)) ?? "100000000"), named = args.filter(arg => !/^\d+$/.test(arg));
const { default: createCubical } = await import(new URL("web/dist/cubical.mjs", root));
const { CubicalProgram } = await import(new URL("web/cubical-program.mjs", root));
const { ReplSession } = await import(new URL("web/repl-session.mjs", root));
const { sourceReader } = await import(new URL("tools/module-sources.mjs", root));
const { assertFreshBuild, sourceHash } = await import(new URL("tools/build-stamp.mjs", root));
assertFreshBuild();

const unat = "import unat;\nuse unat;\n", euclid = "import euclid;\nuse unat;\n";
const rationals = "import rationals;\nuse unat;\n", integers = "import integers;\nuse unat;\n";
// Each acceptance case: its setup, its entry, and the entry main had for it.
const cases = [
  { id: "small-inverse-value", setup: sources.rational, entry: "evaluate small_inverse;", main: "evaluate small_inverse;" },
  { id: "small-inverse-normal", setup: sources.rational, entry: "evaluate small_inverse expecting !!_;", main: "evaluate small_inverse expecting _;" },
  { id: "euclid-3-pattern", setup: euclid, entry: "evaluate euclid(3) expecting (7, _);", main: "evaluate euclid(3) expecting (7, _);" },
  { id: "euclid-4-head", setup: euclid, entry: "evaluate !euclid(4);" },
  { id: "euclid-4-pattern", setup: euclid, entry: "evaluate euclid(4) expecting (5, _);", main: "evaluate euclid(4) expecting (5, _);" },
  { id: "bare-hole", setup: euclid, entry: "evaluate euclid(3) expecting _;", main: "evaluate euclid(3) expecting _;" },
  { id: "eta-successor-head", setup: unat, entry: "print(evaluate(!(fun (n : UNat) => succ(n))));" },
  // The constructs whose full normal forms the corpus test leaves out.
  ...[["rational-literal-normal", rationals, "rationals.(2/3)"], ["decimal-literal-normal", rationals, "rationals.(0.5)"],
    ["theory-parent-normal", integers, "integers.additive_"]].map(([id, setup, term]) =>
    ({ id, setup, entry: `evaluate ${term} expecting !!_;`, main: `evaluate ${term} expecting _;` })),
];

const sha256 = text => createHash("sha256").update(text).digest("hex");
const module = await createCubical();
const kernelSources = sourceHash("kernel");
for (const item of cases) {
  const entry = option ? item.main : item.entry;
  if (!entry || named.length && !named.includes(item.id)) continue;
  const program = new CubicalProgram(module, sourceReader(), { collectReferences: false });
  try {
    const session = new ReplSession(program), kernel = program.kernel;
    const setup = await session.run(item.setup);
    const refused = setup.find(result => result.kind === "error");
    if (refused) throw new Error(`${item.id}: the setup is refused: ${refused.text}`);
    kernel.stepBudget = budget;
    kernel.maxQuerySteps = budget;
    kernel.setStepBudget(budget);
    // The entry's whole-term normalizations: every attempt is counted, and
    // the last is described, by the normal form's digest, taken while its
    // handle holds (a committed or abandoned entry moves its nodes), or by
    // its failure.
    let normalizations = 0, failedNormalizations = 0, normal = null;
    const { normalize } = kernel, work = () => kernel.work();
    kernel.normalize = function (handle) {
      normalizations++;
      const before = work(), ticks = () => Number(work().querySteps - before.querySteps);
      try {
        const result = normalize.call(this, handle);
        const normalTicks = ticks(), { digest, objects } = sharedNormalDigest(program.checker.syntax.decode(result, program.checker.dimensions));
        normal = { normalTicks, normalObjects: objects, normalDigest: digest };
        return result;
      } catch (error) {
        failedNormalizations++;
        normal = { normalTicks: ticks(), normalFailure: error.message };
        throw error;
      }
    };
    const before = work();
    const [result] = await session.run(entry);
    const after = work();
    const record = { case: item.id, entry, queryBudget: String(budget), kernelSources,
      outcome: result.kind, text: result.text.length > 160 ? `${result.text.slice(0, 159)}…` : result.text,
      length: result.text.length, sha256: sha256(result.text),
      queryTicks: Number(after.querySteps - before.querySteps), queries: Number(after.queries - before.queries),
      normalizations, failedNormalizations, ...normal };
    console.log(JSON.stringify(record));
  } finally { program.dispose(); }
}
