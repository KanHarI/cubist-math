// A7 baseline for the HoTT automation roadmap: one observation, not a
// performance comparison. The proof-ergonomics baseline stays unchanged in
// ../proof-ergonomics/baseline.json. Run from any directory after building the
// C/WASM runtime: node docs/examples/hott-automation/measure.mjs
import { readFile, writeFile } from "node:fs/promises";
import { execFileSync } from "node:child_process";
import { createHash } from "node:crypto";
import { cpus } from "node:os";
import { fileURLToPath } from "node:url";
import createCubical from "../../../web/dist/cubical.mjs";
import { CubicalProgram } from "../../../web/cubical-program.mjs";
import { cubicalSourceFile } from "../../../web/cubical-sources.mjs";
import { parse, tokenize } from "../../../web/mathscript/parser.mjs";

const root = new URL("../../../", import.meta.url);
const selection = [
  ["group_identity", "group_laws_prop"],
  ["group_total_identity", "group_total_laws_path"],
  ["identity_systems", "identity_system_retraction"],
  ["circle", "code_upper"],
  ["circle", "upper_transition"],
  ["equivalence_from_inverse", "adjoint_triangle"],
  ["paths", "cancel_left"],
  ["paths", "transport_concat"],
  // Raw inferred signatures; folded signatures arrive with A1.
  ["paths", "right_unit"],
  ["paths", "transport_constant"],
  ["paths", "transport_ap"],
  // Equivalence construction, and transport along univalence.
  ["equivalence_from_inverse", "equiv_from_inverse"],
  ["binary_univalence_transfer", "univalence_transfer_equality"],
  ["group_hom_universes", "group_hom_ext_at"],
  ["quotient_descent", "quotient_rec_beta"],
];
const modules = [...new Set(selection.map(([module]) => module))];
const readSource = name => readFile(new URL(`web/proofs/${cubicalSourceFile(name)}`, root), "utf8");
// A universe template has no single checked translation. Measure each selected
// template through its U0 specialization instead.
const firstDomain = declaration => declaration.params[0]?.type ?? declaration.value?.domain;
const specializations = [];
for (const module of modules) for (const declaration of parse(await readSource(module)).declarations) {
  const domain = firstDomain(declaration), name = declaration.name.text;
  if (domain?.kind === "name" && domain.name === "Universe"
    && selection.some(([m, n]) => m === module && n === name)) specializations.push([module, name, "U0"]);
}

const observations = new Map();
let current = null;
const program = new CubicalProgram(await createCubical(), readSource, {
  collectReferences: false,
  onDeclarationStart(module, syntax, checker) {
    current = { binding: `${module}__${syntax.name.text}`, started: performance.now(),
      steps: checker.steps, queries: 0, retries: 0, finalCheckSteps: 0, specializationSteps: 0 };
  },
  onDeclaration(module, _syntax, result, checker) {
    observations.set(`${module}__${result.name}`, {
      status: result.status,
      elapsedMs: +(performance.now() - current.started).toFixed(3),
      nativeCheckingSteps: checker.steps - current.steps,
      finalCheckSteps: current.finalCheckSteps,
      specializationSteps: current.specializationSteps,
      nativeQueries: current.queries,
      budgetRetries: current.retries,
      rewriteWork: result.rewriteWork,
      finalCheckArenaNodes: result.native?.arenaNodes ?? null,
      finalCheckArenaBytes: result.native?.arenaBytes ?? null,
    });
    current = null;
  },
});

// Count native queries and the retries caused by exhausting the step budget.
const grow = program.kernel.withGrowingBudget.bind(program.kernel);
program.kernel.withGrowingBudget = operation => {
  if (current) current.queries++;
  let attempts = 0;
  return grow(() => {
    if (attempts++ && current) current.retries++;
    return operation();
  });
};
// Separate universe specialization and the declaration's closing check from
// elaboration queries. The closing check is the context-free infer call that
// immediately precedes the translator's define.
const checker = program.checker, infer = checker.infer, define = checker.define;
const specialize = checker.specializeSchema;
let specializing = 0, lastContextFreeSteps = 0;
checker.infer = function (term, context) {
  const before = this.steps, result = infer.call(this, term, context);
  if (context === undefined && !specializing) lastContextFreeSteps = this.steps - before;
  return result;
};
checker.define = function (...args) {
  if (current) current.finalCheckSteps = lastContextFreeSteps;
  return define.apply(this, args);
};
// A specialization is checked once per session and then reused, so also
// record the inclusive cost of each first specialization and its trigger.
const specializationCosts = new Map();
checker.specializeSchema = function (name, levels, elaborate) {
  const key = `${name}__${levels.map(level => `U${level}`).join("_")}`;
  const cached = this.schemaSpecializations.has(key), before = this.steps;
  specializing++;
  try { return specialize.call(this, name, levels, elaborate); }
  finally {
    specializing--;
    const steps = this.steps - before;
    if (!cached && !specializationCosts.has(key))
      specializationCosts.set(key, { steps, triggeredBy: current?.binding ?? null });
    if (current && !specializing) current.specializationSteps += steps;
  }
};

// Fresh session: the whole import graph, checked once in a new kernel.
const specializationSource = suffix => specializations.map(([, name, level]) =>
  `def ${name}_${level}${suffix} = ${name}(${level});`).join("\n");
const fresh = await program.check(`${modules.map(module => `import ${module};`).join("\n")}
${specializationSource("")}`, "hott_baseline");
if (!fresh.complete) throw new Error(`Baseline did not fully check: ${JSON.stringify(fresh.gaps)}`);
const freshObservations = new Map(observations);
const freshTemplates = Object.values(program.symbols).filter(symbol => symbol.template).length;
observations.clear();

// Reused session: check each selected module's source again in the same,
// already populated kernel, then specialize the reused templates.
for (const module of modules) {
  const reused = await program.check(await readSource(module), `${module}_reused`);
  if (!reused.complete) throw new Error(`Reused ${module} did not fully check.`);
}
await program.check(`${[...new Set(specializations.map(([module]) => module))]
  .map(module => `import ${module}_reused;`).join("\n")}
${specializationSource("_reused")}`, "hott_baseline_reused");

const assumptionLabel = binding => program.checker.assumptionLabels.get(binding) ?? binding;
const row = (module, name) => {
  const binding = `${module}__${name}`, info = program.symbols[binding];
  if (!info?.verified && !info?.template) throw new Error(`Unchecked baseline ${binding}`);
  return { info, fresh: freshObservations.get(binding),
    reused: observations.get(`${module}_reused__${name}`) };
};
const selected = await Promise.all(selection.map(async ([module, name]) => {
  const source = await readSource(module);
  const declaration = parse(source).declarations.find(d => d.name.text === name);
  if (!declaration) throw new Error(`Missing baseline declaration ${module}.${name}`);
  const text = source.slice(declaration.start, declaration.end);
  const { info, fresh: freshRow, reused } = row(module, name);
  const specialization = specializations.find(([m, n]) => m === module && n === name);
  const typed = specialization ? program.symbols[`hott_baseline__${name}_${specialization[2]}`] : info;
  const measured = specialization ? {
    template: true, specializedAt: specialization[2],
    firstSpecialization: {
      fresh: specializationCosts.get(`${module}__${name}__${specialization[2]}`) ?? null,
      reused: specializationCosts.get(`${module}_reused__${name}__${specialization[2]}`) ?? null,
    },
    fresh: freshObservations.get(`hott_baseline__${name}_${specialization[2]}`),
    reused: observations.get(`hott_baseline_reused__${name}_${specialization[2]}_reused`),
  } : { template: false, fresh: freshRow, reused };
  return { module, name, sourcePath: `web/proofs/${cubicalSourceFile(module)}`,
    sourceSha256: createHash("sha256").update(source).digest("hex"),
    declarationSha256: createHash("sha256").update(text).digest("hex"),
    sourceTokens: tokenize(text).length - 1, sourceLines: text.split("\n").length,
    publicType: typed.type ?? null, foldedType: null,
    assumptions: (typed.axioms ?? []).map(assumptionLabel), ...measured };
}));

const git = args => execFileSync("git", args, { cwd: fileURLToPath(root), encoding: "utf8" }).trim();
const snapshot = {
  version: 1, generatedAt: new Date().toISOString(), revision: git(["rev-parse", "HEAD"]),
  dirty: !!git(["status", "--porcelain"]), runtime: process.version, cpu: cpus()[0]?.model,
  method: "The fresh session checks the selected modules' import graph once in a new kernel, with references disabled and declaration transactions. The reused session then checks each selected module's source again, under a new module name, in the same kernel. Native checking steps count every checker query during a declaration. Final-check steps are the translator's closing check; specialization steps are spent inside universe specialization; the rest is elaboration. The kernel's own re-check during definition is not reported to JavaScript. Native queries count calls into the kernel; budget retries count queries repeated after the growing step budget was exhausted. Arena values snapshot the kernel at the final check and are cumulative. Elapsed times are one observation. Tokens exclude comments, whitespace and EOF. A template is measured through a declaration that names its U0 specialization; that specialization may already be cached, so firstSpecialization records the inclusive steps of the first specialization in each session and the declaration that triggered it. foldedType stays null until A1 introduces folded signatures.",
  unmeasured: ["kernel re-check during definition", "peak temporary arena", "retained arena delta",
    "generated proof DAG size", "repeated-run variance", "prelude cost (no prelude before A1)"],
  graph: { modules: Object.keys(program.sources).length,
    checked: [...freshObservations.values()].filter(o => o.status === "checked-native-cubical").length,
    templates: freshTemplates },
  selected,
};
program.dispose();
const destination = new URL("./baseline.json", import.meta.url);
await writeFile(destination, JSON.stringify(snapshot, null, 2) + "\n");
console.log(`Wrote ${fileURLToPath(destination)}; ${selected.length} declarations.`);
