// Record what the elaborator produces for a set of source modules, so that a
// refactor of the untrusted elaborator can be shown to change nothing:
// - every declaration's status, checked term and type (hashed up to bound
//   names), assumptions, displayed type and rewrite work;
// - every other checked definition, such as universe specializations;
// - every inspector record: source site, role, description, freeze edit and
//   the hashed term in its local context;
// - the template link sites and evaluation results.
//   node tools/elaboration-fingerprint.mjs [--write FILE] [--compare FILE] [--examples] [module ...]
// Without module names, every archive/first-library module is recorded.
// --examples adds the checked design examples under docs/examples.
import { readFile, readdir, writeFile } from "node:fs/promises";
import { fileURLToPath } from "node:url";
import createCubical from "../web/dist/cubical.mjs";
import { CubicalProgram } from "../web/cubical-program.mjs";
import { canonicalHasher } from "./proof-migration.mjs";

const root = fileURLToPath(new URL("../", import.meta.url));
const LINKS = "__fingerprint_links";

// A local term is hashed closed over its context and dimensions, so the
// generated names of its free variables do not matter, only their positions.
const closed = (term, context = new Map(), dimensions = new Map()) => {
  for (const [name, type] of [...context].reverse()) term = { tag: "Lam", name, domain: type, body: term };
  for (const dim of [...dimensions.keys()].reverse()) term = { tag: "PLam", dim, family: null, body: term };
  return term;
};

export async function elaborationFingerprint({ modules, readSource }) {
  const program = new CubicalProgram(await createCubical(), readSource);
  try {
    await program.check(modules.map(name => `import ${name};`).join("\n"), "fingerprint");
    const views = program.checker.definitionViews;
    // Generated unfolding helpers are named by a session serial; hash them
    // by their checked bodies instead.
    const helper = name => /__unfolding_\d+$/.test(name) && views.has(name);
    let hash;
    hash = canonicalHasher({ definitionName: name => helper(name) ? `helper:${hash(views.get(name).term)}` : name });
    const declarations = {}, definitions = {}, references = {}, links = {};
    for (const [binding, symbol] of Object.entries(program.symbols)) {
      if (binding.startsWith("fingerprint__")) continue;
      const view = views.get(binding);
      declarations[binding] = { status: symbol.status, reason: symbol.reason ?? null,
        errorStart: symbol.errorStart ?? null, errorEnd: symbol.errorEnd ?? null,
        axioms: [...symbol.axioms].sort(), unfoldingHints: symbol.unfoldingHints.length,
        displayedType: symbol.type, rewriteWork: symbol.rewriteWork ?? null,
        term: view ? hash(view.term) : null, type: view ? hash(view.type) : null,
        references: program.declarationReferences.get(binding)?.map(({ start, binding }) =>
          `${start}:${helper(binding) ? "helper" : binding}`) ?? null };
    }
    // Inspecting a template elaborates its body at the selected levels.
    const inspections = {};
    for (const binding of program.templates.keys()) {
      const levels = program.symbols[binding].templateParameters.map(() => 0);
      try {
        const view = program.inspect(binding, { universes: levels });
        inspections[binding] = { expression: hash(view.expression), type: hash(view.type), typeText: view.typeText };
      } catch (error) { inspections[binding] = { error: error.message }; }
    }
    for (const [binding, view] of views) if (!program.symbols[binding] && !helper(binding))
      definitions[binding] = { term: hash(view.term), type: hash(view.type) };
    for (const [binding, view] of program.views) {
      const symbol = program.localSymbols[binding] ?? {}, node = view.node ?? {};
      references[binding] = {
        node: { name: node.name, start: node.start, end: node.end, role: node.role ?? null,
          description: node.description ?? null, expansion: node.expansion ?? null,
          expansionIndex: node.expansionIndex ?? null, traceParent: node.traceParent ?? null,
          isBinding: !!node.isBinding, expressionSite: !!node.expressionSite,
          schemaBinding: node.schemaBinding ?? null, universes: node.universes ?? null },
        symbol: { name: symbol.name, role: symbol.role, description: symbol.description ?? null,
          freeze: symbol.freeze ?? null, definitionStart: symbol.definitionStart ?? null,
          rewriteSteps: symbol.rewriteSteps?.map(step => step.binding) ?? null },
        aliases: (view.aliases ?? []).map(alias => [alias.name, alias.start, alias.end]),
        unfoldingHints: view.unfoldingHints?.length ?? 0,
        term: hash(closed(view.term, view.context, view.dimensions)),
      };
    }
    // Template link sites are computed only for a main module. Check each
    // module with a template again as a main module under another name.
    for (const module of modules) {
      if (![...program.templates.keys()].some(binding => binding.startsWith(`${module}__`))) continue;
      const main = `${module}${LINKS}`, before = program.links.length;
      await program.check(await readSource(module), main);
      links[module] = program.links.slice(before).filter(link => link.templateBinding).map(link => ({
        name: link.name, start: link.start, end: link.end, role: link.role,
        template: link.templateBinding.slice(main.length + 2), offset: link.templateOffset,
        expansion: link.templateExpansion ?? null }));
    }
    return { declarations, definitions, inspections, references, links,
      evaluations: program.evaluations.filter(item => !item.module.endsWith(LINKS)),
      gaps: program.gaps.filter(gap => !gap.module.endsWith(LINKS)).map(gap => ({ ...gap })) };
  } finally { program.dispose(); }
}

// Differences between two fingerprints, as readable lines.
export function compareFingerprints(before, after, limit = 50) {
  const differences = [];
  const compare = (path, left, right) => {
    if (differences.length >= limit) return;
    if (JSON.stringify(left) === JSON.stringify(right)) return;
    if (left && right && typeof left === "object" && typeof right === "object" && !Array.isArray(left)) {
      for (const key of new Set([...Object.keys(left), ...Object.keys(right)])) compare(`${path}.${key}`, left[key], right[key]);
      return;
    }
    differences.push(`${path}: ${JSON.stringify(left)?.slice(0, 300)} -> ${JSON.stringify(right)?.slice(0, 300)}`);
  };
  compare("fingerprint", before, after);
  return differences;
}

if (process.argv[1] === fileURLToPath(import.meta.url)) {
  const args = process.argv.slice(2), option = name => {
    const index = args.indexOf(name);
    if (index < 0) return undefined;
    const value = args[index + 1];
    args.splice(index, 2);
    return value;
  };
  const output = option("--write"), baseline = option("--compare");
  const examples = args.includes("--examples");
  if (examples) args.splice(args.indexOf("--examples"), 1);
  if (args.some(arg => arg.startsWith("--"))) throw new Error(`Unknown option: ${args.find(arg => arg.startsWith("--"))}`);
  const sources = new Map(), add = async directory => {
    for (const file of (await readdir(`${root}${directory}`)).filter(name => name.endsWith(".cubist")).sort())
      sources.set(directory === "archive/first-library" ? file.slice(0, -".cubist".length)
        : `${directory}/${file.slice(0, -".cubist".length)}`.replace(/\W/g, "_"), `${root}${directory}/${file}`);
  };
  await add("archive/first-library");
  const modules = args.length ? args : [...sources.keys()];
  if (examples) for (const directory of ["docs/examples/hott-automation", "docs/examples/proof-ergonomics/current",
    "docs/examples/proof-ergonomics/implemented"]) {
    const before = new Set(sources.keys());
    await add(directory);
    modules.push(...[...sources.keys()].filter(name => !before.has(name)));
  }
  const started = performance.now();
  const fingerprint = await elaborationFingerprint({ modules,
    readSource: name => readFile(sources.get(name) ?? `${root}archive/first-library/${name}.cubist`, "utf8") });
  const seconds = ((performance.now() - started) / 1000).toFixed(1);
  const counts = Object.fromEntries(Object.entries(fingerprint).map(([key, value]) =>
    [key, Array.isArray(value) ? value.length : Object.keys(value).length]));
  console.log(`${modules.length} modules in ${seconds} s: ${JSON.stringify(counts)}`);
  if (output) await writeFile(output, JSON.stringify(fingerprint) + "\n");
  if (baseline) {
    const differences = compareFingerprints(JSON.parse(await readFile(baseline, "utf8")), fingerprint);
    for (const line of differences) console.log(line);
    console.log(differences.length ? `${differences.length}${differences.length >= 50 ? "+" : ""} differences.` : "Identical.");
    process.exitCode = differences.length ? 1 : 0;
  }
}
