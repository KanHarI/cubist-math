// What the instruction driver does to derive a closed term's folded normal
// form (docs/reports/driver-derivation-sharing.md): the normal form's size
// as a graph and as a tree, then, in a rolled-back checkpoint, the
// derivation's instructions, time and peak memory, its deriveNode calls,
// the distinct handles and scopes they met, and its agree calls.
//   node docs/reports/driver-derivation-sharing/census.mjs ROOT SETUP TERM
// as
//   node docs/reports/driver-derivation-sharing/census.mjs . \
//     "import binary_rationals; use binary_rationals;" "typed(BQ, 1/2)"
import { resolve } from "node:path";
import { pathToFileURL } from "node:url";
const [root, setup, term] = process.argv.slice(2);
const at = path => pathToFileURL(resolve(root, path)).href;
const { default: createCubical } = await import(at("web/dist/cubical.mjs"));
const { CubicalProgram } = await import(at("web/cubical-program.mjs"));
const { ReplSession } = await import(at("web/repl-session.mjs"));
const { CubicalDeclarationTransaction } = await import(at("web/cubical-transaction.mjs"));
const { InstructionDriver } = await import(at("web/cubical-instruction-driver.mjs"));
const { sourceReader } = await import(at("tools/module-sources.mjs"));
const program = new CubicalProgram(await createCubical(), sourceReader(), { collectReferences: false });
const session = new ReplSession(program);
let on = false;
const handles = new Set(), scopes = new Set(), counts = { deriveNode: 0, agree: 0 };
const { deriveNode, agree } = InstructionDriver.prototype;
InstructionDriver.prototype.deriveNode = function (handle, scope) {
  if (on) { counts.deriveNode++; handles.add(handle); scopes.add(this.scopeKey(scope)); }
  return deriveNode.call(this, handle, scope);
};
InstructionDriver.prototype.agree = function (...args) { if (on) counts.agree++; return agree.apply(this, args); };
try {
  const prepared = await session.run(`${setup} def census_term := ${term};`);
  const failed = prepared.find(answer => answer.kind === "error");
  if (failed) throw new Error(failed.text);
  const { checker, kernel } = program;
  const name = [...checker.definitionViews.keys()].find(name => name.endsWith("census_term"));
  const transaction = new CubicalDeclarationTransaction(kernel, checker);
  try {
    const handle = kernel.normalizeFolded(checker.evaluated(checker.definitionViews.get(name).term).expression);
    const nodes = new Set(), stack = [handle], trees = new Map();
    while (stack.length) { const h = stack.pop(); if (h && !nodes.has(h)) { nodes.add(h); stack.push(...kernel.node(h).children); } }
    const tree = h => {
      if (!h) return 0;
      if (!trees.has(h)) trees.set(h, 1 + kernel.node(h).children.reduce((sum, child) => sum + tree(child), 0));
      return trees.get(h);
    };
    const normal = checker.syntax.decode(handle, checker.dimensions);
    const before = kernel.work(), started = performance.now();
    on = true;
    checker.infer(normal);
    on = false;
    const after = kernel.work();
    console.log(JSON.stringify({ term, graphNodes: nodes.size, treeNodes: tree(handle), ms: Math.round(performance.now() - started),
      instructions: after.instructions - before.instructions, instructionSteps: Number(after.instructionSteps - before.instructionSteps),
      ...counts, distinctHandles: handles.size, distinctScopes: scopes.size,
      maxRssMiB: Math.round(process.resourceUsage().maxRSS / 1024) }));
  } finally { transaction.finish(false); }
} finally { program.dispose(); }
