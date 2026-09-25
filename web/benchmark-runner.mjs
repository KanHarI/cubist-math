// Shared by the Node benchmark and browser worker; source checks are identical.
import createCubical from "./dist/cubical.mjs";
import { CubicalProgram } from "./cubical-program.mjs";
import { sourceModules, cubicalSourceModules } from "./mathscript/modules.mjs";
import { cubicalSourceFile } from "./cubical-sources.mjs";
import { CubicalDeclarationTransaction } from "./cubical-transaction.mjs";

export function category(result, elapsedMs, limitMs) {
  if (result.reason?.startsWith("Universe schema:")) return "template";
  if (result.blockedBy || result.reason?.startsWith("Untranslated dependency:")) return "blocked";
  if (result.reason?.includes("Declaration time limit exceeded") || elapsedMs > limitMs) return "optimize";
  return result.status === "checked-native-cubical" ? "checked" : "failed";
}

export async function benchmark({ modules = [...sourceModules, ...cubicalSourceModules], limitMs = 100, optimizations = {},
  readSource = async name => {
    const response = await fetch(new URL(`./archive/first-library/${cubicalSourceFile(name)}`, import.meta.url));
    if (!response.ok) throw Error(`Could not load ${name}: HTTP ${response.status}`);
    return response.text();
  },
  onResult = () => {}, onSnapshot = () => {} } = {}) {
  if (!Number.isFinite(limitMs) || limitMs <= 0) throw new Error("The declaration limit must be a positive number of milliseconds.");
  const started = performance.now(), declarations = [];
  let declarationStart, declarationStartSteps, transaction;
  const program = new CubicalProgram(await createCubical(), readSource, {
    collectReferences: false, optimizations, manageTransactions: false,
    onDeclarationStart(_module,_syntax,checker) {
      transaction = new CubicalDeclarationTransaction(program.kernel,program.checker);
      declarationStart = performance.now();
      declarationStartSteps = checker.steps;
      program.kernel.setDeadline(limitMs);
    },
    onDeclaration(module, syntax, result, checker) {
      const elapsedMs = performance.now() - declarationStart;
      program.kernel.setDeadline();
      const row = { binding: `${module}__${result.name}`, module, name: result.name,
        category: category(result, elapsedMs, limitMs), elapsedMs: +elapsedMs.toFixed(3),
        nativeCheckingSteps: checker.steps-declarationStartSteps,
        rewriteWork: result.rewriteWork,
        finalCheckArenaNodes: result.native?.arenaNodes ?? null,
        finalCheckArenaBytes: result.native?.arenaBytes ?? null,
        reason: result.reason, blockedBy: result.blockedBy,
        line: program.sources[module].slice(0, syntax.start).split("\n").length };
      if (row.category === "optimize") {
        result.status = "not-translated";
        result.reason = "Declaration time limit exceeded.";
      }
      transaction.finish(row.category === "checked");
      transaction = null;
      declarations.push(row); onResult(row);
    },
  });
  try {
    await program.check([...new Set(modules)].map(name => `import ${name};`).join("\n"), "benchmark",
      progress => { if (progress.phase === "checked") onSnapshot({ declarations, total: progress.total, current: progress.current, elapsedSeconds: (performance.now() - started) / 1000 }); });
    const byName = new Map(declarations.map(d => [d.binding, d]));
    for (const row of declarations) {
      const seen = new Set(); let next = row;
      while (next.blockedBy && !seen.has(next.blockedBy)) {
        seen.add(next.blockedBy); next = byName.get(next.blockedBy) ?? next;
      }
      if (row.blockedBy) row.rootBlocker = next.binding;
    }
    return { version: 1, generatedAt: new Date().toISOString(), limitMs, optimizations: program.kernel.optimizations,
      elapsedSeconds: +((performance.now() - started) / 1000).toFixed(2),
      modules: Object.keys(program.sources).length - 1, declarations,
      counts: Object.fromEntries(["checked", "optimize", "blocked", "failed", "template"].map(c =>
        [c, declarations.filter(d => d.category === c).length])),
      importErrors: program.gaps.filter(g => !g.name) };
  } finally { program.dispose(); }
}
