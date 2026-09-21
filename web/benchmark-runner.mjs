// Shared by the Node benchmark and browser worker; source checks are identical.
import createCubical from "./dist/cubical.mjs";
import { CubicalProgram } from "./cubical-program.mjs";
import { sourceModules, cubicalSourceModules } from "./mathscript/modules.mjs";
import { cubicalSourceFile } from "./cubical-sources.mjs";

export function category(result, elapsedMs, limitMs) {
  if (result.reason?.startsWith("Universe schema:")) return "template";
  if (result.blockedBy || result.reason?.startsWith("Untranslated dependency:")) return "blocked";
  if (result.reason?.includes("Declaration time limit exceeded") || elapsedMs > limitMs) return "optimize";
  return result.status === "checked-native-cubical" ? "checked" : "failed";
}

export async function benchmark({ modules = [...sourceModules, ...cubicalSourceModules], limitMs = 1000,
  readSource = async name => {
    const response = await fetch(new URL(`./proofs/${cubicalSourceFile(name)}`, import.meta.url));
    if (!response.ok) throw Error(`Could not load ${name}: HTTP ${response.status}`);
    return response.text();
  },
  onResult = () => {}, onSnapshot = () => {} } = {}) {
  const started = performance.now(), declarations = [];
  let declarationStart, definitionsBefore;
  const program = new CubicalProgram(await createCubical(), readSource, {
    collectReferences: false,
    onDeclarationStart() {
      definitionsBefore = new Set(program.kernel.definitions.keys());
      program.kernel.module._cb_checkpoint(program.kernel.handle);
      declarationStart = performance.now();
      program.kernel.setDeadline(limitMs);
    },
    onDeclaration(module, syntax, result) {
      const elapsedMs = performance.now() - declarationStart;
      program.kernel.setDeadline();
      const row = { binding: `${module}__${result.name}`, module, name: result.name,
        category: category(result, elapsedMs, limitMs), elapsedMs: +elapsedMs.toFixed(3),
        reason: result.reason, blockedBy: result.blockedBy,
        line: program.sources[module].slice(0, syntax.start).split("\n").length };
      if (row.category !== "checked" && row.category !== "template") {
        if (row.category === "optimize") {
          result.status = "not-translated";
          result.reason = "Declaration time limit exceeded.";
        }
        program.kernel.module._cb_rollback(program.kernel.handle);
        program.kernel.unfoldingHints = [];
        for (const name of program.kernel.definitions.keys()) if (!definitionsBefore.has(name)) {
          program.kernel.definitions.delete(name); program.checker.definitionViews.delete(name);
        }
        for (const key of program.checker.schemaSpecializations.keys())
          if (!program.kernel.definitions.has(key)) program.checker.schemaSpecializations.delete(key);
        // Handle reuse is confined to rejected attempts. Never reuse a JS
        // cache entry whose native node may have been discarded.
        program.checker.syntax.encoded = new WeakMap();
        program.checker.syntax.decoded.clear();
      }
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
    return { version: 1, generatedAt: new Date().toISOString(), limitMs,
      elapsedSeconds: +((performance.now() - started) / 1000).toFixed(2),
      modules: Object.keys(program.sources).length - 1, declarations,
      counts: Object.fromEntries(["checked", "optimize", "blocked", "failed", "template"].map(c =>
        [c, declarations.filter(d => d.category === c).length])),
      importErrors: program.gaps.filter(g => !g.name) };
  } finally { program.dispose(); }
}
