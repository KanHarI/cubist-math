// Shared by the Node benchmark and browser worker; source checks are identical.
// Each declaration is elaborated and checked by the term checker, then derived
// again by the instruction kernel (cc_instr_*), through the untrusted driver
// that replays the checked term one rule at a time. It counts as checked only
// when both succeed within the declaration's deadline.
import createCubical from "./dist/cubical.mjs";
import { CubicalProgram } from "./cubical-program.mjs";
import { InstructionDriver } from "./cubical-instruction-driver.mjs";
import { sourceModules, cubicalSourceModules } from "./mathscript/modules.mjs";
import { cubicalSourceFile } from "./cubical-sources.mjs";
import { CubicalDeclarationTransaction } from "./cubical-transaction.mjs";

export function category(result, elapsedMs, limitMs, instructions = null) {
  if (result.template) return "template";
  if (result.blockedBy) return "blocked";
  if (result.failure === "deadline" || instructions?.deadline || elapsedMs > limitMs) return "optimize";
  if (instructions && !instructions.derived) return "failed";
  return result.status === "checked-native-cubical" ? "checked" : "failed";
}

// The checked definition, derived again by instructions within what is left
// of the deadline: the time, the judgements the derivation added to the
// kernel's graph, or why it failed.
export function deriveByInstructions(kernel, binding, remainingMs) {
  const reference = kernel.definitions.get(binding);
  if (!reference) return null;
  const { value, type } = kernel.definition(reference), started = performance.now();
  kernel.setDeadline(Math.max(remainingMs, 1));
  const driver = new InstructionDriver(kernel), before = driver.graph.count;
  try {
    driver.check(value, type);
    return { derived: true, ms: +(performance.now() - started).toFixed(3), judgements: driver.graph.count - before };
  } catch (error) {
    return { derived: false, ms: +(performance.now() - started).toFixed(3), reason: error.message,
      deadline: error.kind === "deadline" || /time limit exceeded/i.test(error.message) };
  } finally { kernel.setDeadline(); }
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
      const checkMs = performance.now() - declarationStart;
      program.kernel.setDeadline();
      const binding = `${module}__${result.name}`;
      const instructions = result.status === "checked-native-cubical" && !result.template && checkMs <= limitMs
        ? deriveByInstructions(program.kernel, binding, limitMs - checkMs) : null;
      const elapsedMs = performance.now() - declarationStart;
      const row = { binding, module, name: result.name,
        category: category(result, elapsedMs, limitMs, instructions), elapsedMs: +elapsedMs.toFixed(3),
        checkMs: +checkMs.toFixed(3), instructionMs: instructions?.ms ?? null,
        instructionJudgements: instructions?.judgements ?? null,
        nativeCheckingSteps: checker.steps-declarationStartSteps,
        rewriteWork: result.rewriteWork,
        finalCheckArenaNodes: result.native?.arenaNodes ?? null,
        finalCheckArenaBytes: result.native?.arenaBytes ?? null,
        reason: instructions && !instructions.derived ? `Instruction kernel: ${instructions.reason}` : result.reason,
        blockedBy: result.blockedBy,
        line: program.sources[module].slice(0, syntax.start).split("\n").length };
      // Rolled back below, so the program must not count it as checked: its
      // dependents are then blocked on it.
      if (row.category === "optimize" || (instructions && !instructions.derived)) {
        result.status = "not-translated";
        result.reason = row.category === "optimize" ? "Declaration time limit exceeded." : row.reason;
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
