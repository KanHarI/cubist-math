// Shared by the Node benchmark and browser worker; source checks are identical.
// Each declaration is elaborated, and the instruction kernel admits it: the
// untrusted driver derives its checked body one kernel instruction (cc_instr_*)
// per rule, and Define registers the closed judgement. The row records the
// time and judgements of that derivation, and of every derivation the
// declaration needed, the elaborator's included: the kernel's share.
import createCubical from "./dist/cubical.mjs";
import { CubicalProgram } from "./cubical-program.mjs";
import { archiveModules, cubistTestModules, libraryModules } from "./cubist/modules.mjs";
import { moduleListing } from "./module-listing.mjs";
import { listedReader } from "./module-resolution.mjs";
import { normal, stated } from "./cubist/stated-comments.mjs";
import { diagnosticCode } from "./diagnostics.mjs";

// The areas a benchmark can measure, each with its modules: the rebuilt
// library, the archive, and the Cubist tests (cubist-tests/). A test module's
// intended errors are its "Needs fixing" entries.
export const benchmarkAreas = Object.freeze({ library: libraryModules, archive: archiveModules, tests: cubistTestModules });
function knownArea(area) {
  if (!Object.hasOwn(benchmarkAreas, area)) throw new Error(`The benchmark area is library, archive or tests, not ${area}.`);
  return area;
}

export function category(result, elapsedMs, limitMs) {
  if (result.blockedBy) return "blocked";
  if (result.failure === "deadline" || elapsedMs > limitMs) return "optimize";
  return result.status === "checked-native-cubical" ? "checked" : "failed";
}

export async function benchmark({ area = "archive", modules = benchmarkAreas[knownArea(area)], limitMs = 100, optimizations = {},
  // The benchmark's check imports the area's modules as a module there
  // does: an archive module from the archive, then the library; a library
  // module from the library; a test from the tests, the library, then the
  // archive.
  readSource = listedReader(moduleListing, async path => {
    const response = await fetch(new URL(`./${path}`, import.meta.url));
    if (!response.ok) throw Error(`Could not load ${path}: HTTP ${response.status}`);
    return response.text();
  }, "benchmark", knownArea(area)),
  onResult = () => {}, onSnapshot = () => {} } = {}) {
  knownArea(area);
  if (!Number.isFinite(limitMs) || limitMs <= 0) throw new Error("The declaration limit must be a positive number of milliseconds.");
  const started = performance.now(), declarations = [];
  // The errors each module's comments state, by line: a Cubist test marks
  // its intended failures so (stated-comments.mjs).
  const intended = new Map();
  const statedErrors = module => {
    if (!intended.has(module)) {
      const byLine = new Map();
      for (const item of stated(program.sources[module] ?? "")) if (item.label === "Error")
        byLine.set(item.line, [...(byLine.get(item.line) ?? []), item.text]);
      intended.set(module, byLine);
    }
    return intended.get(module);
  };
  let declarationStart, declarationStartSteps, kernelStart;
  const program = new CubicalProgram(await createCubical(), readSource, {
    collectReferences: false, optimizations,
    onDeclarationStart(_module,_syntax,checker) {
      declarationStart = performance.now();
      declarationStartSteps = checker.steps;
      kernelStart = { ...program.checker.instructionWork };
      program.kernel.setDeadline(limitMs);
    },
    onDeclaration(module, syntax, result, checker) {
      const elapsedMs = performance.now() - declarationStart, kernel = program.checker.instructionWork;
      program.kernel.setDeadline();
      const binding = `${module}__${result.name}`;
      const admission = result.status === "checked-native-cubical" ? program.checker.definitionViews.get(binding)?.admission : null;
      const line = program.sources[module].slice(0, syntax.start).split("\n").length;
      // A failure or a block its source's comment states, as it is
      // reported, is intended: a test's refusal, not something to fix.
      let rowCategory = category(result, elapsedMs, limitMs);
      const code = result.reason ? diagnosticCode(result.reason) : null;
      if (["failed", "blocked"].includes(rowCategory)
        && statedErrors(module).get(line - 1)?.includes(normal(code ? `${code}: ${result.reason}` : result.reason ?? "")))
        rowCategory = "intended";
      const row = { binding, module, name: result.name,
        category: rowCategory, elapsedMs: +elapsedMs.toFixed(3),
        instructionMs: admission?.ms ?? null, instructionJudgements: admission?.judgements ?? null,
        // Every derivation the declaration needed, its admission's and the
        // elaborator's as it checked its parts: the kernel's share of the time.
        kernelMs: +(kernel.ms - kernelStart.ms).toFixed(3), kernelJudgements: kernel.judgements - kernelStart.judgements,
        nativeCheckingSteps: checker.steps-declarationStartSteps,
        rewriteWork: result.rewriteWork,
        finalCheckArenaNodes: result.native?.arenaNodes ?? null,
        finalCheckArenaBytes: result.native?.arenaBytes ?? null,
        reason: result.reason, blockedBy: result.blockedBy, line };
      if (row.category === "optimize") {
        result.status = "not-translated";
        result.reason = "Declaration time limit exceeded.";
      }
      declarations.push(row); onResult(row);
    },
  });
  try {
    await program.check([...new Set(modules)].map(name => `import ${name};`).join("\n"), "benchmark",
      progress => { if (progress.phase === "checked") onSnapshot({ declarations, total: progress.total, current: progress.current, elapsedSeconds: (performance.now() - started) / 1000 }); });
    const byName = new Map(declarations.map(d => [d.binding, d]));
    // Work on an earlier member is real, but a later family failure means
    // its checked term was rolled back and must not be reported as published.
    for(const [module,groups] of program.publications)for(const group of groups)if(group.state!=="checked")
      for(const member of group.members) {
        const row=byName.get(`${module}__${member}`);
        if(row?.category==="checked")Object.assign(row,{category:"blocked",blockedBy:group.cause.binding,
          reason:`Untranslated dependency: ${group.cause.name}`});
      }
    for (const row of declarations) {
      const seen = new Set(); let next = row;
      while (next.blockedBy && !seen.has(next.blockedBy)) {
        seen.add(next.blockedBy); next = byName.get(next.blockedBy) ?? next;
      }
      if (row.blockedBy) row.rootBlocker = next.binding;
    }
    return { version: 1, area, generatedAt: new Date().toISOString(), limitMs, optimizations: program.kernel.optimizations,
      elapsedSeconds: +((performance.now() - started) / 1000).toFixed(2),
      modules: Object.keys(program.sources).length - 1, declarations,
      counts: Object.fromEntries(["checked", "optimize", "blocked", "failed", "intended"].map(c =>
        [c, declarations.filter(d => d.category === c).length])),
      importErrors: program.gaps.filter(g => !g.name) };
  } finally { program.dispose(); }
}
