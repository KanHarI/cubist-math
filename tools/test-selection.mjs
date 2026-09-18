import { execFileSync } from "node:child_process";
import { readFile } from "node:fs/promises";
import { resolve, relative, basename } from "node:path";
import { fileURLToPath } from "node:url";
import { parse } from "../web/mathscript/parser.mjs";

export const projectRoot = fileURLToPath(new URL("../", import.meta.url));
export const defaultTests = ["tests/workbench.test.mjs", "tests/mathscript.test.mjs", "tests/test-runner.test.mjs"];
export const help = `Usage: npm test -- [options] [module | file ...]

  npm test                              Full regression suite (final check)
  npm test -- complex_inverses           Check one proof and its imports
  npm test -- --module ordered_squares   Same, with an explicit module flag
  npm test -- web/proofs/circle.proof     Check a proof by path
  npm test -- --changed                  Check added/modified .proof files
  npm test -- tests/workbench.test.mjs    Run one JavaScript test file
  npm test -- --test-name-pattern="complex inverses"  Filter regression tests

Repeat modules/files to select several. Node test flags are forwarded before
file arguments. --changed includes staged, unstaged and untracked proof sources;
it does not select JavaScript, browser or C tests. Imports are always checked.
Selected-proof checks validate proofs, not the separate mutation/UI regressions.
`;

export function changedProofs(root = projectRoot) {
  const tracked = execFileSync("git", ["diff", "--name-only", "-z", "--diff-filter=ACMR", "HEAD", "--"], { cwd: root, encoding: "utf8" });
  const untracked = execFileSync("git", ["ls-files", "--others", "--exclude-standard", "-z"], { cwd: root, encoding: "utf8" });
  return [...new Set((tracked + untracked).split("\0").filter(p => p.endsWith(".proof")))];
}

export function selectTests(args, { root = projectRoot, changed = () => changedProofs(root) } = {}) {
  const tests = [], proofs = [], flags = [];
  let explicitSelection = false;
  const proof = value => {
    const path = /^[A-Za-z_][A-Za-z0-9_]*$/.test(value) ? `web/proofs/${value}.proof` : value;
    if (!path.endsWith(".proof")) throw new Error(`Expected a proof module or .proof path: ${value}`);
    proofs.push(resolve(root, path));
  };
  const valueFlags = new Set(["--test-name-pattern", "--test-skip-pattern", "--test-reporter", "--test-reporter-destination", "--test-timeout", "--test-concurrency", "--test-shard"]);
  for (let i = 0; i < args.length; i++) {
    const arg = args[i];
    if (arg === "--help" || arg === "-h") return { help: true };
    if (arg === "--") continue;
    if (arg === "--changed") {
      explicitSelection = true;
      changed().forEach(proof);
    } else if (arg === "--module" || arg.startsWith("--module=")) {
      explicitSelection = true;
      const value = arg === "--module" ? args[++i] : arg.slice(9);
      if (!value || value.startsWith("--")) throw new Error("--module needs a module name or .proof path.");
      proof(value);
    } else if (arg.startsWith("--")) {
      flags.push(arg);
      if (valueFlags.has(arg)) {
        const value = args[++i];
        if (!value || value.startsWith("--")) throw new Error(`${arg} needs a value.`);
        flags.push(value);
      }
    } else if (/\.test\.[cm]?js$/.test(arg)) {
      explicitSelection = true;
      tests.push(resolve(root, arg));
    } else {
      explicitSelection = true;
      proof(arg);
    }
  }
  if (!explicitSelection) tests.push(...defaultTests.map(p => resolve(root, p)));
  if (proofs.length) {
    if (flags.some(flag => /^--test-(?:name|skip)-pattern(?:=|$)/.test(flag))) {
      throw new Error("Use module selection or a test-name filter separately, so proof checks cannot be silently skipped.");
    }
    tests.push(resolve(root, "tests/proof-modules.test.mjs"));
  }
  return { tests: [...new Set(tests)], proofs: [...new Set(proofs)], flags };
}

// Load only the selected proof's transitive source imports. Parsing is shared
// with the compiler, so comments are not mistaken for imports.
export async function loadProof(path, root = projectRoot) {
  const sources = {}, loading = new Set();
  const source = await readFile(path, "utf8");
  async function visit(text) {
    if (/^\s*(?:\/\/[^\n]*\n\s*)*construction\b/.test(text)) return;
    for (const name of parse(text).imports) {
      if (name === "prelude" || loading.has(name)) continue;
      loading.add(name);
      const imported = await readFile(resolve(root, "web/proofs", `${name}.proof`), "utf8");
      sources[name] = imported;
      await visit(imported);
    }
  }
  await visit(source);
  return { source, sources, label: relative(root, path) || basename(path) };
}
