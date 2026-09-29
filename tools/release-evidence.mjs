// Release evidence (the H1 specification's release checklist, item 5; the
// daily report of 2026-09-29, recommendation 1): one record of the checks run
// on one revision, with the revision, its build stamp, each command and its
// outcome, and the CI jobs that ran on that same revision. A record is only
// ever of the revision it names: the working tree is clean before and after
// the local checks, and a CI run counts only when its commit is that
// revision, never an earlier run standing in for it.
//
//   node tools/release-evidence.mjs [--local] [--ci] [--out FILE]
//
// --local runs the local checks, which take tens of minutes; --ci reads the
// runs of ci.yml on the revision through the gh CLI. With neither, both. The
// record is Markdown, on standard output or in FILE. The exit status is 1
// when a local check failed, the tree changed, or no CI run of the revision
// passed.
import { execFileSync, spawnSync } from "node:child_process";
import { readFileSync, realpathSync, writeFileSync } from "node:fs";
import { fileURLToPath } from "node:url";

const root = fileURLToPath(new URL("..", import.meta.url));
const nodeSummary = /^ℹ (tests|pass|fail) \d+$/gm, pageSummary = /^(PASS|FAIL) .*$/gm;
const coverageSummary = /^.*(Archive checked|definitions derive|Coverage complete).*$/gm;

// The local checks, in order: the kernel's tests and lint; the fatal
// undefined-behaviour sanitizer, with the address sanitizer too where it runs
// (not on macOS, whose Apple clang cannot start it; CI runs both); the WASM
// build and its stamp; instruction coverage with the guide and with the
// oracle, which re-derive the archive; the Node suite; and the browser and
// site checks. A check's summary is the lines its pattern finds in its
// output, or else its last line.
export const localChecks = (platform = process.platform) => [
  { name: "Kernel tests", command: ["make", "-C", "kernel", "test"] },
  { name: "Lint", command: ["make", "lint"] },
  { name: "Sanitizers", command: ["make", "sanitize", ...(platform === "darwin" ? ["SANITIZERS=undefined"] : [])] },
  { name: "WASM build", command: ["make", "wasm"] },
  { name: "Build stamp", command: ["node", "tools/build-stamp.mjs", "check"] },
  { name: "Instruction coverage", command: ["node", "tools/instruction-coverage.mjs"], summary: coverageSummary },
  { name: "Instruction coverage with the oracle", command: ["node", "tools/instruction-coverage.mjs", "--oracle"], summary: coverageSummary },
  { name: "Node suite", command: ["npm", "test"], summary: nodeSummary },
  { name: "Workbench browser tests", command: ["npm", "run", "test:browser"], summary: pageSummary },
  ...["cubical", "statement", "proof-navigation", "landing"].map(page =>
    ({ name: `Browser test ${page}`, command: ["node", `tests/${page}.browser.mjs`] })),
  { name: "Site build", command: ["node", "tools/build-site.mjs"] },
  { name: "Site browser test", command: ["node", "tests/site.browser.mjs"], summary: pageSummary },
];

// A command's outcome: its exit status, time and summary.
export function outcome({ name, command, summary }, { status, output, seconds }) {
  const lines = summary ? [...output.matchAll(summary)].map(match => match[0].trim())
    : [output.trim().split("\n").at(-1)?.trim() ?? ""];
  return { name, command: command.join(" "), status, passed: status === 0, seconds, summary: lines.filter(Boolean) };
}
function runCheck(check) {
  const started = Date.now();
  const result = spawnSync(check.command[0], check.command.slice(1), { cwd: root, encoding: "utf8", maxBuffer: 1 << 30 });
  return outcome(check, { status: result.status ?? result.signal ?? result.error?.code ?? "not run",
    output: `${result.stdout ?? ""}${result.stderr ?? ""}`, seconds: Math.round((Date.now() - started) / 1000) });
}

// The revision: HEAD, its branch, and whether the tree is clean.
export function revision(git) {
  return { sha: git(["rev-parse", "HEAD"]).trim(), branch: git(["rev-parse", "--abbrev-ref", "HEAD"]).trim(),
    changes: git(["status", "--porcelain"]).trim() };
}

// The runs of ci.yml on exactly `sha`, newest first, each with its jobs. A
// run on any other commit is left out, whatever the listing returns.
export function ciRuns(sha, gh) {
  const runs = JSON.parse(gh(["run", "list", "--workflow", "ci.yml", "--commit", sha, "--limit", "20",
    "--json", "databaseId,headSha,status,conclusion,url,createdAt,event"]));
  return runs.filter(run => run.headSha === sha).sort((a, b) => b.createdAt.localeCompare(a.createdAt)).map(run => ({
    ...run, jobs: JSON.parse(gh(["run", "view", String(run.databaseId), "--json", "jobs"])).jobs
      .map(({ name, conclusion, url }) => ({ name, conclusion, url })) }));
}

// Whether the record passes: every local check passed, on a tree that stayed
// clean, and a CI run of the revision passed, as far as each was asked for.
export function verdict({ local, ci, changed }) {
  const failures = [];
  if (local) {
    for (const check of local) if (!check.passed) failures.push(`${check.name} failed.`);
    if (changed) failures.push("The working tree changed during the local checks.");
  }
  if (ci && !ci.some(run => run.conclusion === "success")) failures.push("No CI run of this revision passed.");
  return failures;
}

const cell = text => String(text).replaceAll("|", "\\|").replaceAll("\n", " ");
// The record, as Markdown.
export function render({ sha, branch, date, stamp, local, ci, changed }) {
  const lines = [`# Release evidence for \`${sha.slice(0, 7)}\``, "",
    `- Revision: \`${sha}\`, on ${branch}, with a clean working tree`, `- Recorded: ${date}`];
  if (stamp) lines.push(`- Build stamp: kernel sources \`${stamp.kernel.sources.slice(0, 12)}\`, outputs \`${stamp.kernel.outputs.slice(0, 12)}\`; ` +
    `translator copy sources \`${stamp.runtime.sources.slice(0, 12)}\`, outputs \`${stamp.runtime.outputs.slice(0, 12)}\``);
  if (local) {
    lines.push("", "## Local checks", "", "| Check | Command | Outcome | Seconds | Summary |", "| --- | --- | --- | --- | --- |");
    for (const check of local)
      lines.push(`| ${cell(check.name)} | \`${cell(check.command)}\` | ${check.passed ? "passed" : `failed (${cell(check.status)})`} | ${check.seconds} | ${cell(check.summary.join("; "))} |`);
    if (changed) lines.push("", `The working tree changed during the checks:\n\n\`\`\`\n${changed}\n\`\`\``);
  }
  if (ci) {
    lines.push("", "## CI runs of this revision", "");
    if (!ci.length) lines.push("None. Dispatch one with `gh workflow run ci.yml --ref BRANCH` once the revision is pushed.");
    for (const run of ci) {
      lines.push(`- [Run ${run.databaseId}](${run.url}), ${run.event}, ${run.createdAt}: ${run.status === "completed" ? run.conclusion : run.status}`);
      for (const job of run.jobs) lines.push(`  - [${job.name}](${job.url}): ${job.conclusion ?? "not finished"}`);
    }
  }
  const failures = verdict({ local, ci, changed });
  lines.push("", "## Verdict", "", failures.length ? failures.map(failure => `- ${failure}`).join("\n") : "Every check asked for passed.");
  return `${lines.join("\n")}\n`;
}

const invoked = () => { try { return realpathSync(process.argv[1]) === fileURLToPath(import.meta.url); } catch { return false; } };
if (invoked()) {
  const args = process.argv.slice(2), out = args.includes("--out") ? args[args.indexOf("--out") + 1] : null;
  const both = !args.includes("--local") && !args.includes("--ci");
  const git = argv => execFileSync("git", argv, { cwd: root, encoding: "utf8" });
  const gh = argv => execFileSync("gh", argv, { cwd: root, encoding: "utf8" });
  const before = revision(git);
  if (before.changes) {
    console.error(`The working tree has changes; evidence is recorded only of a committed revision:\n${before.changes}`);
    process.exit(2);
  }
  const record = { ...before, date: new Date().toISOString() };
  if (both || args.includes("--local")) {
    record.local = [];
    for (const check of localChecks()) {
      console.error(`${check.name}: ${check.command.join(" ")}`);
      record.local.push(runCheck(check));
    }
    const after = revision(git);
    record.changed = after.sha !== before.sha ? `HEAD moved to ${after.sha}` : after.changes;
    try { record.stamp = JSON.parse(readFileSync(new URL("../web/dist/build-stamp.json", import.meta.url), "utf8")); }
    catch { record.stamp = null; }
  }
  if (both || args.includes("--ci")) record.ci = ciRuns(record.sha, gh);
  const text = render(record);
  if (out) writeFileSync(out, text); else process.stdout.write(text);
  process.exitCode = verdict(record).length ? 1 : 0;
}
