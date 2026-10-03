// Release evidence (the H1 specification's release checklist, item 5; the
// daily report of 2026-09-29, recommendation 1): one record of the checks run
// on one revision, with the revision, its build stamp, each command and its
// outcome, and the CI jobs that ran on that same revision. A record is only
// ever of the revision it names. The local checks run in a fresh checkout of
// it, apart from the developer's tree, so every build in them is made from
// it, and that checkout must still be the revision, unchanged, when they end.
// A CI run counts only when it was dispatched on that commit: a pull
// request's run checks out a merge commit, and no run of another commit
// stands in for it.
//
//   node tools/release-evidence.mjs [--local] [--ci] [--out FILE]
//
// The revision is HEAD's commit. --local runs the local checks, which take
// tens of minutes; --ci reads the runs of ci.yml on the revision through the
// gh CLI. With neither, both. The record is Markdown, on standard output or in
// FILE. The exit status is 1 when a local check failed, the checkout changed,
// or no dispatched CI run of the revision passed.
import { execFileSync, spawnSync } from "node:child_process";
import { existsSync, mkdtempSync, readFileSync, realpathSync, rmSync, symlinkSync, writeFileSync } from "node:fs";
import { tmpdir } from "node:os";
import { join } from "node:path";
import { fileURLToPath } from "node:url";

const root = fileURLToPath(new URL("..", import.meta.url));
const nodeSummary = /^ℹ (tests|pass|fail) \d+$/gm, pageSummary = /^(PASS|FAIL) .*$/gm;
const coverageSummary = /^.*(Archive checked|definitions derive|Coverage complete).*$/gm;

// The local checks, in order: the kernel's tests and lint; the fatal
// undefined-behaviour sanitizer, with the address sanitizer too where it runs
// (not on macOS, whose Apple clang cannot start it; CI runs both); the WASM
// build and its stamp; instruction coverage, which checks the archive and
// re-derives every definition; the Node suite; and the browser and site
// checks. A check's summary is the lines its pattern finds in its
// output, or else its last line.
export const localChecks = (platform = process.platform) => [
  { name: "Kernel tests", command: ["make", "-C", "kernel", "test"] },
  { name: "Lint", command: ["make", "lint"] },
  { name: "Sanitizers", command: ["make", "sanitize", ...(platform === "darwin" ? ["SANITIZERS=undefined"] : [])] },
  { name: "WASM build", command: ["make", "wasm"] },
  { name: "Build stamp", command: ["node", "tools/build-stamp.mjs", "check"] },
  { name: "Instruction coverage", command: ["node", "tools/instruction-coverage.mjs"], summary: coverageSummary },
  { name: "Node suite", command: ["npm", "test"], summary: nodeSummary },
  { name: "Workbench browser tests", command: ["npm", "run", "test:browser"], summary: pageSummary },
  ...["cubical", "statement", "proof-navigation", "landing"].map(page =>
    ({ name: `Browser test ${page}`, command: ["node", `tests/${page}.browser.mjs`] })),
  { name: "Site build", command: ["node", "tools/build-site.mjs"] },
  { name: "Site browser test", command: ["node", "tests/site.browser.mjs"], summary: pageSummary },
];

// A command's outcome. It passed only when it ran and exited with 0: an
// error in running it, such as output beyond the buffer, fails it, whatever
// it exited with. Its output is read without terminal escapes, such as the
// colours of the Node test runner's summary.
export function outcome({ name, command, summary }, { status, error = null, output: raw, seconds }) {
  const output = raw.replace(/\x1b\[[0-?]*[ -/]*[@-~]/g, "");
  const found = summary ? [...output.matchAll(summary)].map(match => match[0].trim()).filter(Boolean) : [];
  const last = output.trim().split("\n").at(-1)?.trim();
  return { name, command: command.join(" "), status: error ?? status, passed: !error && status === 0, seconds,
    summary: found.length ? found : last ? [last] : [] };
}
function runCheck(check, cwd) {
  const started = Date.now();
  const result = spawnSync(check.command[0], check.command.slice(1), { cwd, encoding: "utf8", maxBuffer: 1 << 30 });
  return outcome(check, { status: result.status ?? result.signal, error: result.error?.code ?? result.error?.message ?? null,
    output: `${result.stdout ?? ""}${result.stderr ?? ""}`, seconds: Math.round((Date.now() - started) / 1000) });
}

// The revision of a checkout: its HEAD and the changes to its tree.
export function revision(git) {
  return { sha: git(["rev-parse", "HEAD"]).trim(), changes: git(["status", "--porcelain"]).trim() };
}

// The local checks of `sha`, in a checkout of it that `tree` makes and
// `remove` takes away, however they end. The checkout's links to the shared
// packages and toolchain are no changes of it.
export function checkRevision(sha, { tree, remove, git, run, stamp, checks = localChecks() }) {
  const dir = tree(sha);
  try {
    const local = checks.map(check => run(check, dir));
    const after = revision(args => git(dir, args));
    const changes = after.changes.split("\n").filter(line => line && !/^\?\? (node_modules|\.tools)$/.test(line)).join("\n");
    return { local, changed: after.sha !== sha ? `HEAD moved to ${after.sha}` : changes, stamp: stamp(dir) };
  } finally { remove(dir); }
}

// The runs of ci.yml dispatched on exactly `sha`, newest first, each with its
// jobs. A pull request's run checks out a merge commit, not `sha`, and a run
// of another commit or workflow is no run of this one.
export function ciRuns(sha, gh) {
  const runs = JSON.parse(gh(["run", "list", "--workflow", "ci.yml", "--commit", sha, "--limit", "50",
    "--json", "databaseId,headSha,event,status,conclusion,url,createdAt"]));
  return runs.filter(run => run.headSha === sha && run.event === "workflow_dispatch")
    .sort((a, b) => b.createdAt.localeCompare(a.createdAt)).map(run => ({
      ...run, jobs: JSON.parse(gh(["run", "view", String(run.databaseId), "--json", "jobs"])).jobs
        .map(({ name, conclusion, url }) => ({ name, conclusion, url })) }));
}

// Whether the record passes: every local check passed, in a checkout that
// stayed the revision, and a dispatched CI run of the revision passed, as far
// as each was asked for.
export function verdict({ local, ci, changed }) {
  const failures = [];
  if (local) {
    for (const check of local) if (!check.passed) failures.push(`${check.name} failed.`);
    if (changed) failures.push("The checkout changed during the local checks.");
  }
  if (ci && !ci.some(run => run.status === "completed" && run.conclusion === "success"))
    failures.push("No dispatched CI run of this revision passed.");
  return failures;
}

// Output as the text of a table cell: backslashes first, then the characters
// that would end the cell, open code, HTML, emphasis or a link.
export const cell = text => String(text).replaceAll("\\", "\\\\").replace(/[|`<>&*_[\]~]/g, "\\$&").replace(/\s*\n\s*/g, " ");
const hash = part => part ? `sources \`${part.sources?.slice(0, 12) ?? "none"}\`, outputs \`${part.outputs?.slice(0, 12) ?? "none"}\`` : "none";
// The record, as Markdown.
export function render({ sha, date, stamp, local, ci, changed }) {
  const lines = [`# Release evidence for \`${sha.slice(0, 7)}\``, "", `- Revision: \`${sha}\``, `- Recorded: ${date}`];
  if (local) {
    lines.push("- Local checks: in a fresh checkout of the revision",
      stamp ? `- Build stamp: kernel ${hash(stamp.kernel)}; translator copy ${hash(stamp.runtime)}` : "- Build stamp: none");
    lines.push("", "## Local checks", "", "| Check | Command | Outcome | Seconds | Summary |", "| --- | --- | --- | --- | --- |");
    for (const check of local)
      lines.push(`| ${cell(check.name)} | ${cell(check.command)} | ${check.passed ? "passed" : `failed (${cell(check.status)})`} | ${check.seconds} | ${cell(check.summary.join("; "))} |`);
    if (changed) lines.push("", "The checkout changed during the checks:", "", "```", changed, "```");
  }
  if (ci) {
    lines.push("", "## CI runs dispatched on this revision", "");
    if (!ci.length) lines.push("None. Dispatch one with `gh workflow run ci.yml --ref BRANCH` once the revision is pushed.");
    for (const run of ci) {
      lines.push(`- [Run ${run.databaseId}](${run.url}), ${run.createdAt}: ${run.status === "completed" ? run.conclusion : run.status}`);
      for (const job of run.jobs) lines.push(`  - [${cell(job.name)}](${job.url}): ${job.conclusion || "not finished"}`);
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
  const git = (cwd, argv) => execFileSync("git", argv, { cwd, encoding: "utf8" });
  const record = { sha: revision(argv => git(root, argv)).sha, date: new Date().toISOString() };
  if (both || args.includes("--local")) Object.assign(record, checkRevision(record.sha, {
    // A worktree of its own, detached at the revision, with the developer's
    // installed packages and toolchain linked in.
    tree: sha => {
      const dir = mkdtempSync(join(tmpdir(), `cubist-evidence-${sha.slice(0, 7)}-`));
      git(root, ["worktree", "add", "--detach", dir, sha]);
      for (const shared of ["node_modules", ".tools"]) if (existsSync(join(root, shared))) symlinkSync(join(root, shared), join(dir, shared));
      return dir;
    },
    remove: dir => {
      try { git(root, ["worktree", "remove", "--force", dir]); }
      catch { rmSync(dir, { recursive: true, force: true }); git(root, ["worktree", "prune"]); }
    },
    git,
    run: (check, dir) => { console.error(`${check.name}: ${check.command.join(" ")}`); return runCheck(check, dir); },
    stamp: dir => { try { return JSON.parse(readFileSync(join(dir, "web/dist/build-stamp.json"), "utf8")); } catch { return null; } },
  }));
  if (both || args.includes("--ci")) record.ci = ciRuns(record.sha, argv => execFileSync("gh", argv, { cwd: root, encoding: "utf8" }));
  const text = render(record);
  if (out) writeFileSync(out, text); else process.stdout.write(text);
  process.exitCode = verdict(record).length ? 1 : 0;
}
