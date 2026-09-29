// The release-evidence record (tools/release-evidence.mjs): a record is only
// of the revision it names, its CI runs are that revision's alone, and its
// verdict fails on any failed check, a changed tree, or no passing CI run.
import test from "node:test";
import assert from "node:assert/strict";
import { ciRuns, localChecks, outcome, render, revision, verdict } from "../tools/release-evidence.mjs";

const sha = "0123456789abcdef0123456789abcdef01234567", other = "fedcba9876543210fedcba9876543210fedcba98";
// A gh CLI that lists runs of several commits, as a listing might, and
// answers each run's jobs.
const gh = runs => args => {
  if (args[0] === "run" && args[1] === "list") return JSON.stringify(runs);
  const id = Number(args[2]);
  return JSON.stringify({ jobs: [{ name: `lint of ${id}`, conclusion: "success", url: `https://ci/${id}/lint`, steps: [] }] });
};
const run = (id, headSha, createdAt, conclusion = "success") =>
  ({ databaseId: id, headSha, status: "completed", conclusion, url: `https://ci/${id}`, createdAt, event: "workflow_dispatch" });

test("a CI run counts only for the commit it ran on, newest first", () => {
  const runs = ciRuns(sha, gh([run(1, sha, "2026-09-28T10:00:00Z"), run(2, other, "2026-09-29T10:00:00Z"), run(3, sha, "2026-09-29T09:00:00Z", "failure")]));
  assert.deepEqual(runs.map(run => run.databaseId), [3, 1]);
  assert.deepEqual(runs[0].jobs, [{ name: "lint of 3", conclusion: "success", url: "https://ci/3/lint" }]);
  // An earlier commit's passing run does not stand in for this one's.
  assert.deepEqual(verdict({ ci: ciRuns(sha, gh([run(2, other, "2026-09-29T10:00:00Z")])) }), ["No CI run of this revision passed."]);
});

test("the verdict fails on a failed check, a changed tree, or no passing run", () => {
  const passed = { name: "Lint", passed: true }, failed = { name: "Node suite", passed: false };
  assert.deepEqual(verdict({ local: [passed], ci: [run(1, sha, "t")] }), []);
  assert.deepEqual(verdict({ local: [passed, failed] }), ["Node suite failed."]);
  assert.deepEqual(verdict({ local: [passed], changed: " M web/index.html" }), ["The working tree changed during the local checks."]);
  assert.deepEqual(verdict({ ci: [run(1, sha, "t", "failure")] }), ["No CI run of this revision passed."]);
  // What was not asked for is not required.
  assert.deepEqual(verdict({}), []);
});

test("a check's outcome: its status, and the summary its pattern finds or its last line", () => {
  const node = localChecks().find(check => check.name === "Node suite");
  assert.deepEqual(outcome(node, { status: 0, output: "noise\nℹ tests 9\nℹ pass 9\nℹ fail 0\nℹ duration_ms 3\n", seconds: 4 }),
    { name: "Node suite", command: "npm test", status: 0, passed: true, seconds: 4, summary: ["ℹ tests 9", "ℹ pass 9", "ℹ fail 0"] });
  const lint = localChecks().find(check => check.name === "Lint");
  assert.deepEqual(outcome(lint, { status: 2, output: "checking\nerror: style\n\n", seconds: 1 }).summary, ["error: style"]);
  assert.equal(outcome(lint, { status: 2, output: "", seconds: 1 }).passed, false);
});

test("the local checks run both sanitizers but where the address sanitizer cannot start", () => {
  const sanitizers = platform => localChecks(platform).find(check => check.name === "Sanitizers").command.join(" ");
  assert.equal(sanitizers("darwin"), "make sanitize SANITIZERS=undefined");
  assert.equal(sanitizers("linux"), "make sanitize");
  const names = localChecks().map(check => check.name);
  for (const name of ["Kernel tests", "Lint", "WASM build", "Build stamp", "Instruction coverage with the oracle", "Node suite", "Site browser test"])
    assert.ok(names.includes(name), name);
});

test("the revision is HEAD, its branch and the tree's changes", () => {
  const git = args => ({ "rev-parse HEAD": `${sha}\n`, "rev-parse --abbrev-ref HEAD": "h1-signatures\n", "status --porcelain": "" })[args.join(" ")];
  assert.deepEqual(revision(git), { sha, branch: "h1-signatures", changes: "" });
});

test("the record names the revision, its stamp, each command's outcome and its CI jobs", () => {
  const stamp = { kernel: { sources: "a".repeat(64), outputs: "b".repeat(64) }, runtime: { sources: "c".repeat(64), outputs: "d".repeat(64) } };
  const local = [{ name: "Lint", command: "make lint", status: 0, passed: true, seconds: 3, summary: ["ok | done"] },
    { name: "Node suite", command: "npm test", status: 1, passed: false, seconds: 60, summary: ["ℹ fail 1"] }];
  const ci = ciRuns(sha, gh([run(7, sha, "2026-09-29T10:00:00Z")]));
  const text = render({ sha, branch: "h1-signatures", date: "2026-09-29T12:00:00Z", stamp, local, ci });
  assert.match(text, /^# Release evidence for `0123456`$/m);
  assert.match(text, new RegExp(`- Revision: \`${sha}\`, on h1-signatures`));
  assert.match(text, /kernel sources `aaaaaaaaaaaa`, outputs `bbbbbbbbbbbb`; translator copy sources `cccccccccccc`/);
  assert.match(text, /^\| Lint \| `make lint` \| passed \| 3 \| ok \\\| done \|$/m);
  assert.match(text, /^\| Node suite \| `npm test` \| failed \(1\) \| 60 \| ℹ fail 1 \|$/m);
  assert.match(text, /^- \[Run 7\]\(https:\/\/ci\/7\), workflow_dispatch, 2026-09-29T10:00:00Z: success$/m);
  assert.match(text, /^ {2}- \[lint of 7\]\(https:\/\/ci\/7\/lint\): success$/m);
  assert.match(text, /## Verdict\n\n- Node suite failed\.\n$/);
  assert.match(render({ sha, branch: "main", date: "d", ci: [] }), /None\. Dispatch one with `gh workflow run ci\.yml --ref BRANCH`/);
});
