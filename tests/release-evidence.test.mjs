// The release-evidence record (tools/release-evidence.mjs): a record is only
// of the revision it names. Its local checks run in a checkout of that
// revision, which must still be it when they end; its CI runs are those
// dispatched on that commit, of ci.yml; and its verdict fails on any failed
// check, a changed checkout, or no passing run.
import test from "node:test";
import assert from "node:assert/strict";
import { cell, checkRevision, ciRuns, localChecks, outcome, render, revision, verdict } from "../tools/release-evidence.mjs";

const sha = "0123456789abcdef0123456789abcdef01234567", other = "fedcba9876543210fedcba9876543210fedcba98";
const run = (id, { headSha = sha, event = "workflow_dispatch", workflow = "ci.yml", createdAt = `2026-09-29T0${id}:00:00Z`,
  status = "completed", conclusion = "success" } = {}) =>
  ({ databaseId: id, headSha, event, workflow, status, conclusion, url: `https://ci/${id}`, createdAt });
// A gh CLI over `runs`, which filters a listing by its --workflow and
// --commit as GitHub does, and answers each run's jobs.
const gh = runs => args => {
  if (args[0] === "run" && args[1] === "list") {
    const option = name => args.includes(name) ? args[args.indexOf(name) + 1] : null;
    return JSON.stringify(runs.filter(run => (!option("--workflow") || run.workflow === option("--workflow"))
      && (!option("--commit") || run.headSha === option("--commit"))).map(({ workflow, ...run }) => run));
  }
  const id = Number(args[2]);
  return JSON.stringify({ jobs: [{ name: `lint of ${id}`, conclusion: "success", url: `https://ci/${id}/lint`, steps: [] }] });
};

test("a CI run counts only when dispatched on the commit, in ci.yml, newest first", () => {
  const runs = ciRuns(sha, gh([run(1), run(3, { conclusion: "failure" }), run(4, { headSha: other }),
    run(5, { event: "pull_request" }), run(6, { workflow: "pages.yml" })]));
  assert.deepEqual(runs.map(run => run.databaseId), [3, 1]);
  assert.deepEqual(runs[0].jobs, [{ name: "lint of 3", conclusion: "success", url: "https://ci/3/lint" }]);
  // A pull request's run checks out a merge commit; another workflow's run,
  // or another commit's, is no run of this one.
  const none = ["No dispatched CI run of this revision passed."];
  assert.deepEqual(verdict({ ci: ciRuns(sha, gh([run(4, { headSha: other })])) }), none);
  assert.deepEqual(verdict({ ci: ciRuns(sha, gh([run(5, { event: "pull_request" })])) }), none);
  assert.deepEqual(verdict({ ci: ciRuns(sha, gh([run(6, { workflow: "pages.yml" })])) }), none);
  // A listing that returned another commit's run would not make it count.
  const unfiltered = args => args[1] === "list" ? JSON.stringify([run(4, { headSha: other })]) : gh([])(args);
  assert.deepEqual(ciRuns(sha, unfiltered), []);
});

test("the verdict fails on a failed check, a changed checkout, or no finished passing run", () => {
  const passed = { name: "Lint", passed: true }, failed = { name: "Node suite", passed: false };
  assert.deepEqual(verdict({ local: [passed], ci: [run(1)] }), []);
  assert.deepEqual(verdict({ local: [passed, failed] }), ["Node suite failed."]);
  assert.deepEqual(verdict({ local: [passed], changed: "HEAD moved to x" }), ["The checkout changed during the local checks."]);
  for (const unfinished of [run(1, { status: "in_progress", conclusion: "" }), run(1, { conclusion: "cancelled" }), run(1, { conclusion: "failure" })])
    assert.deepEqual(verdict({ ci: [unfinished] }), ["No dispatched CI run of this revision passed."]);
  // What was not asked for is not required.
  assert.deepEqual(verdict({}), []);
});

test("a check's outcome: it passes only when it ran and exited with 0", () => {
  const node = localChecks().find(check => check.name === "Node suite");
  assert.deepEqual(outcome(node, { status: 0, output: "noise\nℹ tests 9\nℹ pass 9\nℹ fail 0\nℹ duration_ms 3\n", seconds: 4 }),
    { name: "Node suite", command: "npm test", status: 0, passed: true, seconds: 4, summary: ["ℹ tests 9", "ℹ pass 9", "ℹ fail 0"] });
  // Its summary is found through the runner's colours, which it leaves out.
  assert.deepEqual(outcome(node, { status: 0, output: "\x1b[34mℹ tests 9\x1b[39m\n\x1b[34mℹ fail 0\x1b[39m\n", seconds: 1 }).summary,
    ["ℹ tests 9", "ℹ fail 0"]);
  // An error in running it fails it, even with status 0.
  assert.deepEqual(outcome(node, { status: 0, error: "ENOBUFS", output: "ℹ pass 9\n", seconds: 1 }).passed, false);
  assert.deepEqual(outcome(node, { status: 0, error: "ENOBUFS", output: "", seconds: 1 }).status, "ENOBUFS");
  // Where its pattern finds nothing, its last line is its summary.
  const pages = localChecks().find(check => check.name === "Workbench browser tests");
  assert.deepEqual(outcome(pages, { status: 1, output: "browserType.launch: Executable does not exist\n\n", seconds: 1 }).summary,
    ["browserType.launch: Executable does not exist"]);
  assert.deepEqual(outcome(pages, { status: 1, output: "", seconds: 1 }).summary, []);
});

test("the local checks are the commands CI and the project's verification run", () => {
  const command = (name, platform) => localChecks(platform).find(check => check.name === name)?.command.join(" ");
  assert.equal(command("Sanitizers", "darwin"), "make sanitize SANITIZERS=undefined");
  assert.equal(command("Sanitizers", "linux"), "make sanitize");
  assert.equal(command("Instruction coverage"), "node tools/instruction-coverage.mjs");
  assert.deepEqual(localChecks().map(check => check.command.join(" ")).filter(text => !text.startsWith("node tests/")), [
    "make -C kernel test", "make lint", localChecks()[2].command.join(" "), "make wasm", "node tools/build-stamp.mjs check",
    "node tools/instruction-coverage.mjs", "npm test", "npm run test:browser",
    "node tools/build-site.mjs"]);
});

test("the local checks run in a checkout of the revision, which must end as it began", () => {
  const made = [], removed = [], ran = [];
  const tree = sha => { made.push(sha); return "/tmp/checkout"; };
  const remove = dir => removed.push(dir);
  const checks = [{ name: "One", command: ["true"] }, { name: "Two", command: ["true"] }];
  const passing = (check, dir) => { ran.push([check.name, dir]); return { name: check.name, passed: true }; };
  const git = moved => (dir, args) => ({ "rev-parse HEAD": `${moved ?? sha}\n`, "status --porcelain": "?? node_modules\n?? .tools\n" })[args.join(" ")];
  const record = checkRevision(sha, { tree, remove, git: git(), run: passing, stamp: dir => ({ read: dir }), checks });
  assert.deepEqual([made, ran, removed], [[sha], [["One", "/tmp/checkout"], ["Two", "/tmp/checkout"]], ["/tmp/checkout"]]);
  // The shared packages' and toolchain's links are no change of the checkout.
  assert.deepEqual(record, { local: [{ name: "One", passed: true }, { name: "Two", passed: true }], changed: "", stamp: { read: "/tmp/checkout" } });
  assert.equal(checkRevision(sha, { tree, remove, git: git(other), run: passing, stamp: () => null, checks }).changed, `HEAD moved to ${other}`);
  const edited = (dir, args) => args[0] === "status" ? " M web/index.html\n?? .tools\n" : `${sha}\n`;
  assert.equal(checkRevision(sha, { tree, remove, git: edited, run: passing, stamp: () => null, checks }).changed, "M web/index.html");
  // The checkout is removed however the checks end.
  removed.length = 0;
  assert.throws(() => checkRevision(sha, { tree, remove, git: git(), run: () => { throw Error("stopped"); }, stamp: () => null, checks }), /stopped/);
  assert.deepEqual(removed, ["/tmp/checkout"]);
});

test("the revision is HEAD and the tree's changes", () => {
  const git = args => ({ "rev-parse HEAD": `${sha}\n`, "status --porcelain": "" })[args.join(" ")];
  assert.deepEqual(revision(git), { sha, changes: "" });
});

test("the record names the revision, its stamp, each outcome and the dispatched runs", () => {
  const stamp = { kernel: { sources: "a".repeat(64), outputs: "b".repeat(64) }, runtime: { sources: "c".repeat(64), outputs: "d".repeat(64) } };
  const local = [{ name: "Lint", command: "make lint", status: 0, passed: true, seconds: 3, summary: ["ok"] },
    { name: "Node suite", command: "npm test", status: 1, passed: false, seconds: 60, summary: ["ℹ fail 1"] }];
  const text = render({ sha, date: "2026-09-29T12:00:00Z", stamp, local, ci: ciRuns(sha, gh([run(7)])) });
  assert.match(text, /^# Release evidence for `0123456`$/m);
  assert.match(text, new RegExp(`^- Revision: \`${sha}\`$`, "m"));
  assert.match(text, /^- Local checks: in a fresh checkout of the revision$/m);
  assert.match(text, /^- Build stamp: kernel sources `aaaaaaaaaaaa`, outputs `bbbbbbbbbbbb`; translator copy sources `cccccccccccc`, outputs `dddddddddddd`$/m);
  assert.match(text, /^\| Lint \| make lint \| passed \| 3 \| ok \|$/m);
  assert.match(text, /^\| Node suite \| npm test \| failed \(1\) \| 60 \| ℹ fail 1 \|$/m);
  assert.match(text, /^- \[Run 7\]\(https:\/\/ci\/7\), 2026-09-29T07:00:00Z: success$/m);
  assert.match(text, /^ {2}- \[lint of 7\]\(https:\/\/ci\/7\/lint\): success$/m);
  assert.match(text, /## Verdict\n\n- Node suite failed\.\n$/);
  assert.match(render({ sha, date: "d", ci: [] }), /None\. Dispatch one with `gh workflow run ci\.yml --ref BRANCH`/);
  // A build that failed may leave a stamp of one part, or none.
  assert.match(render({ sha, date: "d", local, stamp: { runtime: stamp.runtime } }), /^- Build stamp: kernel none; translator copy sources `cccccccccccc`/m);
  assert.match(render({ sha, date: "d", local, stamp: { kernel: stamp.kernel } }), /; translator copy none$/m);
  assert.match(render({ sha, date: "d", local, stamp: null }), /^- Build stamp: none$/m);
});

test("output is shown as literal text in a table cell", () => {
  assert.equal(cell("a\\|b"), "a\\\\\\|b");
  assert.equal(cell("`x` <b>&amp; *y* _z_ [l](u) ~s~"), "\\`x\\` \\<b\\>\\&amp; \\*y\\* \\_z\\_ \\[l\\](u) \\~s\\~");
  assert.equal(cell("one\n  two"), "one two");
  const row = render({ sha, date: "d", local: [{ name: "N", command: "c", status: 0, passed: true, seconds: 0, summary: ["a\\|b"] }] })
    .split("\n").find(line => line.startsWith("| N |"));
  // Five cells, the last the summary: its pipe escaped after its backslash.
  assert.equal(row, "| N | c | passed | 0 | a\\\\\\|b |");
});
