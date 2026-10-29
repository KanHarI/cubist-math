// Every place in web/ that starts or ends a worker (`new Worker(`,
// `.terminate(`), and how it keeps clear of a page's maintenance
// (web/worker-maintenance.mjs). A worker that holds what a page rebuilds or
// restores after a kernel failure, the proof page's and a standalone REPL's,
// is started, replaced and ended only as maintenance, or as a request is
// sent that maintenance's gate let through, so that nothing ends it while a
// rebuild or a restore runs on it. Any other acts at once, with nothing
// awaited between deciding and acting. A site not listed here fails until
// it is, with its reason.
import test from "node:test";
import assert from "node:assert/strict";
import { readFileSync, readdirSync, statSync } from "node:fs";
import { join, relative } from "node:path";
import { fileURLToPath } from "node:url";

const root = fileURLToPath(new URL("..", import.meta.url));
const sources = directory => readdirSync(directory).flatMap(name => {
  const path = join(directory, name);
  if (statSync(path).isDirectory()) return name === "dist" ? [] : sources(path);
  return name.endsWith(".mjs") ? [path] : [];
});
const read = path => readFileSync(join(root, path), "utf8");

const sites = new Map([
  ["web/proof.mjs", new Map([
    ["worker = new WorkerRequests(new Worker(url, { type: \"module\" }), { onError: error => {",
      "in startWorker, which only replaceWorker calls, as maintenance"],
    ["worker?.terminate();", "in replaceWorker, as maintenance"],
    ["currentWorker.terminate(new Error(\"The checking worker stopped making progress. Reload the page to restart the kernel.\"));",
      "a stalled request's deadline ends the worker it was sent to, at once, and tells the page only while that worker is current"],
  ])],
  ["web/repl-console.mjs", new Map([
    ["worker ??= new WorkerRequests(new Worker(new URL(\"./cubical-worker.mjs\", import.meta.url), { type: \"module\" }),",
      "in standaloneRepl's send, which only its maintenance's gate calls"],
  ])],
  ["web/reference/examples.mjs", new Map([
    ["worker ??= new WorkerRequests(new Worker(workerURL, { type: \"module\" }),",
      "as a request is sent; each example is checked in turn, and nothing is rebuilt or restored"],
  ])],
  ["web/cubical-workbench.mjs", new Map([
    ["const requests = new WorkerRequests(new Worker(\"./cubical-workbench-worker.mjs\", { type: \"module\" }), { onError: workerStopped });",
      "once, as the page loads; never replaced"],
    ["requests.terminate(error);", "when the worker fails, at once; the page then stops"],
    ["addEventListener(\"pagehide\", () => requests.terminate());", "as the page goes"],
  ])],
  ["web/benchmark.mjs", new Map([
    ["worker?.terminate(); worker = null;", "a benchmark run's own worker, which holds no session, ended at once"],
    ["worker = new Worker(new URL(\"./benchmark-worker.mjs\", import.meta.url), { type: \"module\" });",
      "a benchmark run's own worker, started at once once the last is ended"],
  ])],
  ["web/worker-requests.mjs", new Map([
    ["if (error.fatal) { this.terminate(error); onError(error); }", "the transport, on a fatal reply"],
    ["this.terminate(error);", "the transport, when its worker fails to load or run"],
    ["this.worker.terminate();", "the transport's own terminate"],
  ])],
]);

test("every site in web/ that starts or ends a worker is listed, with how it keeps clear of maintenance", () => {
  const found = new Map();
  for (const path of sources(join(root, "web"))) {
    const lines = readFileSync(path, "utf8").split("\n").map(line => line.trim())
      .filter(line => /new Worker\(|\.terminate\(/.test(line) && !line.startsWith("//"));
    if (lines.length) found.set(relative(root, path), lines);
  }
  assert.deepEqual([...found.keys()].sort(), [...sites.keys()].sort());
  for (const [path, lines] of found) assert.deepEqual(lines.sort(), [...sites.get(path).keys()].sort(), path);
});

// A top-level function's text, to its closing brace.
const body = (source, header) => {
  const start = source.indexOf(header);
  assert.ok(start >= 0, header);
  return source.slice(start, source.indexOf("\n}\n", start) + 2);
};

test("the proof page starts and replaces its worker only as maintenance", () => {
  const proof = read("web/proof.mjs"), replace = body(proof, "function replaceWorker(");
  // startWorker is called once, in replaceWorker, which runs as maintenance.
  const calls = [...proof.matchAll(/(?<!function )\bstartWorker\(/g)];
  assert.equal(calls.length, 1);
  assert.ok(replace.includes("startWorker("));
  assert.match(replace, /^function replaceWorker\(.*\) \{\n  return upkeep\.run\(/);
  // The old worker is ended there too, and nowhere else but by a stalled
  // request's deadline.
  assert.ok(replace.includes("worker?.terminate();"));
  // Each replacement says whether it is still wanted when its turn comes:
  // a compiler update, a failure's replacement, and the reader's retry.
  for (const name of ["refreshCompiler", "restartAfterFault", "retry"])
    assert.match(body(proof, `function ${name}(`), /replaceWorker\(\{[^]*prepare: /, name);
  assert.match(proof, /\nawait replaceWorker\(\);\n/);
});

test("a standalone REPL starts its worker only as a request its maintenance let through is sent", () => {
  const repl = body(read("web/repl-console.mjs"), "export function standaloneRepl(");
  assert.match(repl, /const send = \(command, args\) => \(\) => \{\n    worker \?\?= new WorkerRequests/);
  const uses = [...repl.matchAll(/\bsend\(command, args\)/g)].map(match => repl.slice(Math.max(0, match.index - 40), match.index));
  assert.equal(uses.length, 2);
  for (const use of uses) assert.match(use, /upkeep\.(request|internal)\($/);
  assert.match(repl, /maintain: work => upkeep\.run\(\(\) => work\(internal\)\)/);
});
