import test from "node:test";
import assert from "node:assert/strict";
import { readFile, readdir, mkdtemp, writeFile, rm } from "node:fs/promises";
import { spawnSync } from "node:child_process";
import { tmpdir } from "node:os";
import { join } from "node:path";
import { fileURLToPath } from "node:url";
import createCubical from "../web/dist/cubical.mjs";
import { CubicalProgram } from "../web/cubical-program.mjs";
import { ReplSession, replTranscript } from "../web/repl-session.mjs";
import { budget } from "./timing.mjs";
import { referenceExamples, statedErrors, transcript } from "./reference-pages.mjs";

// Every code example in the language references declares how it is checked:
//   data-check="accept"                     the example checks completely;
//   data-check="reject"                     checking fails with the errors stated in
//                                           the example's `// Error: …` comments;
//   data-check="excerpt" data-module="m"    the text is quoted from library module m;
//   data-check="fragment" data-reason="…"   an unchecked sketch, with the reason;
//   data-check="cli" data-files="a,b"      a command-line session, run for real;
//   data-check="repl"                      a REPL transcript, run on top of the
//                                           accepted example before it on the page
//                                           (data-base="none": on an empty program).
// An accepted example with data-name="a" on the same page is the file a.cubist
// of a session. An example without a declared check fails this test.
const chapters = (await readdir(new URL("../web/reference/", import.meta.url))).filter(name => name.endsWith(".html")).sort();
const pages = [
  { file: "language.html", scope: source => source },
  ...chapters.map(name => ({ file: `reference/${name}`, scope: source => source })),
  // Only the quick reference panel of the proof workspace holds examples.
  { file: "proof.html", scope: source => source.slice(source.indexOf('id="language-guide"'), source.indexOf("</details>", source.indexOf('id="language-guide"'))) },
];
// Modules resolve as in the CLI: the rebuilt library first, then the archive.
const readLibrary = name => readFile(new URL(`../library/${name}.cubist`, import.meta.url), "utf8")
  .catch(error => { if (error.code !== "ENOENT") throw error; return readFile(new URL(`../archive/first-library/${name}.cubist`, import.meta.url), "utf8"); });
const squash = text => text.replace(/\s+/g, " ").trim();

async function check(text, name) {
  const program = new CubicalProgram(await createCubical(), readLibrary, { collectReferences: false });
  try {
    const result = await program.check(text, name);
    const failures = result.outputs.filter(output => !output.verified && !output.template)
      .map(output => `${output.name}: ${output.reason}`);
    const gaps = program.gaps.map(gap => `${gap.module ?? "?"}${gap.name ? `.${gap.name}` : ""}: ${gap.reason}`);
    return { failures: [...failures, ...gaps] };
  } catch (error) {
    return { failures: [error.message] };
  } finally { program.dispose(); }
}

const cli = fileURLToPath(new URL("../cli/repl.mjs", import.meta.url));
const linePattern = line => new RegExp(`^${line.split("…").map(part => part.replace(/[.*+?^${}()|[\]\\]/g, "\\$&")).join(".*")}$`);

async function runSession(example, named) {
  const { args, input, expected } = transcript(example.text);
  const directory = await mkdtemp(join(tmpdir(), "cubist-reference-"));
  try {
    for (const name of (example.attrs["data-files"] ?? "").split(",").filter(Boolean)) {
      assert.ok(named.has(name), `${example.label}: no accepted example with data-name="${name}"`);
      await writeFile(join(directory, `${name}.cubist`), named.get(name));
    }
    const run = spawnSync(process.execPath, [cli, ...args], { cwd: directory, encoding: "utf8",
      input: input.length ? `${input.join("\n")}\n` : "", timeout: budget(120000) });
    const streams = [run.stdout, run.stderr].map(output => ({ lines: output.split("\n").map(line => line.trimEnd()), next: 0 }));
    for (const line of expected) {
      const pattern = linePattern(line);
      const stream = streams.find(({ lines, next }) => lines.slice(next).some(candidate => pattern.test(candidate)));
      assert.ok(stream, `${example.label}: output line not found in order: ${line}\n${run.stdout}${run.stderr}`);
      stream.next += stream.lines.slice(stream.next).findIndex(candidate => pattern.test(candidate)) + 1;
    }
  } finally { await rm(directory, { recursive: true, force: true }); }
}

// Each entry's results must be exactly the transcript's lines after it.
async function runRepl({ label, text, attrs }, base) {
  const program = new CubicalProgram(await createCubical(), readLibrary, { collectReferences: false });
  try {
    let session = new ReplSession(program);
    if (attrs["data-base"] !== "none") {
      assert.ok(base, `${label}: a REPL example follows the accepted example it runs on`);
      const result = await program.check(base, "example");
      assert.ok(result.complete, `${label}: the example before it should check`);
      session = new ReplSession(program, { base: "example" });
    }
    for (const { input, results } of replTranscript(text)) {
      const actual = (await session.run(input)).flatMap(result => result.text.split("\n"));
      const message = `${label}: \`${input}\` gives ${JSON.stringify(actual)}`;
      assert.equal(actual.length, results.length, message);
      results.forEach((line, i) => assert.match(actual[i], linePattern(line), message));
    }
  } finally { program.dispose(); }
}

async function verify(example, index, named = new Map(), base = null) {
  const { attrs, text, label } = example;
  const kind = attrs["data-check"];
  assert.ok(!("data-error" in attrs), `${label}: state the error as an \`// Error:\` comment, not data-error`);
  if (kind === "accept") {
    assert.deepEqual(statedErrors(text), [], `${label}: an accepted example states no error`);
    const { failures } = await check(text, `reference_example_${index}`);
    assert.deepEqual(failures, [], `${label} should check`);
  } else if (kind === "reject") {
    const stated = statedErrors(text);
    assert.ok(stated.length, `${label}: a rejected example states its errors in \`// Error:\` comments`);
    const { failures } = await check(text, `reference_example_${index}`);
    assert.ok(failures.length, `${label} should be rejected`);
    for (const error of stated)
      assert.ok(failures.some(failure => failure.includes(error)),
        `${label} should fail with "${error}", got ${JSON.stringify(failures)}`);
    for (const failure of failures)
      assert.ok(stated.some(error => failure.includes(error)), `${label}: the error "${failure}" is not stated in a comment`);
  } else if (kind === "excerpt") {
    assert.ok(attrs["data-module"], `${label}: an excerpt names its data-module`);
    const module = await readLibrary(attrs["data-module"]);
    assert.ok(squash(module).includes(squash(text)), `${label} should quote ${attrs["data-module"]} exactly`);
  } else if (kind === "fragment") {
    assert.ok(attrs["data-reason"], `${label}: an unchecked fragment states its data-reason`);
  } else if (kind === "cli") {
    await runSession(example, named);
  } else if (kind === "repl") {
    await runRepl(example, base);
  } else {
    assert.fail(`${label} has no declared check (data-check="${kind ?? ""}")`);
  }
}

test("every language reference example declares and passes its check", async t => {
  let index = 0;
  const counts = {}, problems = [];
  for (const { file, scope } of pages) {
    const source = scope(await readFile(new URL(`../web/${file}`, import.meta.url), "utf8"));
    const examples = referenceExamples(file, source);
    const named = new Map(examples.filter(example => example.attrs["data-name"] && example.attrs["data-check"] === "accept")
      .map(example => [example.attrs["data-name"], example.text]));
    let base = null;
    for (const example of examples) {
      // Report every failing example at once, not only the first.
      try { await verify(example, index++, named, base); }
      catch (error) { problems.push(error.message.split("\n")[0] + (error.actual ? ` ${JSON.stringify(error.actual)}` : "")); }
      counts[example.attrs["data-check"]] = (counts[example.attrs["data-check"]] ?? 0) + 1;
      if (example.attrs["data-check"] === "accept") base = example.text;
    }
  }
  assert.ok(index > 0, "the references contain examples");
  assert.deepEqual(problems, []);
  t.diagnostic(`reference examples: ${JSON.stringify(counts)}`);
});

test("the harness distinguishes accepted, rejected, excerpted and unmarked examples", async () => {
  const page = `
<pre><code data-check="accept">def one := succ(0);</code></pre>
<pre data-check="reject">def wrong : 0 = 1 { exact refl(0); }  // Error: Type mismatch: found 0 = 0, expected 0 = 1.</pre>
<pre><code data-check="excerpt" data-module="primes">def Divides(d, n : Nat) :=</code></pre>
<pre><code>def unmarked := 0;</code></pre>`;
  const [accepted, rejected, excerpt, unmarked] = referenceExamples("sample.html", page);
  await verify(accepted, 0);
  await verify(rejected, 1);
  await verify(excerpt, 2);
  await assert.rejects(verify(unmarked, 3), /no declared check/);
  await assert.rejects(verify({ ...rejected, text: "def wrong : 0 = 1 { exact refl(0); }  // Error: not this message" }, 4),
    /should fail with/);
  await assert.rejects(verify({ ...rejected, text: "def wrong : 0 = 1 { exact refl(0); }" }, 6), /states its errors/);
  await assert.rejects(verify({ ...rejected, text: "def wrong : 0 = 1 { exact refl(0); }  // Error: Type mismatch: found 0 = 0, expected 0 = 1.\ndef later := missing;" }, 7),
    /is not stated in a comment/);
  await assert.rejects(verify({ ...accepted, text: "def one := succ(0);  // Error: Type mismatch: found Nat, expected Unit." }, 8), /states no error/);
  await assert.rejects(verify({ ...rejected, attrs: { ...rejected.attrs, "data-error": "Type mismatch" } }, 9), /not data-error/);
  assert.deepEqual(statedErrors("  // Error: first part\n  //   second part\nx;  // Error: other\n  //   not a continuation"),
    ["first part second part", "other"]);
  await assert.rejects(verify({ ...accepted, text: "def wrong : 0 = 1 { exact refl(0); }" }, 5), /should check/);
});

test("the harness replays REPL transcripts on the example before them", async () => {
  const transcriptOf = text => ({ label: "sample.html:1", attrs: { "data-check": "repl" }, text });
  const base = "def two := succ(succ(0));";
  await verify(transcriptOf("> typeof two;\nNat\n> let three := succ(two);\nthree : Nat\n> three\n3"), 0, new Map(), base);
  await assert.rejects(verify(transcriptOf("> evaluate two;\n3"), 1, new Map(), base), /gives \["2"\]/);
  await assert.rejects(verify(transcriptOf("> evaluate two;"), 2, new Map(), base), /gives \["2"\]/);
  await assert.rejects(verify(transcriptOf("> evaluate two;\n2"), 3), /follows the accepted example/);
  await verify({ ...transcriptOf("> evaluate succ(1);\n2"), attrs: { "data-check": "repl", "data-base": "none" } }, 4);
});

test("the harness runs command-line sessions against named examples", async () => {
  const named = new Map([["sample", "def two := succ(succ(0));\nevaluate two expecting 2;\n"]]);
  const session = text => ({ label: "sample.html:1", attrs: { "data-check": "cli", "data-files": "sample" }, text });
  await verify(session("$ node cli/repl.mjs check sample.cubist\nChecked 1 declarations · … kernel steps\nevaluate at line 2: 2"), 0, named);
  await verify(session("$ node cli/repl.mjs\n> check sample.cubist\n> inspect two\nChecked …\nAssumptions: none\n> inspect missing\nNo checked native definition for this name."), 1, named);
  await assert.rejects(verify(session("$ node cli/repl.mjs check sample.cubist\nevaluate at line 2: 3"), 2, named), /output line not found/);
  await assert.rejects(verify(session("$ node cli/repl.mjs check sample.cubist\nAssumptions: none\nChecked …"), 3, named), /output line not found/);
  await assert.rejects(verify({ ...session("$ node cli/repl.mjs check other.cubist"), attrs: { "data-check": "cli", "data-files": "other" } }, 4, named),
    /no accepted example with data-name="other"/);
  assert.throws(() => transcript("$ ls\n"), /one `node cli\/repl.mjs` command/);
});
