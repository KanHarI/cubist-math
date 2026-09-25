import test from "node:test";
import assert from "node:assert/strict";
import { readFile } from "node:fs/promises";
import createCubical from "../web/dist/cubical.mjs";
import { CubicalProgram } from "../web/cubical-program.mjs";

// Every code example in the language references declares how it is checked:
//   data-check="accept"                     the example checks completely;
//   data-check="reject" data-error="text"   checking fails with that message;
//   data-check="excerpt" data-module="m"    the text is quoted from library module m;
//   data-check="fragment" data-reason="…"   an unchecked sketch, with the reason.
// An example without a declared check fails this test.
const pages = [
  { file: "language.html", scope: source => source },
  // Only the quick reference panel of the proof workspace holds examples.
  { file: "proof.html", scope: source => source.slice(source.indexOf('id="language-guide"'), source.indexOf("</details>", source.indexOf('id="language-guide"'))) },
];
const readLibrary = name => readFile(new URL(`../archive/first-library/${name}.cubist`, import.meta.url), "utf8");
const decode = text => text.replace(/&lt;/g, "<").replace(/&gt;/g, ">").replace(/&quot;/g, "\"").replace(/&#39;/g, "'").replace(/&amp;/g, "&");
const attributes = text => Object.fromEntries([...text.matchAll(/([a-z-]+)="([^"]*)"/g)].map(([, key, value]) => [key, decode(value)]));
const squash = text => text.replace(/\s+/g, " ").trim();

export function referenceExamples(file, source) {
  const examples = [];
  for (const match of source.matchAll(/<pre([^>]*)>(?:<code([^>]*)>)?([\s\S]*?)(?:<\/code>)?<\/pre>/g)) {
    const attrs = { ...attributes(match[1]), ...attributes(match[2] ?? "") };
    const line = source.slice(0, match.index).split("\n").length;
    examples.push({ label: `${file}:${line}`, attrs, text: decode(match[3]) });
  }
  return examples;
}

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

async function verify(example, index) {
  const { attrs, text, label } = example;
  const kind = attrs["data-check"];
  if (kind === "accept") {
    const { failures } = await check(text, `reference_example_${index}`);
    assert.deepEqual(failures, [], `${label} should check`);
  } else if (kind === "reject") {
    assert.ok(attrs["data-error"], `${label}: a rejected example states its data-error`);
    const { failures } = await check(text, `reference_example_${index}`);
    assert.ok(failures.length, `${label} should be rejected`);
    assert.ok(failures.some(failure => failure.includes(attrs["data-error"])),
      `${label} should fail with "${attrs["data-error"]}", got ${JSON.stringify(failures)}`);
  } else if (kind === "excerpt") {
    assert.ok(attrs["data-module"], `${label}: an excerpt names its data-module`);
    const module = await readLibrary(attrs["data-module"]);
    assert.ok(squash(module).includes(squash(text)), `${label} should quote ${attrs["data-module"]} exactly`);
  } else if (kind === "fragment") {
    assert.ok(attrs["data-reason"], `${label}: an unchecked fragment states its data-reason`);
  } else {
    assert.fail(`${label} has no declared check (data-check="${kind ?? ""}")`);
  }
}

test("every language reference example declares and passes its check", async t => {
  let index = 0;
  const counts = {}, problems = [];
  for (const { file, scope } of pages) {
    const source = scope(await readFile(new URL(`../web/${file}`, import.meta.url), "utf8"));
    for (const example of referenceExamples(file, source)) {
      // Report every failing example at once, not only the first.
      try { await verify(example, index++); }
      catch (error) { problems.push(error.message.split("\n")[0] + (error.actual ? ` ${JSON.stringify(error.actual)}` : "")); }
      counts[example.attrs["data-check"]] = (counts[example.attrs["data-check"]] ?? 0) + 1;
    }
  }
  assert.ok(index > 0, "the references contain examples");
  assert.deepEqual(problems, []);
  t.diagnostic(`reference examples: ${JSON.stringify(counts)}`);
});

test("the harness distinguishes accepted, rejected, excerpted and unmarked examples", async () => {
  const page = `
<pre><code data-check="accept">def one = succ(0);</code></pre>
<pre data-check="reject" data-error="Type mismatch">def wrong : 0 = 1 { exact refl(0); }</pre>
<pre><code data-check="excerpt" data-module="primes">def Divides(d n : Nat) =</code></pre>
<pre><code>def unmarked = 0;</code></pre>`;
  const [accepted, rejected, excerpt, unmarked] = referenceExamples("sample.html", page);
  await verify(accepted, 0);
  await verify(rejected, 1);
  await verify(excerpt, 2);
  await assert.rejects(verify(unmarked, 3), /no declared check/);
  await assert.rejects(verify({ ...rejected, attrs: { ...rejected.attrs, "data-error": "not this message" } }, 4),
    /should fail with/);
  await assert.rejects(verify({ ...accepted, text: "def wrong : 0 = 1 { exact refl(0); }" }, 5), /should check/);
});
