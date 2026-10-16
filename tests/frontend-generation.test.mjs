import "./fresh-build.mjs";
import test from "node:test";
import assert from "node:assert/strict";
import { readFile } from "node:fs/promises";
import createCubical from "../web/dist/cubical.mjs";
import { lint } from "../web/cubist/lint.mjs";
import { checkProgram } from "./check-program.mjs";
import { cases, extras, observe } from "./frontend-generation-cases.mjs";
import { observeModule } from "./module-observation.mjs";

const module = await createCubical();

// Semantic expectations stay in the independently written source fixtures.
// Group prefixes remain selectable by the mutation gate.
for (const c of cases) test(`${c.group}: [${c.id}] ${c.contract}`, async t => {
  const { observed, desired } = await observe(t, c, module);
  assert.deepEqual(observed, desired, c.id);
});

test("case IDs are unique, extras name cases, and the manifest lists every case", async () => {
  const ids = cases.map(c => c.id);
  assert.equal(new Set(ids).size, ids.length);
  for (const id of Object.keys(extras)) assert.ok(ids.includes(id), id);
  const manifest = await readFile(new URL("./fixtures/frontend-generation.md", import.meta.url), "utf8");
  const listed = [...manifest.matchAll(/^\| `([\w-]+)` \|/gm)].map(match => match[1]);
  assert.deepEqual(listed.sort(), [...ids].sort());
});

test("historical and passing coverage still names executable tests", async () => {
  const manifestURL = new URL("./fixtures/frontend-generation.md", import.meta.url);
  const manifest = await readFile(manifestURL, "utf8");
  const rows = [...manifest.matchAll(/^\| ([HP][1-5]) \| \[[^\]]+\]\(([^)]+)\) \| `([^`]+)` \|$/gm)];
  assert.deepEqual(rows.map(row => row[1]).sort(), ["H1", "H2", "H3", "H4", "H5", "P1", "P2", "P3", "P4", "P5"]);
  for (const [, id, path, name] of rows) {
    const source = await readFile(new URL(path, manifestURL), "utf8");
    assert.ok(source.includes(`test(${JSON.stringify(name)},`), `${id}: ${path} must still execute ${name}`);
  }
});

// G5's advice stays suppressed on operation binders; ordinary unused binders
// keep theirs, and each arrow-form rewrite still checks.
for (const { source, code, from, to } of [
  { source: "def g : forall x : Unit. Unit := fun (x : Unit) => tt;", code: "W705", from: "forall x : Unit. Unit", to: "Unit -> Unit" },
  { source: "def g : forall x, y : Unit. Unit := fun (x, y : Unit) => tt;", code: "W706", from: "forall x, y : Unit. Unit", to: "Unit -> Unit -> Unit" },
]) test(`control: safe unused-binder advice remains available (${code})`, async t => {
  assert.ok(lint(source).some(warning => warning.code === code), `${code} safe unused-binder advice must remain available`);
  for (const candidate of [source, source.replace(from, to)]) {
    const { result } = await checkProgram(t, candidate, { module });
    assert.deepEqual(observeModule(result).gaps, []);
    assert.ok(result.outputs.every(output => output.verified && !output.axioms?.length));
  }
});
