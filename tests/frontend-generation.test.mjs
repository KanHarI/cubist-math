import "./fresh-build.mjs";
import test from "node:test";
import assert from "node:assert/strict";
import { readFile } from "node:fs/promises";
import { inspect, isDeepStrictEqual } from "node:util";
import createCubical from "../web/dist/cubical.mjs";
import { lint } from "../web/cubist/lint.mjs";
import { checkProgram } from "./check-program.mjs";
import { cases, extras, observe } from "./frontend-generation-cases.mjs";
import { knownDefects } from "./fixtures/frontend-generation-defects.mjs";

const module = await createCubical();
const strict = process.env.CUBIST_GENERATION_STRICT === "1";

// A case passes when its check shows what it should. A case with a record of
// a documented defect is a TODO only while its check shows exactly that
// record: a TODO never counts as completion, and any other result fails.
// Group prefixes stay in the names for test selection.
for (const c of cases) test(`${c.group}: [${c.id}] ${c.contract}`, async t => {
  const { observed, desired } = await observe(t, c, module), record = strict ? undefined : knownDefects[c.id];
  if (isDeepStrictEqual(observed, desired)) {
    assert.ok(!record, `${c.id} shows its desired outcome: remove its record from fixtures/frontend-generation-defects.mjs`);
    return;
  }
  if (record && isDeepStrictEqual(observed, record)) {
    t.todo(`${c.phase}: documented ${c.id} defect; never counts as completion`);
    assert.fail(`${c.id}: ${inspect(observed, { depth: null })}`);
  }
  assert.deepEqual(observed, desired, record ? `${c.id} shows neither its desired outcome nor its recorded defect` : c.id);
});

test("case IDs are unique, records and extras name cases, and the manifest lists every case", async () => {
  const ids = cases.map(c => c.id);
  assert.equal(new Set(ids).size, ids.length);
  for (const id of [...Object.keys(knownDefects), ...Object.keys(extras)]) assert.ok(ids.includes(id), id);
  const manifest = await readFile(new URL("./fixtures/frontend-generation.md", import.meta.url), "utf8");
  const listed = [...manifest.matchAll(/^\| `([\w-]+)` \|/gm)].map(match => match[1]);
  assert.deepEqual(listed.sort(), [...ids].sort());
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
    assert.deepEqual(result.gaps, []);
    assert.ok(result.outputs.every(output => output.verified && !output.axioms?.length));
  }
});
