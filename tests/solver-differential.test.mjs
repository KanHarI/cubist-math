// The argument solver's differential suite (tools/solver-differential.mjs):
// every program of tests/fixtures/solver-differential.mjs elaborates as on
// main, whose verdicts, checked terms and types (hashed up to bound names)
// and evaluations tests/fixtures/solver-differential.json records. Record
// it again from main's tree only:
//   node tools/solver-differential.mjs --root=MAIN --write --from=main-<commit>
import "./fresh-build.mjs";
import test from "node:test";
import assert from "node:assert/strict";
import { readFile } from "node:fs/promises";
import { differences, elaborate, fixture } from "../tools/solver-differential.mjs";
import { programs } from "./fixtures/solver-differential.mjs";

test("every differential program elaborates as on main", async () => {
  const recorded = JSON.parse(await readFile(fixture, "utf8"));
  assert.deepEqual(Object.keys(recorded.programs), Object.keys(programs), "the record covers every program, in order");
  assert.deepEqual(differences(recorded.programs, await elaborate()), []);
});
