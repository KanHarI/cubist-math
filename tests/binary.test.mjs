import "./fresh-build.mjs";
import test from "node:test";
import assert from "node:assert/strict";
import { checkProgram } from "./check-program.mjs";

test("Binary operations compute their complete truth tables without assumptions", async t => {
  const cases = [
    ["Not(False)", "True"], ["Not(True)", "False"],
    ["And(False, False)", "False"], ["And(False, True)", "False"],
    ["And(True, False)", "False"], ["And(True, True)", "True"],
    ["Or(False, False)", "False"], ["Or(False, True)", "True"],
    ["Or(True, False)", "True"], ["Or(True, True)", "True"],
    ["Xor(False, False)", "False"], ["Xor(False, True)", "True"],
    ["Xor(True, False)", "True"], ["Xor(True, True)", "False"],
    ["Nor(False, False)", "True"], ["Nor(False, True)", "False"],
    ["Nor(True, False)", "False"], ["Nor(True, True)", "False"],
  ];
  const { result } = await checkProgram(t, `import binary; use nat;
    computable def false_value : False = typed(Fin(2), (0, tt)) { rfl; }
    computable def true_value : True = typed(Fin(2), (1, tt)) { rfl; }
    ${cases.map(([expression, expected], i) => `
      computable def table_${i} : ${expression} = ${expected} { rfl; }
      print(evaluate((${expression}).1));
    `).join("\n")}
  `);
  assert.ok(result.complete, JSON.stringify(result.gaps));
  assert.equal(result.outputs.length, cases.length + 2);
  assert.ok(result.outputs.every(output => output.verified && !output.axioms.length));
  assert.deepEqual(result.prints.map(output => output.text),
    cases.map(([, expected]) => expected === "True" ? "1" : "0"));
});

test("Binary rejects out-of-range values while Fin retains large binary indices", async t => {
  const { result, get } = await checkProgram(t, `import binary; use nat;
    computable def large : Fin(18446744073709551617) := (18446744073709551616, tt);
    print(evaluate(large.1));
    def invalid : Binary := (2, tt);
  `);
  assert.equal(result.complete, false);
  assert.equal(get("large").verified, true);
  assert.deepEqual(get("large").axioms, []);
  assert.deepEqual(result.prints.map(output => output.text), ["18446744073709551616"]);
  assert.equal(get("invalid").verified, false);
  assert.match(get("invalid").reason, /Type mismatch/);
});
