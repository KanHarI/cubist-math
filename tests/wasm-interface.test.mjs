import "./fresh-build.mjs";
import test from "node:test";
import assert from "node:assert/strict";
import { readFileSync } from "node:fs";
import createCubical from "../web/dist/cubical.mjs";
import { CubicalKernel, cubicalKinds } from "../web/cubical-kernel.mjs";
import { InstructionGraph, instructions, stepRules } from "../web/cubical-instructions.mjs";

const header = readFileSync(new URL("../kernel/include/cubical_kernel.h", import.meta.url), "utf8")
  .replace(/\/\*[\s\S]*?\*\//g, "");
function enumeration(type, prefix, retired = []) {
  const body = header.match(new RegExp(`typedef enum\\s*\\{([^}]+)\\}\\s*${type};`));
  assert.ok(body, type);
  const values = [""];
  let next = 0;
  for (const entry of body[1].split(",")) {
    const match = entry.trim().match(/^([A-Z_]+)(?:\s*=\s*(\d+))?$/);
    assert.ok(match, `${type}: ${entry}`);
    if (match[2]) next = Number(match[2]);
    const name = match[1].replace(prefix, "");
    values[next++] = retired.includes(name) ? null : name.replaceAll("_", "").toLowerCase();
  }
  return values;
}
const lower = values => values.map(value => value?.toLowerCase() ?? null);

test("JS term, instruction, step and error encodings agree with the C header", () => {
  assert.deepEqual(lower(cubicalKinds), enumeration("cc_term_kind", /^CC_/, [
    "NAT", "ZERO", "SUCC", "NATREC", "W", "SUP", "WREC", "PUSHOUT", "PUSH_LEFT", "PUSH_RIGHT", "PUSH_PATH", "PUSH_ELIM",
  ]));
  assert.deepEqual(lower(instructions), enumeration("cc_instruction", /^CC_INSTR_/, [
    "NAT", "ZERO", "SUCC", "NAT_ELIM", "PUSHOUT", "PUSH_POINT", "PUSH_PATH", "PUSH_ELIM", "W", "SUP", "W_ELIM",
  ]));
  assert.deepEqual(stepRules, enumeration("cc_step_rule", /^CC_STEP_/));
  const errors = enumeration("cc_error_kind", /^CC_ERROR_/);
  for (const [code, name] of errors.entries())
    assert.equal(CubicalKernel.prototype.errorKind.call({ handle: 1, module: { _cb_error_kind: () => code } }), name);
});

const module = await createCubical();
test("syntactic comparison separates inequality from failure and does not reduce", t => {
  const kernel = new CubicalKernel(module);
  t.after(() => kernel.dispose());
  const unit = kernel.term("Unit"), point = kernel.term("Point");
  const x = kernel.term("Var", 10), y = kernel.term("Var", 20);
  const a = kernel.term("Lam", 10, unit, x), b = kernel.term("Lam", 20, unit, y);
  const applied = kernel.term("App", 0, a, point);
  assert.ok(kernel.alphaEqual(a, b));
  assert.ok(!kernel.alphaEqual(a, kernel.term("Lam", 20, unit, x)));
  assert.ok(!kernel.alphaEqual(applied, point));
  assert.ok(kernel.alphaEqual(kernel.head(applied), point));
  assert.ok(!kernel.alphaEqual(applied, point), "normalization must not change syntactic equality");
  for (const value of [-1, 1.5, 2 ** 32]) assert.throws(() => kernel.alphaEqual(value, point), TypeError);
  assert.throws(() => kernel.alphaEqual(0, point), /Unknown cubical node/);
  assert.equal(module._cb_alpha_equal(0, a, b), -1);
  assert.equal(module._cb_alpha_equal(kernel.handle, a, 0xffffffff), -1);
  const c = kernel.term("Lam", 30, unit, kernel.term("Var", 30));
  kernel.setStepBudget(1n);
  assert.throws(() => kernel.alphaEqual(a, c), error => error.kind === "budget");
  kernel.setStepBudget(kernel.stepBudget);
  assert.ok(kernel.alphaEqual(a, c), "failed queries are retryable");
});

test("budget writes retain both 32-bit halves and restore the session baseline on failure", t => {
  const writes = [];
  const kernel = new CubicalKernel({ ...module, _cb_step_budget: (...args) => {
    writes.push(args.slice(1));
    return module._cb_step_budget(...args);
  } });
  t.after(() => kernel.dispose());
  const graph = new InstructionGraph(kernel);
  kernel.stepBudget = 0x12345678abcdef01n;
  kernel.setStepBudget(kernel.stepBudget);
  assert.deepEqual(writes.at(-1), [0xabcdef01, 0x12345678]);
  graph.head(kernel.term("Unit"), 0x100000002n);
  assert.deepEqual(writes.slice(-2), [[2, 1], [0xabcdef01, 0x12345678]]);
  const failure = new Error("probe");
  assert.throws(() => graph.within(0xffffffffffffffffn, () => { throw failure; }), error => error === failure);
  assert.deepEqual(writes.slice(-2), [[0xffffffff, 0xffffffff], [0xabcdef01, 0x12345678]]);
  const count = writes.length;
  for (const budget of [-1n, 1n << 64n]) assert.throws(() => kernel.setStepBudget(budget), TypeError);
  assert.equal(writes.length, count, "invalid values never reach the native interface");
});
