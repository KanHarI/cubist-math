// apply and refine (work-plan L4.4): what the verdicts of
// cubist-tests/apply_refine.cubist do not show. Each subgoal is visible: its
// clause's statements are recorded with the subgoal as their goal, as the
// workspace's Elaboration panel shows them. The statements parse and format.
import "./fresh-build.mjs";
import test from "node:test";
import assert from "node:assert/strict";
import createCubical from "../web/dist/cubical.mjs";
import { parse } from "../web/cubist/parser.mjs";
import { formatCubist } from "../web/cubist/formatter.mjs";
import { testModule } from "./check-program.mjs";

const cases = testModule("apply_refine", { module: await createCubical() });

test("each subgoal is a goal of its clause's statements", async () => {
  const { program, verdicts } = await cases();
  assert.equal(verdicts.joined, true);
  const goals = name => program.steps("apply_refine").filter(step => step.declaration === name).map(step => [step.kind, step.goal]);
  assert.deepEqual(goals("joined"), [["apply", "a = c"], ["exact", "a = b"], ["exact", "b = c"]]);
  assert.deepEqual(goals("around"), [["apply", "a = a"], ["rfl", "a = a"], ["let", "a = a"], ["exact", "a = a"]]);
  assert.deepEqual(goals("witness"), [["refine", "exists n : Nat. n = 2"], ["rfl", "2 = 2"]]);
});

test("apply and refine parse with their clauses, and format as blocks", () => {
  const { declarations: [declaration] } = parse("def d(a : Nat) : a = a { refine f(?p, x) { p => { rfl; } } }");
  const [statement] = declaration.body;
  assert.equal(statement.kind, "refine");
  assert.deepEqual(statement.clauses.map(clause => clause.name.text), ["p"]);
  assert.deepEqual(statement.value.args.map(arg => arg.kind), ["goalHole", "name"]);
  assert.throws(() => parse("def d := f(? p);"), /no space: \?p/);
  const source = "def d(a : Nat) : a = a {\n  apply f(y := a) {\n    p => {\n      rfl;\n    }\n  }\n}\n";
  assert.equal(formatCubist(source), source);
  assert.equal(formatCubist("def d : Nat { refine f( ?x ) { x => { exact 1; } } }\n"),
    "def d : Nat {\n  refine f(?x) {\n    x => {\n      exact 1;\n    }\n  }\n}\n");
});
