import "./fresh-build.mjs";
import test from "node:test";
import assert from "node:assert/strict";
import { checkProgram } from "./check-program.mjs";
import { ReplSession } from "../web/repl-session.mjs";

// `induction` on any declared type. Its cases, refusals and warning are
// cubist-tests/induction.cubist, whose comments state each error and warning
// (tests/cubist-tests.test.mjs); here, how an eliminator prints, and that
// the printed source checks.
const lists = `
inductive List(U < UU0, A : U) : U {
  nil;
  cons(head : A, tail : List(U, A));
}
`;

test("a recursive eliminator prints as the induction that builds it, and that source checks", async t => {
  const tree = "inductive Tree : U0 { leaf; node(left : Tree, right : Tree); }";
  const { program } = await checkProgram(t, `${tree}
def size(t : Tree) : Nat := match t { leaf => 1; node(left, right) => succ(size(left)); };`, { name: "printed" });
  const [printed] = (await new ReplSession(program, { base: "printed" }).run("evaluate size;")).map(output => output.text);
  assert.match(printed, /^fun \(x : Tree\) => induction x return Nat \{ leaf => 1; node\(left, right, \w+, \w+\) => succ\(\w+\); \}$/);
  const { result, verdicts } = await checkProgram(t, `${tree}
def size(t : Tree) : Nat := match t { leaf => 1; node(left, right) => succ(size(left)); };
def again := ${printed};
def same : size = again { rfl; }`);
  assert.equal(result.complete, true, JSON.stringify(verdicts));
});

// An instance carries no erased universe, so the printer writes __U in its
// place, and whoever writes the instance out supplies it: the elaborator
// says what __U stands for.
test("an erased universe prints as __U, which the elaborator asks to replace", async t => {
  const { program } = await checkProgram(t, `${lists}
def length(xs : List(U0, Nat)) : Nat := induction xs return Nat { nil => 0; cons(head, tail, ih) => succ(ih); };`, { name: "printed" });
  const [printed] = (await new ReplSession(program, { base: "printed" }).run("evaluate length;")).map(output => output.text);
  assert.equal(printed, "fun (x : List(__U, Nat)) => induction x return Nat { nil => 0; cons(head, tail, ih) => succ(ih); }");
  const { get } = await checkProgram(t, `${lists}
def again := ${printed};`);
  assert.match(get("again").reason, /^__U stands for a universe that the printer could not show: write the universe in its place/);
  assert.ok(get("again").code);
  // Written out, it checks.
  const { result, verdicts } = await checkProgram(t, `${lists}
def again := ${printed.replace("__U", "U0")};`);
  assert.equal(result.complete, true, JSON.stringify(verdicts));
});
