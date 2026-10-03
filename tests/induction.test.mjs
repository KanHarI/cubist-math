import "./fresh-build.mjs";
import test from "node:test";
import assert from "node:assert/strict";
import { checkProgram } from "./check-program.mjs";
import { ReplSession } from "../web/repl-session.mjs";
import { diagnosticCode } from "../web/diagnostics.mjs";

// `induction` on any declared type: a clause per constructor, as in match,
// whose names are the constructor's arguments and then, optionally, an
// induction hypothesis for each recursive argument. Natural numbers keep
// their own form, zero => …; succ h => …;, as well.
const lists = `
inductive List(U < UU0, A : U) : U {
  nil;
  cons(head : A, tail : List(U, A));
}
`;

test("an induction expression names its hypotheses after the arguments", async t => {
  const { result, verdicts } = await checkProgram(t, `${lists}
def length(xs : List(U0, Nat)) : Nat := induction xs return Nat {
  nil => 0;
  cons(head, tail, ih) => succ(ih);
};
def append(xs, ys : List(U0, Nat)) : List(U0, Nat) := induction xs return List(U0, Nat) {
  nil => ys;
  cons(head, tail, rest) => cons(head, rest);
};
// The motive may depend on the value, so the hypothesis is the statement for the tail.
def append_nil(xs : List(U0, Nat)) : append(xs, nil) = xs := induction xs as v return append(v, nil) = v {
  nil => refl(typed(List(U0, Nat), nil));
  cons(head, tail, ih) => cong(fun (rest : List(U0, Nat)) => typed(List(U0, Nat), cons(head, rest)), ih);
};
// Hypotheses may be left out, as a match does.
def head_or_zero(xs : List(U0, Nat)) : Nat := induction xs return Nat { nil => 0; cons(head, tail) => head; };
def two : length(cons(1, cons(2, nil))) = 2 { rfl; }
def joined : append(cons(1, nil), cons(2, nil)) = cons(1, cons(2, nil)) { rfl; }`);
  assert.equal(result.complete, true, JSON.stringify(verdicts));
});

test("the induction statement proves a goal with a hypothesis for each recursive argument", async t => {
  const { result, verdicts } = await checkProgram(t, `${lists}
def append(xs, ys : List(U0, Nat)) : List(U0, Nat) := induction xs return List(U0, Nat) {
  nil => ys;
  cons(head, tail, rest) => cons(head, rest);
};
def append_assoc(xs, ys, zs : List(U0, Nat)) : append(append(xs, ys), zs) = append(xs, append(ys, zs)) {
  induction xs {
    nil => { rfl; }
    cons(head, tail, ih) => {
      exact cong(fun (rest : List(U0, Nat)) => typed(List(U0, Nat), cons(head, rest)), ih);
    }
  }
}`);
  assert.equal(result.complete, true, JSON.stringify(verdicts));
});

test("natural numbers take the general form and their own, which agree", async t => {
  const { result, verdicts } = await checkProgram(t, `
def general(n : Nat) : Nat := induction n return Nat { zero => 0; succ(k, h) => succ(succ(h)); };
def own(n : Nat) : Nat := induction n return Nat { zero => 0; succ h => succ(succ(h)); };
def same : general = own { rfl; }
def six : general(3) = 6 { rfl; }`);
  assert.equal(result.complete, true, JSON.stringify(verdicts));
});

test("path constructors and function-typed recursive arguments", async t => {
  const { result, verdicts } = await checkProgram(t, `
inductive Circle : U0 { base; loop : base = base; }
def flat(c : Circle) : Nat := induction c return Nat { base => 0; loop @ i => 0; };
inductive Tree : U0 { leaf; node(children : Nat -> Tree); }
// The hypothesis for children is a function: the result for each child.
def leftmost_depth(t : Tree) : Nat := induction t return Nat { leaf => 0; node(children, below) => succ(below(0)); };`);
  assert.equal(result.complete, true, JSON.stringify(verdicts));
});

test("refusals and the warning, each with its code", async t => {
  const { get } = await checkProgram(t, `${lists}
def too_few(xs : List(U0, Nat)) : Nat := induction xs return Nat { nil => 0; cons(head) => 1; };
def a_pair(p : Nat and Nat) : Nat := induction p return Nat { pair(a, b) => a; };
def after(n : Nat) : Nat {
  induction n {
    zero => { exact 0; }
    succ(k, h) => { exact h; }
  }
  exact 0;
}`);
  assert.match(get("too_few").reason, /^cons takes 2 arguments here, then its induction hypothesis if you name them: cons\(…\) with 2 or 3 names\./);
  assert.match(get("a_pair").reason, /^induction requires a value of a declared type\./);
  assert.match(get("after").reason, /^Statements after induction are unreachable/);
  for (const name of ["too_few", "a_pair", "after"]) assert.ok(get(name).code, name);
  const { result } = await checkProgram(t, `${lists}
def unused(xs : List(U0, Nat)) : Nat := induction xs as v return Nat { nil => 0; cons(head, tail, ih) => ih; };`);
  assert.deepEqual(result.warnings.map(warning => [warning.code, warning.message]),
    [[diagnosticCode("v is unused: the return type does not mention it. Omit as v: induction xs return …."),
      "v is unused: the return type does not mention it. Omit as v: induction xs return …."]]);
});

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
