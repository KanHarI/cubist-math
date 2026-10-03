import "./fresh-build.mjs";
import test from "node:test";
import assert from "node:assert/strict";
import { lint } from "../web/cubist/lint.mjs";
import { ReplSession } from "../web/repl-session.mjs";
import { checkProgram } from "./check-program.mjs";

// What the printer shows is source the linter accepts: it writes no binding
// the linter would ask to remove, such as an `as` name the return type does
// not use, or a quantified variable its body does not mention. Eliminators
// print as the induction or match that builds them, not as kernel notation.
test("printed terms and types pass the linter", async t => {
  const { program, result } = await checkProgram(t, `
def or_swap(A, B : U0) : A or B -> B or A {
  intro either;
  cases either {
    left a => { exact right(a); }
    right b => { exact left(b); }
  }
}
def swap_sides(A, B : U0, value : A or B) := match value return B or A {
  left a => right(a);
  right b => left(b);
};
def Shape(value : Unit or Unit) := match value return U0 { left a => Nat; right b => Unit; };
def default(value : Unit or Unit) := match value as z return Shape(z) { left a => 0; right b => tt; };
def copy(n : Nat) := induction n return Nat { zero => 0; succ previous => succ(previous); };
def predecessor(n : Nat) := induction n as k return Nat { zero => 0; succ previous => k; };
def constant : forall x : Nat. Nat := fun (x : Nat) => 0;
def pairs : exists n : Nat. Unit := (0, tt);
inductive Bool : U0 { false; true; }
def negate(value : Bool) : Bool := match value { false => true; true => false; };
inductive Circle : U0 { base; loop : base = base; }
def reverse(c : Circle) : Circle := match c { base => base; loop @ i => loop @ -i; };
inductive List(U < UU0, A : U) : U { nil; cons(head : A, tail : List(U, A)); }
def length(xs : List(U0, Nat)) : Nat := match xs { nil => 0; cons(head, tail) => succ(length(tail)); };`, { name: "printed" });
  assert.equal(result.complete, true, JSON.stringify(result.gaps));
  const session = new ReplSession(program, { base: "printed" });
  for (const name of ["or_swap", "swap_sides", "default", "copy", "predecessor", "constant", "pairs", "negate", "reverse", "length"])
    for (const request of ["evaluate", "typeof"]) {
      const [printed] = (await session.run(`${request} ${name};`)).map(output => output.text);
      const warnings = lint(`def shown := ${printed};`).map(warning => warning.message);
      assert.deepEqual(warnings, [], `${request} ${name} printed ${printed}`);
    }
  // A declared type's eliminator prints as the match that builds it.
  assert.deepEqual((await session.run("evaluate negate;")).map(output => output.text),
    ["fun (x : Bool) => match x return Bool { false => true; true => false; }"]);
  assert.deepEqual((await session.run("evaluate copy;")).map(output => output.text),
    ["fun (n : Nat) => induction n return Nat { zero => 0; succ h => succ(h); }"]);
  // The sum's clauses keep the names the source gave them.
  assert.deepEqual((await session.run("evaluate or_swap;")).map(output => output.text),
    ["fun (A, B : U0, either : A or B) => match either return B or A { left a => right(a); right b => left(b); }"]);
});
