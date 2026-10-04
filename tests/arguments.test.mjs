// Holes and named arguments (work-plan L4.1a): what the verdicts and prints of
// cubist-tests/arguments.cubist do not show. The syntax and its formatting,
// the linter, the inspector's record of each solved hole, and the
// known-signature elaboration of a call, which never asks the kernel for the
// type of the growing application.
import "./fresh-build.mjs";
import test from "node:test";
import assert from "node:assert/strict";
import createCubical from "../web/dist/cubical.mjs";
import { parse } from "../web/cubist/parser.mjs";
import { formatCubist } from "../web/cubist/formatter.mjs";
import { lint } from "../web/cubist/lint.mjs";
import { checkProgram, testModule } from "./check-program.mjs";

const module = await createCubical();
const cases = testModule("arguments", { module });

test("a named argument is a node of its call; a hole is a name", () => {
  const { declarations: [declaration] } = parse("def d := f(_, x := a, b);");
  const [hole, named, plain] = declaration.value.args;
  assert.deepEqual([hole.kind, hole.name], ["name", "_"]);
  assert.equal(named.kind, "namedArgument");
  assert.equal(named.name.text, "x");
  assert.deepEqual([named.value.kind, named.value.name], ["name", "a"]);
  assert.deepEqual([named.start, named.end], [named.name.start, named.value.end]);
  assert.equal(plain.name, "b");
  // `:=` outside an argument list is still a declaration's.
  assert.throws(() => parse("def d := (x := a);"), /Expected/);
});

test("the formatter keeps holes and named arguments", () => {
  const source = "def d(n : Nat) : Nat := apply(U0, _, _, f := fun x => succ(x), a := n);\n";
  assert.equal(formatCubist(source), source);
});

test("a named argument's name is its function's parameter, not a use", () => {
  const unused = "def f(a : Nat) : Nat := a;\ndef g(n : Nat) : Nat {\n  let a := n;\n  exact f(a := n);\n}\n";
  assert.deepEqual(lint(unused).map(warning => warning.code), ["W702"]);
  assert.deepEqual(lint(unused.replace("f(a := n)", "f(a := a)")), []);
});

test("the inspector shows what each hole and each omitted parameter became", async () => {
  const { result, verdicts } = await cases();
  assert.equal(verdicts.endpoints, true);
  const inferred = result.links.filter(link => link.role === "inferred argument");
  const endpoints = result.links.filter(link => link.role === "inferred argument"
    && /of concat, inferred/.test(link.description));
  assert.deepEqual(endpoints.map(link => link.description), [
    "The parameter A of concat, inferred: Nat.",
    "The parameter x of concat, inferred: x.",
    "The parameter y of concat, inferred: y.",
    "The parameter z of concat, inferred: z.",
  ]);
  assert.ok(inferred.every(link => link.name === "_" && link.end === link.start + 1));
  const omitted = result.links.filter(link => link.role === "inferred arguments");
  assert.ok(omitted.some(link => link.description === "Arguments of inverse_equiv inferred: A := P, B := Unit."));
  assert.ok(omitted.some(link => link.description === "Arguments of glue_path inferred: A := P, B := Unit."));
});

test("a call asks for its function's type once, never for the growing application's", async t => {
  const source = "def concat(U < UU0, A : U, x, y, z : A, p : x = y, q : y = z) : x = z := trans(p, q);\n"
    + "def joined(a, b, c : Nat, p : a = b, q : b = c) : a = c := concat(U0, Nat, a, b, c, p, q);\n";
  const asked = [];
  const { verdicts } = await checkProgram(t, source, { module, options: {
    onDeclarationStart: (name, declaration, checker) => {
      if (declaration.name.text !== "joined") return;
      const infer = checker.infer;
      checker.infer = function (term, ...rest) { asked.push(term); return infer.call(this, term, ...rest); };
    },
  } });
  assert.equal(verdicts.joined, true);
  const head = term => { while (term.tag === "App" || term.tag === "LApp") term = term.fn; return term; };
  const spines = asked.filter(term => head(term).tag === "DefRef" && head(term).name.endsWith("concat"));
  // Only the function itself: each argument's type is read off its type.
  assert.deepEqual(spines.map(term => term.tag), ["DefRef"]);
});
