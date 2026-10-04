// Holes and named arguments (work-plan L4.1a), implicit parameters, implicit
// arguments in double braces and universe holes (L4.1b): what the verdicts and prints
// of cubist-tests/arguments.cubist and implicit_parameters.cubist do not show.
// The syntax and its formatting, goals that show implicit arguments,
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
const implicit = testModule("implicit_parameters", { module });

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

test("implicit parameters are a double brace group before the parameter list, each marked", () => {
  const { declarations } = parse("def f{{U < UU0, A : U}}(a : A) : A := a;\ndef g{{A : U0}} := fun (x : A) => x;");
  const [f, g] = declarations;
  assert.deepEqual(f.params.map(p => [p.name.text, !!p.implicit]), [["U", true], ["A", true], ["a", false]]);
  assert.deepEqual(g.valueParameters.map(p => [p.name.text, !!p.implicit]), [["A", true]]);
  assert.deepEqual(f.implicitParameters, { opens: [5, 6], closes: [22, 23], start: 5, end: 23 });
  // The formatter keeps the group on the name, as it keeps the parameter list.
  const source = "def f{{U < UU0, A : U}}(a : A) : A := a;\n";
  assert.equal(formatCubist(source), source);
  assert.equal(formatCubist("def f {{ U < UU0, A : U }} ( a : A ) : A := a;\n"), source);
  // One brace is a block's, or a clause list's: implicit parameters are in
  // two, opened and closed together.
  assert.throws(() => parse("def f{U < UU0}(a : Nat) : Nat := a;"), /Implicit parameters are in double braces: def f\{\{/);
  assert.throws(() => parse("def f{{U < UU0} }(a : Nat) : Nat := a;"), /Close double braces with \}\}/);
});

test("implicit arguments are a double brace group after a name; a block after a name stays a block", () => {
  const value = source => parse(source).declarations[0].value;
  const call = value("def d := f{{U0, _}}(x, y := b);");
  assert.equal(call.kind, "call");
  assert.deepEqual(call.implicitArgs.map(arg => arg.name), ["U0", "_"]);
  assert.deepEqual(call.args.map(arg => arg.kind), ["name", "namedArgument"]);
  assert.deepEqual(call.implicitGroup, { opens: [10, 11], closes: [18, 19], start: 10, end: 19 });
  // Without parentheses, the double braces alone; nested, one inside another.
  assert.deepEqual([value("def d := f{{U0}};").args, value("def d := f{{U0}};").implicitArgs.length], [[], 1]);
  assert.equal(value("def d := f{{g{{A}}}}(x);").implicitArgs[0].implicitArgs[0].name, "A");
  // A named argument in double braces names an implicit parameter.
  const named = value("def d := f{{A := Nat, U0}}(x);").implicitArgs;
  assert.deepEqual(named.map(arg => arg.kind), ["namedArgument", "name"]);
  assert.equal(named[0].name.text, "A");
  assert.equal(formatCubist("def d := f{{ A:=Nat }}(x);\n"), "def d := f{{A := Nat}}(x);\n");
  // Clauses or a proof block after a name, even written tight, are what
  // they were.
  assert.equal(value("def d := match n{ zero => 0; succ(m) => m; };").kind, "match");
  assert.equal(parse("def d : Nat{ exact 1; }").declarations[0].body[0].kind, "exact");
  assert.equal(parse("def d(n : Nat) : Nat { match n{ zero => { exact 0; } succ(m) => { exact m; } } }")
    .declarations[0].body[0].kind, "matchStatement");
  // One brace after a name is no argument list.
  assert.throws(() => parse("def d := f{U0}(x);"), /Expected ';'/);
  assert.equal(formatCubist("def d := concat{{ U0,Nat }}(p,q);\n"), "def d := concat{{U0, Nat}}(p, q);\n");
  assert.equal(formatCubist("def d := same{{U0, Nat}};\n"), "def d := same{{U0, Nat}};\n");
});

test("a goal shows a definition's implicit arguments in double braces, as a call writes them", async () => {
  const { program } = await implicit();
  const goals = name => program.steps("lists").filter(step => step.declaration === name).map(step => step.goal);
  assert.deepEqual(goals("append_nil"), ["append{{U, A}}(xs, nil) = xs", "append{{U, A}}(nil, nil) = nil",
    "append{{U, A}}(cons(head, tail), nil) = cons(head, tail)"]);
});

test("the inspector shows each inferred universe, and the omitted implicit arguments", async () => {
  const { result, verdicts } = await implicit();
  assert.equal(verdicts.from_argument, true);
  const omitted = result.links.filter(link => link.role === "inferred arguments").map(link => link.description);
  assert.ok(omitted.includes("Arguments of same inferred: U := U0, A := Nat."), omitted.join("\n"));
  assert.ok(omitted.includes("Arguments of same inferred: U := U1, A := U0."), omitted.join("\n"));
  assert.ok(omitted.includes("Arguments of append inferred: U := U0, A := Nat."), omitted.join("\n"));
  const holes = result.links.filter(link => link.role === "inferred argument").map(link => link.description);
  assert.ok(holes.includes("The universe U of same, inferred: U2."), holes.join("\n"));
});
