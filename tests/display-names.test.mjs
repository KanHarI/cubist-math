// The display's naming rules (lib/cubical/names.mjs), and the printer that
// applies them: whatever the rules predict a name shows as, the printer
// shows. Code that must name things apart from what a view prints, such as
// CubicalProgram's eliminator view, relies on the predictions.
import "./fresh-build.mjs";
import test from "node:test";
import assert from "node:assert/strict";
import { localName, numberedName, printedForms, printsAsItself, stem } from "../lib/cubical/names.mjs";
import { T } from "../lib/cubical/core.mjs";
import { displayTerm } from "../web/cubical-elaborator.mjs";
import { sourceText } from "../web/cubical-source-text.mjs";

test("each rule on each kind of name", () => {
  for (const [name, expected] of [["n11", "n"], ["U_1", "U"], ["UU_2", "UU"], ["native12", "x"], ["a1_", "a1_"],
    ["__assumption_T", "__assumption_T"], ["7", "7"]]) assert.equal(stem(name), expected, name);
  for (const [name, expected] of [["paths__refl", "refl"], ["__assumption_T", "__assumption_T"], ["n", "n"]])
    assert.equal(localName(name), expected, name);
  assert.equal(numberedName("U", 1), "U_1");
  assert.equal(numberedName("UU", 3), "UU_3");
  assert.equal(numberedName("n", 2), "n2");
  assert.deepEqual(printedForms("mod__n3"), ["mod__n3", "n3", "mod__n", "n"]);
  assert.deepEqual(printedForms("mod__U_2"), ["mod__U_2", "U_2", "mod__U_", "U_"]);
  for (const name of ["x", "motive", "c_", "U", "a1_", "__assumption_T"]) assert.ok(printsAsItself(name), name);
  for (const name of ["x1", "U_", "U_1", "mod__x", "native3", "7"]) assert.ok(!printsAsItself(name), name);
});

// Names built from every part the rules read: stems ending in a letter, a
// digit or an underscore, U's, a serial with or without a separator, a
// module, and the kernel's own symbols.
const names = [
  ...["x", "n", "a1", "U", "UU", "c_", "native", "_y"].flatMap(base => ["", "1", "11", "_2"]
    .flatMap(serial => ["", "mod__"].map(module => `${module}${base}${serial}`))),
  "native0", "native42", "__assumption_T"];

test("the predictions agree with one another on every name", () => {
  for (const name of names) {
    const forms = printedForms(name);
    for (const form of [name, stem(name), localName(name), localName(stem(name))]) assert.ok(forms.includes(form), `${name}: ${form}`);
    if (printsAsItself(name)) assert.deepEqual(forms, [name], name);
    for (const index of [1, 2, 10])
      assert.ok(!printsAsItself(numberedName(stem(name), index)), `${name}: no numbered name prints as itself`);
  }
});

test("the printer shows every name in a form the rules predict", () => {
  const shown = term => sourceText(displayTerm(term));
  // A form the rules predict, or the name's stem numbered apart, shown by
  // its local name where it is free.
  const predicted = (name, text) => printedForms(name).includes(text)
    || [1, 2, 3].some(index => [numberedName(stem(name), index), localName(numberedName(stem(name), index))].includes(text));
  for (const name of names) {
    const variable = shown(T.variable(name));
    assert.ok(predicted(name, variable), `${name} as a variable: ${variable}`);
    const definition = shown({ tag: "DefRef", name });
    assert.equal(definition, localName(name), `${name} as a definition`);
    // Bound twice, the inner binder's name with the same stem, as n and n9:
    // the inner one is numbered apart, and a name that prints as itself
    // shows as it is.
    const inner = `${name}9`;
    const binders = shown(T.lam(name, T.unit, T.lam(inner, T.unit, T.app(T.variable(name), T.variable(inner)))));
    const [, group, applied, argument] = /^fun \(([^:]+) : Unit\) => (.+)\((.+)\)$/.exec(binders) ?? [];
    const [outerShown, innerShown] = group?.split(", ") ?? [];
    assert.ok(outerShown && predicted(name, outerShown), `${name} as a binder: ${binders}`);
    assert.ok(innerShown && predicted(inner, innerShown) && innerShown !== outerShown, `${inner} inside it: ${binders}`);
    assert.deepEqual([applied, argument], [outerShown, innerShown], `${name}: each bound variable shows as its binder: ${binders}`);
    if (printsAsItself(name)) assert.equal(outerShown, name, `${name} as a binder prints as itself`);
  }
});

// The first review of #79: a binder's name held in the domains after it in
// a group, and inside a form the printer leaves to cubicalText.
test("a bound variable prints as its binder in later domains and in fallback forms", () => {
  // With the display's names, as the elaborator gives them, which show a
  // module's definition by its local name.
  const displayNames = new Proxy({}, { get: (_, name) => typeof name === "string" && localName(name) !== name
    ? { name: localName(name) } : undefined });
  const shown = term => sourceText(displayTerm(term), displayNames);
  for (const name of names) {
    const dependent = shown(T.lam(name, T.universe(0), T.lam("y", T.variable(name), T.variable("y"))));
    const [, binder, domain] = /^fun \((\S+) : U0, y : (\S+)\) => y$/.exec(dependent) ?? [];
    assert.ok(binder && domain === binder, `${name} in a later domain: ${dependent}`);
    const fallen = shown(T.lam(name, T.unit, T.pair(null, T.variable(name), T.unitrec(T.lam("u", T.unit, T.unit), T.variable(name), T.point))));
    const [, bound, first, inside] = /^fun \((\S+) : Unit\) => \((\S+), UnitRec\(λ \(u : Unit\)\. Unit, (\S+), ⋆\)\)$/.exec(fallen) ?? [];
    assert.ok(bound && first === bound && inside === bound, `${name} inside a fallback: ${fallen}`);
  }
  // cubicalText keeps its own binder apart from a variable bound around it:
  // its motive's binder mod__x shows as x, and would capture the x bound
  // outside.
  const motive = T.lam("mod__x", T.unit, T.variable("x"));
  const apart = shown(T.lam("x", T.universe(0), T.unitrec(motive, T.variable("p"), T.point)));
  assert.equal(apart, "fun (x : U0) => UnitRec(λ (x′ : Unit). x, p, ⋆)");
  // The second review of #79: a definition keeps its label inside such a
  // form, though a binder the display shortens to mod__x shares its name.
  const definition = { tag: "DefRef", name: "mod__x" };
  const labelled = shown(T.lam("mod__x42", T.unit, T.pair(null, definition, T.unitrec(T.lam("u", T.unit, T.unit), definition, T.point))));
  assert.equal(labelled, "fun (mod__x : Unit) => (x, UnitRec(λ (u : Unit). Unit, x, ⋆))");
});
