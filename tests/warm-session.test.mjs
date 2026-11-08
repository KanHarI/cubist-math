// A warm session checks as a fresh one does. The kernel's handles, the
// driver's binder keys and entry names outlive a derivation and a
// declaration (docs/roadmaps/kernel/locally-nameless-kernel.md, section 5.3),
// and a driver keeps its caches between derivations: so each program below
// is run in one long-lived session, one after another, with one driver, and
// alone in a fresh session, and what it derives, or its refusal, must agree,
// up to the names of bound variables (tools/canonical-hash.mjs). A program
// derives terms in contexts through the driver, as the elaborator does, or
// checks a module's source.
import "./fresh-build.mjs";
import test from "node:test";
import assert from "node:assert/strict";
import createCubical from "../web/dist/cubical.mjs";
import { CubicalProgram } from "../web/cubical-program.mjs";
import { sourceReader } from "../tools/module-sources.mjs";
import { canonicalHasher } from "../tools/canonical-hash.mjs";

const module = await createCubical();
const v = name => ({ tag: "Var", name }), U0 = { tag: "U", level: 0 }, unit = { tag: "Unit" };
const lam = (name, domain, body) => ({ tag: "Lam", name, domain, body });
const pi = (name, domain, body) => ({ tag: "Pi", name, domain, body });
const app = (fn, arg) => ({ tag: "App", fn, arg });

// A session: one program, and the driver its derivations share.
const session = () => {
  const program = new CubicalProgram(module, sourceReader(), { collectReferences: false });
  return { program, driver: program.checker.driver };
};
// The derivation of `term` in `context`, a list of [name, type] in order,
// with `dimensions` live, shown with the context's names: its term and type
// hashed, or its refusal. `raw` makes the term from the scope instead.
const derive = (context, term, { dimensions = 0n, raw = null } = {}) => ({ program, driver }) => {
  const { kernel, checker } = program, syntax = checker.syntax;
  const encode = (syntaxTerm, scope) => syntax.encode(syntaxTerm, new Map(), scope);
  try {
    const scope = driver.scopeOf(context.map(([name, type]) => [kernel.symbol(name), type]), dimensions, encode);
    const handle = raw ? raw(kernel, scope, encode) : encode(term, scope);
    const judgement = driver.graph.judgement(driver.derive(handle, scope)), naming = checker.namingOf(scope), hash = canonicalHasher();
    return ["derived", hash(syntax.decode(judgement.term, new Map(), null, naming)), hash(syntax.decode(judgement.type, new Map(), null, naming))];
  } catch (error) { return ["refused", error.message]; }
};
// A module's source checked: each declaration's verdict and its elaborated
// term and type hashed.
const source = (name, text) => async ({ program }) => {
  const result = await program.check(text, name), hash = canonicalHasher(), views = program.checker.definitionViews;
  return Object.fromEntries(result.outputs.map(output => {
    const binding = output.binding ?? output.name, view = views.get(binding);
    return [binding, [output.verified, view ? hash(view.term) : null, view ? hash(view.type) : null]];
  }));
};

const A = v("A"), B = v("B"), x = v("x"), y = v("y"), w = v("w"), f = v("f");
const programs = [
  // The driver's names (tests/driver-names.test.mjs): one name bound twice and
  // three times, and around a variable whose type depends on the first.
  ["twice", derive([], lam("x", unit, lam("x", unit, x)))],
  ["thrice", derive([], lam("x", unit, lam("x", unit, lam("x", unit, x))))],
  ["kept", derive([["A", U0], ["B", pi("_", A, U0)]], lam("x", A, lam("y", app(B, x), lam("x", A, y))))],
  ["kept twice", derive([["A", U0], ["B", pi("_", A, U0)]], lam("x", A, lam("y", app(B, x), lam("x", A, lam("x", A, y)))))],
  // Codex review, round 1: the unnamed λ (_ : A). y derived, then written
  // λ (x : A). y, and derived with one more live dimension.
  ...(() => {
    const context = [["A", U0], ["B", pi("_", A, U0)], ["x", A], ["y", app(B, x)]];
    const unnamed = (kernel, scope, encode) => kernel.term("Lam", 0, encode(A, scope), encode(y, scope));
    return [["unnamed", derive(context, null, { raw: unnamed })], ["named", derive(context, lam("x", A, y))],
      ["named, a dimension more", derive(context, lam("x", A, y), { dimensions: 1n })]];
  })(),
  // Codex review, round 2: λ (x : Unit). f(w) with w, then λ (w : Unit).
  // λ (z : Unit). f(w) without it, whose inner λ, once w is opened, is the
  // first's node, keyed by x, which f's type depends on.
  ...(() => {
    const context = [["x", unit], ["f", pi("_", unit, { tag: "Path", dim: "i", family: unit, left: x, right: x })]];
    return [["f(w) under x", derive([...context, ["w", unit]], lam("x", unit, app(f, w)))],
      ["f(w) under w and z", derive(context, lam("w", unit, lam("z", unit, app(f, w))))]];
  })(),
  // Library modules, in sequence.
  ["unat", source("unat_import", "import unat;\n")],
  ["lists", source("lists_import", "import lists;\n")],
  ["hlevels", source("hlevels_import", "import hlevels;\n")],
];

test("a warm session derives and checks each program as a fresh session does", async t => {
  const warm = session();
  t.after(() => warm.program.dispose());
  for (const [name, run] of programs) {
    const found = await run(warm), fresh = session();
    try {
      const expected = await run(fresh);
      // A warm session reports the declarations it checked before too: each
      // the fresh one checks is compared.
      const comparable = Array.isArray(expected) ? found : Object.fromEntries(Object.keys(expected).map(binding => [binding, found[binding]]));
      assert.deepEqual(comparable, expected, name);
      if (Array.isArray(expected)) assert.equal(expected[0], "derived", `${name}: ${expected[1]}`);
      else assert.ok(Object.values(expected).every(([verified]) => verified), name);
    } finally { fresh.program.dispose(); }
  }
});
