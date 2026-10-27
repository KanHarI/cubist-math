import "./fresh-build.mjs";
import test from "node:test";
import assert from "node:assert/strict";
import create from "../web/dist/cubical.mjs";
import { CubicalProgram } from "../web/cubical-program.mjs";
import { ContextualSession } from "../web/contextual-session.mjs";
import { ReplSession } from "../web/repl-session.mjs";
import { elaboration } from "../web/cubical-elaboration.mjs";
import { sourceReader } from "../tools/module-sources.mjs";

// Every printed text reads back as the same term where it is printed, or is
// the explicit form, which reads back anywhere: a numeral abbreviation, bare
// or name.(n), is printed only where the scope establishes the notation that
// reads it (notationContext in web/translator/notation-context.mjs). Each
// program combines a way of shadowing a reader's name with each kind of
// numeral, and each printed text is read back on every surface that shows
// one: a print, a declaration's type mismatch, the message of a use before
// its declaration's scope, the elaboration view, a REPL typeof, and a
// contextual typeof.
const module = await create();
const imports = "import unat;\nimport bnat;\n";
const header = `theory Counted(U < UU0) {
  M : U;
  inj(n : BNat) : M;
  def of_nat(n : BNat) : M := inj(n) notation numeral;
}
theory Holder(U < UU0) {
  m : Unit;
}
def counted : Counted(U0) := Counted.make(M := BNat, inj := fun (n : BNat) => n);
def m : Counted(U0) := Counted.make(M := BNat, inj := fun (n : BNat) => n);
notation m {
  numeral(n : BNat) := n;
}
`;
// The numeral kinds, written without any notation: a unary two, a binary
// three (which m's rule and bnat_numerals both read), and a theory numeral
// six of a declared model.
const kinds = {
  unary: "succ(succ(zero))",
  binary: "b_positive(bp_odd(bp_one))",
  theory: "counted.of_nat(b_positive(bp_even(bp_odd(bp_one))))",
};
// Each shadowing: declarations after the header, and how a value's proof is
// wrapped, as a binder of the printed text would take a reader's name.
// Named notations that take the library readers' names, alone and under
// the other shadowings: then m's rule is the only other reader of a binary
// three.
const named = "notation bnat_numerals {\n  numeral(n : BNat) := b_zero;\n}\nnotation unat {\n  numeral(n : UNat) := succ(n);\n}\n";
const shadowings = {
  none: { declarations: "", proofs: value => [`refl(${value})`] },
  named: { declarations: named, proofs: value => [`refl(${value})`] },
  // A binder named counted cannot enclose a written reference to the model
  // counted; shift supplies it from outside.
  binder: {
    declarations: `${named}def shift(c : Counted(U0), n : BNat) : Unit -> c.M := fun (counted : Unit) => c.of_nat(n);\n`,
    // Each binder is used, so that the printed type binds its name.
    proofs: value => [`fun (m : Unit) => typed(m = m and ${value} = ${value}, (refl(m), refl(${value})))`,
      `fun (unat : Unit) => typed(unat = unat and ${value} = ${value}, (refl(unat), refl(${value})))`,
      "refl(shift(counted, b_positive(bp_odd(bp_one))))"],
  },
  use: {
    declarations: "use counted;\n",
    proofs: value => [`refl(${value})`, `fun (counted : Counted(U0)) => refl(counted.of_nat(b_positive(bp_odd(bp_one))))`],
  },
  import: { imports: "import shadows;\n", declarations: "", proofs: value => [`refl(${value})`] },
  opening: { declarations: named, proofs: value => [`refl(${value})`], section: true },
};
const fallback = sourceReader();
const reader = async (name, ...rest) => name === "shadows"
  ? "import bnat;\nnotation bnat_numerals {\n  numeral(n : BNat) := b_zero;\n}\n" : fallback(name, ...rest);
// A program checked, used and disposed at once: the WASM module holds a
// bounded number of kernel sessions.
const withChecked = async (source, use, options = {}) => {
  const program = new CubicalProgram(module, reader, options);
  try { return await use(program, await program.check(source, "main")); }
  finally { program.dispose(); }
};
const typeOfMismatch = reason => /found (.*), expected Unit\./.exec(reason)?.[1];
const typeOfUse = reason => /this is a value of type (.*)\.$/.exec(reason.replace(/ at \d+:\d+$/, ""))?.[1];

for (const [shadowing, { imports: shadowingImports = "", declarations, proofs, section }] of Object.entries(shadowings)) test(`printed numerals read back where they are printed: ${shadowing}`, async t => {
  const cases = Object.entries(kinds).flatMap(([kind, value]) => proofs(value).map((proof, k) => ({ name: `${kind}_${k}`, proof })));
  const body = section ? "" : cases.map(({ name, proof }) => `print(typeof(${proof}));\ndef shown_${name} := ${proof};\ndef diag_${name} : Unit := ${proof};\n`).join("");
  const anchor = section ? "section (H : Holder(U0)) {\n  def anchor : Unit := tt;\n}\n" : "def anchor : Unit := tt;\n";
  const prefix = imports + shadowingImports + header + declarations;
  const source = `${prefix}${body}${anchor}`;
  await withChecked(source, async (program, result) => {
  const texts = [];
  if (!section) {
    // A print, a mismatch's found type, and the elaboration view's type.
    assert.equal(result.prints.length, cases.length);
    const views = elaboration(program, "main");
    cases.forEach(({ name, proof }, k) => {
      texts.push({ surface: "print", proof, text: result.prints[k].text });
      const gap = result.gaps.find(gap => gap.name === `diag_${name}`);
      texts.push({ surface: "diagnostic", proof, text: typeOfMismatch(gap?.reason ?? "") });
      texts.push({ surface: "elaboration", proof, text: views.find(view => view.name === `shown_${name}`)?.type });
    });
    // A use before its declaration's scope reports the used value's type.
    for (const { proof } of cases)
      texts.push({ surface: "use", proof, text: await withChecked(`${prefix}def used := ${proof};\nuse used;\ndef after_use : Unit := tt;\n`,
        (_, used) => typeOfUse(used.gaps.find(gap => gap.name === "after_use")?.reason ?? "")) });
    // A REPL entry after the module.
    const repl = new ReplSession(program, { base: "main" });
    for (const { proof } of cases) texts.push({ surface: "repl", proof, text: (await repl.run(`typeof ${proof};`))[0]?.text });
    for (const { surface, proof, text } of texts) assert.ok(text, `${surface}: ${proof}`);
    // Every file-level text reads back in the module.
    const readback = texts.filter(({ surface }) => surface !== "repl")
      .map(({ proof, text }, k) => `def readback_${k} : ${text} := ${proof};\n`).join("");
    await withChecked(`${prefix}${readback}`, (_, again) => {
      for (const output of again.outputs.filter(output => output.name.startsWith("readback_")))
        assert.equal(output.verified, true, `${texts[Number(output.name.slice(9))].surface}: ${output.reason}`);
    });
    for (const { proof, text } of texts.filter(({ surface }) => surface === "repl")) {
      const answers = await repl.run(`def repl_readback : ${text} := ${proof};`);
      assert.ok(answers.every(answer => answer.kind !== "error"), `repl: ${text}: ${JSON.stringify(answers)}`);
    }
  }
  // A contextual query at the anchor, in its scope (inside the section, where
  // H's field m is opened).
  const at = source.lastIndexOf("tt;");
  const point = [...program.scopePoints.values()].find(point => point.origin.module === "main"
    && point.origin.start === at && point.phase === "expression" && point.available);
  assert.ok(point);
  for (const { proof } of cases) {
    const session = new ContextualSession(program, point.id);
    try {
      const [shown] = await session.run(`typeof ${proof}`);
      assert.equal(shown.kind, "type", JSON.stringify(shown));
      const [read] = await session.run(`typed(${shown.text}, ${proof})`);
      assert.notEqual(read.kind, "error", `contextual: ${shown.text}: ${JSON.stringify(read)}`);
    } finally { session.dispose(); }
  }
  }, { collectScopes: true });
});

// Every kind of printing entry a notation registers carries what the
// printer's checks read: a reader's notation identity, `attached` exactly
// for a rule a model's module added (which a binder of the model's name
// shadows), and an operator's view identities. A new kind fails here until
// it is classified.
test("every kind of notation printing entry carries the metadata the read-back checks need", async () => {
  const source = `import unat;
import bnat;
import lexemes;
use unat;
theory Counted(U < UU0) {
  M : U;
  inj(n : BNat) : M;
  op(x, y : M) : M notation x + y;
  def of_nat(n : BNat) : M := inj(n) notation numeral;
}
def bits_model : Counted(U0) := Counted.make(M := BNat, inj := fun (n : BNat) => n, op := fun (x, y : BNat) => x);
notation bits_model {
  numeral(n : BNat) := n;
}
def literal_model : Counted(U0) := Counted.make(M := UNat, inj := fun (n : BNat) => 0, op := add);
notation literal_model {
  literal(s : Lexeme) := natural_literal(s);
}
def tagged(a, b : UNat) : UNat := a;
def numeral_model : Counted(U0) := Counted.make(M := UNat, inj := fun (n : BNat) => 0, op := add);
notation numeral_model {
  numeral(n : UNat) := tagged(n, 0);
}
notation fixed {
  numeral(n : UNat) := tagged(n, 0);
}
notation unary_view {
  numeral(n : UNat) := n;
}
notation reader {
  literal(s : Lexeme) := natural_literal(s);
}
def pow(x, n : UNat) : UNat := x;
notation powers {
  x ^ unat.(n) := pow(x, n);
}
`;
  await withChecked(source, (program, result) => {
    assert.deepEqual(result.gaps, [], JSON.stringify(result.gaps));
    const attachedNotations = new Set(["bits_model", "literal_model", "numeral_model"]);
    const kind = entry => entry.identityNumeral ? "identityNumeral" : entry.literal ? "literal" : Array.isArray(entry.numeral) ? "numeral"
      : entry.operator && entry.model ? "modelOperator" : entry.operator ? "operator" : entry.theoryNumeral ? "theoryNumeral"
      : entry.modelRules ? "modelRules" : "unknown";
    const seen = new Map();
    for (const [binding, entries] of program.checker.notationPrinting) for (const entry of entries) {
      const k = kind(entry);
      assert.notEqual(k, "unknown", `${binding}: ${JSON.stringify(entry)}`);
      if (!seen.has(k)) seen.set(k, new Set());
      seen.get(k).add(entry.notation ?? binding);
      if (["identityNumeral", "literal", "numeral", "operator"].includes(k)) {
        assert.equal(typeof entry.identity, "string", `${binding}: ${JSON.stringify(entry)}`);
        assert.equal(entry.attached === true, attachedNotations.has(entry.notation), `${binding}: ${JSON.stringify(entry)}`);
      }
      if (["operator", "modelOperator"].includes(k)) {
        assert.deepEqual(Object.keys(entry.views ?? {}).sort(), ["left", "right"], `${binding}: ${JSON.stringify(entry)}`);
        for (const side of ["left", "right"]) if (entry.recipe[side]) assert.equal(typeof entry.views[side], "string");
      }
    }
    assert.deepEqual([...seen.keys()].sort(),
      ["identityNumeral", "literal", "modelOperator", "modelRules", "numeral", "operator", "theoryNumeral"]);
    // Each fixture's rule is among them, attached or not.
    for (const name of ["bits_model", "unary_view"]) assert.ok(seen.get("identityNumeral").has(name), name);
    for (const name of ["literal_model", "reader"]) assert.ok(seen.get("literal").has(name), name);
    for (const name of ["numeral_model", "fixed"]) assert.ok(seen.get("numeral").has(name), name);
    assert.ok(seen.get("operator").has("powers"));
  });
});

// Terms shown after checking, as an inspector shows them, print in the last
// module's scope, whose transitively imported readers it resolves.
test("terms shown after checking print in the checked module's scope", async () => {
  await withChecked("import nat;\ndef big : Nat := nat.(18446744073709551616);\n", async (program, result) => {
    assert.ok(result.complete, JSON.stringify(result.gaps));
    const { checker } = program;
    const { expression } = checker.checkSyntax({ tag: "DefRef", name: "main__big" }, null, new Map(), new Map());
    const text = checker.displayText(checker.normalForm(expression), []);
    assert.equal(text, "bnat.(18446744073709551616)");
    const again = await withChecked(`import nat;\ndef big_again : Nat := ${text};\ndef same : big_again = nat.(18446744073709551616) := refl(big_again);\n`,
      (_, read) => read.outputs.every(output => output.verified));
    assert.ok(again);
  });
});

// A model's opening hides names that the module's environment still binds:
// where a use opens one before the selection a message prints in, the
// selected receiver and every name but a named notation's are unknown, and
// a numeral prints as written. (The explicit form names the declared model
// m, which the opening also hides; display naming does not qualify it.)
const opened = `import unat;
import bnat;
theory Counted(U < UU0) {
  M : U;
  inj(n : BNat) : M;
  def of_nat(n : BNat) : M := inj(n) notation numeral;
}
def m : Counted(U0) := Counted.make(M := BNat, inj := fun (n : BNat) => n);
def other : Counted(U0) := Counted.make(M := BNat, inj := fun (n : BNat) => b_zero);
theory Holder(U < UU0) {
  m : Counted(U0);
}
def holder : Holder(U0) := Holder.make(m := other);
`;
test("a use before a declaration's scope trusts no name an earlier opening may hide", async () => {
  await withChecked(`${opened}def p := refl(m.of_nat(b_positive(bp_odd(bp_one))));\nuse holder;\nuse m;\nuse p;\ndef after : Unit := tt;\n`, (_, result) => {
    const text = typeOfUse(result.gaps.find(gap => gap.name === "after")?.reason ?? "");
    assert.equal(text, "Counted.of_nat{{U0}}(m, bnat_numerals.(3)) = Counted.of_nat{{U0}}(m, bnat_numerals.(3))");
  });
});

// After checking, a term prints in the module's final scope, the one a
// definition appended to it reads: its uses applied, openings included.
// holder's field m hides m's attached rule, however many items follow the
// use, and a notation declared after it is in scope; m's own opening leaves
// m's name, and its rule, in place.
test("terms shown after checking keep the openings of the module's uses", async () => {
  const declarations = `${opened}notation m {\n  numeral(n : BNat) := n;\n}\nnotation bnat_numerals {\n  numeral(n : BNat) := b_zero;\n}\ndef three : BNat := b_positive(bp_odd(bp_one));\n`;
  const explicit = "b_positive(bp_odd(bp_one))";
  for (const [tail, expected] of [["use holder;\n", explicit], ["use holder;\ndef later : Unit := tt;\n", explicit],
    ["use holder;\nnotation later {\n  numeral(n : BNat) := n;\n}\n", "later.(3)"], ["use m;\n", "m.(3)"]])
    await withChecked(declarations + tail, async (program, result) => {
      assert.deepEqual(result.gaps, [], JSON.stringify(result.gaps));
      const { checker } = program;
      const { expression } = checker.checkSyntax({ tag: "DefRef", name: "main__three" }, null, new Map(), new Map());
      const text = checker.displayText(checker.normalForm(expression), []);
      assert.equal(text, expected, tail);
      assert.ok(await withChecked(`${declarations}${tail}def three_again : three = ${text} := refl(three);\n`,
        (_, again) => again.outputs.every(output => output.verified)), tail);
    });
});

// A display's lookups cost a few reads of the scope's environment, whatever
// its size: no lookup walks the environment (the review measured a
// quadratic rebuild of it per display), so displays scale linearly with the
// number of terms shown. The checker is a real one, whose compilation
// bindings a rebuild would read.
test("a printing scope's lookups read the environment without walking it", async () => {
  const { notationContext, notationForUses, notationBinding } = await import("../web/translator/notation-context.mjs");
  class CountingMap extends Map {
    reads = 0;
    walks = 0;
    get(key) { this.reads++; return super.get(key); }
    entries() { this.walks++; return super.entries(); }
    [Symbol.iterator]() { return this.entries(); }
    keys() { this.walks++; return super.keys(); }
    values() { this.walks++; return super.values(); }
    forEach(...rest) { this.walks++; return super.forEach(...rest); }
  }
  await withChecked("import unat;\n", ({ checker }) => {
    assert.ok(checker.compilationBindings);
    const costs = [];
    for (const size of [100, 10000]) {
      const env = new CountingMap([...Array(size)].map((_, k) => [`name_${k}`, { tag: "DefRef", name: `main__name_${k}` }]));
      env.set(notationBinding("unat"), { tag: "Notation", bindingId: "unat-id" });
      env.reads = 0;
      for (let k = 0; k < 100; k++) {
        const context = k % 2 ? notationContext({ env, checker }, null) : notationForUses(env, checker, [{ kind: "name", name: "unat" }]);
        const found = [context.reads("unat"), context.reads("name_1"), context.opens("name_1", { tag: "DefRef", name: "main__name_1" }, false)];
        assert.equal(env.walks, 0, `size ${size}: a lookup walked the environment`);
        assert.deepEqual(found, ["unat-id", null, true]);
      }
      costs.push(env.reads);
    }
    assert.equal(costs[0], costs[1], `reads at 100 and 10000 names: ${costs}`);
    assert.ok(costs[0] <= 100 * 12, `${costs[0]} reads for 100 displays`);
  });
});
