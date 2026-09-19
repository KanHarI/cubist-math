import test from "node:test";
import assert from "node:assert/strict";
import { readFile } from "node:fs/promises";
import { spawnSync } from "node:child_process";
import createKernel from "../web/dist/kernel.mjs";
import { compile } from "../web/mathscript/compiler.mjs";
import { Kernel } from "../web/kernel.mjs";
import { sourceModules } from "../web/mathscript/modules.mjs";
import catalogue from "../web/proofs/catalogue.mjs";
import { MAX_STEPS } from "../web/language.mjs";
const module = await createKernel();
const source = async (name) =>
  readFile(new URL("../web/proofs/" + name, import.meta.url), "utf8");
const primes = await source("primes.proof");
const sources = Object.fromEntries(
  await Promise.all(
    sourceModules.map(async (name) => [name, await source(name + ".proof")]),
  ),
);
function expression(k, binding) {
  return k.module._wb_view(k.handle, 0, k.bindings.get(binding).id, 0);
}
function canonical(k, id) {
  const n = k.node(id);
  return [n.kind, n.parameter, ...n.children.map((c) => canonical(k, c))];
}
function normalize(k, name) {
  for (let i = 0; i < 40; i++) {
    const next = "comparison" + i;
    k.apply({ name: next, op: "DefBetaReduceGrossKnuth", args: [name] });
    if (expression(k, next) === expression(k, name)) return expression(k, next);
    name = next;
  }
  throw new Error("Normalization did not converge");
}
test("complete prime development is checked from mathematical source, without axioms", () => {
  const c = compile(module, primes);
  try {
    assert.equal(c.outputs.length, 42);
    assert.ok(
      !c.outputs.some((o) =>
        ["InfinitelyManyPrimes", "infinitely_many_primes"].includes(o.name),
      ),
    );
    assert.equal(c.axiomCount, 0);
    for (const o of c.outputs)
      assert.ok(c.kernel.verify(o.proposition, o.binding), o.name);
    assert.match(
      c.outputs.find((o) => o.name === "factorial_positive").type,
      /forall n : Nat, \(1 <= factorial\(n\)\)/,
    );
  } finally {
    c.kernel.dispose();
  }
});
test("Euclid imports source and proves the same proposition as the original saved proof", async () => {
  const c = compile(module, await source("euclid.proof"), primes),
    k = new Kernel(module, false);
  try {
    const doc = JSON.parse(await source("primes.thth.json"));
    for (const s of doc.steps) k.apply(s);
    assert.deepEqual(
      canonical(c.kernel, normalize(c.kernel, "euclid_type")),
      canonical(k, normalize(k, "InfinitelyManyPrimes")),
    );
    assert.equal(
      c.outputs.find((o) => o.name === "euclid").type,
      "InfinitelyManyPrimes",
    );
    assert.ok(c.outputs.some((o) => o.name === "InfinitelyManyPrimes"));
    assert.ok(
      !c.imports.some((o) =>
        ["InfinitelyManyPrimes", "infinitely_many_primes"].includes(o.name),
      ),
    );
    assert.ok(c.kernel.verify("InfinitelyManyPrimes", "euclid"));
    assert.ok(c.links.some((l) => l.name === "InfinitelyManyPrimes"));
    assert.ok(c.steps.some((s) => s.goal === "InfinitelyManyPrimes"));
    assert.ok(
      c.steps.some((s) =>
        s.locals.some((v) => v.name === "n" && v.type === "Nat"),
      ),
    );
    assert.equal(
      c.imports.find((d) => d.name === "factorial_positive").sourceName,
      "factorial_positive",
    );
    assert.ok(
      c.links.some(
        (l) =>
          l.role === "notation" && l.name === "<" && l.sourceName === "isLt",
      ),
    );
    assert.ok(c.links.some((l) => l.name === "2" && l.type === "Nat"));
    const bounded = c.steps
      .flatMap((s) => s.locals)
      .find((v) => v.name === "bounded");
    assert.equal(bounded.type, "(p <= n)");
  } finally {
    c.kernel.dispose();
    k.dispose();
  }
});
test("functions, pairs, higher-order substitution, and numeral computation", async () => {
  const c = compile(module, await source("basics.proof"));
  try {
    assert.ok(c.kernel.verify("copy_of_two_type", "copy_of_two"));
  } finally {
    c.kernel.dispose();
  }
  const dependent = compile(
    module,
    "def Both = fun (A : Type) => A and A; theorem duplicate = fun (A : Type) => fun (x : A) => typed(Both(A), (x,x));",
  );
  dependent.kernel.dispose();
});
test("intro opens aliased dependent goals and implications without changing their checked types", () => {
  const c = compile(
    module,
    `
    def Reflexive = forall n : Nat, n = n;
    def Alias = Reflexive;
    theorem reflexive : Alias { intro k; exact refl(k); }
    def Repeated = forall n : Nat, forall m : Nat, (n = m) -> (n = m);
    theorem repeated : Repeated { intro x; intro y; intro h; exact h; }
  `,
  );
  try {
    assert.ok(c.kernel.verify("Alias", "reflexive"));
    assert.ok(c.kernel.verify("Repeated", "repeated"));
    assert.equal(c.outputs.find((o) => o.name === "reflexive").type, "Alias");
  } finally {
    c.kernel.dispose();
  }
  assert.throws(
    () => compile(module, "theorem bad : Nat { intro n; exact n; }"),
    /intro requires/,
  );
  assert.throws(
    () =>
      compile(
        module,
        "def FalseGoal = forall n : Nat, Void; theorem bad : FalseGoal { intro n; exact n; }",
      ),
    /Expected Void/,
  );
  assert.throws(
    () =>
      compile(
        module,
        "def Goal = forall n : Nat, n = n; theorem bad : Goal { intro n; exact refl(0); }",
      ),
    /Expected/,
  );
});
test("rejects wrong induction branches, unbound variables, and invalid conclusions", () => {
  assert.throws(
    () => compile(module, "theorem wrong : Void { exact 0; }"),
    /Expected Void; got Nat/,
  );
  assert.throws(
    () =>
      compile(
        module,
        "def bad(n : Nat) = induction n as k return Nat { zero => tt; succ ih => ih; };",
      ),
    /Expected.*Nat/,
  );
  assert.throws(
    () => compile(module, "def escaped = missing;"),
    /Unknown name/,
  );
  assert.throws(
    () =>
      compile(
        module,
        "import primes; theorem bogus(n : Nat) : n < n { exact tt; }",
        primes,
      ),
    /Expected/,
  );
});
test("all audit translations preserve every checked instruction and exported result", async () => {
  for (const entry of catalogue) {
    const c = compile(module, await source(entry.id + ".construction.proof")),
      k = new Kernel(module, entry.allowAxioms);
    try {
      for (const step of JSON.parse(await source(entry.file)).steps)
        k.apply(step);
      assert.equal(c.instructionCount, k.steps.length, entry.id);
      for (const name of entry.exports)
        assert.equal(
          c.kernel.bindings.get(name).id,
          k.bindings.get(name).id,
          entry.id + ":" + name,
        );
      if (entry.verify) assert.ok(c.kernel.verify(...entry.verify));
      assert.equal(c.allowAxioms, entry.allowAxioms);
    } finally {
      c.kernel.dispose();
      k.dispose();
    }
  }
});
test("CLI compiles mathematical source and retains selection commands", () => {
  const run = spawnSync(process.execPath, ["cli/repl.mjs"], {
    cwd: new URL("..", import.meta.url),
    input:
      "prove web/proofs/basics.proof\nuse copy_of_two\nselect type.left\ncheck copy_of_two_type copy_of_two\nquit\n",
    encoding: "utf8",
  });
  assert.equal(run.status, 0, run.stderr);
  assert.doesNotMatch(run.stdout, /ERROR:/);
  assert.match(run.stdout, /CHECKED copy_of_two/);
  assert.match(run.stdout, /VERIFIED/);
  assert.match(run.stdout, /⟦/);
});

test("suspension induction, path computation, and integer equivalence are checked from source", () => {
  for (const name of ["suspension", "integers", "circle"]) {
    const c = compile(module, sources[name], sources);
    try {
      for (const o of c.outputs)
        assert.ok(
          c.kernel.verify(o.proposition, o.binding),
          `${name}:${o.name}`,
        );
      assert.equal(c.allowAxioms, name === "circle");
      if (name === "suspension") {
        assert.ok(c.kernel.steps.some((s) => s.op === "SuspMeridComp"));
        assert.equal(c.axiomCount, 0);
      }
      if (name === "circle") {
        assert.equal(c.axiomCount, 3);
        assert.ok(
          c.kernel.verify(
            "FundamentalGroupS1IsZ",
            "fundamental_group_of_circle",
          ),
        );
        for (const source of Object.values(sources))
          assert.doesNotMatch(source, /construction\s+\w+\s*\{/);
        assert.ok(c.kernel.bindings.has("lib_univalence"));
        assert.ok(c.kernel.bindings.has("lib_ua_elim"));
        assert.ok(
          c.kernel.verify("successor_transport_type", "successor_transport"),
        );
      }
    } finally {
      c.kernel.dispose();
    }
  }
});
test("dependent matches check each branch against its injected motive", () => {
  assert.throws(
    () =>
      compile(
        module,
        "def S = Unit or Nat; def bad(s : S) = match s as x return x = x { left u => refl(s); right n => refl(s); };",
      ),
    /Expected/,
  );
  assert.throws(
    () =>
      compile(module, "def S = Suspension(Unit); def bad = meridian(Unit, 0);"),
    /Expected Unit/,
  );
  assert.throws(
    () => compile(module, "import missing; def x = 0;", sources),
    /requires its mathematical/,
  );
  assert.throws(
    () =>
      compile(module, "import a; def x = 0;", {
        a: "import b; def a = 0;",
        b: "import a; def b = 0;",
      }),
    /Cyclic module/,
  );
});

test("circle proof rejects a wrong winding number and a fake inverse law", () => {
  assert.throws(
    () =>
      compile(
        module,
        sources.circle.replace(
          "winding(loop) = nonnegative(1)",
          "winding(loop) = zeroZ",
        ),
        sources,
      ),
    /Expected/,
  );
  assert.throws(
    () =>
      compile(
        module,
        sources.circle.replace(
          "exact decode_encode(base, p);",
          "exact refl(p);",
        ),
        sources,
      ),
    /Expected/,
  );
});
test("CLI opens the complete high-level fundamental-group proof", () => {
  const run = spawnSync(process.execPath, ["cli/repl.mjs"], {
    cwd: new URL("..", import.meta.url),
    encoding: "utf8",
    input:
      "prove web/proofs/circle.proof\ncheck FundamentalGroupS1IsZ fundamental_group_of_circle\nquit\n",
  });
  assert.equal(run.status, 0, run.stderr);
  assert.doesNotMatch(run.stdout, /ERROR:/);
  assert.match(run.stdout, /VERIFIED/);
});

test("axioms are tracked per result rather than per imported module", () => {
  const c = compile(
    module,
    "import prelude; import paths; def plain = 0; theorem reflexive : 0 = 0 { exact refl(0); } theorem extensional : (fun (x : Nat) => x) = (fun (x : Nat) => x) { exact funext(Nat, (fun (x : Nat) => Nat), (fun (x : Nat) => x), (fun (x : Nat) => x), (fun (x : Nat) => refl(x))); }",
    sources,
  );
  try {
    assert.equal(c.axiomCount, 3);
    assert.deepEqual(c.outputs.find((o) => o.name === "plain").axioms, []);
    assert.deepEqual(c.outputs.find((o) => o.name === "reflexive").axioms, []);
    assert.deepEqual(c.outputs.find((o) => o.name === "extensional").axioms, [
      "lib_funext",
    ]);
    assert.deepEqual(c.kernel.inspect("extensional").axioms, ["lib_funext"]);
  } finally {
    c.kernel.dispose();
  }
});

test("finite types, structural subsets, and all finite functions have checked counts", () => {
  for (const name of ["finite", "binomial", "function_counting"]) {
    const c = compile(module, sources[name], sources);
    try {
      for (const o of c.outputs)
        assert.ok(c.kernel.verify(o.proposition, o.binding), o.name);
      if (name === "binomial")
        assert.ok(
          c.kernel.verify(
            "five_choose_two_bijection_type",
            "five_choose_two_bijection",
          ),
        );
      if (name === "function_counting") {
        assert.deepEqual(
          c.outputs.find((o) => o.name === "endofunction_count").axioms,
          ["lib_funext"],
        );
        assert.ok(c.kernel.verify("three_to_three_type", "three_to_three"));
        assert.ok(c.kernel.verify("empty_to_empty_type", "empty_to_empty"));
      }
    } finally {
      c.kernel.dispose();
    }
  }
  assert.throws(
    () =>
      compile(
        module,
        sources.function_counting.replace("Fin(27)", "Fin(26)"),
        sources,
      ),
    /Expected/,
  );
});


test("opaque concepts preserve names, support conversion, and explicitly unfold", () => {
  const c = compile(module, `
    opaque def Box = Nat;
    opaque def successor(n : Nat) = succ(n);
    def boxed : Box { exact 2; }
    def folded = successor(1);
    def opened = unfold(folded);
    def beta = (fun (x : Nat) => succ(x))(1);
    theorem converted : successor(1) = 2 { exact refl(2); }
  `);
  try {
    for (const o of c.outputs) assert.ok(c.kernel.verify(o.proposition, o.binding));
    assert.equal(c.kernel.node(expression(c.kernel, "Box")).kind, "DRef");
    assert.equal(c.kernel.node(expression(c.kernel, "folded")).kind, "Ap");
    assert.equal(expression(c.kernel, "opened"), expression(c.kernel, "beta"));
    assert.equal(c.axiomCount, 0);
  } finally { c.kernel.dispose(); }
  assert.throws(() => compile(module, "opaque def wrong : Nat { exact tt; }"), /Expected/);
});

test("declared axioms keep their names and only affect dependent results", () => {
  const c = compile(module, "axiom chosen : Nat; def witness = chosen; def plain = 0;");
  try {
    assert.equal(c.axiomCount, 1);
    assert.equal(c.outputs.find(o => o.name === "chosen").kind, "axiom");
    assert.deepEqual(c.kernel.axiomsFor("witness"), ["chosen"]);
    assert.deepEqual(c.kernel.axiomsFor("plain"), []);
  } finally { c.kernel.dispose(); }
  assert.throws(() => compile(module, "axiom invalid : 0;"), /type/i);
});

test("Rijke binomial types and full permutation equivalences have checked counts", () => {
  for (const name of ["permutations", "binomial_counting"]) {
    const c = compile(module, sources[name], sources);
    try {
      for (const o of c.outputs) assert.ok(c.kernel.verify(o.proposition, o.binding), o.name);
      // These real developments exceed the former 131,072 instruction limit.
      assert.ok(c.instructionCount > 131072);
      if (name === "permutations") {
        assert.deepEqual(c.kernel.axiomsFor("finite_permutation_equivalence"), ["lib_funext"]);
      } else {
        const assumptions = ["lib_funext", "lib_Trunc", "lib_trunc_intro", "lib_trunc_is_trunc", "lib_trunc_elim"].sort();
        assert.deepEqual(c.kernel.axiomsFor("finite_binomial_equivalence").sort(), assumptions);
        assert.deepEqual(c.kernel.axiomsFor("choose_units_five_two").sort(), [...assumptions, "lib_univalence"].sort());
      }
    } finally { c.kernel.dispose(); }
  }
  for (const [name, from, to] of [["permutations", "Fin(6)", "Fin(7)"], ["binomial_counting", "Fin(10)", "Fin(9)"]]) {
    assert.throws(() => compile(module, sources[name].replace(from, to), sources), /Expected/);
  }
});


test("truncation elimination uses the prelude axiom and checks both premises", () => {
  const c = compile(module, `import truncation;
    def map_identity(A : Type) = mere_map(A, A, (fun (a : A) => a));`, sources);
  try {
    assert.deepEqual(c.kernel.axiomsFor("map_identity").sort(),
      ["lib_Trunc", "lib_trunc_intro", "lib_trunc_is_trunc", "lib_trunc_elim"].sort());
    assert.ok(!c.kernel.steps.some(s => s.op === "Axiom" && s.name === "mere_eliminate"));
    assert.ok(c.kernel.steps.some(s => s.op === "Axiom" && s.name === "lib_trunc_elim"));
  } finally { c.kernel.dispose(); }
  assert.throws(() => compile(module, `import truncation;
    def bad(A : Type, P : Type, prop : IsProp(P), f : Type -> P) =
      mere_eliminate(A, P, prop, f);`, sources), /Expected/);
  assert.throws(() => compile(module, `import truncation;
    def bad(A : Type, P : Type, f : A -> P) = mere_eliminate(A, P, tt, f);`, sources), /Expected/);
});


test("every surjection between sets has a right inverse using the existing choice axiom", () => {
  const c = compile(module, sources.surjections, sources);
  try {
    for (const o of c.outputs)
      assert.ok(c.kernel.verify(o.proposition, o.binding), o.name);
    assert.ok(c.kernel.verify("EverySurjectionHasRightInverse", "every_surjection_has_right_inverse"));
    assert.deepEqual(c.kernel.axiomsFor("every_surjection_has_right_inverse").sort(),
      ["AOC", "lib_Trunc", "lib_trunc_elim", "lib_trunc_intro", "lib_trunc_is_trunc"].sort());
    for (const name of ["right_inverse_from_preimages", "subtype_is_set", "fiber_is_set"])
      assert.deepEqual(c.kernel.axiomsFor(name), [], name);
    assert.ok(c.links.some(link => link.name === "set_choice" && link.binding === "AOC" &&
      link.sourceModule === "prelude_library_construction"));
  } finally { c.kernel.dispose(); }
  // Choice gives mere existence, not a distinguished inverse function.
  assert.throws(() => compile(module, sources.surjections.replace(
    "-> Mere(RightInverse(A, B, f));", "-> RightInverse(A, B, f);"), sources), /Expected/);
});

test("set choice checks its family, setness conditions, and inhabitation evidence", () => {
  const program = `import sets; import truncation;
    def choose(A : Type, B : A -> Type, base : IsSet(A),
      fibers : (forall x : A, IsSet(B(x))), inhabited : (forall x : A, Mere(B(x)))) =
      set_choice(A, B, base, fibers, inhabited);`;
  const c = compile(module, program, sources);
  try {
    assert.ok(c.kernel.verify("choose_type", "choose"));
    assert.deepEqual(c.kernel.axiomsFor("choose").sort(), ["AOC", "lib_Trunc"]);
  } finally { c.kernel.dispose(); }
  for (const args of [
    "A, (fun (x : A) => tt), base, fibers, inhabited",
    "A, B, tt, fibers, inhabited",
    "A, B, base, tt, inhabited",
    "A, B, base, fibers, tt",
  ]) {
    assert.throws(() => compile(module, program.replace(
      "set_choice(A, B, base, fibers, inhabited)", `set_choice(${args})`), sources), /Expected/);
  }
});

test("Cantor-Schroeder-Bernstein constructs a full equivalence without choice", () => {
  const c = compile(module, sources.schroeder_bernstein, sources);
  try {
    for (const o of c.outputs)
      assert.ok(c.kernel.verify(o.proposition, o.binding), o.name);
    assert.ok(c.kernel.verify("CantorSchroederBernstein", "cantor_schroeder_bernstein"));
    const expected = [...new Set([
      ...c.kernel.axiomsFor("LEM"), "lib_Trunc", "lib_trunc_elim", "lib_funext",
    ])].sort();
    assert.deepEqual(c.kernel.axiomsFor("cantor_schroeder_bernstein").sort(), expected);
    assert.ok(!c.kernel.bindings.has("AOC"));
    assert.equal(c.kernel.bindings.get("s0121_Axiom").id, c.kernel.bindings.get("lib_Trunc").id);
    assert.ok(!c.kernel.axiomsFor("cantor_schroeder_bernstein").includes("s0121_Axiom"));
    assert.ok(c.preludeAxioms.includes("LEM"));
    assert.deepEqual(c.kernel.axiomsFor("injective_split_bijection"), []);
  } finally { c.kernel.dispose(); }
  // The supplied injection f is not generally surjective; it cannot replace
  // the constructed piecewise bijection while retaining its inverse proofs.
  assert.throws(() => compile(module, sources.schroeder_bernstein.replace(
    "injective_split_bijection(A, B, csb_map(A, B, f, g, embedG), csb_injective",
    "injective_split_bijection(A, B, f, csb_injective"), sources), /Expected/);
});

test("classical logic checks double-negation evidence and restricts elimination to propositions", () => {
  const valid = `import classical;
    def eliminate(P : Type, prop : Proposition(P), nn : (P -> Void) -> Void) = double_negation(P, prop, nn);`;
  for (const call of ["double_negation(P, tt, nn)", "double_negation(P, prop, tt)"])
    assert.throws(() => compile(module, valid.replace("double_negation(P, prop, nn)", call), sources), /Expected/);
});

test("compiler reports completed definitions including imports and stops on errors", () => {
  const updates = [];
  const c = compile(module, "import helper; theorem two : second = 2 { exact refl(2); }",
    {helper: "def first = 1; def second = succ(first);"}, {onProgress: p => updates.push(p)});
  try {
    assert.equal(updates[0].completed, 0);
    assert.equal(updates[0].total, 3);
    assert.equal(updates[0].current, "first");
    assert.equal(updates.at(-1).completed, 3);
    assert.ok(updates.every((p, i) => !i || p.completed >= updates[i - 1].completed));
  } finally { c.kernel.dispose(); }
  const failed = [];
  assert.throws(() => compile(module, "def first = 1; theorem bad : Void { exact 0; }", {},
    {onProgress: p => failed.push(p)}), /Expected/);
  assert.equal(failed.at(-1).completed, 1);
  assert.equal(failed.at(-1).current, "bad");
  const audit = [];
  const a = compile(module, "construction tiny { export N = natural_type(); }", {},
    {onProgress: p => audit.push(p)});
  try {
    assert.equal(audit[0].completed, 0);
    assert.equal(audit.at(-1).completed, 1);
    assert.equal(audit.at(-1).total, 1);
    assert.equal(audit.at(-1).unit, "steps");
  } finally { a.kernel.dispose(); }
});

test("explicit universe primitives support large types and reject invalid specialization", () => {
  const c = compile(module, `import prelude;
    def large = truncation_at(Type1, Type);
    def larger = truncation_at(Type2, Type1);
    def large_intro = truncation_intro_at(Type1, Type, Unit);
    def large_prop = truncation_prop_at(Type1, Type);
    theorem high_funext(A : Type2, B : A -> Type2, f : (forall a : A, B(a))) : f = f {
      exact funext_at(Type2, A, B, f, f, (fun (a : A) => refl(f(a))));
    }
    def high_elim(A : Type2, P : Type2, prop : (forall x : P, forall y : P, x = y), f : A -> P) =
      truncation_elim_at(Type2, A, P, prop, f);`, sources);
  try {
    for (const o of c.outputs) assert.ok(c.kernel.verify(o.proposition, o.binding), o.name);
    assert.deepEqual(c.kernel.axiomsFor("high_funext"), ["lib_funext"]);
    assert.deepEqual(c.kernel.axiomsFor("high_elim").sort(), ["lib_Trunc", "lib_trunc_elim"]);
    assert.deepEqual(c.kernel.axiomsFor("large"), ["lib_Trunc"]);
    assert.ok(c.links.some(link => link.name === "funext_at" && link.binding === "lib_funext"));
    assert.ok(c.links.some(link => link.name === "truncation_at" && link.binding === "lib_Trunc"));
    assert.ok(!c.kernel.bindings.has("LEM"));
    assert.ok(!c.kernel.bindings.has("AOC"));
  } finally { c.kernel.dispose(); }
  for (const expression of [
    "truncation_at(Type, Type)",
    "truncation_at(Unit, Unit)",
    "truncation_intro_at(Type1, Unit, 0)",
    "truncation_elim_at(Type1, Unit, Nat, (fun (a : Nat) => fun (b : Nat) => refl(a)), (fun (x : Unit) => 0))",
    "truncation_elim_at(Type1, Unit, Type1, tt, tt)",
  ]) {
    assert.throws(() => compile(module, `import prelude; def bad = ${expression};`, sources), /Expected/);
  }
});

test("real-field foundations and constructive constructions do not acquire classical or choice axioms", () => {
  const allowed = new Set(["lib_Trunc", "lib_trunc_intro", "lib_trunc_elim", "lib_trunc_is_trunc", "lib_funext", "lib_univalence"]);
  for (const name of ["field_logic", "field_extensionality", "ordered_fields", "complete_fields", "dedekind_cuts", "set_quotients", "cauchy_quotient"]) {
    const c = compile(module, sources[name], sources);
    try {
      for (const o of c.outputs) {
        assert.ok(c.kernel.verify(o.proposition, o.binding), `${name}.${o.name}`);
        assert.ok(c.kernel.axiomsFor(o.binding).every(a => allowed.has(a)), `${name}.${o.name} axiom dependencies`);
      }
      assert.ok(!c.kernel.bindings.has("LEM"), name);
      assert.ok(!c.kernel.bindings.has("AOC"), name);
      if (name === "complete_fields") {
        assert.deepEqual(c.kernel.axiomsFor("FieldCauchy"), []);
        assert.deepEqual(c.kernel.axiomsFor("field_constant_converges"), []);
      }
      if (name === "ordered_fields") {
        assert.deepEqual(c.kernel.axiomsFor("field_inverse_unique"), []);
        assert.deepEqual(c.kernel.axiomsFor("field_add_cancel"), []);
      }
      if (name === "cauchy_quotient") assert.deepEqual(c.kernel.axiomsFor("close_tails_compose"), []);
    } finally { c.kernel.dispose(); }
  }
});

test("Boolean cut encoding is classical while decoding preserves constructive assumptions", () => {
  const c = compile(module, sources.boolean_cuts, sources);
  try {
    for (const o of c.outputs) assert.ok(c.kernel.verify(o.proposition, o.binding), o.name);
    assert.deepEqual(c.kernel.axiomsFor("boolean_to_dedekind"), ["lib_Trunc"]);
    assert.deepEqual(c.kernel.axiomsFor("decision_truth"), []);
    assert.ok(c.kernel.axiomsFor("dedekind_to_boolean").includes("LEM"));
    assert.ok(c.kernel.axiomsFor("classical_lower_membership").includes("LEM"));
    assert.ok(c.kernel.axiomsFor("classical_upper_membership").includes("LEM"));
    assert.ok(!c.kernel.bindings.has("AOC"));
  } finally { c.kernel.dispose(); }
});

test("quotient representatives and their choice-dependent sequences remain merely inhabited", () => {
  // Neither the class map's surjectivity proof nor a truncated choice conclusion
  // can supply a distinguished representative (or sequence of representatives).
  const single = sources.set_quotients.replace(
    "FieldExists(exists a : A, quotient_class(A, relation, a) = q) {",
    "(exists a : A, quotient_class(A, relation, a) = q) {");
  assert.notEqual(single, sources.set_quotients);
  assert.throws(() => compile(module, single, sources), /Expected/);
  const sequence = sources.cauchy_quotient.replace(
    "FieldExists(forall n : Nat, exists s : CauchySequence(Q, zero, addQ, ltQ),",
    "(forall n : Nat, exists s : CauchySequence(Q, zero, addQ, ltQ),");
  assert.notEqual(sequence, sources.cauchy_quotient);
  assert.throws(() => compile(module, sequence, sources), /Expected/);
});

test("puncture graph constructions and all-loop generation check without classical logic or choice", () => {
  const foundational = ["lib_Trunc", "lib_trunc_intro", "lib_trunc_elim", "lib_trunc_is_trunc", "lib_funext", "lib_univalence", "lib_ua_elim"].sort();
  for (const name of ["path_actions", "loop_words", "puncture_graph", "bouquet_cover", "bouquet_generation", "bouquet_invariants", "bouquet_actions", "puncture_winding", "puncture_noncommutative"]) {
    const c = compile(module, sources[name], sources);
    try {
      for (const o of c.outputs) {
        assert.ok(c.kernel.verify(o.proposition, o.binding), `${name}.${o.name}`);
        assert.ok(c.kernel.axiomsFor(o.binding).every(a => foundational.includes(a)), `${name}.${o.name} axioms`);
      }
      assert.ok(!c.kernel.bindings.has("LEM"), name);
      assert.ok(!c.kernel.bindings.has("AOC"), name);
      assert.ok(!c.outputs.some(o => o.kind === "axiom"), name);
      if (["path_actions", "puncture_graph"].includes(name)) {
        for (const o of c.outputs) assert.deepEqual(c.kernel.axiomsFor(o.binding), [], o.name);
      }
      if (name === "loop_words") assert.deepEqual(c.kernel.axiomsFor("word_backtrack_cancels"), []);
      if (name === "bouquet_generation") {
        assert.deepEqual(c.kernel.axiomsFor("every_puncture_loop_generated").sort(), foundational);
        assert.match(c.outputs.find(o => o.name === "every_puncture_loop_generated").type, /Mere\(exists word/);
      }
      if (name === "bouquet_invariants") {
        assert.deepEqual(c.kernel.axiomsFor("bouquet_maps_determined_by_generators").sort(), foundational);
        assert.match(c.outputs.find(o => o.name === "bouquet_maps_determined_by_generators").type, /Type1/);
      }
      if (name === "puncture_noncommutative") {
        assert.deepEqual(c.kernel.axiomsFor("puncture_commutator_nontrivial").sort(), ["lib_ua_elim", "lib_univalence"]);
        assert.deepEqual(c.kernel.axiomsFor("winding_vector_does_not_classify_loops").sort(), ["lib_funext", "lib_ua_elim", "lib_univalence"]);
      }
    } finally { c.kernel.dispose(); }
  }
});

test("the generation proof cannot replace mere word existence with a selected word", () => {
  const untruncated = sources.bouquet_generation.replace(
    "Mere(exists word : Word(Fin(n)),", "(exists word : Word(Fin(n)),");
  assert.notEqual(untruncated, sources.bouquet_generation);
  assert.throws(() => compile(module, untruncated, sources), /Expected/);
  assert.throws(() => compile(module, `import bouquet_generation;
    theorem empty_word_for_every_loop(A : Type, p : BouquetLoops(A)) : BouquetGenerated(A, p) {
      exact generated_identity(A, Bouquet(A), bouquet_base(A), bouquet_generator(A));
    }`, sources), /Expected/);
});

test("signed cancellation and noncommutativity reject incorrect generator actions", () => {
  const wrongSigns = sources.loop_words.replace(
    "left a => right(a);\n  right a => left(a);",
    "left a => left(a);\n  right a => right(a);");
  assert.notEqual(wrongSigns, sources.loop_words);
  assert.throws(() => compile(module, wrongSigns, sources), /Expected/);
  // If both generators act by the same transposition, the claimed action of
  // the commutator is false. The kernel must reject the purported witness.
  const collapsedAction = sources.puncture_noncommutative.replace(
    "left u => second_permutation;", "left u => first_permutation;");
  assert.notEqual(collapsedAction, sources.puncture_noncommutative);
  assert.throws(() => compile(module, collapsedAction, sources), /Expected/);
});

test("large-proposition elimination still checks proposition evidence", () => {
  assert.throws(() => compile(module, `import field_logic;
    def invalid(A : Type, h : truncation(A)) : A {
      exact small_mere_eliminate(A, A, (fun (x : A) => fun (y : A) => refl(x)), (fun (x : A) => x), h);
    }`, sources), /Expected/);
});

test("complex ring and polynomial identities check at Type1 with only stated assumptions", () => {
  const truncation = ["lib_Trunc", "lib_trunc_intro", "lib_trunc_elim", "lib_trunc_is_trunc"].sort();
  for (const name of ["field_products", "ring_laws", "complex_coordinates", "complex_numbers", "complex_algebra", "complex_polynomials", "polynomial_difference"]) {
    const c = compile(module, sources[name], sources);
    try {
      for (const o of c.outputs) {
        assert.ok(c.kernel.verify(o.proposition, o.binding), `${name}.${o.name}`);
        const expected = o.name === "algebraic_closure_implies_square_roots" ? truncation :
          o.name === "MonicAlgebraicClosure" ? ["lib_Trunc"] : [];
        assert.deepEqual(c.kernel.axiomsFor(o.binding).sort(), expected, `${name}.${o.name} axioms`);
      }
      assert.ok(!c.kernel.bindings.has("LEM"), name);
      assert.ok(!c.kernel.bindings.has("AOC"), name);
      if (name === "complex_algebra") {
        assert.match(c.outputs.find(o => o.name === "complex_commutative_ring").type, /CommutativeRing/);
        assert.match(c.outputs.find(o => o.name === "complex_inverse_from_norm").type, /normLaw/);
      }
      if (name === "complex_numbers") {
        assert.match(c.outputs.find(o => o.name === "Complex").type, /Type1/);
      }
      if (name === "complex_polynomials") {
        assert.match(c.outputs.find(o => o.name === "algebraic_closure_implies_square_roots").type, /closed : MonicAlgebraicClosure/);
      }
    } finally { c.kernel.dispose(); }
  }
});

test("complex multiplication signs and exact-root truncation cannot be changed silently", () => {
  const wrongSign = sources.complex_numbers.replace(
    "negF(mulF(complex_imag(F, z), complex_imag(F, w)))",
    "mulF(complex_imag(F, z), complex_imag(F, w))");
  assert.notEqual(wrongSign, sources.complex_numbers);
  assert.throws(() => compile(module, sources.complex_algebra, { ...sources, complex_numbers: wrongSign }), /Expected/);
  const chosenRoot = sources.complex_polynomials.replace(
    "FieldExists(exists z : F, mulF(z, z) = a) {",
    "(exists z : F, mulF(z, z) = a) {");
  assert.notEqual(chosenRoot, sources.complex_polynomials);
  assert.throws(() => compile(module, chosenRoot, sources), /Expected/);
  const wrongDifference = sources.polynomial_difference.replace(
    "addF(monic_eval(F, one, addF, mulF, k, tail, r), mulF(x, previous(tail)))",
    "addF(monic_eval(F, one, addF, mulF, k, tail, r), mulF(r, previous(tail)))");
  assert.notEqual(wrongDifference, sources.polynomial_difference);
  assert.throws(() => compile(module, wrongDifference, sources), /Expected|Conversion types differ/);
});

test("complex inverses preserve constructive apartness and isolate excluded middle", () => {
  const truncation = ["lib_Trunc", "lib_trunc_intro", "lib_trunc_elim"];
  for (const name of ["ordered_squares", "complex_norm_coordinates", "complex_inverses", "classical_complex_inverses"]) {
    const c = compile(module, sources[name], sources);
    try {
      for (const o of c.outputs) {
        assert.ok(c.kernel.verify(o.proposition, o.binding), `${name}.${o.name}`);
        const dependencies = c.kernel.axiomsFor(o.binding);
        if (name === "classical_complex_inverses") {
          assert.ok(dependencies.includes("LEM"), o.name);
          assert.ok(dependencies.every(a => [...truncation, "lib_trunc_is_trunc", "LEM"].includes(a)), o.name);
        } else {
          assert.ok(dependencies.every(a => truncation.includes(a)), `${name}.${o.name}`);
        }
      }
      assert.ok(!c.kernel.bindings.has("AOC"), name);
      if (name !== "classical_complex_inverses") assert.ok(!c.kernel.bindings.has("LEM"), name);
      if (name === "complex_inverses") {
        assert.deepEqual(c.kernel.axiomsFor("complex_norm_multiplicative"), []);
        assert.deepEqual(c.kernel.axiomsFor("complex_apart_inverse").sort(), ["lib_Trunc", "lib_trunc_intro"]);
        assert.match(c.outputs.find(o => o.name === "complex_apart_inverse").type, /ComplexUnit/);
        assert.doesNotMatch(c.outputs.find(o => o.name === "complex_apart_inverse").type, /FieldExists/);
      }
    } finally { c.kernel.dispose(); }
  }
});

test("circle degree obstructs contraction without classical logic or choice", () => {
  for (const name of ["homotopy_paths", "circle_degree"]) {
    const c = compile(module, sources[name], sources);
    try {
      for (const o of c.outputs) {
        assert.ok(c.kernel.verify(o.proposition, o.binding), `${name}.${o.name}`);
        const axioms = c.kernel.axiomsFor(o.binding);
        assert.ok(axioms.every(a => ["lib_univalence", "lib_ua_elim"].includes(a)), o.name);
        if (name === "homotopy_paths") assert.deepEqual(axioms, [], o.name);
      }
      assert.ok(!c.kernel.bindings.has("LEM"));
      assert.ok(!c.kernel.bindings.has("AOC"));
      if (name === "circle_degree") {
        assert.deepEqual(c.kernel.axiomsFor("positive_degree_no_contractible_extension").sort(), ["lib_ua_elim", "lib_univalence"]);
        assert.match(c.outputs.find(o => o.name === "positive_degree_no_contractible_extension").type, /X : Type1/);
      }
    } finally { c.kernel.dispose(); }
  }
  const zeroDegree = sources.circle_degree.replace(
    "circle_map_from_loop(S1, base, positive_loops(n), x)",
    "circle_map_from_loop(S1, base, positive_loops(0), x)");
  assert.notEqual(zeroDegree, sources.circle_degree);
  assert.throws(() => compile(module, zeroDegree, sources), /Expected|Conversion types differ/);
});

test("dominant-term deformation avoids zero constructively and needs strict dominance", () => {
  const c = compile(module, sources.complex_deformation, sources);
  try {
    for (const o of c.outputs) {
      assert.ok(c.kernel.verify(o.proposition, o.binding), o.name);
      assert.ok(c.kernel.axiomsFor(o.binding).every(a => a === "lib_Trunc"), o.name);
    }
    assert.ok(!c.kernel.bindings.has("LEM"));
    assert.ok(!c.kernel.bindings.has("AOC"));
    assert.deepEqual(c.kernel.axiomsFor("complex_linear_deformation_nonzero"), ["lib_Trunc"]);
  } finally { c.kernel.dispose(); }
  const nonStrict = sources.complex_deformation.replace(
    "dominates : lt(complex_norm_squared(F, addF, mulF, error), complex_norm_squared(F, addF, mulF, z))",
    "dominates : FieldLe(F, lt, complex_norm_squared(F, addF, mulF, error), complex_norm_squared(F, addF, mulF, z))");
  assert.notEqual(nonStrict, sources.complex_deformation);
  assert.throws(() => compile(module, nonStrict, sources), /Expected|Conversion types differ/);
});

test("signed multiples and finite sums keep their constructive algebraic laws", () => {
  for (const name of ["integer_multiples", "finite_sums", "quadratic_identities", "ordered_bounds"]) {
    const c = compile(module, sources[name], sources);
    try {
      for (const o of c.outputs) {
        assert.ok(c.kernel.verify(o.proposition, o.binding), `${name}.${o.name}`);
        const axioms = c.kernel.axiomsFor(o.binding);
        if (name === "ordered_bounds") assert.ok(axioms.every(a => a === "lib_Trunc"), o.name);
        else assert.deepEqual(axioms, [], `${name}.${o.name}`);
      }
    } finally { c.kernel.dispose(); }
  }
  // Our negative(n) represents -(n+1), not -n. Losing this offset must fail.
  const wrongNegative = sources.integer_multiples.replace(
    "right n => natural_multiple(G, zero, addG, negG, negG(x), succ(n));",
    "right n => natural_multiple(G, zero, addG, negG, negG(x), n);");
  assert.notEqual(wrongNegative, sources.integer_multiples);
  assert.throws(() => compile(module, wrongNegative, sources), /Expected|Conversion types differ/);
});

test("homotopy periods satisfy the winding sum without collapsing nontrivial loops", () => {
  const allowed = new Set([
    "lib_Trunc", "lib_funext", "lib_trunc_elim", "lib_trunc_intro",
    "lib_trunc_is_trunc", "lib_ua_elim", "lib_univalence",
  ]);
  for (const [name, theorem] of [
    ["puncture_periods", "puncture_period_formula"],
    ["complex_periods", "complex_puncture_period_formula"],
    ["puncture_period_examples", "nontrivial_loop_with_zero_period"],
  ]) {
    const c = compile(module, sources[name], sources);
    try {
      assert.ok(c.outputs.some(o => o.name === theorem));
      for (const o of c.outputs) {
        assert.ok(c.kernel.verify(o.proposition, o.binding), `${name}.${o.name}`);
        assert.ok(c.kernel.axiomsFor(o.binding).every(a => allowed.has(a)), o.name);
      }
      assert.ok(!c.kernel.bindings.has("LEM"));
      assert.ok(!c.kernel.bindings.has("AOC"));
      // The analytic work is an explicit input, not a hidden integral axiom.
      if (name === "complex_periods") {
        const type = c.outputs.find(o => o.name === theorem).type;
        assert.match(type, /periodLaws/);
        assert.match(type, /localValues/);
        assert.match(type, /normalization/);
      }
    } finally { c.kernel.dispose(); }
  }
  // Ignoring winding makes the generator calculation false.
  const ignoredWinding = sources.puncture_periods.replace(
    "values(i), puncture_winding(n, i, p)", "values(i), zeroZ");
  assert.notEqual(ignoredWinding, sources.puncture_periods);
  assert.throws(() => compile(module, ignoredWinding, sources), /Expected|Conversion types differ/);
});

test("Cauchy limits and homotopy periods keep their constructive assumptions", () => {
  const allowed = new Set(["lib_Trunc", "lib_trunc_intro", "lib_trunc_elim"]);
  for (const name of ["complex_limits", "complex_limit_periods", "cauchy_ordered"]) {
    const c = compile(module, sources[name], sources);
    try {
      for (const o of c.outputs) {
        assert.ok(c.kernel.verify(o.proposition, o.binding), `${name}.${o.name}`);
        const dependencies = c.kernel.axiomsFor(o.binding);
        assert.ok(dependencies.every(a => allowed.has(a) ||
          (name === "cauchy_ordered" && ["lib_funext", "lib_trunc_is_trunc"].includes(a))), o.name);
      }
      assert.ok(!c.kernel.bindings.has("LEM"), name);
      assert.ok(!c.kernel.bindings.has("AOC"), name);
      if (name === "complex_limits") {
        assert.deepEqual(c.kernel.axiomsFor("complex_cauchy_complete"), []);
        assert.match(c.outputs.find(o => o.name === "complex_cauchy_complete").type, /complete : CauchyComplete/);
      }
      if (name === "complex_limit_periods") {
        const type = c.outputs.find(o => o.name === "complex_cauchy_approximation_period_laws").type;
        assert.match(type, /realEstimates : PeriodApproximationLaws/);
        assert.match(type, /imagEstimates : PeriodApproximationLaws/);
        assert.match(type, /LoopMapLaws/);
        assert.deepEqual(c.kernel.axiomsFor("half_sum_from_inverse_two"), []);
      }
    } finally { c.kernel.dispose(); }
  }
});

test("limit proofs reject an unhalved radius and a wrong limiting sum", () => {
  const unhalved = sources.ordered_halves.replace(
    "let half = fun (epsilon : F) => mulF(epsilon, reciprocal);",
    "let half = fun (epsilon : F) => epsilon;");
  assert.notEqual(unhalved, sources.ordered_halves);
  assert.throws(() => compile(module, unhalved, sources), /Expected|Conversion types differ/);
  const wrongSum = sources.limit_periods.replace(
    "period(append_path(X, point, point, point, p, q)) = addF(period(p), period(q))",
    "period(append_path(X, point, point, point, p, q)) = addF(period(p), period(p))");
  assert.notEqual(wrongSum, sources.limit_periods);
  assert.throws(() => compile(module, wrongSum, sources), /Expected|Conversion types differ/);
});

test("limits descend from representatives without choosing curves or finite-stage invariance", () => {
  const c = compile(module, sources.homotopy_limits, sources);
  try {
    for (const o of c.outputs) assert.ok(c.kernel.verify(o.proposition, o.binding), o.name);
    assert.deepEqual(c.kernel.axiomsFor("homotopy_limit_period").sort(),
      ["lib_Trunc", "lib_funext", "lib_trunc_elim", "lib_trunc_intro"]);
    assert.ok(!c.kernel.bindings.has("LEM"));
    assert.ok(!c.kernel.bindings.has("AOC"));
    const type = c.outputs.find(o => o.name === "homotopy_limit_period").type;
    assert.match(type, /C : Type1/);
    assert.match(type, /covered/);
    assert.match(type, /homotopyError/);
    assert.match(type, /FieldAsymptotic/);
    assert.match(type, /LoopMapLaws/);
  } finally { c.kernel.dispose(); }
  // Constancy on presentation fibers is essential to extracting a unique value.
  const inconsistent = sources.surjective_descent.replace(
    "consistent(a2, a, trans(same, sym(represents)))", "refl(value(a))");
  assert.notEqual(inconsistent, sources.surjective_descent);
  assert.throws(() => compile(module, inconsistent, sources), /Expected|Conversion types differ/);
});

test("finite contour sums compose and account for refinement errors constructively", () => {
  for (const name of ["complex_contour_sums", "sample_error_bounds"]) {
    const c = compile(module, sources[name], sources);
    try {
      for (const o of c.outputs) {
        assert.ok(c.kernel.verify(o.proposition, o.binding), `${name}.${o.name}`);
        const allowed = name === "sample_error_bounds" ? ["lib_Trunc"] : [];
        assert.ok(c.kernel.axiomsFor(o.binding).every(a => allowed.includes(a)), o.name);
      }
      assert.ok(!c.kernel.bindings.has("LEM"));
      assert.ok(!c.kernel.bindings.has("AOC"));
      if (name === "complex_contour_sums") {
        assert.ok(c.outputs.some(o => o.name === "complex_identity_backtrack_nonzero"));
        assert.match(c.outputs.find(o => o.name === "complex_contour_composes").type, /meets/);
        for (const theorem of ["sample_sum_telescopes", "contour_sum_add",
          "contour_edge_refinement", "contour_sum_change_tags", "identity_backtrack_sum"]) {
          assert.ok(c.kernel.bindings.has(theorem), theorem);
          assert.deepEqual(c.kernel.axiomsFor(theorem), []);
        }
      } else {
        assert.ok(c.outputs.some(o => o.name === "sample_sum_error_bound"));
      }
    } finally { c.kernel.dispose(); }
  }
});

test("finite contour sums reject false cancellation and reversed tag errors", () => {
  const cancelled = sources.contour_examples.replace(
    "backtrack_vertices(F, zero, one), backtrack_tags(F, zero, one)) = negF(one)",
    "backtrack_vertices(F, zero, one), backtrack_tags(F, zero, one)) = zero");
  assert.notEqual(cancelled, sources.contour_examples);
  assert.throws(() => compile(module, cancelled, sources), /Expected|Conversion types differ/);
  const reversed = sources.contour_refinement.replace(
    "coordinate_difference(F, addF, negF, f(oldTag), f(newTag))",
    "coordinate_difference(F, addF, negF, f(newTag), f(oldTag))");
  assert.notEqual(reversed, sources.contour_refinement);
  assert.throws(() => compile(module, reversed, sources), /Expected|Conversion types differ/);
});

test("finite error bounds retain positive slack for the empty sum", () => {
  const noSlack = sources.sample_error_bounds.replaceAll(
    /addF\((sample_sum\(C, F, zero, addF, radius, [nk], vertices, tags\)), epsilon\)/g,
    "$1");
  assert.notEqual(noSlack, sources.sample_error_bounds);
  assert.throws(() => compile(module, noSlack, sources), /Expected|Conversion types differ/);
});

test("constructive magnitude and variation estimates control contour tag errors", () => {
  for (const [name, theorem] of [
    ["sample_magnitude_bounds", "sample_weighted_sum_bound"],
    ["complex_magnitude", "complex_box_mul_rectangle"],
    ["contour_tag_limits", "contour_tag_errors_converge"],
  ]) {
    const c = compile(module, sources[name], sources);
    try {
      assert.ok(c.outputs.some(o => o.name === theorem));
      for (const o of c.outputs) {
        assert.ok(c.kernel.verify(o.proposition, o.binding), `${name}.${o.name}`);
        assert.ok(c.kernel.axiomsFor(o.binding).every(a => a === "lib_Trunc"), o.name);
      }
      assert.ok(!c.kernel.bindings.has("LEM"));
      assert.ok(!c.kernel.bindings.has("AOC"));
      if (name === "contour_tag_limits") {
        const type = c.outputs.find(o => o.name === theorem).type;
        assert.match(type, /vanishes : FieldConverges/);
        assert.match(type, /variation/);
        assert.match(type, /ContourTagBounds/);
        assert.match(c.outputs.find(o => o.name === "contour_tag_change_close").type, /small : lt/);
      }
    } finally { c.kernel.dispose(); }
  }
});

test("magnitude estimates reject one-sided bounds and loss of the variation factor", () => {
  // An upper bound alone cannot control magnitude (large negative values).
  const oneSided = sources.field_magnitude.replace(
    "FieldLe(F, lt, negF(x), radius);", "FieldLe(F, lt, x, radius);");
  assert.notEqual(oneSided, sources.field_magnitude);
  assert.throws(() => compile(module, oneSided, sources), /Expected|Conversion types differ/);
  const missingLength = sources.sample_magnitude_bounds.replace(
    "other(a, b, t))), n, vertices, tags), mulF(delta, length)) {",
    "other(a, b, t))), n, vertices, tags), delta) {");
  assert.notEqual(missingLength, sources.sample_magnitude_bounds);
  assert.throws(() => compile(module, missingLength, sources), /Expected|Conversion types differ/);
});

test("magnitude closeness needs a strict radius margin", () => {
  const closedMargin = sources.field_magnitude_close.replaceAll(
    "small : lt(radius, epsilon)", "small : FieldLe(F, lt, radius, epsilon)");
  assert.notEqual(closedMargin, sources.field_magnitude_close);
  assert.throws(() => compile(module, closedMargin, sources), /Expected|Conversion types differ/);
});

test("larger contour proofs check beyond the former million-instruction limit", () => {
  // Real mathematical imports exercise the raised limit without bypassing
  // kernel verification or allocating millions of artificial instructions.
  const source = "import contour_sums;\nimport sample_magnitude_bounds;\n" + sources.contour_tag_limits;
  const c = compile(module, source, sources);
  try {
    assert.ok(c.instructionCount > 1048576, c.instructionCount);
    assert.ok(c.instructionCount <= MAX_STEPS);
    for (const o of c.outputs) assert.ok(c.kernel.verify(o.proposition, o.binding), o.name);
  } finally { c.kernel.dispose(); }
});

test("vanishing sampled errors preserve the limit of complex contour sums", t => {
  const allowed = new Set(["lib_Trunc", "lib_trunc_intro", "lib_trunc_elim"]);
  for (const [name, theorem] of [
    ["complex_contour_tag_limits", "complex_contour_tag_independent_limit"],
    ["contour_tag_limits", "contour_tag_errors_from_vanishing_values"],
  ]) {
    const c = compile(module, sources[name], sources);
    try {
      assert.ok(c.outputs.some(o => o.name === theorem));
      for (const o of c.outputs) {
        assert.ok(c.kernel.verify(o.proposition, o.binding), `${name}.${o.name}`);
        assert.ok(c.kernel.axiomsFor(o.binding).every(a => allowed.has(a)), o.name);
      }
      assert.ok(!c.kernel.bindings.has("LEM"));
      assert.ok(!c.kernel.bindings.has("AOC"));
      const type = c.outputs.find(o => o.name === theorem).type;
      assert.match(type, /vanishes : FieldConverges\(F, zero, addF, lt, delta, zero\)/);
      assert.match(type, /nonnegativeLength/);
      assert.match(type, /variation/);
      if (name === "complex_contour_tag_limits") {
        assert.ok(c.kernel.stats().judgements > 500000, "exercises the raised judgment budget");
        assert.match(type, /oldConverges : ComplexConverges/);
        assert.ok(c.kernel.bindings.has("field_small_scaled_radius"));
        assert.ok(c.kernel.bindings.has("complex_contour_tag_error_variation_bound"));
      }
      t.diagnostic(`${name}: ${c.instructionCount.toLocaleString()} instructions; ${c.kernel.stats().judgements.toLocaleString()} judgments`);
    } finally { c.kernel.dispose(); }
  }
});

test("contour estimates retain the zero-length margin and imaginary variation", () => {
  const noMargin = sources.field_scale_limits.replace(
    "let denominator = addF(one, length);", "let denominator = length;");
  assert.notEqual(noMargin, sources.field_scale_limits);
  assert.throws(() => compile(module, noMargin, sources), /Expected|Conversion types differ/);
  const noImaginaryVariation = sources.complex_contour_bounds.replaceAll(
    "addF(realWeight(a, b, t), imagWeight(a, b, t))", "realWeight(a, b, t)");
  assert.notEqual(noImaginaryVariation, sources.complex_contour_bounds);
  assert.throws(() => compile(module, noImaginaryVariation, sources), /Expected|Conversion types differ/);
});

test("straight complex interval curves have constructive continuity, endpoints and zero avoidance", t => {
  const c = compile(module, sources.complex_curves, sources);
  try {
    const allowed = new Set(["lib_Trunc", "lib_trunc_intro"]);
    for (const output of c.outputs) {
      assert.ok(c.kernel.verify(output.proposition, output.binding), output.name);
      assert.ok(c.kernel.axiomsFor(output.binding).every(a => allowed.has(a)), output.name);
    }
    for (const name of ["complex_straight_curve_uniform", "complex_straight_curve_endpoints",
      "complex_interval_deformation_uniform", "complex_interval_deformation_avoids_zero"]) {
      assert.ok(c.outputs.some(o => o.name === name), name);
    }
    const uniform = c.outputs.find(o => o.name === "complex_straight_curve_uniform");
    assert.match(uniform.type, /FieldInverses/);
    assert.match(uniform.type, /FieldLattice/);
    assert.doesNotMatch(uniform.type, /uniform :|bounded :/);
    const avoidance = c.outputs.find(o => o.name === "complex_interval_deformation_avoids_zero");
    assert.match(avoidance.type, /dominates : lt/);
    assert.match(avoidance.type, /forall t : FieldUnitInterval/);
    assert.ok(!c.kernel.bindings.has("LEM"));
    assert.ok(!c.kernel.bindings.has("AOC"));
    t.diagnostic(`${c.instructionCount.toLocaleString()} instructions; ${c.kernel.stats().judgements.toLocaleString()} judgments`);
  } finally { c.kernel.dispose(); }
});

test("affine curves require the oriented parameter increment and both coordinate bounds", () => {
  const backwards = sources.field_affine.replaceAll("addF(negF(t), s)", "addF(negF(s), t)");
  assert.notEqual(backwards, sources.field_affine);
  assert.throws(() => compile(module, backwards, sources), /Expected|Conversion types differ/);
  const missingImaginaryBound = sources.complex_affine.replace(
    "maxF(maxF(complex_real(F, z), negF(complex_real(F, z))), maxF(complex_imag(F, z), negF(complex_imag(F, z))))",
    "maxF(complex_real(F, z), negF(complex_real(F, z)))");
  assert.notEqual(missingImaginaryBound, sources.complex_affine);
  assert.throws(() => compile(module, missingImaginaryBound, sources), /Expected|Conversion types differ/);
});

test("ordered samples of complex affine curves have uniformly bounded coordinate variation", t => {
  const c = compile(module, sources.complex_curve_variation, sources);
  try {
    for (const output of c.outputs) {
      assert.ok(c.kernel.verify(output.proposition, output.binding), output.name);
      assert.ok(c.kernel.axiomsFor(output.binding).every(a => a === "lib_Trunc"), output.name);
    }
    const result = c.outputs.find(o => o.name === "complex_interval_deformation_variation");
    assert.ok(result);
    assert.match(result.type, /ComplexCurveVariation/);
    assert.match(result.type, /FieldLattice/);
    assert.doesNotMatch(result.type, /FieldInverses|variation :|bounded :/);
    assert.ok(c.kernel.bindings.has("interval_weight_sum_bound"));
    assert.ok(c.kernel.bindings.has("interval_affine_increment_bounds"));
    assert.ok(!c.kernel.bindings.has("LEM"));
    assert.ok(!c.kernel.bindings.has("AOC"));
    t.diagnostic(`${c.instructionCount.toLocaleString()} instructions; ${c.kernel.stats().judgements.toLocaleString()} judgments`);
  } finally { c.kernel.dispose(); }
});

test("curve variation needs forward ordered parameters and includes imaginary variation", () => {
  const backwards = sources.affine_variation.replace(
    "FieldLe(F, lt, field_interval_coordinate(F, zero, one, lt, s), field_interval_coordinate(F, zero, one, lt, t))",
    "FieldLe(F, lt, field_interval_coordinate(F, zero, one, lt, t), field_interval_coordinate(F, zero, one, lt, s))");
  assert.notEqual(backwards, sources.affine_variation);
  assert.throws(() => compile(module, backwards, sources), /Expected|Conversion types differ/);
  const noImaginaryLength = sources.complex_curve_variation.replace(
    "addF(maxF(complex_real(F, error), negF(complex_real(F, error))), maxF(complex_imag(F, error), negF(complex_imag(F, error))))",
    "maxF(complex_real(F, error), negF(complex_real(F, error)))");
  assert.notEqual(noImaginaryLength, sources.complex_curve_variation);
  assert.throws(() => compile(module, noImaginaryLength, sources), /Expected|Conversion types differ/);
});

test("mapped affine contour limits use the proved geometric variation bound", t => {
  const c = compile(module, sources.curve_contour_limits, sources);
  try {
    const allowed = new Set(["lib_Trunc", "lib_trunc_intro", "lib_trunc_elim"]);
    for (const output of c.outputs) {
      assert.ok(c.kernel.verify(output.proposition, output.binding), output.name);
      assert.ok(c.kernel.axiomsFor(output.binding).every(a => allowed.has(a)), output.name);
    }
    const result = c.outputs.find(o => o.name === "affine_curve_contour_tag_independent_limit");
    assert.ok(result);
    assert.match(result.type, /oldConverges : ComplexConverges/);
    assert.match(result.type, /vanishes : FieldConverges/);
    assert.match(result.type, /IntervalOrderedSamples/);
    assert.match(result.type, /curve_contour_samples/);
    assert.doesNotMatch(result.type, /variation :|increments :|realWeight :|imagWeight :/);
    assert.ok(c.kernel.bindings.has("complex_interval_deformation_variation"));
    assert.ok(c.kernel.bindings.has("parameter_contour_sum_is_mapped"));
    assert.ok(!c.kernel.bindings.has("LEM"));
    assert.ok(!c.kernel.bindings.has("AOC"));
    t.diagnostic(`${c.instructionCount.toLocaleString()} instructions; ${c.kernel.stats().judgements.toLocaleString()} judgments`);
  } finally { c.kernel.dispose(); }
});

test("mapping contour samples preserves the integrand and the orientation of tag errors", () => {
  const c = compile(module, sources.sample_maps, sources);
  try {
    assert.ok(c.outputs.some(o => o.name === "map_sample_sum"));
    for (const output of c.outputs) {
      assert.ok(c.kernel.verify(output.proposition, output.binding), output.name);
      assert.deepEqual(c.kernel.axiomsFor(output.binding), []);
    }
  } finally { c.kernel.dispose(); }
  const wrongSign = sources.parameter_contours.replace(
    "curve(a), curve(b), values(oldTag), values(newTag)", "curve(a), curve(b), values(newTag), values(oldTag)");
  assert.notEqual(wrongSign, sources.parameter_contours);
  assert.throws(() => compile(module, wrongSign, sources), /Expected|Conversion types differ/);
  const identityIntegrand = sources.parameter_contours.replace(
    "contour_sum(F, zero, addF, mulF, negF, integrand, n, map_sample_vertices",
    "contour_sum(F, zero, addF, mulF, negF, (fun (x : F) => x), n, map_sample_vertices");
  assert.notEqual(identityIntegrand, sources.parameter_contours);
  assert.throws(() => compile(module, identityIntegrand, sources), /Expected|Conversion types differ/);
});
