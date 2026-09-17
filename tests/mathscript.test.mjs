import test from "node:test";
import assert from "node:assert/strict";
import { readFile } from "node:fs/promises";
import { spawnSync } from "node:child_process";
import createKernel from "../web/dist/kernel.mjs";
import { compile } from "../web/mathscript/compiler.mjs";
import { Kernel } from "../web/kernel.mjs";
import { sourceModules } from "../web/mathscript/modules.mjs";
import catalogue from "../web/proofs/catalogue.mjs";
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
