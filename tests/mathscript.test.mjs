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
