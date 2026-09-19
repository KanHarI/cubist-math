import test from "node:test";
import assert from "node:assert/strict";
import createKernel from "../web/dist/kernel.mjs";
import { Kernel } from "../web/kernel.mjs";
import { compile } from "../web/mathscript/compiler.mjs";

const module = await createKernel();
const configurations = Array.from({ length: 4 }, (_, mask) => ({
  normalForms: !!(mask & 1),
  instructions: !!(mask & 2),
}));

// Replay into the same kernel so agreement is checked by the kernel itself,
// rather than by comparing display strings or IDs from different engines.
function replayInto(kernel, compiled, prefix) {
  const renamed = name => name == null ? null : prefix + name;
  for (const step of compiled.kernel.steps) {
    kernel.apply({
      ...step,
      name: renamed(step.name),
      args: step.args.map(renamed),
      free: step.free.map(renamed),
      context: renamed(step.context),
    });
  }
  return compiled.outputs.map(output => ({
    name: output.name,
    proposition: renamed(output.proposition),
    binding: renamed(output.binding),
  }));
}

const fixtures = {
  "dependent functions and higher universes": `
    def identity(A : U1, x : A) = x;
    def naturalType = identity(U0, Nat);
    theorem identity_path(A : U1, x : A) : identity(A, x) = x {
      exact refl(x);
    }
    theorem independent_binders(A : U0, x : A, y : A) : y = y {
      exact refl(y);
    }
  `,
  "opaque definitions and explicit unfolding": `
    opaque def Box = Nat;
    opaque def successor(n : Nat) = succ(n);
    def boxed : Box { exact 2; }
    def folded = successor(1);
    def opened = unfold(folded);
    theorem converted : successor(1) = 2 { exact refl(2); }
  `,
  "opaque quantified propositions": `
    opaque def ReflexiveNaturals = forall n : Nat, n = n;
    theorem all_reflexive : ReflexiveNaturals {
      intro n;
      exact refl(n);
    }
  `,
  "axiom dependencies through erased arguments": `
    axiom chosen : Nat;
    def erase(n : Nat) = 0;
    def dependent = erase(chosen);
    def independent = 0;
    theorem plain : 0 = 0 { exact refl(0); }
    theorem erased : dependent = 0 { exact refl(dependent); }
  `,
  "recursive functions": `
    def copy(n : Nat) = induction n as k return Nat {
      zero => 0;
      succ previous => succ(previous);
    };
    theorem computes : copy(3) = 3 { exact refl(3); }
  `,
};

for (const [label, source] of Object.entries(fixtures)) {
  test(`compiler optimizations preserve checked statements: ${label}`, () => {
    const shared = new Kernel(module, true);
    let baseline, dependencies;
    try {
      for (const [index, optimizations] of configurations.entries()) {
        const compiled = compile(module, source, {}, { optimizations });
        try {
          assert.deepEqual(compiled.optimizations, optimizations);
          const replayed = replayInto(shared, compiled, `mode${index}_`);
          const axioms = compiled.outputs.map(output => compiled.kernel.axiomsFor(output.binding).sort());
          if (label === "axiom dependencies through erased arguments") {
            assert.deepEqual(compiled.kernel.axiomsFor("independent"), []);
            assert.deepEqual(compiled.kernel.axiomsFor("plain"), []);
            assert.deepEqual(compiled.kernel.axiomsFor("dependent"), ["chosen"]);
          }
          if (!baseline) { baseline = replayed; dependencies = axioms; }
          assert.deepEqual(axioms, dependencies);
          assert.deepEqual(replayed.map(output => output.name), baseline.map(output => output.name));
          for (const [i, output] of replayed.entries()) {
            assert.ok(shared.verify(output.proposition, output.binding), output.name);
            assert.ok(shared.verify(baseline[i].proposition, output.binding), `baseline statement: ${output.name}`);
            assert.ok(shared.verify(output.proposition, baseline[i].binding), `optimized statement: ${output.name}`);
          }
        } finally { compiled.kernel.dispose(); }
      }
    } finally { shared.dispose(); }
  });
}

test("each compiler optimization configuration still rejects invalid proofs", () => {
  const invalid = [
    "def wrong : Nat { exact tt; }",
    "opaque def successor(n : Nat) = succ(n); theorem wrong : successor(1) = 3 { exact refl(2); }",
    "theorem wrong(A : U0, x : A, y : A) : x = y { exact refl(x); }",
    `theorem wrong(n : Nat) : n = 0 {
      exact induction n as k return (k = 0) {
        zero => refl(0);
        succ previous => refl(0);
      };
    }`,
  ];
  for (const optimizations of configurations)
    for (const source of invalid)
      assert.throws(() => compile(module, source, {}, { optimizations }), /Expected|Conversion types differ|rejected/);
});
