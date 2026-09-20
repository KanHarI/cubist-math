// Generate the native library proof of univalence's operations from ONE axiom.
// Every line emitted to C is replayed through the public kernel first.
import { readFile, writeFile } from "node:fs/promises";
import assert from "node:assert/strict";
import createKernel from "../../web/dist/kernel.mjs";
import { Builder } from "../../web/mathscript/builder.mjs";
import { paths } from "./paths.mjs";

const module = await createKernel();
const b = new Builder(module, { loadLibrary: false, allowAxioms: true,
  optimizations: { normalForms: true, instructions: true } });
// Only the constructive prefix is needed. This also works after regeneration,
// when the file already contains the new single-axiom development.
const library = JSON.parse(await readFile(new URL("../../web/proofs/homotopy.thth.json", import.meta.url)));
for (const step of library.steps) {
  b.k.apply(step);
  if (step.name === "lib_AreEquiv") break;
}
const start = b.k.steps.length;
// This proof is closed over its two input definitions; create its own contexts.
b.indexedContextSteps = start;
const op = (...args) => b.emit(...args), app = (...args) => b.app(...args);
const norm = x => b.norm(x), eq = (...args) => b.eq(...args), refl = x => b.refl(x);
const { J, cat } = paths(b, null);
const ap = (A, B, f, x, y, p) => J(A,
  (x, y) => eq(B, app(f, x), app(f, y)), x => refl(app(f, x)), x, y, p);
const sigma = (A, B) => { const x = b.fresh(A); return op("SigmaForm", [A, B(x.v)], [x.c]); };
function fst(A, B, pair) {
  const x = b.fresh(A), y = b.fresh(B(x.v));
  return norm(op("SigmaElim", [A, x.v, pair], [null, x.c, y.c]));
}
function snd(A, B, pair) {
  const x = b.fresh(A), y = b.fresh(B(x.v)), z = b.fresh(sigma(A, B));
  const motive = B(fst(A, B, z.v));
  const t = b.fresh(A);
  const xy = op("SigmaIntro", [x.v, B(t.v), y.v], [t.c]);
  const atPair = op("UnHigh", [op("BetaReducePointed", [op("HighExp", [
    op("PiElim", [op("PiIntro", [z.A, motive], [z.c]), xy])])])]);
  return norm(op("SigmaElim", [motive, b.coerce(y.v, atPair), pair], [z.c, x.c, y.c]));
}
const Universe = op("UIntroOmega");
const equiv = (U, A, B) => sigma(b.arrow(A, B), f => app("lib_isEquiv", U, A, B, f));
const forward = (U, A, B, e) => fst(b.arrow(A, B), f => app("lib_isEquiv", U, A, B, f), e);
const idtoequiv = (U, A, B) => app("lib_AreEquiv", U, A, B);
// The same half-adjoint IsEquiv as the library, expanded here because its
// carrier includes the universe itself. No successor of a universe variable
// needs to be added to the kernel or the language.
function isEquivData(A, B, f) {
  const inverse = b.arrow(B, A);
  const eta = g => b.pi(A, x => eq(A, app(g, app(f, x)), x));
  const epsilon = g => b.pi(B, y => eq(B, app(f, app(g, y)), y));
  const coherence = (g, eta, epsilon) => b.pi(A, x => eq(
    eq(B, app(f, app(g, app(f, x))), app(f, x)),
    ap(A, B, f, app(g, app(f, x)), x, app(eta, x)), app(epsilon, app(f, x))));
  const rest = g => sigma(eta(g), h => sigma(epsilon(g), k => coherence(g, h, k)));
  return { type: sigma(inverse, rest), inverse, eta, epsilon, coherence, rest };
}
const axiomType = b.pi(Universe, U => b.pi(U, A => b.pi(U, B =>
  isEquivData(eq(U, A, B), equiv(U, A, B), idtoequiv(U, A, B)).type)));
const univalence = op("Axiom", [axiomType], [], null, "standard_univalence");
function data(U, A, B) {
  const P = eq(U, A, B), E = equiv(U, A, B), f = idtoequiv(U, A, B);
  const d = isEquivData(P, E, f), witness = app(univalence, U, A, B);
  const g = fst(d.inverse, d.rest, witness);
  const rest = snd(d.inverse, d.rest, witness);
  const tail = h => sigma(d.epsilon(g), k => d.coherence(g, h, k));
  const eta = fst(d.eta(g), tail, rest), tailValue = snd(d.eta(g), tail, rest);
  const epsilon = fst(d.epsilon(g), k => d.coherence(g, eta, k), tailValue);
  return { P, E, f, g, eta, epsilon };
}
const ua = b.named(b.lam(Universe, U => b.lam(U, A => b.lam(U, B => data(U, A, B).g))), "derived_ua");
// Transport and the underlying function of idtoequiv agree, by path induction.
function transport(U, A, B, p, x) {
  // Derive universe transport by J so the native library trace also replays
  // in the independent Rust kernel, which has no Transport convenience rule.
  return app(J(U, (A, B) => b.arrow(A, B), A => b.lam(A, x => x), A, B, p), x);
}
const beta = b.named(b.lam(Universe, U => b.lam(U, A => b.lam(U, B => {
  const d = data(U, A, B);
  return b.lam(d.E, e => b.lam(A, x => {
    const p = app(d.g, e);
    const transportAgrees = J(U, (A, B, p) => b.pi(A, x => eq(B,
      transport(U, A, B, p, x), app(forward(U, A, B, app(idtoequiv(U, A, B), p)), x))),
      A => b.lam(A, x => refl(x)), A, B, p);
    const evaluate = b.lam(d.E, e => app(forward(U, A, B, e), x));
    const ep = ap(d.E, B, evaluate, app(d.f, p), e, app(d.epsilon, e));
    return cat(B, transport(U, A, B, p, x), app(evaluate, app(d.f, p)),
      app(evaluate, e), app(transportAgrees, x), ep);
  }));
}))), "derived_ua_beta");
const eta = b.named(b.lam(Universe, U => b.lam(U, A => b.lam(U, B => data(U, A, B).eta))), "derived_ua_eta");
for (const name of [ua, beta, eta]) assert.deepEqual(b.k.axiomsFor(name), [univalence]);
const emitted = b.k.steps.slice(start), byName = new Map(emitted.map(s => [s.name, s]));
const needed = new Set();
function need(name) {
  if (needed.has(name) || !byName.has(name)) return;
  needed.add(name);
  const s = byName.get(name);
  [...s.args, ...s.free, s.context].forEach(need);
}
[univalence, ua, beta, eta].forEach(need);
const steps = emitted.filter(s => needed.has(s.name));
assert.equal(steps.filter(s => s.op === "Axiom").length, 1);
// Native code receives the two already-checked constructive definitions.
const external = { lib_isEquiv: "is_equiv", lib_AreEquiv: "id_to_equiv" };
const names = new Set(steps.map(s => s.name));
const ref = name => {
  if (!name) return "0";
  if (names.has(name)) return name;
  if (external[name]) return external[name];
  throw new Error(`Unexpected proof dependency: ${name}`);
};
const array = xs => xs.length ? `(tt_id[]){${xs.map(ref).join(", ")}}` : "NULL";
const lines = ["/* Generated by tools/proofs/univalence.mjs; all steps kernel-checked. */",
  "static proof_tuple standard_univalence_proofs(tt_engine *e, tt_id is_equiv, tt_id id_to_equiv) {",
  ...steps.map(s => `    tt_id ${s.name} = proof_step(e, TT_${s.op}, ${array(s.args)}, ${s.args.length}, ${ref(s.context)}, ${array(s.free)}, ${s.free.length}, __FILE__, __LINE__);`),
  `    return (proof_tuple){{${univalence}, ${ua}, ${beta}, ${eta}}};`, "}", ""];
await writeFile(new URL("../../src/univalence_generated.inc", import.meta.url), lines.join("\n"));
b.k.dispose();
console.log(`Generated single-axiom univalence and its derived laws (${steps.length} checked steps).`);
