// Differential checking of the instruction driver against the term checker.
// The term checker's conversion is the reference: whatever it accepts, the
// driver should derive, and whatever it refuses, the driver must refuse. A
// seeded generator poses problems where eta and computation meet: a type, a
// neutral term of it, and two terms made from it by random expansions that
// preserve definitional equality (beta, pair eta, Glue eta with pieces on a
// face, type-level beta, and a large shared graph in an annotation), or one
// made from another neutral term. Each problem is a composition with a
// constant tube, which checks only if the tube agrees with the base.
//
//   node tools/differential-driver.mjs [--seeds=N] [--from=S] [--verbose]
import { existsSync, realpathSync } from "node:fs";
import { fileURLToPath } from "node:url";
import { T } from "../lib/cubical/core.mjs";
import { face as F, interval as I } from "../lib/cubical/lattice.mjs";
import { identityEquivalence } from "../lib/cubical/equivalence.mjs";
import { sourceText } from "../web/cubical-source-text.mjs";

// A small seeded generator (mulberry32): the same seed, the same problem.
export function random(seed) {
  let a = seed >>> 0;
  const next = () => {
    a = (a + 0x6D2B79F5) >>> 0;
    let t = a;
    t = Math.imul(t ^ (t >>> 15), t | 1);
    t ^= t + Math.imul(t ^ (t >>> 7), t | 61);
    return ((t ^ (t >>> 14)) >>> 0) / 4294967296;
  };
  return { next, below: n => Math.floor(next() * n), chance: p => next() < p,
    pick: items => items[Math.floor(next() * items.length)] };
}

const equivalence = identityEquivalence(T.unit);
const U0 = T.universe(0);
// A type equal to a base type only by a beta step: (λ X. X)(A).
const redex = type => T.app(T.lam("X", U0, T.variable("X")), type);

// The types problems range over. Each knows its neutral terms in the
// context, how to write an equal variant of itself, and which expansions it
// admits. A Glue type over a face depends on the dimension i.
const types = {
  nat: { term: T.nat, neutral: ["n", "n2"] },
  sigma: { term: T.sigma("s", T.nat, T.nat), neutral: ["u", "u2"] },
  glueNat: { term: T.glueType(T.nat, []), neutral: ["g", "g2"], base: "nat" },
  glueSigma: { term: T.glueType(T.sigma("s", T.nat, T.nat), []), neutral: ["h", "h2"], base: "sigma" },
  glueNested: { term: T.glueType(T.glueType(T.nat, []), []), neutral: ["w", "w2"], base: "glueNat" },
};
const faceType = (dimension, face) => T.glueType(T.unit, [{ face: F.endpoint(dimension, face), type: T.unit, equiv: equivalence }]);

// A type equal to `name`'s, written differently where the generator chooses.
function variant(r, name) {
  switch (name) {
  case "nat": return r.chance(0.3) ? redex(T.nat) : T.nat;
  case "sigma": return T.sigma("s", variant(r, "nat"), variant(r, "nat"));
  case "glueNat": return T.glueType(variant(r, "nat"), []);
  case "glueSigma": return T.glueType(variant(r, "sigma"), []);
  case "glueNested": return T.glueType(variant(r, "glueNat"), []);
  case "face": return T.glueType(r.chance(0.3) ? redex(T.unit) : T.unit,
    [{ face: F.endpoint("i", 0), type: T.unit, equiv: equivalence }]);
  default: throw new Error(`No type ${name}.`);
  }
}

let fresh = 0;
// A term equal to `term`, of type `name`, by up to `depth` random expansions.
function expand(r, term, name, depth) {
  if (depth <= 0 || r.chance(0.25)) return term;
  const inner = () => expand(r, term, name, depth - 1);
  const choices = ["beta"];
  if (name === "sigma") choices.push("pair", "pair");
  if (types[name]?.base) choices.push("glue", "glue");
  if (name === "face") choices.push("glueFace", "glueFace");
  switch (r.pick(choices)) {
  case "beta": {
    const z = `z${fresh++}`;
    return T.app(T.lam(z, variant(r, name), T.variable(z)), inner());
  }
  case "pair": return T.pair(variant(r, "sigma"), T.first(inner()), T.second(inner()));
  case "glue": {
    // glue [] (unglue g) is g; the base, at the Glue type's base type, is
    // expanded in turn: a pair eta, a nested Glue eta, a beta.
    const base = types[name].base;
    return T.glue(variant(r, name), expand(r, T.unglue(types[name].term, inner()), base, depth - 1), []);
  }
  case "glueFace": {
    // glue [i = 0 ↦ t] (unglue b) is b, when t is b at i = 0: here b at
    // i = 0 is p @ 0, which is point by p's type.
    const piece = r.pick([T.point, T.at(T.variable("p"), I.zero), T.app(T.lam(`z${fresh++}`, T.unit, T.variable(`z${fresh - 1}`)), T.point)]);
    return T.glue(variant(r, "face"), T.unglue(faceType("i", 0), inner()), [{ face: F.endpoint("i", 0), term: piece }]);
  }
  }
  return term;
}

// The context every problem shares, with a large shared graph in p's type
// when `shared` holds: r(n + 1) = f(r(n))(r(n)) over x : Unit.
function context(shared) {
  let graph = T.variable("x");
  for (let n = 0; n < 30; n++) graph = T.app(T.app(T.variable("f"), graph), graph);
  const end = shared ? T.glue(T.glueType(T.unit, []), graph, []) : T.variable("b1");
  const entries = [["x", T.unit], ["f", T.pi("a", T.unit, T.pi("b", T.unit, T.unit))],
    ["b1", T.glueType(T.unit, [{ face: F.bottom, type: T.unit, equiv: equivalence }])]];
  for (const [name, type] of Object.entries(types)) for (const variable of type.neutral) entries.push([variable, type.term]);
  const along = T.path("j", faceType("j", 0), T.point, end);
  entries.push(["p", along], ["q", along]);
  return entries;
}

// A problem: a composition over a type whose constant tube is `left` and
// whose base is `right`, which checks exactly when the two agree.
export function problem(seed) {
  const r = random(seed);
  fresh = 0;
  const name = r.pick([...Object.keys(types), "face", "face"]);
  const equal = r.chance(0.8), shared = r.chance(0.3), depth = 1 + r.below(4);
  const type = name === "face" ? faceType("i", 0) : types[name].term;
  const neutral = name === "face" ? [T.at(T.variable("p"), I.variable("i")), T.at(T.variable("q"), I.variable("i"))]
    : types[name].neutral.map(variable => T.variable(variable));
  const left = expand(r, neutral[0], name, depth);
  const right = expand(r, equal ? neutral[0] : neutral[1], name, depth);
  const composite = T.comp("k", type, [{ face: F.endpoint("m", 0), term: left }], right);
  return { seed, name, equal, shared, type, left, right, composite, context: context(shared),
    dimensions: new Map([["i", 0], ["m", 1]]) };
}

// Each checker's verdict on a problem: true, or the error it gave.
export function verdicts(program, p) {
  const attempt = check => { try { check(); return true; } catch (error) { return error; } };
  return {
    reference: attempt(() => program.checker.syntax.check(p.composite, p.type, p.context, p.dimensions)),
    driver: attempt(() => program.checker.checkView(p.composite, p.type, p.context, p.dimensions)),
  };
}

// What a disagreement means, or null when the two agree as they should.
export function disagreement(p, v) {
  const reference = v.reference === true, driver = v.driver === true;
  if (p.equal && !reference) return "the reference refuses an equal pair: the generator's construction is wrong";
  if (p.equal && !driver) return "the driver refuses what the reference accepts";
  if (!p.equal && reference) return "the reference accepts different terms";
  if (!p.equal && driver) return "the driver accepts different terms";
  return null;
}

const shown = term => { const text = sourceText(term, undefined, 400); return text.length > 240 ? `${text.slice(0, 239)}…` : text; };
export const describe = p => `seed ${p.seed} (${p.name}${p.equal ? "" : ", different"}${p.shared ? ", shared graph" : ""}): `
  + `${shown(p.left)}  vs  ${shown(p.right)}`;

// Run as a command, by any path to this file.
const invoked = () => { try { return realpathSync(process.argv[1]) === fileURLToPath(import.meta.url); } catch { return false; } };
if (invoked()) {
  // A run that checked fewer problems than asked must not report success, so
  // an argument this tool does not take, or a count that is not one, stops it.
  const args = process.argv.slice(2), usage = "Usage: node tools/differential-driver.mjs [--seeds=N] [--from=S] [--verbose]";
  const stop = message => { process.stderr.write(`${message}\n${usage}\n`); process.exit(2); };
  const unknown = args.find(arg => !/^--(seeds|from)=|^--verbose$/.test(arg));
  if (unknown !== undefined) stop(`Unknown argument "${unknown}".`);
  const integer = (name, fallback, least) => {
    const text = args.findLast(arg => arg.startsWith(`--${name}=`))?.slice(name.length + 3);
    const value = text === undefined ? fallback : /^\d+$/.test(text) ? Number(text) : NaN;
    if (!Number.isSafeInteger(value) || value < least) stop(`--${name} takes a whole number of at least ${least}, not ${text}.`);
    return value;
  };
  // Seeds are 32-bit (random): beyond, two seeds would pose the same problem.
  const count = integer("seeds", 200, 1), from = integer("from", 1, 0), verbose = args.includes("--verbose");
  if (from + count - 1 > 0xFFFFFFFF) stop(`Seeds run up to ${0xFFFFFFFF}.`);
  // The build stamp, where this tree has one (tools/build-stamp.mjs).
  const stamp = new URL("./build-stamp.mjs", import.meta.url);
  if (existsSync(stamp)) (await import(stamp)).assertFreshBuild();
  const { default: createCubical } = await import("../web/dist/cubical.mjs");
  const { CubicalProgram } = await import("../web/cubical-program.mjs");
  const program = new CubicalProgram(await createCubical(), async () => { throw new Error("No modules."); });
  await program.check("def unit_point : Unit := tt;\n", "differential");
  const found = new Map();
  for (let seed = from; seed < from + count; seed++) {
    const p = problem(seed), v = verdicts(program, p), reason = disagreement(p, v);
    if (verbose) process.stdout.write(`${describe(p)}  ->  ${reason ?? "agree"}\n`);
    if (!reason) continue;
    found.set(reason, [...(found.get(reason) ?? []), p]);
    const detail = [v.reference, v.driver].map(verdict => verdict === true ? "accepted" : String(verdict.message).slice(0, 160));
    process.stdout.write(`${reason}\n  ${describe(p)}\n  reference: ${detail[0]}\n  driver: ${detail[1]}\n`);
  }
  process.stdout.write(`${count} problems from seed ${from}: ${[...found.values()].flat().length} disagreements.\n`);
  program.dispose();
  process.exitCode = found.size ? 1 : 0;
}
