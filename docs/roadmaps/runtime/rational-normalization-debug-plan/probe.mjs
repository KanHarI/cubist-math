// Fixed-budget full-normalization probes for the rational normalization
// debugging plan beside this directory. Every query runs in a fresh checked
// program with a fixed budget and a long deadline, using main's library only:
// no binary_rationals import and no source overlays. Modes:
//   node probe.mjs normalize <name,...> [budget]   one query per name; graph metrics on success
//   node probe.mjs ladder <name> <budget,...>      the same name at rising budgets, stopping at success
//   node probe.mjs survey <name,...> [budget]      composition residue classification of a completed normal form
//   node probe.mjs canonical <name,...> [budget]   the normal form's decoding: its distinct parts up to bound names
// Names are the definitions of the two fixtures below; a query checks the
// whole fixture that defines its name. A query's ticks depend on the rest
// of its fixture by a few percent, its normal form not at all: compare ticks
// only between runs of one fixture, whose hash each record carries.
import { createHash } from "node:crypto";
import createCubical from "../../../../web/dist/cubical.mjs";
import { CubicalProgram } from "../../../../web/cubical-program.mjs";
import { sourceReader } from "../../../../tools/module-sources.mjs";
import { assertFreshBuild, sourceHash } from "../../../../tools/build-stamp.mjs";
import { sharedNormalDigest } from "../../../../tools/evaluation-baseline.mjs";
import { sources } from "../../historical/evaluation-demand-marks/probe-sources.mjs";

assertFreshBuild();
// `binary`: the binary rationals without #283, the demand marks' report's
// fixture, with this plan's further queries. `two_thirds` is the literal as
// #283's parser builds it, with a compact zero decision on the denominator.
const binary = `${sources.rational}
def q_inv_open := q_inv{{U0}}(binary_integers, bint_decide, bint_mul_nonzero, bint_zero_ne_one);

computable def wide : BQ := match bint_decide_zero(bint_of_nat(18446744073709551615)) return BQ {
    left same => binary_rationals.zero;
    right nonzero => class((
      bint_of_nat(340282366920938463463374607431768211455), bint_of_nat(18446744073709551615), nonzero
    ));
  };

computable def wide_inverse : BQ := q_inv{{U0}}(
  binary_integers, bint_decide, bint_mul_nonzero, bint_zero_ne_one, binary_rationals.neg(wide)
);

// The retained annotation and open-operation costs.
def relation := SameRatio{{U0}}(binary_integers, bint_decide, bint_mul_nonzero, bint_zero_ne_one);

def field_one := binary_rationals.one;

def multiplication := bint_mul;

def addition := bint_add;

def negation := bint_neg;

// The certificate path of a negative integer equality decision.
def setness := prop_type_is_set(U0);

def rel_open := related_to(
  U0, BNat and BNat, BIntSameDifference, bint_same_difference_props, bint_same_difference_sym,
  bint_same_difference_trans, (2, 0)
);

def eff_open := quotient_effective(
  U0, BNat and BNat, BIntSameDifference, bint_same_difference_props, bint_same_difference_refl,
  bint_same_difference_sym, bint_same_difference_trans, (2, 0), (0, 0)
);

def decision := bint_decide(bint_of_nat(2), bint_zero);

def nat_decision := bnat_decide(2, 0);

def zero_decision := bint_decide_zero(bint_of_nat(2));

// Lemmas on the setness path, open in their arguments.
def l_path_into := fun (A, P : U0, h : IsProp(U0, P)) => path_into_prop_is_prop(U0, A, P, h);

def l_equiv_into := fun (A, P : U0, h : IsProp(U0, P)) => equiv_into_prop_is_prop(U0, A, P, h);

def l_glue_eta := fun (A, B : U0, p : A = B) => glue_path_idtoequiv(U0, A, B, p);

def l_idtoequiv := fun (A, B : U0, p : A = B) => idtoequiv(U0, A, B, p);

def l_prop_path := fun (x, y : Prop(U0), f : x.1 -> y.1, g : y.1 -> x.1) => prop_path(U0, x, y, f, g);

def l_prop_ext := fun (P, Q : U0, hP : IsProp(U0, P), hQ : IsProp(U0, Q), f : P -> Q, g : Q -> P) =>
  prop_ext(U0, P, Q, hP, hQ, f, g);

def l_is_prop_is_prop := fun (X : U0) => is_prop_is_prop(U0, X);

def l_prop_is_set := fun (X : U0) => prop_is_set(U1, IsProp(U0, X), is_prop_is_prop(U0, X));

def l_retract0 := retract_has_level(U1, unat.(0));

def l_sigma0 := sigma_has_level(U1, unat.(0));

def l_pathp := fun (x, y : Prop(U0), p : x.1 = y.1) => pathp_has_level(
  U1, unat.(0), U0, fun (X : U0) => IsProp(U0, X),
  fun (X : U0) => prop_is_set(U1, IsProp(U0, X), is_prop_is_prop(U0, X)), x.1, x.2, y.1, p, y.2
);

// Lemmas on the quotient multiplication path, open in their arguments.
def m_left := fun (p, s, q : BNat and BNat, r : BIntSameDifference(p, s)) =>
  difference_mul_pairs_left{{U0}}(bnat_semiring, bnat_decide, bnat_add_cancel, p, s, q, r);

def m_comm := fun (p, q : BNat and BNat) =>
  difference_mul_pairs_comm{{U0}}(bnat_semiring, bnat_decide, bnat_add_cancel, p, q);

def m_pairs := fun (p, q : BNat and BNat) =>
  difference_mul_pairs{{U0}}(bnat_semiring, bnat_decide, bnat_add_cancel, p, q);

def m_path := fun (p, q : BNat and BNat, r : BIntSameDifference(p, q)) =>
  difference_path{{U0}}(bnat_semiring, bnat_decide, bnat_add_cancel, p, q, r);

def m_set := difference_is_set{{U0}}(bnat_semiring, bnat_decide, bnat_add_cancel);

def m_add_left := fun (p, s, q : BNat and BNat, r : BIntSameDifference(p, s)) =>
  difference_add_pairs_left{{U0}}(bnat_semiring, bnat_decide, bnat_add_cancel, p, s, q, r);
`;
// `unary`: the unary compatibility rationals and integers, over UNat, which
// were main's public ones until NUM2's default switch.
const unary = `import unary_rationals;
import unary_integers;
use unat;

def q_two_thirds := unary_rationals.(2/3);

def q_half := unary_rationals.(0.5);

def q_one := unary_rationals.one;

// A literal's nonzero certificate, open in the equation it refutes.
def q_nonzero_open := uq_succ_nonzero(2);

def q_effective_open := quotient_effective(
  U0, UNat and UNat, UIntSameDifference, uint_same_difference_props, uint_same_difference_refl,
  uint_same_difference_sym, uint_same_difference_trans, (succ(2), 0), (0, 0)
);

def z_decision := uint_decide(uint(2, 0), uint_zero);

// The additive group and the operations and laws it carries.
def z_additive := unary_integers.additive_;

def z_add := unary_integers.add;

def z_zero_add := unary_integers.zero_add;

def z_neg_add := unary_integers.neg_add;

def z_add_comm := unary_integers.add_comm;

def z_add_assoc := unary_integers.add_assoc;
`;
const fixtures = { binary, unary };
const sha256 = text => createHash("sha256").update(text).digest("hex");
const fixtureOf = name => {
  const found = Object.keys(fixtures).filter(key => new RegExp(`^(computable )?def ${name} `, "m").test(fixtures[key]));
  if (found.length !== 1) throw new Error(`${name} is defined in ${found.length} fixtures`);
  return found[0];
};
const [mode = "normalize", namesText = "small_inverse", budgetsText] = process.argv.slice(2);
const names = namesText.split(",");
const budgets = (budgetsText ?? "100000000").split(",").map(BigInt);
const deadlineMs = 600000;
const module = await createCubical();

async function fresh(name) {
  const program = new CubicalProgram(module, sourceReader(), { collectReferences: false });
  const checked = await program.check(fixtures[fixtureOf(name)], "probe");
  if (!checked.complete) throw new Error(JSON.stringify(checked.gaps.map(g => [g.name, g.code, g.reason])));
  const expression = program.checker.checkSyntax({ tag: "DefRef", name: `probe__${name}` }, null, new Map(), new Map()).expression;
  return { program, kernel: program.kernel, expression };
}

function measure(kernel, expression, steps) {
  kernel.stepBudget = steps;
  kernel.maxQuerySteps = steps;
  kernel.setStepBudget(steps);
  kernel.setDeadline(deadlineMs);
  const before = { ticks: kernel.work().querySteps, arena: kernel.arena() };
  const started = performance.now();
  let outcome, result = 0;
  try {
    result = kernel.normalize(expression);
    outcome = { status: "normalized" };
  } catch (error) {
    if (!["budget", "deadline", "resource"].includes(error.kind)) throw error;
    outcome = { status: "limited", kind: error.kind, message: error.message };
  }
  const after = { ticks: kernel.work().querySteps, arena: kernel.arena() };
  return { result, record: { ...outcome, queryBudget: String(steps), deadlineMs,
    querySteps: after.ticks - before.ticks, allocatedNodes: after.arena.nodes - before.arena.nodes,
    arenaBytesAfter: after.arena.bytes, elapsedMs: Math.round(performance.now() - started) } };
}

// Reachable handles including annotations, preserving exact sharing, with a
// kind tally; the same bounded traversal as tools/transport-normalization-probe.mjs.
function graph(kernel, root, visitBound = 60000000, ms = 300000) {
  const pending = [[root, false]], depth = new Map(), kinds = new Map(), deadline = performance.now() + ms;
  let visits = 0;
  while (pending.length) {
    if (++visits > visitBound || (visits % 1024 === 0 && performance.now() >= deadline))
      return { error: "graph inspection exceeded its independent bound", nodesSoFar: depth.size };
    const [id, done] = pending.pop();
    if (!id || depth.has(id)) continue;
    const node = kernel.node(id);
    if (done) {
      depth.set(id, 1 + Math.max(0, ...node.children.map(c => depth.get(c) ?? 0)));
      kinds.set(node.kind, (kinds.get(node.kind) ?? 0) + 1);
    } else {
      pending.push([id, true]);
      for (const child of node.children) if (child && !depth.has(child)) pending.push([child, false]);
    }
  }
  return { nodes: depth.size, depth: depth.get(root),
    kinds: Object.fromEntries([...kinds].sort((a, b) => b[1] - a[1]).slice(0, 12)) };
}

// For each Comp, Trans and HComp in a completed normal form: does its family
// mention its own dimension (shadowing ignored, so "constant" is a lower
// bound), is its system empty, and what are the family, face and value heads?
// A family headed by a declared sort is named by its sort, and the value heads
// are also counted by family, since a data sort's composition is stuck by its
// base or tubes and a higher sort's by its family. A value or tube term is
// read by the root of its application spine, so that a constructor applied
// counts as a constructor; where the base is one, the first tube term that is
// none is what blocks.
function survey(kernel, root, syntax) {
  const rootKind = id => {
    let node = kernel.node(id);
    while (["App", "Fst", "Snd", "PApp", "LApp"].includes(node.kind)) node = kernel.node(node.children[0]);
    return node.kind;
  };
  const formulaMemo = new Map(), termMemo = new Map();
  const formulaMentions = (fid, dim) => {
    const key = `${fid}:${dim}`;
    if (!formulaMemo.has(key)) {
      const bit = 1n << BigInt(dim);
      formulaMemo.set(key, kernel.inspectFormula(fid).clauses.some(([pos, neg]) => (pos & bit) !== 0n || (neg & bit) !== 0n));
    }
    return formulaMemo.get(key);
  };
  const mentions = (id, dim) => {
    const key = `${id}:${dim}`;
    if (termMemo.has(key)) return termMemo.get(key);
    const stack = [id], seen = new Set();
    let hit = false;
    while (stack.length && !hit) {
      const t = stack.pop();
      if (!t || seen.has(t)) continue;
      seen.add(t);
      const node = kernel.node(t);
      if ((node.kind === "PApp" || node.kind === "Tube" || node.kind === "GlueSystem") && node.payload && formulaMentions(node.payload, dim)) hit = true;
      else for (const c of node.children) if (c) stack.push(c);
    }
    termMemo.set(key, hit);
    return hit;
  };
  const faceShape = tubeId => {
    const tube = kernel.node(tubeId);
    if (!tube.payload) return "none";
    const face = kernel.inspectFormula(tube.payload);
    if (face.clauses.length === 0) return "bottom";
    return face.clauses.length === 1 && face.clauses[0][0] === 0n && face.clauses[0][1] === 0n ? "top" : "other";
  };
  const count = (table, key) => { table[key] = (table[key] ?? 0) + 1; };
  const tally = {};
  const pending = [root], seen = new Set();
  while (pending.length) {
    const id = pending.pop();
    if (!id || seen.has(id)) continue;
    seen.add(id);
    const node = kernel.node(id);
    if (node.kind === "Comp" || node.kind === "Trans" || node.kind === "HComp") {
      const row = tally[node.kind] ??= { total: 0, constantFamily: 0, emptySystem: 0, constantAndEmpty: 0,
        familyHeads: {}, faces: {}, valueHeads: {}, valueHeadsByFamily: {}, baseRootsByFamily: {}, blockingTubesByFamily: {} };
      const family = kernel.node(node.children[0]);
      const familyKey = family.kind === "Sort" ? `Sort ${syntax.signatureRecord(family.payload).name}` : family.kind;
      const constant = !mentions(node.children[0], node.payload), empty = !node.children[1];
      row.total++;
      if (constant) row.constantFamily++;
      if (empty) row.emptySystem++;
      if (constant && empty) row.constantAndEmpty++;
      count(row.familyHeads, familyKey);
      if (node.kind === "Trans") count(row.faces, faceShape(node.children[1]));
      count(row.valueHeads, kernel.node(node.children[2]).kind);
      count(row.valueHeadsByFamily[familyKey] ??= {}, kernel.node(node.children[2]).kind);
      const baseRoot = rootKind(node.children[2]);
      count(row.baseRootsByFamily[familyKey] ??= {}, baseRoot);
      if (baseRoot === "Con" && node.kind !== "Trans") {
        let blocking = "none";
        for (let tube = node.children[1]; tube; tube = kernel.node(tube).children[1]) {
          const kind = rootKind(kernel.node(tube).children[0]);
          if (kind !== "Con") { blocking = kind; break; }
        }
        count(row.blockingTubesByFamily[familyKey] ??= {}, blocking);
      }
    }
    for (const c of node.children) if (c) pending.push(c);
  }
  return { reachable: seen.size, tally };
}

for (const name of names) {
  for (const steps of mode === "ladder" ? budgets : [budgets[0]]) {
    const { program, kernel, expression } = await fresh(name);
    let record;
    try {
      const measured = measure(kernel, expression, steps), fixture = fixtureOf(name);
      record = { case: name, mode, ...measured.record, kernelSourceHash: sourceHash("kernel"), fixture, fixtureSha256: sha256(fixtures[fixture]) };
      if (measured.result && mode === "survey") Object.assign(record, survey(kernel, measured.result, program.checker.syntax));
      else if (measured.result) record.normal = graph(kernel, measured.result);
      // Decoded as the REPL reads it: annotations decoding drops are not counted.
      if (measured.result && mode === "canonical") {
        const { objects, distinct } = sharedNormalDigest(program.checker.syntax.decode(measured.result, program.checker.dimensions));
        record.decoding = { objects, distinct };
      }
      console.log(JSON.stringify(record));
    } finally {
      program.dispose();
    }
    if (record.status === "normalized") break;
  }
}
