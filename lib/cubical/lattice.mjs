// CCHM sections 3–4. Two distinct free distributive lattices in antichain DNF.
// A clause is a meet of generators; the outer array is their join.
// [] is false/zero, [[]] is true/one. Absorption removes supersets.
const subset = (a, b, budget) => a.every(x => {budget.tick();return b.includes(x);});
const literal = x => typeof x === "string" && /^[A-Za-z_][A-Za-z_0-9]*:[01]$/.test(x);
const MAX_CLAUSES = 4096, MAX_LITERALS = 256, MAX_WORK = 1000000;
const tooLarge = () => { throw Error("Cubical lattice term-size budget exceeded."); };
export function latticeBudget(checkDeadline = null, deadline = performance.now() + 1000) {
  let work = 0;
  return { tick() {
    if (++work > MAX_WORK) tooLarge();
    if ((work & 255) === 1) {
      checkDeadline?.();
      if (performance.now() > deadline)
        throw Error("Cubical lattice elapsed-work budget exceeded.");
    }
  } };
}
function canonical(clauses, disjointEndpoints, budget = latticeBudget()) {
  if (!Array.isArray(clauses)) throw new Error("Expected a lattice DNF.");
  if (clauses.length > MAX_CLAUSES) tooLarge();
  const normalized = [];
  clauses: for (const clause of clauses) {
    budget.tick();
    if (clause?.length > MAX_LITERALS) tooLarge();
    if (!Array.isArray(clause) || !clause.every(literal)) throw new Error("Malformed lattice generator.");
    const c = [...new Set(clause)].sort();
    if (disjointEndpoints && c.some(x => {budget.tick();return c.includes(x.slice(0, -1) + (x.endsWith("0") ? "1" : "0"));})) continue;
    for (const d of normalized) {budget.tick();if (subset(d, c, budget)) continue clauses;}
    for (let i = normalized.length - 1; i >= 0; i--) {
      budget.tick();
      if (subset(c, normalized[i], budget)) normalized.splice(i, 1);
    }
    normalized.push(c);
  }
  const keys = new Map(normalized.map(clause => [clause, JSON.stringify(clause)]));
  normalized.sort((a, b) => {budget.tick();return keys.get(a).localeCompare(keys.get(b));});
  return Object.freeze(normalized.map(Object.freeze));
}
const join = (a, b, face, budget) => {
  if (a.length + b.length > MAX_CLAUSES) tooLarge();
  return canonical([...a, ...b], face, budget);
};
const meet = (a, b, face, budget) => {
  if (a.length * b.length > MAX_CLAUSES) tooLarge();
  return canonical(a.flatMap(c => b.map(d => {
    budget.tick();
    if (c.length + d.length > MAX_LITERALS) tooLarge();
    return [...c, ...d];
  })), face, budget);
};
const empty = Object.freeze([]), full = Object.freeze([Object.freeze([])]);
function name(n) {
  if (typeof n !== "string" || !/^[A-Za-z_][A-Za-z_0-9]*$/.test(n)) throw new Error("Invalid dimension name.");
  return n;
}

// In interval DNF, i:1 means i and i:0 means its reversal, not an endpoint test.
export const interval = Object.freeze({
  zero: empty, one: full,
  variable: (n, budget = latticeBudget()) => canonical([[`${name(n)}:1`]], false, budget),
  normalize: (x, budget = latticeBudget()) => canonical(x, false, budget),
  join: (a, b, budget = latticeBudget()) => join(a, b, false, budget),
  meet: (a, b, budget = latticeBudget()) => meet(a, b, false, budget),
  reverse(a, budget = latticeBudget()) {
    a = canonical(a, false, budget);
    return a.reduce((acc, clause) => meet(acc,
      clause.reduce((sum, x) => join(sum, [[x.slice(0, -1) + (x.endsWith("0") ? "1" : "0")]], false, budget), empty), false, budget), full);
  },
  substitute(a, n, value, budget = latticeBudget()) {
    name(n); a = canonical(a, false, budget); value = canonical(value, false, budget);
    return a.reduce((sum, c) => join(sum, c.reduce((product, x) => {
      const v = x.slice(0, -2) === n ? (x.endsWith("1") ? value : interval.reverse(value, budget)) : [[x]];
      return meet(product, v, false, budget);
    }, full), false, budget), empty);
  },
  equal: (a, b) => {
    const budget = latticeBudget();
    return JSON.stringify(canonical(a, false, budget)) === JSON.stringify(canonical(b, false, budget));
  },
  names: a => {
    if (!Array.isArray(a) || a.length > MAX_CLAUSES) tooLarge();
    for (const clause of a) if (!Array.isArray(clause) || clause.length > MAX_LITERALS) tooLarge();
    return [...new Set(a.flat().map(x => x.slice(0, -2)))];
  },
});

// In face DNF, i:0 and i:1 assert endpoint equalities. They are disjoint.
export const face = Object.freeze({
  bottom: empty, top: full,
  normalize: (x, budget = latticeBudget()) => canonical(x, true, budget),
  join: (a, b, budget = latticeBudget()) => join(a, b, true, budget),
  meet: (a, b, budget = latticeBudget()) => meet(a, b, true, budget),
  endpoint(n, end) {
    if (end !== 0 && end !== 1) throw new Error("Expected endpoint 0 or 1.");
    return canonical([[`${name(n)}:${end}`]], true);
  },
  // For a DNF interval term: r=1 iff one monomial is entirely 1;
  // r=0 iff each monomial has a factor equal to 0.
  equalEndpoint(r, end, budget = latticeBudget()) {
    if (end !== 0 && end !== 1) throw new Error("Expected endpoint 0 or 1.");
    r = canonical(r, false, budget);
    if (end === 1) return canonical(r, true, budget);
    return r.reduce((acc, clause) => meet(acc,
      clause.reduce((sum, x) => join(sum, [[x.slice(0, -1) + (x.endsWith("0") ? "1" : "0")]], true, budget), empty), true, budget), full);
  },
  substitute(phi, n, r, budget = latticeBudget()) {
    name(n); r = canonical(r, false, budget);
    return canonical(phi, true, budget).reduce((sum, clause) => join(sum, clause.reduce((product, x) => meet(product,
      x.slice(0, -2) === n ? face.equalEndpoint(r, Number(x.at(-1)), budget) : [[x]], true, budget), full), true, budget), empty);
  },
  // Greatest face independent of n that entails phi. Endpoint cases do NOT
  // cover an interval: forall i. ((i=0) or (i=1)) is bottom, not top.
  forall(n,phi) {
    name(n);
    return canonical(phi,true).filter(clause=>clause.every(x=>x.slice(0,-2)!==n));
  },
  entails(phi, psi) {
    const budget = latticeBudget();
    phi = canonical(phi, true, budget); psi = canonical(psi, true, budget);
    return phi.every(c => psi.some(d => {budget.tick();return subset(d, c, budget);}));
  },
  equal: (a, b) => {
    const budget = latticeBudget();
    return JSON.stringify(canonical(a, true, budget)) === JSON.stringify(canonical(b, true, budget));
  },
});
