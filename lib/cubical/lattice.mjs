// CCHM sections 3–4. Two distinct free distributive lattices in antichain DNF.
// A clause is a meet of generators; the outer array is their join.
// [] is false/zero, [[]] is true/one. Absorption removes supersets.
const subset = (a, b) => a.every(x => b.includes(x));
const literal = x => typeof x === "string" && /^[A-Za-z_][A-Za-z_0-9]*:[01]$/.test(x);
function canonical(clauses, disjointEndpoints) {
  if (!Array.isArray(clauses)) throw new Error("Expected a lattice DNF.");
  const normalized = [];
  for (const clause of clauses) {
    if (!Array.isArray(clause) || !clause.every(literal)) throw new Error("Malformed lattice generator.");
    const c = [...new Set(clause)].sort();
    if (disjointEndpoints && c.some(x => c.includes(x.slice(0, -1) + (x.endsWith("0") ? "1" : "0")))) continue;
    if (normalized.some(d => subset(d, c))) continue;
    for (let i = normalized.length - 1; i >= 0; i--) if (subset(c, normalized[i])) normalized.splice(i, 1);
    normalized.push(c);
  }
  normalized.sort((a, b) => JSON.stringify(a).localeCompare(JSON.stringify(b)));
  return Object.freeze(normalized.map(Object.freeze));
}
const join = (a, b, face) => canonical([...a, ...b], face);
const meet = (a, b, face) => canonical(a.flatMap(c => b.map(d => [...c, ...d])), face);
const empty = Object.freeze([]), full = Object.freeze([Object.freeze([])]);
function name(n) {
  if (typeof n !== "string" || !/^[A-Za-z_][A-Za-z_0-9]*$/.test(n)) throw new Error("Invalid dimension name.");
  return n;
}

// In interval DNF, i:1 means i and i:0 means its reversal, not an endpoint test.
export const interval = Object.freeze({
  zero: empty, one: full,
  variable: n => canonical([[`${name(n)}:1`]], false),
  normalize: x => canonical(x, false),
  join: (a, b) => join(a, b, false),
  meet: (a, b) => meet(a, b, false),
  reverse(a) {
    return a.reduce((acc, clause) => meet(acc,
      clause.reduce((sum, x) => join(sum, [[x.slice(0, -1) + (x.endsWith("0") ? "1" : "0")]], false), empty), false), full);
  },
  substitute(a, n, value) {
    name(n); value = canonical(value, false);
    return a.reduce((sum, c) => join(sum, c.reduce((product, x) => {
      const v = x.slice(0, -2) === n ? (x.endsWith("1") ? value : interval.reverse(value)) : [[x]];
      return meet(product, v, false);
    }, full), false), empty);
  },
  equal: (a, b) => JSON.stringify(canonical(a, false)) === JSON.stringify(canonical(b, false)),
  names: a => [...new Set(a.flat().map(x => x.slice(0, -2)))],
});

// In face DNF, i:0 and i:1 assert endpoint equalities. They are disjoint.
export const face = Object.freeze({
  bottom: empty, top: full,
  normalize: x => canonical(x, true),
  join: (a, b) => join(a, b, true),
  meet: (a, b) => meet(a, b, true),
  endpoint(n, end) {
    if (end !== 0 && end !== 1) throw new Error("Expected endpoint 0 or 1.");
    return canonical([[`${name(n)}:${end}`]], true);
  },
  // For a DNF interval term: r=1 iff one monomial is entirely 1;
  // r=0 iff each monomial has a factor equal to 0.
  equalEndpoint(r, end) {
    if (end !== 0 && end !== 1) throw new Error("Expected endpoint 0 or 1.");
    r = canonical(r, false);
    if (end === 1) return canonical(r, true);
    return r.reduce((acc, clause) => meet(acc,
      clause.reduce((sum, x) => join(sum, [[x.slice(0, -1) + (x.endsWith("0") ? "1" : "0")]], true), empty), true), full);
  },
  substitute(phi, n, r) {
    name(n); r = canonical(r, false);
    return canonical(phi, true).reduce((sum, clause) => join(sum, clause.reduce((product, x) => meet(product,
      x.slice(0, -2) === n ? face.equalEndpoint(r, Number(x.at(-1))) : [[x]], true), full), true), empty);
  },
  // Greatest face independent of n that entails phi. Endpoint cases do NOT
  // cover an interval: forall i. ((i=0) or (i=1)) is bottom, not top.
  forall(n,phi) {
    name(n);
    return canonical(phi,true).filter(clause=>clause.every(x=>x.slice(0,-2)!==n));
  },
  entails(phi, psi) {
    phi = canonical(phi, true); psi = canonical(psi, true);
    return phi.every(c => psi.some(d => subset(d, c)));
  },
  equal: (a, b) => JSON.stringify(canonical(a, true)) === JSON.stringify(canonical(b, true)),
});
