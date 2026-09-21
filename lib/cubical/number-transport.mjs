// Native factorial migration helpers. These build ordinary cubical terms from
// checked source definitions; every registered result is checked again in C.
// The production half-adjoint Equiv representation is not reused as a Glue
// witness: its two inverse laws construct a contractible-fiber equivalence.
import { T } from "./core.mjs";
import { interval as I, face as F } from "./lattice.mjs";
import { equiv, equivalenceFromInverse, univalencePath, univalenceTransportBeta } from "./equivalence.mjs";

export function numberEquivalence(checker, name, A, B, forward, inverse, eta, epsilon) {
  const equivalence = checker.define(`${name}_equiv`,
    equivalenceFromInverse(A, B, forward, inverse, eta, epsilon), equiv(A, B));
  const path = checker.define(`${name}_path`, univalencePath(A, B, equivalence),
    T.path("i", T.universe(0), A, B));
  // Prove the computation law with a variable argument once, before applying
  // it to a large arithmetic expression. The shared checked body stays folded.
  const x = T.variable("argument");
  const betaType = T.pi("argument", A, T.path("i", B,
    T.comp("move", T.at(path, I.variable("move")), [], x), T.app(forward, x)));
  const beta = checker.define(`${name}_beta`, checker.ascribe(T.lam("argument", A,
    univalenceTransportBeta(A, B, equivalence, x)), betaType), betaType);
  return { A, B, forward, equivalence, path, beta };
}

export function transportNumberEquality(checker, name, equivalence, proof) {
  const source = checker.nf(checker.infer(proof).type);
  if (source.tag !== "Path") throw new Error("Number transport requires an equality proof.");
  const move = term => T.comp("move", T.at(equivalence.path, I.variable("move")), [], term);
  const term = T.line("proof", equivalence.B, move(T.at(proof, I.variable("proof"))));
  const type = T.path("proof", equivalence.B, move(source.left), move(source.right));
  return checker.define(name, term, type);
}

// These helpers only build paths. Final registration checks matching endpoints.
const reverse = (A, p) => T.line("reverse", A, T.at(p, I.reverse(I.variable("reverse"))));
const join = (A, p, q, left) => T.line("join", A, T.comp("along", A, [
  { face: F.endpoint("join", 0), term: left },
  { face: F.endpoint("join", 1), term: T.at(q, I.variable("along")) },
], T.at(p, I.variable("join"))));

export function mapNumberEqualityThroughUnivalence(checker, name, e, proof) {
  const source = checker.nf(checker.infer(proof).type);
  if (source.tag !== "Path") throw new Error("Number transport requires an equality proof.");
  const moved = transportNumberEquality(checker, `${name}_transported`, e, proof);
  const movedType = checker.nf(checker.infer(moved).type);
  const left = T.app(e.forward, source.left), right = T.app(e.forward, source.right);
  const beta = (suffix, x, transported, mapped) => checker.define(`${name}_${suffix}`,
    T.app(e.beta, x), T.path("i", e.B, transported, mapped));
  const betaLeft = beta("beta_left", source.left, movedType.left, left);
  const betaRight = beta("beta_right", source.right, movedType.right, right);
  const term = join(e.B, reverse(e.B, betaLeft), join(e.B, moved, betaRight, movedType.left), left);
  const type = T.path("i", e.B, left, right);
  return checker.define(name, checker.ascribe(term, type), type);
}

export function factorialThroughUnivalence(checker, name, e, proof, compatibility) {
  const mapped = mapNumberEqualityThroughUnivalence(checker, `${name}_mapped`, e, proof);
  const mappedType = checker.nf(checker.infer(mapped).type);
  // Compatibility runs from the mapped factorial to the original target one.
  const law = checker.nf(checker.infer(compatibility).type);
  if (law.tag !== "Path") throw new Error("Factorial compatibility requires an equality proof.");
  const type = T.path("i", e.B, law.right, mappedType.right);
  const term = join(e.B, reverse(e.B, compatibility), mapped, law.right);
  return checker.define(name, checker.ascribe(term, type), type);
}
