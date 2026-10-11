// Supported source variants avoid each case's original defect while keeping its
// independent clients. They establish that the acceptance predicate is
// reachable, without claiming to fix the original source. Every edit must
// apply, so a stale variant cannot silently keep part of the old source.
import assert from "node:assert/strict";

const replaced = (source, from, to) => {
  assert.equal(source.split(from).length - 1, 1, `supported variant must replace ${JSON.stringify(from)} once`);
  return source.replace(from, to);
};
const edited = (source, pattern, edit) => {
  assert.match(source, pattern, `supported variant must find ${pattern}`);
  return source.replace(pattern, edit);
};

// Nat results keep every branch distinct; all model references become Nat values.
export function natMotive(c) {
  c.source = edited(replaced(c.source, "import hlevels;", "import hlevels; import nat;"),
    /def value[^;]+(?:;[^}]+)*?};/, declaration => declaration
      .replace(": M :=", ": Nat :=").replace(/\bop\(/g, "succ(").replace(/\bc\b/g, "zero"))
    .replaceAll("S.op(S.op(S.c))", "succ(succ(zero))").replaceAll("S.op(S.c)", "succ(zero)").replaceAll("= S.c {", "= zero {");
  assert.doesNotMatch(c.source, /\bS\.(op|c)\b/, "every client must state a Nat result");
}
// The derived parameter no longer collides with the helper's free field.
export function renameParameter(c) {
  c.source = edited(c.source, /def kk\([^;]+;/, declaration => declaration.replace(/\bc\b/g, "z"));
}
// Two unrolled steps avoid the recursive-call defect for the finite witnesses.
export function nonrecursive(c) {
  c.source = replaced(c.source, "match n { zero => c; succ(k) => op(iter(k)); }",
    "match n { zero => c; succ(k) => match k { zero => op(c); succ(j) => op(op(c)); }; }");
}

export const supportedSources = {
  // The domain moves to the model's universe, which the generator supports;
  // a U1 model's Hom then lives in U2.
  G2: c => {
    c.source = replaced(replaced(c.source, "op(A : U0, x : A) : M", "op(A : U, x : A) : M"),
      "def level_u1(S : T(U1)) : U1", "def level_u1(S : T(U1)) : U2");
  },
  G4: natMotive,
  "G4-flat": natMotive,
  G9: c => {
    const scope = "law l(z : M) : k(z) = op(z, z);";
    c.source = replaced(c.source, c.observations.scope, scope);
    c.observations = {...c.observations, scope, label: "z"};
  },
  G11: renameParameter,
  "G11-grouped-dependent": renameParameter,
  "G11-inherited": renameParameter,
  "G11-initial": renameParameter,
  G12: nonrecursive,
  "G12-inherited": nonrecursive,
  "G12-initial": nonrecursive,
  "G12-shadowed": c => {
    c.source = replaced(c.source, "twice(iter : Nat -> M, n : Nat) : M := op(iter(n))", "twice(local : Nat -> M, n : Nat) : M := op(local(n))");
  },
};
