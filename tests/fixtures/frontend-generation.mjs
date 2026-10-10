// Sources are independent clients, not snapshots of generated syntax. Keep
// expected failures here until the responsible implementation slice lands.
export const baseline = "00d4ecce016f7e18d13eedeced07dc098a2277cb";
export const expectedFailures = new Set(["G5", "G9"]);
export const gaps = {
  G1: {
    phase: "FG1", contract: "a duplicate declaration preserves the first binding and its clients",
    source: `def N : Unit := tt;
inductive N : U0 { c; }
def original : Unit := N;
def independent : Unit := tt;`,
    clients: ["original", "independent"],
  },
  G2: {
    phase: "FG3", contract: "fixed argument domains contribute to generated universes",
    source: `import hlevels;
theory T(U < UU0) { M : set U; op(A : U0, x : A) : M; }
def identity(S : T(U0)) : T.Hom(S, S) := T.Hom.id(S);
def computation(S : T(U0), x : S.M) :
  T.Hom.compose(identity(S), identity(S)).map(x) = x { rfl; }
def iso(S : T(U0)) : T.Iso(S, S) := T.Iso.id(S);`,
    clients: ["T.Hom", "identity", "computation", "iso"],
  },
  G3: {
    phase: "FG2", contract: "unsupported law-dependent transport leaves a usable theory and no partial Hom family",
    source: `import hlevels;
theory T(U < UU0) { M : set U; c : M; law l : c = c; op(p : l = l) : M; }
def usable(S : T(U0)) : S.M := S.op(refl(S.l));
def unsupported(S : T(U0)) := T.Hom.id(S);`,
    clients: ["T", "T.make", "T.op", "usable"],
    absentFamilies: ["T.Hom", "T.Iso"], refusedClients: ["unsupported"],
  },
  G4: {
    phase: "FG4", contract: "nested matches retain checked carrier evidence",
    source: `import hlevels;
inductive Bit : set U0 { off; yes; }
inductive Bits : set U0 { nil; cons(b : Bit, rest : Bits); }
theory T(U < UU0) { M : set U; c : M;
  def value(n : Bits) : M := match n { nil => c; cons(off, rest) => c; cons(yes, rest) => c; };
}
def computation(S : T(U0)) : S.value(cons(yes, nil)) = S.c { rfl; }`,
    clients: ["T.value", "computation"],
  },
  G5: {
    phase: "FG5", contract: "unused-binder advice preserves named arguments and generated interfaces",
    source: `import hlevels;
theory T(U < UU0) { M : set U; op : forall x, y : M. M; }
def identity(S : T(U0)) := T.Hom.id(S);
def named(S : T(U0), a : S.M) : S.M := S.op(x := a, y := a);
initial N : T(U0);`,
    clients: ["identity", "named", "N", "N.model", "N.fold"],
  },
  G6: {
    phase: "FG1", contract: "a child reports the failed parent once without repeating its root error",
    source: `import hlevels;
theory P(U < UU0) { M : set U; e : M; law bad : e = Undefined; }
theory C(U < UU0) extends P { law again : e = e; }
def independent : Unit := tt;`,
    clients: ["independent"],
  },
  G8: {
    phase: "FG4", contract: "a wildcard mismatch retains its endpoints and written body range",
    source: `import hlevels;
inductive T : set U0 { t0; t1; seg : t0 = t1; }
def h(x : T) : T := match x { t0 => t0; _ => t1; };`,
    diagnostic: {code: "E606", found: "t1 = t1", expected: "t0 = t1", token: "t1"},
  },
  G9: {
    phase: "FG5", contract: "freshened law binders and every use retain written labels and definition targets",
    source: `import hlevels;
theory T(U < UU0) { M : set U; c : M; op(x, y : M) : M;
  def k(x : M) : M := op(x, c);
  law l(c : M) : k(c) = op(c, c);
}
def meaning(S : T(U0), x : S.M) : S.op(x, S.c) = S.op(x, x) := S.l(x);`,
    clients: ["meaning"],
    observations: {scope: "law l(c : M) : k(c) = op(c, c);", label: "c", sites: 4},
  },
  G10: {
    phase: "FG2/FG5", contract: "a capture refusal points to the conflicting binder or helper call",
    source: `import hlevels; import nat;
theory T(U < UU0) { M : set U; c : M;
  def k(n : Nat) : M := c;
  law l(n : Nat) : (match n return M { zero => c; succ(c) => k(c); }) = c;
}`,
    diagnostic: {code: "E871", conflict: "succ(c) => k(c)"},
  },
  G11: {
    phase: "FG2", contract: "complete declaration telescopes protect helper fields from caller parameters",
    source: `import hlevels;
theory T(U < UU0) { M : set U; c : M; op(x, y : M) : M;
  def k(x : M) : M := op(x, c);
  def kk(c : M) : M := k(c);
}
def intended(S : T(U0), x : S.M) : S.kk(x) = S.op(x, S.c) := refl(S.op(x, S.c));
def captured(S : T(U0), x : S.M) : S.kk(x) = S.op(x, x) := refl(S.op(x, x));`,
    clients: ["intended"], refusedClients: ["captured"],
  },
  G12: {
    phase: "FG2/FG4", contract: "ordinary calls to earlier recursive values check and compute",
    source: `import hlevels; import nat;
theory T(U < UU0) { M : set U; c : M; op(x : M) : M;
  def iter(n : Nat) : M := match n { zero => c; succ(k) => op(iter(k)); };
  def twice(n : Nat) : M := op(iter(n));
}
def computation(S : T(U0)) : S.twice(zero) = S.op(S.c) { rfl; }`,
    clients: ["T.iter", "T.twice", "computation"],
  },
};

// Existing protection is named, not copied; these tests remain in the normal
// npm test run. G7 is historical and needs controlled failure injection in FG1.
export const historicalCoverage = {
  H1: ["references.test.mjs", "declaration identities survive every syntax transformation independently of spelling"],
  H2: ["theory-resolution.test.mjs", "initial and free models retain imported global types and law constants"],
  H3: ["theory-resolution.test.mjs", "family indices carry captured syntax through generated homomorphisms and isomorphisms"],
  H4: ["theory-hygiene.test.mjs", "theory capture uses opened fields before globals and retains them across imports and selections"],
  H5: ["theory-hygiene.test.mjs", "inlining preserves a helper's free fields under a caller's binders"],
};
export const passingCoverage = [
  ["theory-hygiene.test.mjs", "generated evidence links nowhere and written compound headers link once"],
  ["theory-hygiene.test.mjs", "freshened parameters and operation arguments keep their public names in diagnostics and inspection"],
  ["theory-hygiene.test.mjs", "substitution considers enclosing binders before refusing a fixed pattern capture"],
  ["theory-hygiene.test.mjs", "generated recursive calls retain their declaration under same-named parameters and patterns"],
  ["theory-hygiene.test.mjs", "catch-all path clauses respect recursive boundaries and require coherence"],
];

// The same independent equations exercise helper chains, a shared parameter
// domain followed by a dependent domain, inheritance, and generated clients.
export const captureVariants = [
  {name: "helper chain with grouped/dependent parameters", extra: "def chain(x : M) : M := k(x);", params: "c, d : M, p : c = c", body: "chain(c)", theory: "T", args: "x, x, refl(x)"},
  {name: "inherited helper chain", extra: "def chain(x : M) : M := k(x);", params: "c : M", body: "chain(c)", theory: "Child", args: "x"},
  {name: "initial-model client", extra: "", params: "c : M", body: "k(c)", theory: "N", args: "x"},
];
export function captureSource(variant) {
  const generated = variant.theory === "N";
  const source = `import hlevels;
theory T(U < UU0) { M : set U; c : M; op(x, y : M) : M;
  def k(x : M) : M := op(x, c);
  ${variant.extra}
  def kk(${variant.params}) : M := ${variant.body};
}
`;
  const setup = variant.theory === "Child" ? "theory Child(U < UU0) extends T {}\n"
    : generated ? "initial N : T(U0);\n" : "";
  const binders = generated ? "x : N" : `S : ${variant.theory}(U0), x : S.M`;
  const model = generated ? "N.model" : "S", op = generated ? "N.op" : "S.op", c = generated ? "N.c" : "S.c";
  return source + setup + `def intended(${binders}) : ${model}.kk(${variant.args}) = ${op}(x, ${c}) := refl(${op}(x, ${c}));
def captured(${binders}) : ${model}.kk(${variant.args}) = ${op}(x, x) := refl(${op}(x, x));`;
}
