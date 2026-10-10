// Sources and desired behavior are independent clients. The historical
// provenance at 00d4ecce is documented in frontend-generation.md.
const definitions = {
  G1: {
    phase: "FG1", contract: "a duplicate declaration preserves the first binding and its clients",
    source: `def N : Unit := tt;
inductive N : U0 { c; }
def original : Unit := N;
def independent : Unit := tt;`,
    clients: ["original", "independent"],
    originalType: "Unit", symbol: "N", invariantClients: ["independent"],
  },
  G2: {
    phase: "FG3", contract: "fixed argument domains contribute to generated universes",
    source: `import hlevels;
theory T(U < UU0) { M : set U; op(A : U0, x : A) : M; }
def identity(S : T(U0)) : T.Hom(S, S) := T.Hom.id(S);
def computation(S : T(U0), x : S.M) :
  T.Hom.compose(identity(S), identity(S)).map(x) = x { rfl; }
def iso(S : T(U0)) : T.Iso(S, S) := T.Iso.id(S);
def identity_u1(S : T(U1)) : T.Hom(S, S) := T.Hom.id(S);
def computation_u1(S : T(U1), x : S.M) :
  T.Hom.compose(identity_u1(S), identity_u1(S)).map(x) = x { rfl; }
def iso_u1(S : T(U1)) : T.Iso(S, S) := T.Iso.id(S);`,
    clients: ["T.Hom", "identity", "computation", "iso", "identity_u1", "computation_u1", "iso_u1"],
  },
  G3: {
    phase: "FG2", contract: "unsupported law-dependent transport leaves a usable theory and no partial Hom family",
    source: `import hlevels;
theory T(U < UU0) { M : set U; c : M; law l : c = c; op(p : l = l) : M; }
def usable(S : T(U0)) : S.M := S.op(refl(S.l));
def unsupported(S : T(U0)) := T.Hom.id(S);`,
    clients: ["T", "T.make", "T.op", "usable"],
    absentFamilies: ["T.Hom", "T.Iso"], refusedClients: ["unsupported"],
    refusalWords: ["op", "p", "l"],
  },
  G4: {
    phase: "FG4", contract: "derived matches retain checked carrier evidence (nested clauses)",
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
    phase: "FG5", contract: "grouped-binder advice preserves supported calls and generated interfaces",
    source: `import hlevels;
theory T(U < UU0) { M : set U; op : forall x, y : M. M; }
def identity(S : T(U0)) := T.Hom.id(S);
def applied(S : T(U0), a : S.M) : S.M := S.op(a, a);
initial N : T(U0);`,
    clients: ["identity", "applied", "N", "N.model", "N.fold"],
    rewrite: {from: "forall x, y : M. M", to: "M -> M -> M"},
  },
  G6: {
    phase: "FG1", contract: "a child reports the failed parent once without repeating its root error",
    source: `import hlevels;
theory P(U < UU0) { M : set U; e : M; law bad : e = Undefined; }
theory C(U < UU0) extends P { law again : e = e; }
def independent : Unit := tt;`,
    clients: ["independent"], parent: "P", child: "C", cause: "Undefined",
  },
  G8: {
    phase: "FG4", contract: "a wildcard mismatch retains its endpoints and written body range",
    source: `import hlevels;
inductive T : set U0 { t0; t1; seg : t0 = t1; }
def h(x : T) : T := match x { t0 => t0; _ => t1; };`,
    diagnostic: {name: "h", code: "E606", found: "t1 = t1", expected: "t0 = t1",
      scope: ":= match x { t0 => t0; _ => t1; };", token: "t1"},
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
    diagnostic: {name: "T", code: "E871", conflict: "succ(c) => k(c)", binder: "c", call: "k(c)"},
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
    phase: "FG2/FG4/FG5", contract: "ordinary calls to earlier recursive values check and compute",
    source: `import hlevels; import nat;
theory T(U < UU0) { M : set U; c : M; op(x : M) : M;
  def iter(n : Nat) : M := match n { zero => c; succ(k) => op(iter(k)); };
  def twice(n : Nat) : M := op(iter(n));
}
def computation(S : T(U0)) : S.twice(zero) = S.op(S.c) { rfl; }`,
    clients: ["T.iter", "T.twice", "computation"],
  },
  "G12-range": {
    phase: "FG5", contract: "recursive type-unfolding refusals cover the responsible original call",
    source: `import hlevels; import nat;
theory T(U < UU0) { M : set U; c : M; op(x : M) : M;
  def iter(n : Nat) : M := match n { zero => c; succ(k) => op(iter(k)); };
  law nope(n : Nat) : iter(n) = c;
}`,
    diagnostic: {name: "T", code: "E845", scope: "law nope(n : Nat) : iter(n) = c;", token: "iter(n)"},
  },
};

const collisionVariants = [
  {
    id: "G1-initial", contract: "an initial-model duplicate preserves the first definition",
    source: `import hlevels; import algebra;
def N : Unit := tt;
initial N : Monoid(U0);
def original : Unit := N;
def independent : Unit := tt;`,
  },
  {
    id: "G1-reverse", contract: "a definition duplicate preserves the first inductive",
    source: `inductive N : U0 { c; }
def N : Unit := tt;
def original : U0 := N;
def constructor : N := c;
def independent : Unit := tt;`,
    originalType: "U0", clients: ["original", "constructor", "independent"],
  },
  {
    id: "G1-same-kind", contract: "a same-kind duplicate preserves the first definition",
    source: `def N : Unit := tt;
def N : U0 := Unit;
def original : Unit := N;
def independent : Unit := tt;`,
  },
];

const matchVariants = [
  {
    id: "G4-flat", contract: "derived matches retain checked carrier evidence (flat clauses)",
    source: `import hlevels;
inductive Bit : set U0 { off; yes; }
inductive Bits : set U0 { nil; cons(b : Bit, rest : Bits); }
theory T(U < UU0) { M : set U; c : M;
  def value(n : Bits) : M := match n { nil => c; cons(b, rest) => c; };
}
def computation(S : T(U0)) : S.value(cons(yes, nil)) = S.c { rfl; }`,
  },
];

const lintVariants = [
  {
    id: "G5-single", contract: "single-binder advice preserves supported calls and generated interfaces",
    source: `import hlevels;
theory T(U < UU0) { M : set U; op : forall x : M. M; }
def identity(S : T(U0)) := T.Hom.id(S);
def applied(S : T(U0), a : S.M) : S.M := S.op(a);
initial N : T(U0);`,
    rewrite: {from: "forall x : M. M", to: "M -> M"},
  },
];

// Existing protection is named, not copied; these tests remain in the normal
// npm test run. G7 is historical and needs controlled failure injection in FG1.
export const historicalCoverage = {
  H1: ["../cubist-tests/initial_models.cubist", ["Constant", "K", "idem_at", "Named", "named_fold"]],
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
const captureVariants = [
  {id: "G11-grouped-dependent", name: "helper chain with grouped/dependent parameters", extra: "def chain(x : M) : M := k(x);", params: "c, d : M, p : c = c", body: "chain(c)", theory: "T", args: "x, x, refl(x)"},
  {id: "G11-inherited", name: "inherited helper chain", extra: "def chain(x : M) : M := k(x);", params: "c : M", body: "chain(c)", theory: "Child", args: "x"},
  {id: "G11-initial", name: "initial-model client", extra: "", params: "c : M", body: "k(c)", theory: "N", args: "x"},
];
function captureSource(variant) {
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


const recursiveVariants = [
  {
    id: "G12-inherited", contract: "inherited calls to earlier recursive values check and compute",
    source: `import hlevels; import nat;
theory T(U < UU0) { M : set U; c : M; op(x : M) : M;
  def iter(n : Nat) : M := match n { zero => c; succ(k) => op(iter(k)); };
  def twice(n : Nat) : M := op(iter(n));
}
theory Child(U < UU0) extends T {}
def computation(S : Child(U0)) : S.twice(zero) = S.op(S.c) { rfl; }`,
    clients: ["Child.iter", "Child.twice", "computation"],
  },
  {
    id: "G12-initial", contract: "initial-model calls to earlier recursive values check and compute",
    source: `import hlevels; import nat;
theory T(U < UU0) { M : set U; c : M; op(x : M) : M;
  def iter(n : Nat) : M := match n { zero => c; succ(k) => op(iter(k)); };
  def twice(n : Nat) : M := op(iter(n));
}
initial N : T(U0);
def computation : N.model.twice(zero) = N.op(N.c) { rfl; }`,
    clients: ["N", "N.model", "computation"],
  },
];

const kinds = {
  G1: "collision", G2: "completion", G3: "unsupported-family", G4: "evidence",
  G5: "lint", G6: "dependency", G8: "wildcard", G9: "links", G10: "capture-range",
  G11: "capture", G12: "completion", "G12-range": "refusal-range",
};

// Explicit observations of the documented baseline defects, not desired output.
// Remove only the fixed case's entry when its independent contract passes.
// A changed diagnostic, client verdict or link must be investigated, not rerecorded.
const knownDefects = {
  "G1": {
    "gaps": ["original E606"],
    "clients": {"original": "refused", "independent": "checked"},
    "originalType": "U0",
    "duplicateRefused": false
  },
  "G2": {
    "gaps": [
      "T.Hom E606",
      "T.Hom.compose E340",
      "T.Hom.id E340",
      "T.Hom.make E340",
      "T.Hom.map E340",
      "T.Hom.map_op E340",
      "T.Iso E340",
      "T.Iso.compose E340",
      "T.Iso.from E340",
      "T.Iso.from_to E340",
      "T.Iso.id E340",
      "T.Iso.inverse E340",
      "T.Iso.make E340",
      "T.Iso.to E340",
      "T.Iso.to_from E340",
      "computation E340",
      "computation_u1 E340",
      "identity E340",
      "identity_u1 E340",
      "iso E340",
      "iso_u1 E340"
    ],
    "clients": {
      "T.Hom": "refused",
      "identity": "refused",
      "computation": "refused",
      "iso": "refused",
      "identity_u1": "refused",
      "computation_u1": "refused",
      "iso_u1": "refused"
    }
  },
  "G3": {
    "gaps": [
      "T.Hom E606",
      "T.Hom.compose E340",
      "T.Hom.id E340",
      "T.Hom.make E340",
      "T.Hom.map E340",
      "T.Hom.map_c E340",
      "T.Hom.map_op E340",
      "T.Iso E340",
      "T.Iso.compose E340",
      "T.Iso.from E340",
      "T.Iso.from_to E340",
      "T.Iso.id E340",
      "T.Iso.inverse E340",
      "T.Iso.make E340",
      "T.Iso.to E340",
      "T.Iso.to_from E340",
      "unsupported E340"
    ],
    "clients": {"T": "checked", "T.make": "checked", "T.op": "checked", "usable": "checked", "unsupported": "refused"},
    "published": [
      "T.Hom",
      "T.Hom.compose",
      "T.Hom.id",
      "T.Hom.make",
      "T.Hom.map",
      "T.Hom.map_c",
      "T.Hom.map_op",
      "T.Iso",
      "T.Iso.compose",
      "T.Iso.from",
      "T.Iso.from_to",
      "T.Iso.id",
      "T.Iso.inverse",
      "T.Iso.make",
      "T.Iso.to",
      "T.Iso.to_from"
    ],
    "refusals": [{"name": "unsupported", "code": "E340", "words": [false, false, false], "unsupported": true}]
  },
  "G4": {
    "gaps": ["T.value E546", "computation E340"],
    "clients": {"T.value": "refused", "computation": "refused"},
    "generation": [["T.value", "Bit.squash"]]
  },
  "G5": {
    "gaps": ["N E864", "identity E817"],
    "clients": {"identity": "refused", "applied": "checked", "N": "refused", "N.model": "missing", "N.fold": "missing"}
  },
  "G6": {
    "gaps": ["C E343", "P E343"],
    "clients": {"independent": "checked"},
    "childNamesParent": false,
    "childRepeatsCause": true
  },
  "G8": {
    "gaps": ["h E546"],
    "clients": {},
    "generation": [["h", "seg"]],
    "endpoints": [false, false],
    "range": {"nonempty": true, "withinScope": true, "coversToken": false}
  },
  "G9": {
    "gaps": [],
    "clients": {"meaning": "checked"},
    "links": [[["c", null]], [["c1", null]], [["c1", null]], [["c1", null]]]
  },
  "G10": {"gaps": ["T E871"], "clients": {}, "range": {"nonempty": false, "withinConflict": false, "coversConflict": false}},
  "G11": {"gaps": ["intended E606"], "clients": {"intended": "refused", "captured": "checked"}},
  "G12": {
    "gaps": ["T E845", "computation E340"],
    "clients": {"T.iter": "missing", "T.twice": "missing", "computation": "refused"}
  },
  "G12-range": {"gaps": ["T E845"], "clients": {}, "range": {"nonempty": false, "withinScope": true, "coversToken": false}},
  "G1-initial": {
    "gaps": ["original E606"],
    "clients": {"original": "refused", "independent": "checked"},
    "originalType": "U0",
    "duplicateRefused": false
  },
  "G1-reverse": {
    "gaps": ["constructor E604", "original E606"],
    "clients": {"original": "refused", "constructor": "refused", "independent": "checked"},
    "originalType": "Unit",
    "duplicateRefused": false
  },
  "G1-same-kind": {
    "gaps": ["N E604", "original E340"],
    "clients": {"original": "refused", "independent": "checked"},
    "originalType": null,
    "duplicateRefused": true
  },
  "G4-flat": {
    "gaps": ["T.value E546", "computation E340"],
    "clients": {"T.value": "refused", "computation": "refused"},
    "generation": [["T.value", "Bits.squash"]]
  },
  "G5-single": {
    "gaps": ["N E864", "identity E817"],
    "clients": {"identity": "refused", "applied": "checked", "N": "refused", "N.model": "missing", "N.fold": "missing"}
  },
  "G11-grouped-dependent": {"gaps": ["intended E606"], "clients": {"intended": "refused", "captured": "checked"}},
  "G11-inherited": {"gaps": ["intended E606"], "clients": {"intended": "refused", "captured": "checked"}},
  "G11-initial": {"gaps": ["intended E606"], "clients": {"intended": "refused", "captured": "checked"}},
  "G12-inherited": {
    "gaps": ["Child E805", "T E845", "computation E340"],
    "clients": {"Child.iter": "missing", "Child.twice": "missing", "computation": "refused"}
  },
  "G12-initial": {
    "gaps": ["N E340", "T E845", "computation E340"],
    "clients": {"N": "refused", "N.model": "missing", "computation": "refused"}
  }
};
const caseOf = (group, variant = {}) => {
  const id = variant.id ?? group;
  return {id, group: group === "G12-range" ? "G12" : group, kind: kinds[group],
    ...definitions[group], ...variant, knownDefect: knownDefects[id]};
};
export const cases = [
  ...Object.keys(definitions).map(group => caseOf(group)),
  ...collisionVariants.map(variant => caseOf("G1", variant)),
  ...matchVariants.map(variant => caseOf("G4", variant)),
  ...lintVariants.map(variant => caseOf("G5", variant)),
  ...captureVariants.map(variant => caseOf("G11", {id: variant.id, contract: variant.name, source: captureSource(variant)})),
  ...recursiveVariants.map(variant => caseOf("G12", variant)),
];

// Existing FG5 provenance/browser consumers look up source fixtures by ID.
// This derived view contains the same case objects, never separate group state.
export const gaps = Object.fromEntries(cases.map(fixture => [fixture.id, fixture]));
