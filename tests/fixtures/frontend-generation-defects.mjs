// What each case with a documented defect shows today
// (frontend-generation-cases.mjs observes it): never desired output, which
// each case module states. Only the runner reads these, and a case is a
// TODO only while it shows exactly its record. Investigate any other
// result before changing a record. Remove a fixed case's record with its
// fix; once every case shows its desired outcome, delete this module.
export const knownDefects = {
  "G1": {
    diagnostics: [
      {"at":"def original : Unit := N;","label":"Error","text":"E606: Type mismatch: found U0, expected Unit."},
    ],
    assumes: [],
  },
  "G10": {
    diagnostics: [
      {"at":"theory T(U < UU0) {","label":"Error","text":"E871: Inlining k here would capture its field c: rename the enclosing pattern or statement binding."},
    ],
    assumes: [],
    range: [
      {"line":"law l(n : Nat) : (match n return M {","covers":""},
    ],
  },
  "G11": {
    diagnostics: [
      {"at":"def intended(S : T(U0), x : S.M) : S.kk(x) = S.op(x, S.c) := refl(S.op(x, S.c));","label":"Error","text":"E606: Type mismatch: found S.op(x, S.c) = S.op(x, S.c), expected T.kk{{U0}}(S, x) = S.op(x, S.c)."},
    ],
    assumes: [],
  },
  "G11-grouped-dependent": {
    diagnostics: [
      {"at":"def intended(S : T(U0), x : S.M) : S.kk(x, x, refl(x)) = S.op(x, S.c) := refl(S.op(x, S.c));","label":"Error","text":"E606: Type mismatch: found S.op(x, S.c) = S.op(x, S.c), expected T.kk{{U0}}(S, x, x, refl(x)) = S.op(x, S.c)."},
    ],
    assumes: [],
  },
  "G11-inherited": {
    diagnostics: [
      {"at":"def intended(S : Child(U0), x : S.M) : S.kk(x) = S.op(x, S.c) := refl(S.op(x, S.c));","label":"Error","text":"E606: Type mismatch: found S.op(x, S.c) = S.op(x, S.c), expected Child.kk{{U0}}(S, x) = S.op(x, S.c)."},
    ],
    assumes: [],
  },
  "G11-initial": {
    diagnostics: [
      {"at":"def intended(x : N) : N.model.kk(x) = N.op(x, N.c) := refl(N.op(x, N.c));","label":"Error","text":"E606: Type mismatch: found N.op(x, N.c) = N.op(x, N.c), expected T.kk{{U0}}(N.model, x) = N.op(x, N.c)."},
    ],
    assumes: [],
  },
  "G12": {
    diagnostics: [
      {"at":"theory T(U < UU0) {","label":"Error","text":"E845: iter is recursive, and a field's type cannot unfold it: state the law over a model, outside the theory."},
      {"at":"def computation(S : T(U0)) : S.twice(succ(zero)) = S.op(S.op(S.c)) {","label":"Error","text":"E340: Untranslated dependency: T"},
      {"at":"def computation2(S : T(U0)) : S.twice(succ(succ(zero))) = S.op(S.op(S.op(S.c))) {","label":"Error","text":"E340: Untranslated dependency: T"},
      {"at":"def base(S : T(U0)) : S.twice(zero) = S.op(S.c) {","label":"Error","text":"E340: Untranslated dependency: T"},
      {"at":"def wrong(S : T(U0)) : S.twice(succ(zero)) = S.op(S.c) {","label":"Error","text":"E340: Untranslated dependency: T"},
    ],
    assumes: [],
  },
  "G12-inherited": {
    diagnostics: [
      {"at":"theory T(U < UU0) {","label":"Error","text":"E845: iter is recursive, and a field's type cannot unfold it: state the law over a model, outside the theory."},
      {"at":"theory Child(U < UU0) extends T {}","label":"Error","text":"E805: T is not a theory here: Child extends theories in scope."},
      {"at":"def computation(S : Child(U0)) : S.twice(succ(zero)) = S.op(S.op(S.c)) {","label":"Error","text":"E340: Untranslated dependency: Child"},
      {"at":"def computation2(S : Child(U0)) : S.twice(succ(succ(zero))) = S.op(S.op(S.op(S.c))) {","label":"Error","text":"E340: Untranslated dependency: Child"},
      {"at":"def base(S : Child(U0)) : S.twice(zero) = S.op(S.c) {","label":"Error","text":"E340: Untranslated dependency: Child"},
      {"at":"def wrong(S : Child(U0)) : S.twice(succ(zero)) = S.op(S.c) {","label":"Error","text":"E340: Untranslated dependency: Child"},
    ],
    assumes: [],
  },
  "G12-initial": {
    diagnostics: [
      {"at":"theory T(U < UU0) {","label":"Error","text":"E845: iter is recursive, and a field's type cannot unfold it: state the law over a model, outside the theory."},
      {"at":"initial N : T(U0);","label":"Error","text":"E340: Untranslated dependency: T"},
      {"at":"def computation : N.model.twice(succ(zero)) = N.op(N.op(N.c)) {","label":"Error","text":"E340: Untranslated dependency: N"},
      {"at":"def computation2 : N.model.twice(succ(succ(zero))) = N.op(N.op(N.op(N.c))) {","label":"Error","text":"E340: Untranslated dependency: N"},
      {"at":"def base : N.model.twice(zero) = N.op(N.c) {","label":"Error","text":"E340: Untranslated dependency: N"},
      {"at":"def wrong : N.model.twice(succ(zero)) = N.op(N.c) {","label":"Error","text":"E340: Untranslated dependency: N"},
    ],
    assumes: [],
  },
  "G12-range": {
    diagnostics: [
      {"at":"theory T(U < UU0) {","label":"Error","text":"E845: iter is recursive, and a field's type cannot unfold it: state the law over a model, outside the theory."},
    ],
    assumes: [],
    range: [
      {"line":"law nope(n : Nat) : iter(n) = c;","covers":""},
    ],
  },
  "G12-shadowed": {
    diagnostics: [
      {"at":"theory T(U < UU0) {","label":"Error","text":"E845: iter is recursive, and a field's type cannot unfold it: state the law over a model, outside the theory."},
      {"at":"def intended(S : T(U0), f : Nat -> S.M) : S.twice(f, zero) = S.op(f(zero)) {","label":"Error","text":"E340: Untranslated dependency: T"},
      {"at":"def captured(S : T(U0), f : Nat -> S.M) : S.twice(f, zero) = S.op(S.c) {","label":"Error","text":"E340: Untranslated dependency: T"},
    ],
    assumes: [],
  },
  "G1-initial": {
    diagnostics: [
      {"at":"def original : Unit := N;","label":"Error","text":"E606: Type mismatch: found U0, expected Unit."},
    ],
    assumes: [],
    published: [
      "N.model",
      "N.fold_map",
      "N.fold",
    ],
  },
  "G1-reverse": {
    diagnostics: [
      {"at":"def original : U0 := N;","label":"Error","text":"E606: Type mismatch: found Unit, expected U0."},
      {"at":"def constructor : N := c;","label":"Error","text":"E604: Instruction kernel: Expected U, found Unit."},
    ],
    assumes: [],
  },
  "G1-same-kind": {
    diagnostics: [
      {"at":"def N : U0 := Unit;","label":"Error","text":"E604: Instruction kernel: Definition symbol is already registered."},
      {"at":"def original : Unit := N;","label":"Error","text":"E340: Untranslated dependency: N"},
    ],
    assumes: [],
  },
  "G2": {
    diagnostics: [
      {"at":"theory T(U < UU0) {","label":"Error","text":"E606: Type mismatch: found max(U, max(V, U1)), expected max(U, V)."},
      {"at":"theory T(U < UU0) {","label":"Error","text":"E340: Untranslated dependency: T.Hom"},
      {"at":"theory T(U < UU0) {","label":"Error","text":"E340: Untranslated dependency: T.Hom"},
      {"at":"theory T(U < UU0) {","label":"Error","text":"E340: Untranslated dependency: T.Hom"},
      {"at":"theory T(U < UU0) {","label":"Error","text":"E340: Untranslated dependency: T.Hom"},
      {"at":"theory T(U < UU0) {","label":"Error","text":"E340: Untranslated dependency: T.Hom"},
      {"at":"theory T(U < UU0) {","label":"Error","text":"E340: Untranslated dependency: T.Hom"},
      {"at":"theory T(U < UU0) {","label":"Error","text":"E340: Untranslated dependency: T.Hom"},
      {"at":"theory T(U < UU0) {","label":"Error","text":"E340: Untranslated dependency: T.Iso"},
      {"at":"theory T(U < UU0) {","label":"Error","text":"E340: Untranslated dependency: T.Iso"},
      {"at":"theory T(U < UU0) {","label":"Error","text":"E340: Untranslated dependency: T.Iso"},
      {"at":"theory T(U < UU0) {","label":"Error","text":"E340: Untranslated dependency: T.Iso"},
      {"at":"theory T(U < UU0) {","label":"Error","text":"E340: Untranslated dependency: T.Iso"},
      {"at":"theory T(U < UU0) {","label":"Error","text":"E340: Untranslated dependency: T.Iso"},
      {"at":"theory T(U < UU0) {","label":"Error","text":"E340: Untranslated dependency: T.Iso"},
      {"at":"def identity(S : T(U0)) : T.Hom(S, S) := T.Hom.id(S);","label":"Error","text":"E340: Untranslated dependency: T.Hom"},
      {"at":"def computation(S : T(U0), x : S.M) : T.Hom.compose(identity(S), identity(S)).map(x) = x {","label":"Error","text":"E340: Untranslated dependency: T.Hom.compose"},
      {"at":"def iso(S : T(U0)) : T.Iso(S, S) := T.Iso.id(S);","label":"Error","text":"E340: Untranslated dependency: T.Iso"},
      {"at":"def preserves(S, R : T(U0), f : T.Hom(S, R), A : U0, x : A) :","label":"Error","text":"E340: Untranslated dependency: T.Hom"},
      {"at":"def level(S : T(U0)) : U1 := T.Hom(S, S);","label":"Error","text":"E340: Untranslated dependency: T.Hom"},
      {"at":"def lowered(S : T(U0)) : U0 := T.Hom(S, S);","label":"Error","text":"E340: Untranslated dependency: T.Hom"},
      {"at":"def identity_u1(S : T(U1)) : T.Hom(S, S) := T.Hom.id(S);","label":"Error","text":"E340: Untranslated dependency: T.Hom"},
      {"at":"def computation_u1(S : T(U1), x : S.M) : T.Hom.compose(identity_u1(S), identity_u1(S)).map(x) = x {","label":"Error","text":"E340: Untranslated dependency: T.Hom.compose"},
      {"at":"def iso_u1(S : T(U1)) : T.Iso(S, S) := T.Iso.id(S);","label":"Error","text":"E340: Untranslated dependency: T.Iso"},
      {"at":"def preserves_u1(S, R : T(U1), f : T.Hom(S, R), A : U0, x : A) :","label":"Error","text":"E340: Untranslated dependency: T.Hom"},
      {"at":"def level_u1(S : T(U1)) : U1 := T.Hom(S, S);","label":"Error","text":"E340: Untranslated dependency: T.Hom"},
    ],
    assumes: [],
  },
  "G3": {
    diagnostics: [
      {"at":"theory T(U < UU0) {","label":"Error","text":"E606: Type mismatch: found A.l = A.l, expected B.l = B.l."},
      {"at":"theory T(U < UU0) {","label":"Error","text":"E340: Untranslated dependency: T.Hom"},
      {"at":"theory T(U < UU0) {","label":"Error","text":"E340: Untranslated dependency: T.Hom"},
      {"at":"theory T(U < UU0) {","label":"Error","text":"E340: Untranslated dependency: T.Hom"},
      {"at":"theory T(U < UU0) {","label":"Error","text":"E340: Untranslated dependency: T.Hom"},
      {"at":"theory T(U < UU0) {","label":"Error","text":"E340: Untranslated dependency: T.Hom"},
      {"at":"theory T(U < UU0) {","label":"Error","text":"E340: Untranslated dependency: T.Hom"},
      {"at":"theory T(U < UU0) {","label":"Error","text":"E340: Untranslated dependency: T.Hom"},
      {"at":"theory T(U < UU0) {","label":"Error","text":"E340: Untranslated dependency: T.Hom"},
      {"at":"theory T(U < UU0) {","label":"Error","text":"E340: Untranslated dependency: T.Iso"},
      {"at":"theory T(U < UU0) {","label":"Error","text":"E340: Untranslated dependency: T.Iso"},
      {"at":"theory T(U < UU0) {","label":"Error","text":"E340: Untranslated dependency: T.Iso"},
      {"at":"theory T(U < UU0) {","label":"Error","text":"E340: Untranslated dependency: T.Iso"},
      {"at":"theory T(U < UU0) {","label":"Error","text":"E340: Untranslated dependency: T.Iso"},
      {"at":"theory T(U < UU0) {","label":"Error","text":"E340: Untranslated dependency: T.Iso"},
      {"at":"theory T(U < UU0) {","label":"Error","text":"E340: Untranslated dependency: T.Iso"},
      {"at":"def unsupported(S : T(U0)) := T.Hom.id(S);","label":"Error","text":"E340: Untranslated dependency: T.Hom.id"},
      {"at":"def unsupported_iso(S : T(U0)) := T.Iso.id(S);","label":"Error","text":"E340: Untranslated dependency: T.Iso.id"},
    ],
    assumes: [],
    published: [
      "T.Hom",
      "T.Hom.make",
      "T.Hom.map",
      "T.Hom.map_c",
      "T.Hom.map_op",
      "T.Hom.id",
      "T.Hom.compose",
      "T.Iso",
      "T.Iso.make",
      "T.Iso.to",
      "T.Iso.from",
      "T.Iso.from_to",
      "T.Iso.to_from",
      "T.Iso.id",
      "T.Iso.compose",
      "T.Iso.inverse",
    ],
  },
  "G4": {
    diagnostics: [
      {"at":"def value(n : Bits) : M := match n {","label":"Error","text":"E546: Cannot generate Bit.squash: m.M must be of h-level 1; no local evidence, hint or rule gives that. Give checked h-level evidence, or an explicit obligation."},
      {"at":"def computation(S : T(U0)) : S.value(cons(yes, nil)) = S.op(S.op(S.c)) {","label":"Error","text":"E340: Untranslated dependency: T.value"},
      {"at":"def off_computation(S : T(U0)) : S.value(cons(off, nil)) = S.op(S.c) {","label":"Error","text":"E340: Untranslated dependency: T.value"},
      {"at":"def empty_computation(S : T(U0)) : S.value(nil) = S.c {","label":"Error","text":"E340: Untranslated dependency: T.value"},
      {"at":"def wrong(S : T(U0)) : S.value(cons(yes, nil)) = S.c {","label":"Error","text":"E340: Untranslated dependency: T.value"},
    ],
    assumes: [],
  },
  "G4-flat": {
    diagnostics: [
      {"at":"def value(n : Bits) : M := match n {","label":"Error","text":"E546: Cannot generate Bits.squash: m.M must be of h-level 1; no local evidence, hint or rule gives that. Give checked h-level evidence, or an explicit obligation."},
      {"at":"def computation(S : T(U0)) : S.value(cons(yes, nil)) = S.op(S.op(S.c)) {","label":"Error","text":"E340: Untranslated dependency: T.value"},
      {"at":"def empty_computation(S : T(U0)) : S.value(nil) = S.c {","label":"Error","text":"E340: Untranslated dependency: T.value"},
      {"at":"def wrong(S : T(U0)) : S.value(cons(yes, nil)) = S.c {","label":"Error","text":"E340: Untranslated dependency: T.value"},
    ],
    assumes: [],
  },
  "G5": {
    diagnostics: [
      {"at":"op : forall x, y : M. M;","label":"Warning","text":"W706: x is unused in the body: take it out of the group and write M -> … for it."},
      {"at":"op : forall x, y : M. M;","label":"Warning","text":"W706: y is unused in the body: take it out of the group and write M -> … for it."},
    ],
    assumes: [],
    advice: [
      {"code":"W706","declaration":"T","message":"x is unused in the body: take it out of the group and write M -> … for it.","covers":"x"},
      {"code":"W706","declaration":"T","message":"y is unused in the body: take it out of the group and write M -> … for it.","covers":"y"},
    ],
  },
  "G5-single": {
    diagnostics: [
      {"at":"op : forall x : M. M;","label":"Warning","text":"W705: x is unused in the body: write M -> … instead of forall x : M. …."},
    ],
    assumes: [],
    advice: [
      {"code":"W705","declaration":"T","message":"x is unused in the body: write M -> … instead of forall x : M. ….","covers":"x"},
    ],
  },
  "G6": {
    diagnostics: [
      {"at":"theory P(U < UU0) {","label":"Error","text":"E343: Untranslated name: Undefined"},
      {"at":"theory C(U < UU0) extends P {","label":"Error","text":"E343: Untranslated name: Undefined"},
    ],
    assumes: [],
  },
  "G8": {
    diagnostics: [
      {"at":"def h(x : T) : T := match x {","label":"Error","text":"E546: Cannot generate seg: T must be a proposition; no local evidence, hint or rule gives that. Give checked h-level evidence, or an explicit obligation."},
    ],
    assumes: [],
    range: [
      {"line":"def h(x : T) : T := match x {","covers":"x"},
    ],
  },
  "G9": {
    diagnostics: [],
    assumes: [],
    links: [
      [{"name":"c","target":null,"start":0,"end":0}],
      [{"name":"c1","target":null,"start":0,"end":0}],
      [{"name":"c1","target":null,"start":0,"end":0}],
      [{"name":"c1","target":null,"start":0,"end":0}],
    ],
  },
};
