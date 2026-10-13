// Review witnesses have independent source clients. Expectations describe
// the intended language, never a type or term copied from generated syntax.
const imports = "import hlevels; import nat;";
const recursive = "def iter(n : Nat) : Nat := match n { zero => zero; succ(k) => iter(k); };";
const global = "def iter(n : Nat) : Nat := succ(zero);";
const recovery = "def independent : Unit := tt;";
const box = "inductive Box(U < UU0, A : U) : U { box(a : A); }";
const refusedTheory = [["main", "T", "E845"], ["main", "captured", "E340"]];

export const bindingCases = [];
bindingCases.push({
  id:"helper-pattern-argument", phase:"CB3", contract:"substituted arguments retain their binder under a helper's pattern",
  source:`${imports}\n${box}
theory T(U < UU0) { M : set U; c : M;
  def pick(x : M) : M := match typed(Box(U,M),box(c)) return M { box(k) => x; };
  law l(k : M) : pick(k) = k;
}
def intended(S : T(U0), x : S.M) : x = x := S.l(x);
def captured(S : T(U0), x : S.M) : S.c = x := S.l(x);
${recovery}`,
  clients:["intended","captured","independent"],
  control:{source:{anchor:"box(k) =>",replacement:"box(other) =>"}},
  desired:{gaps:[["main","captured","E606"]],clients:{intended:true,captured:false,independent:true},assumes:[]},
}, {
  id:"initial-pattern-model", phase:"CB4", contract:"capture repair exposes the real strategy refusal and preserves the usable theory",
  source:`${imports}
theory P(U < UU0) { M : set U; c : M;
  law l(n : Nat) : c = (match n return M { zero => c; succ(k) => c; });
}
initial k : P(U0);
def intended(S : P(U0), n : Nat) : S.c = (match n return S.M { zero => S.c; succ(j) => S.c; }) := S.l(n);
${recovery}`,
  clients:["k","intended","independent"],
  control:{source:{anchor:"succ(k) =>",replacement:"succ(other) =>"}},
  desired:{gaps:[["main","k","E856"]],clients:{k:false,intended:true,independent:true},assumes:[]},
});
for (const [id, fixture, source, model] of [
  ["model-shadows-theory", "theory T(U < UU0) { M : set U; c : M; }", `initial T : T(U0);
def intended : T := T.c;
def captured : Unit := T.c;`, "T"],
  ["model-shadows-header-global", "def N : U0 := Unit; theory T(U < UU0, A : U) { M : set U; c(x : A) : M; }", `initial N : T(U0, N);
def intended : N := N.c(tt);
def captured : N := N.c(N.c(tt));`, "N"],
  ["model-shadows-parameter-global", "def W : U0 := Unit; theory T(U < UU0) { M : set U; }", `free W(A : W) : T(U0) on Unit;
def intended : W(tt) := W.gen(tt);
def captured : W(tt) := W.gen(zero);`, "W"],
]) bindingCases.push({
  id, phase:"CB4", contract:"a new model identity does not replace a captured imported dependency",
  fixtures:{prior:`${imports}\n${fixture}`}, source:`import prior;\n${source}\n${recovery}`,
  clients:[model,"intended","captured","independent"],
  control:{source:{anchor:id === "model-shadows-theory" ? "T(U0)" : id === "model-shadows-header-global" ? "T(U0, N)" : "A : W",
    replacement:id === "model-shadows-theory" ? "Previous(U0)" : id === "model-shadows-header-global" ? "T(U0, Previous)" : "A : Previous"},
    fixture:{name:"prior",anchor:id === "model-shadows-theory" ? "theory T(" : `def ${model} :`,
      replacement:id === "model-shadows-theory" ? "theory Previous(" : "def Previous :"}},
  desired:{gaps:[["main","captured","E606"]],clients:{[model]:true,intended:true,captured:false,independent:true},assumes:[]},
});
export const resolutionLocations = ["absent", "same-module", "imported"];
export function resolutionContext(location, declaration) {
  return { prefix: `${imports}\n${location === "same-module" ? declaration : location === "imported" ? "import prior;" : ""}`,
    fixtures: location === "imported" ? { prior: `${imports}\n${declaration}` } : {} };
}
for (const location of resolutionLocations) {
  const context = resolutionContext(location, global);
  for (const bare of [false, true]) bindingCases.push({
    id: `recursive-${bare ? "bare" : "wrapper"}-${location}`, phase: "CB2",
    contract: "recursive field dependencies cannot become a same-spelled global",
    source: `${context.prefix}
theory T(U < UU0) { M : set U; ${recursive}
  ${bare ? "" : "def wrap(n : Nat) : Nat := iter(n);"}
  op(p : ${bare ? "iter = (fun (n : Nat) => succ(zero))" : "wrap(zero) = succ(zero)"}) : M;
}
def captured(S : T(U0)) : S.M := S.op(${bare ? "refl(fun (n : Nat) => succ(zero))" : "refl(succ(zero))"});
${recovery}`,
    fixtures: context.fixtures,
    clients: ["captured", "independent"],
    desired: { gaps: refusedTheory, clients: { captured: false, independent: true }, assumes: [] },
  });
}

bindingCases.push({
  id: "ordered-header", phase: "CB2", contract: "later helpers cannot replace an earlier header parameter",
  source: `${imports}
theory T(U < UU0, n : Nat) { M : set U; op(p : n = n) : M; def n : Nat := zero; }
def identity(n : Nat, S : T(U0, n)) : T.Hom(S, S) := T.Hom.id(S);
def param(m : Nat, S : T(U0, m), p : m = m) : S.M := S.op(p);
def captured_param(m : Nat, S : T(U0, m)) : S.M := S.op(refl(zero));
initial N : T(U0, succ(zero));
def generated : N := N.op(refl(succ(zero)));
def captured : N := N.op(refl(zero));`,
  clients: ["identity", "param", "captured_param", "N", "generated", "captured"],
  desired: { gaps: [["main", "captured_param", "E606"], ["main", "captured", "E606"]],
    clients: { identity: true, param: true, captured_param: false, N: true, generated: true, captured: false }, assumes: [] },
}, {
  id: "imported-pattern-rename", phase: "CB2/CB3/CB5",
  contract: "inheritance renames field identities without capturing imported pattern binders",
  fixtures: { parent: `${imports}\n${"// imported source ownership padding\n".repeat(16)}
theory P(U < UU0) { M : set U; a : M;
  law l(n : Nat) : (match n return M { zero => a; succ(b) => a; }) = a;
}` },
  source: `import parent;
theory C(U < UU0) extends P(a := b) {}
def meaning(S : C(U0), n : Nat) :
  (match n return S.M { zero => S.b; succ(k) => S.b; }) = S.b := S.l(n);
${recovery}`,
  clients: ["meaning", "independent"],
  desired: { gaps: [], clients: { meaning: true, independent: true }, assumes: [] },
});

for (const location of resolutionLocations) {
  const context = resolutionContext(location, "def Index : U0 := Unit;");
  bindingCases.push({
    id: `family-domain-helper-${location}`, phase: "CB2", contract: "family domains retain the helper instead of an ambient Index",
    fixtures: context.fixtures,
    source: `${context.prefix}
theory T(U < UU0) { M : set U; def Index : U0 := Nat; F(n : Index) : set U; }
def member(S : T(U0)) : U0 := S.F(zero);
def captured(S : T(U0)) : U0 := S.F(tt);
${recovery}`,
    clients: ["member", "captured", "independent"],
    desired: { gaps: [["main", "captured", "E606"]], clients: { member: true, captured: false, independent: true }, assumes: [] },
  });
}

const models = `${imports}
theory Point(U < UU0) { M : set U; one : M; }
def additive_ : Point(U0) := Point.make(Nat, nat_is_set, zero);
def multiplicative : Point(U0) := Point.make(Nat, nat_is_set, succ(zero));`;
bindingCases.push({
  id: "file-opening-precedence", phase: "CB3", contract: "per-item openings outrank module globals but not parameters",
  source: `${models}
use multiplicative;
def one : Nat := zero;
def f : Nat := one;
def local(one : Nat) : Nat := one;
def opened : f = succ(zero) { rfl; }
def shadowed : local(zero) = zero { rfl; }
def captured : f = zero { rfl; }`,
  clients: ["opened", "shadowed", "captured"],
  desired: { gaps: [["main", "captured", "E606"]], clients: { opened: true, shadowed: true, captured: false }, assumes: [] },
}, {
  id: "file-opening-reactivation", phase: "CB3", contract: "each later source item resolves a file-level opening receiver anew",
  source: `${imports} import algebra;
use nat_multiplicative.monoid;
def nat_multiplicative : Nat := nat.(1);
use nat;`,
  clients: ["nat_multiplicative"],
  desired: { gaps: [["main", "use at line 4", "E343"]], clients: { nat_multiplicative: true }, assumes: [] },
});

// The operand recipe selects a numeral rule that distinguishes its receiver
// from a same-spelled client model, without depending on implicit field opening.
const notationModels = `${imports}
theory Numerals(U < UU0) { M : set U; read(n : Nat) : M; def numeral_(n : Nat) : M := read(n) notation numeral; }
def recipe : Numerals(U0) := Numerals.make(Nat, nat_is_set, fun (n : Nat) => n);
def shifted : Numerals(U0) := Numerals.make(Nat, nat_is_set, fun (n : Nat) => succ(n));
theory Power(U < UU0) { M : set U; pow(x : M, n : Nat) : M notation x ^ recipe.(n); }`;
for (const imported of [false, true]) bindingCases.push({
  id: `operand-receiver-${imported ? "global" : "local"}`, phase: "CB3",
  contract: "an operand recipe retains its declaration-scoped model receiver",
  fixtures: imported ? { recipe_definition: notationModels } : {},
  source: `${imported ? "import recipe_definition; def recipe : Numerals(U0) := shifted;" : notationModels}
def client(S : Power(U0), x : S.M) : S.M {
  ${imported ? "" : "let recipe := shifted;"}
  use S; exact x ^ 0;
}
def intended(S : Power(U0), x : S.M) : client(S, x) = S.pow(x, zero) { rfl; }
def captured(S : Power(U0), x : S.M) : client(S, x) = S.pow(x, succ(zero)) { rfl; }`,
  clients: ["client", "intended", "captured"],
  desired: { gaps: [["main", "captured", "E606"]], clients: { client: true, intended: true, captured: false }, assumes: [] },
});

bindingCases.push({
  id: "failed-theory-activation", phase: "CB3", contract: "failed required openings refuse every dependent generated group",
  source: `${imports} import algebra;
${recovery}
def one : Nat := zero;
use nat_multiplicative.monoid;
def nat_multiplicative : Nat := nat.(1);
theory Pointed(U < UU0) { M : set U; c : M; op(n : Nat) : M; law is_one : op(one) = c; }`,
  clients: ["independent"], publication: ["Pointed"],
  desired: { gaps: [["main", "Pointed", "E343"]], clients: { independent: true }, assumes: [], published: [] },
}, {
  id: "operand-local", phase: "CB3", contract: "synthesized operand selection cannot open fields over caller locals",
  source: `${models}
theory Power(U < UU0) { M : set U; pow(x : M, n : Nat) : M notation x ^ additive_.(n); }
def client(S : Power(U0), x : S.M, one : Nat) : S.M := S.(x ^ one);
def intended(S : Power(U0), x : S.M, n : Nat) : client(S, x, n) = S.pow(x, n) { rfl; }
def captured(S : Power(U0), x : S.M, n : Nat) : client(S, x, n) = S.pow(x, zero) { rfl; }`,
  clients: ["client", "intended", "captured"],
  desired: { gaps: [["main", "captured", "E606"]], clients: { client: true, intended: true, captured: false }, assumes: [] },
}, {
  id: "opening-local-model", phase: "CB3", contract: "deferred local and call-produced openings precede ambient globals",
  source: `${models}
def one : Unit := tt;
def selected(m : Point(U0)) : Point(U0) := m;
def local(m : Point(U0)) : m.M { use m; exact one; }
def call(m : Point(U0)) : m.M { use selected(m); exact one; }
def intended : local(multiplicative) = succ(zero) { rfl; }
def call_intended : call(multiplicative) = succ(zero) { rfl; }
def captured : local(multiplicative) = zero { rfl; }`,
  clients: ["local", "call", "intended", "call_intended", "captured"],
  desired: { gaps: [["main", "captured", "E606"]], clients: { local: true, call: true, intended: true, call_intended: true, captured: false }, assumes: [] },
});
