// Source controls and query scripts for the CB1/CB6 replay backend. These
// run through ContextualSession; the separate module REPL has no local context.
// Each marker is a unique substring. Scopes are selected by occurrence and
// instance, never by whichever binding happens to have the same spelling.
import { editedFixture } from "../fixture-edits.mjs";
export const contextualScenarios = [
  {
    id: "nested-induction", phase: "CB6", marker: "succ(inner_ih)",
    source: `import nat;
def nested(n, m : Nat) : Nat := induction n return Nat {
  zero => m;
  succ(k) with ih => induction m return Nat {
    zero => succ(ih);
    succ(j) with inner_ih => succ(inner_ih);
  };
};
def checked_value : nested(succ(zero), zero) = succ(zero) { rfl; }`,
    gaps: [], clients: ["checked_value"],
    sessions: [{ entry: "typed(Nat, add(ih, inner_ih))", accepts: true },
      { entry: "typed(ih = inner_ih, refl(ih))", accepts: false }],
    visible: ["n", "m", "k", "ih", "j", "inner_ih"], absent: [], goal: "Nat",
  },
  {
    id: "nested-function", phase: "CB1", marker: "add(next_, n)",
    source: `import nat;
def outer(k : Nat) : Nat {
  let next_ := succ(k);
  let f := fun (n : Nat) => add(next_, n);
  exact f(zero);
}
def checked_value : outer(zero) = succ(zero) { rfl; }`,
    gaps: [], clients: ["checked_value"],
    sessions: [
      { entry: "typed(next_ = succ(k), refl(next_))", accepts: true },
      { entry: "let scratch := succ(next_)", accepts: true },
      { entry: "evaluate scratch", value: "succ(succ(k))" },
      { entry: "typed(Unit, scratch)", accepts: false },
      { entry: "typeof scratch", type: "Nat" },
    ],
    visible: ["k", "next_", "n"], absent: ["f"], goal: null,
  },
  {
    id: "let-before-after", phase: "CB1", marker: "let next_ := succ(next_)",
    source: `import nat;
def f(next_ : Nat) : Nat { let saved := next_; let next_ := succ(next_); exact next_; }
def checked_value : f(zero) = succ(zero) { rfl; }`,
    gaps: [], clients: ["checked_value"],
    sessions: [{ phase: "initializer", entry: "typed(next_ = saved, refl(next_))", accepts: true },
      { phase: "after", entry: "typed(next_ = saved, refl(next_))", accepts: false },
      { phase: "after", entry: "typed(next_ = succ(saved), refl(next_))", accepts: true }],
    visible: ["next_"], absent: [], goal: "Nat",
  },
  {
    id: "selected-failing-prefix", phase: "CB1", marker: "exact typed(Unit, next_)",
    source: `import nat;
def broken(k : Nat) : Nat { let next_ := succ(k); exact typed(Unit, next_); }
def independent : Unit := tt;`,
    gaps: [["broken", "E606"]], clients: ["independent"],
    sessions: [{ entry: "typed(next_ = succ(k), refl(next_))", accepts: true }, { entry: "evaluate next_", value: "succ(k)" }],
    visible: ["k", "next_"], absent: ["broken"], goal: "Nat",
  },
  {
    id: "branch-instance-set", phase: "CB6", marker: "_, _ => zero;",
    source: `import nat;
def both(a, b : Nat) : Nat := match a, b { zero, zero => succ(zero); _, _ => zero; };
def at_zero : both(zero, zero) = succ(zero) { rfl; }
def at_left : both(succ(zero), zero) = zero { rfl; }
def at_right : both(zero, succ(zero)) = zero { rfl; }`,
    gaps: [], clients: ["at_zero", "at_left", "at_right"],
    sessions: [{ entry: "typed(a = zero, refl(a))", instance: "zero, succ", accepts: true },
      { entry: "typed(a = zero, refl(a))", instance: "succ, any", accepts: false }],
    visible: ["a", "b"], absent: [], goal: "Nat", multipleInstances: true,
  },
  {
    id: "discarded-path-body", phase: "CB1/CB6", marker: "_ => right_;",
    source: `import hlevels;
inductive S1 { base; loop : base = base; }
inductive Two : prop U0 { left_; right_; }
def f(c : S1) : Two := match c { base => left_; _ => right_; };
def checked_value : f(base) = left_ { rfl; }
def captured : f(base) = right_ { rfl; }`,
    gaps: [["captured", "E606"]], clients: ["checked_value"],
    sessions: [{ entry: "typeof c", unavailable: "written body was discarded for automatic coherence" }],
    visible: [], absent: [], goal: null, selectableInstances: 0,
  },
  {
    id: "proof-goal", phase: "CB6", marker: "exact refl(k)",
    source: `import nat;
def proof(k : Nat) : k = k { exact refl(k); }
def checked_value : zero = zero := proof(zero);`,
    gaps: [], clients: ["proof", "checked_value"],
    sessions: [{ entry: "/goal", goal: "k = k" }, { entry: "refl(k)", accepts: true }],
    visible: ["k"], absent: [], goal: "k = k",
  },
];

// Check the proposed query in source at the selected scope and at a nearby
// alternative now, independently of the future session API. A lambda whose
// unused argument is the query preserves the original result of the body.
const scenario = id => contextualScenarios.find(c => c.id === id);
const query = (type, term, body) => `(fun (_ : ${type}) => ${body})(${term})`;
const edit = (anchor, replacement) => ({anchor, replacement});
const nested = scenario("nested-induction");
nested.probes = [
  { id:"inner successor", edit:edit("succ(inner_ih)", query("Nat", "add(ih, inner_ih)", "succ(inner_ih)")), gaps:[] },
  { id:"hypotheses have distinct identities", edit:edit("succ(inner_ih)", query("ih = inner_ih", "refl(ih)", "succ(inner_ih)")),
    gaps:[["nested", "E606"], ["checked_value", "E340"]] },
  { id:"outer successor before inner induction", edit:edit("induction m return Nat", "induction add(ih, inner_ih) return Nat"),
    gaps:[["nested", "E343"], ["checked_value", "E340"]] },
];
const shadow = scenario("let-before-after");
shadow.probes = [
  { id:"initializer sees saved parameter", edit:edit("succ(next_)", query("next_ = saved", "refl(next_)", "succ(next_)")), gaps:[] },
  { id:"body cannot see saved parameter as next_", edit:edit("exact next_;", `exact ${query("next_ = saved", "refl(next_)", "next_")};`),
    gaps:[["f", "E606"], ["checked_value", "E340"]] },
  { id:"body sees successor", edit:edit("exact next_;", `exact ${query("next_ = succ(saved)", "refl(next_)", "next_")};`), gaps:[] },
];
const branch = scenario("branch-instance-set");
// Split the overlapping written wildcard into its two semantic instances.
// Checking the query in the unsplit wildcard would test *both* instances.
branch.probes = [
  { id:"zero, succ", edit:edit(branch.marker,
    `zero, succ(k) => ${query("a = zero", "refl(a)", "zero")}; succ(k), _ => zero;`), gaps:[] },
  { id:"succ, any", edit:edit(branch.marker,
    `zero, succ(k) => zero; succ(k), _ => ${query("a = zero", "refl(a)", "zero")};`),
    gaps:[["both", "E606"], ["at_zero", "E340"], ["at_left", "E340"], ["at_right", "E340"]] },
];
const fn = scenario("nested-function");
fn.probes = [
  { id:"after let", edit:edit(fn.marker, query("next_ = succ(k)", "refl(next_)", fn.marker)), gaps:[] },
  { id:"initializer before let binding", edit:edit("succ(k);", `${query("next_ = succ(k)", "refl(next_)", "succ(k)")};`),
    gaps:[["outer", "E343"], ["checked_value", "E340"]] },
];
const failing = scenario("selected-failing-prefix");
failing.probes = [
  { id:"selected prefix query checks", edit:edit("typed(Unit, next_)", query("next_ = succ(k)", "refl(next_)", "next_")), gaps:[] },
  { id:"before prefix binding query fails", edit:edit("succ(k);", `${query("next_ = succ(k)", "refl(next_)", "succ(k)")};`),
    gaps:[["broken", "E343"]] },
];
const proof = scenario("proof-goal");
proof.probes = [
  { id:"reflexive goal", edit:null, gaps:[] },
  { id:"successor goal", edit:edit("k = k {", "k = succ(k) {"),
    gaps:[["proof", "E606"], ["checked_value", "E340"]] },
];
const discarded = scenario("discarded-path-body");
discarded.probes = [
  { id:"discarded body does not determine point value", edit:null, gaps:discarded.gaps },
  { id:"retained point branch determines value", edit:edit("base => left_; ", ""),
    gaps:[["checked_value", "E606"]] },
];

export function probeSource(scenario, probe) {
  if (probe.edit === null) return scenario.source;
  return editedFixture(scenario.source, probe.edit, `${scenario.id}/${probe.id}`);
}
