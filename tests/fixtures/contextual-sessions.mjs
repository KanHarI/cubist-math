// Source controls and query scripts for the CB1/CB6 replay backend. These
// describe desired sessions; the current module REPL does not implement them.
// Each marker is a unique substring. Scopes are selected by occurrence and
// instance, never by whichever binding happens to have the same spelling.
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
    sessions: [{ entry: "typeof ih", type: "Nat" }, { entry: "typeof inner_ih", type: "Nat" }],
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
      { entry: "typeof next_", type: "Nat" },
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
def f(next_ : Nat) : Nat { let next_ := succ(next_); exact next_; }
def checked_value : f(zero) = succ(zero) { rfl; }`,
    gaps: [], clients: ["checked_value"],
    sessions: [{ phase: "initializer", entry: "evaluate next_", value: "outer next_" },
      { phase: "after", entry: "evaluate next_", value: "succ(outer next_)" }],
    visible: ["next_"], absent: [], goal: "Nat",
  },
  {
    id: "selected-failing-prefix", phase: "CB1", marker: "exact typed(Unit, next_)",
    source: `import nat;
def broken(k : Nat) : Nat { let next_ := succ(k); exact typed(Unit, next_); }
def independent : Unit := tt;`,
    gaps: [["broken", "E606"]], clients: ["independent"],
    sessions: [{ entry: "typeof next_", type: "Nat" }, { entry: "evaluate next_", value: "succ(k)" }],
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
    sessions: [{ entry: "typeof a", type: "Nat", instance: "explicit branch selection required" }],
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
    sessions: [{ entry: "/goal", goal: "k = k" }, { entry: "{ rfl; }", accepts: true }],
    visible: ["k"], absent: [], goal: "k = k",
  },
];

export const sessionLifecycle = [
  "two sessions at one scope keep scratch bindings isolated",
  "source/import revision changes invalidate sessions without matching labels",
  "full ordered prefix replay preserves selected-only recursive accounting and cumulative kernel work",
  "fuel, kernel budget and deadline exhaustion each report context unavailable",
  "failed scratch-history replay preserves history and reports the failed entry",
  "worker cancellation/disposal prevents old requests from using invalid handles",
];
