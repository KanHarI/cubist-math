// The scratch closure evaluator behind the runtime evaluation roadmap's
// preliminary measurements (docs/roadmaps/runtime-evaluation-roadmap.md),
// versioned for EVAL0 so that its observations can be repeated. It is
// feasibility evidence only: nothing checks, renders or trusts what it
// returns, no checker, REPL or page uses it, and it certifies no equality.
//
// It evaluates a checked definition's kernel syntax with environments and
// memoized thunks, in place of substitution, and keeps lambda domains, pair
// types, eliminator motives and unused fields suspended. It supports
// functions, pairs, sums, Unit and the eliminator of a declared type laid
// out as Nat is: two constructors, no parameters, levels, dimensions or
// data, and at most one recursive position. Anything else is refused with
// an error, never guessed: general H1 elimination and cubical computation
// are out of its scope. Recursion is the host's: a deep enough computation
// overflows JavaScript's call stack.
//
// `stats` counts thunks made, thunks forced, forces answered from a
// thunk's memo (hits), beta and iota steps, and the deepest nesting of
// forces, the evaluator's stack depth.
export function closureEvaluator(kernel) {
  const defs = new Map(), stats = { thunks: 0, forces: 0, hits: 0, beta: 0, iota: 0, depth: 0 };
  let depth = 0;
  const thunk = run => (stats.thunks++, { run });
  const force = t => {
    if ("value" in t) { stats.hits++; return t.value; }
    stats.forces++;
    stats.depth = Math.max(stats.depth, ++depth);
    try { const v = t.run(); t.value = v; delete t.run; return v; }
    finally { depth--; }
  };
  const delay = (id, env = null) => thunk(() => evaluate(id, env));
  const at = (env, symbol) => { for (let e = env; e; e = e.parent) if (e.symbol === symbol) return e.term; throw Error(`Unbound ${symbol}`); };
  const list = (id, env) => { const terms = []; for (let c = id; c;) { const n = kernel.node(c); terms.push(delay(n.children[0], env)); c = n.children[1]; } return terms; };
  const apply = (f, x) => thunk(() => {
    const fn = force(f);
    if (fn.tag === "Lam") { stats.beta++; return force(delay(fn.body, { parent: fn.env, symbol: fn.symbol, term: x })); }
    if (fn.tag === "Con") return { ...fn, args: [...fn.args, x] };
    if (fn.tag === "Elim") {
      stats.iota++;
      const v = force(x);
      if (v.tag !== "Con" || v.signature !== fn.signature) throw Error("Non-constructor elimination");
      const signature = kernel.signature(fn.signature), c = signature.constructors[v.index];
      // Nat's first-order constructor layout only.
      if (signature.parameters || signature.levels || signature.constructors.length !== 2 || c.dimensions || c.data
        || c.positions > 1 || v.args.length !== c.positions) throw Error("Unsupported inductive layout");
      let branch = fn.clauses[v.index];
      for (const arg of v.args) branch = apply(branch, arg);
      for (const arg of v.args) branch = apply(branch, apply(f, arg));
      return force(branch);
    }
    throw Error(`Apply ${fn.tag}`);
  });
  function evaluate(id, env) {
    const n = kernel.node(id), c = n.children;
    switch (n.kind) {
      case "DefRef": { if (!defs.has(id)) defs.set(id, delay(kernel.definition(id).value)); return force(defs.get(id)); }
      case "Var": return force(at(env, n.payload));
      case "Lam": return { tag: "Lam", symbol: n.payload, body: c[1], env, domain: delay(c[0], env) };
      case "App": return force(apply(delay(c[0], env), delay(c[1], env)));
      case "Con": return { tag: "Con", signature: kernel.node(c[0]).payload, index: n.payload, args: [] };
      case "Elim": return { tag: "Elim", signature: n.payload, clauses: list(c[1], env), motive: delay(c[0], env) };
      case "Pair": return { tag: "Pair", first: delay(c[1], env), second: delay(c[2], env), as: delay(c[0], env) };
      case "Fst": case "Snd": {
        const p = force(delay(c[0], env));
        if (p.tag !== "Pair") throw Error("Projection of non-pair");
        return force(n.kind === "Fst" ? p.first : p.second);
      }
      case "Inl": case "Inr": return { tag: n.kind, item: delay(c[1], env), as: delay(c[0], env) };
      case "SumRec": {
        const v = force(delay(c[3], env));
        if (!["Inl", "Inr"].includes(v.tag)) throw Error("Match non-sum");
        return force(apply(delay(c[v.tag === "Inl" ? 1 : 2], env), v.item));
      }
      case "Point": return { tag: "Point" };
      case "UnitRec": { if (force(delay(c[2], env)).tag !== "Point") throw Error("Non-unit"); return force(delay(c[1], env)); }
      default: throw Error(`Unsupported computation ${n.kind}`);
    }
  }
  // A unary natural's value as a number, forcing its successor chain.
  function natural(t) {
    let n = 0;
    for (;;) {
      const v = force(t);
      if (v.tag !== "Con") throw Error("Expected natural");
      if (v.index === 0) return n;
      if (v.index !== 1 || v.args.length !== 1) throw Error("Bad successor");
      n++; t = v.args[0];
    }
  }
  return { delay, force, natural, stats };
}
