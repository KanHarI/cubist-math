// Migration backend for mathematical proof combinators. It records functions,
// induction and equality reasoning, not kernel instructions. The resulting text
// is independently parsed and checked by MathScript; this exporter is untrusted.
export const declarations = [];
const names = new WeakMap();
let serial = 0;
const node = (kind, props = {}) => ({ kind, ...props });
const name = (n) => node("name", { name: n });
const variable = (hint) => node("var", { id: ++serial, hint });
const hints = (f) =>
  f
    .toString()
    .match(/^\s*(?:\(([^)]*)\)|([A-Za-z_][A-Za-z_0-9]*))\s*=>/)
    ?.slice(1)
    .find(Boolean)
    ?.split(",")
    .map((x) => x.trim()) ?? [];
const call = (f, ...args) =>
  node("call", { fn: typeof f === "string" ? name(f) : f, args });
const binary = (operator, left, right) =>
  node("binary", { operator, left, right });
function binder(kind, A, fn, hint) {
  const x = variable(hint ?? hints(fn)[0] ?? "x");
  return node(kind, { A, x, body: fn(x) });
}
const lam = (A, f, h) => binder("fun", A, f, h),
  pi = (A, f, h) => binder("forall", A, f, h),
  sigma = (A, f, h) => binder("exists", A, f, h);
const arr = (A, B) => binary("->", A, B),
  and = (A, B) => binary("and", A, B),
  sum = (A, B) => binary("or", A, B);
const named = (body, n, theorem = false) => {
  declarations.push({ name: n, body, theorem });
  names.set(body, n);
  return name(n);
};
const aliases = {
  nat_add: "add",
  nat_mul: "mul",
  nat_le: "le",
  nat_factorial: "factorial",
};
export function foundation() {
  const N = name("Nat"),
    Z = node("number", { value: 0 }),
    U = name("Type"),
    V = name("Void"),
    T = name("Unit"),
    tt = name("tt");
  const S = (n) =>
      n.kind === "number"
        ? node("number", { value: n.value + 1 })
        : call("succ", n),
    one = S(Z),
    two = S(one);
  const eq = (x, y) => binary("=", x, y),
    refl = (x) => call("refl", x),
    not = (A) => arr(A, V);
  const typed = (A, x) => call("typed", A, x);
  const L = (A, B, x) => typed(sum(A, B), call("left", x)),
    R = (A, B, x) => typed(sum(A, B), call("right", x));
  const absurd = (A, x) => typed(A, call("absurd", x));
  const cases = (A, B, v, C, l, r) => call("cases", v, C, lam(A, l), lam(B, r));
  const pair = (A, B, x, y) =>
    typed(sigma(A, B), node("pair", { left: x, right: y }));
  const split = (A, B, p, C, f) =>
    call(
      "unpack",
      p,
      C,
      lam(A, (x) => lam(B(x), (y) => f(x, y), hints(f)[1]), hints(f)[0]),
    );
  const both = (A, B, x, y) =>
    typed(and(A, B), node("pair", { left: x, right: y }));
  const ind = (C, base, step, n) =>
    call(
      "induct",
      n,
      lam(N, C),
      base,
      lam(
        N,
        (k) => lam(C(k), (h) => step(k, h), hints(step)[1]),
        hints(step)[0],
      ),
    );
  const rec = (A, base, step, n) => ind(() => A, base, step, n);
  const J = (A, C, base, a, c, p) =>
    call(
      "path_induction",
      A,
      lam(
        A,
        (x) =>
          lam(
            A,
            (y) =>
              lam(binary("=", x, y), (q) => C(x, y, q), hints(C)[2] ?? "path"),
            hints(C)[1],
          ),
        hints(C)[0],
      ),
      lam(A, base),
      a,
      c,
      p,
    );
  const transport = (A, C, x, y, p, t) =>
    call(
      J(
        A,
        (x, y) => arr(C(x), C(y)),
        (x) => lam(C(x), (t) => t),
        x,
        y,
        p,
      ),
      t,
    );
  const def = (n, body) => named(body, n, true);
  const b = {
    named: (body, n) => named(body, n),
    k: { verify: () => true, steps: [], stats: () => ({}) },
  };
  const op = () => {
    throw new Error(
      "Kernel instructions are not part of the mathematical source backend.",
    );
  };
  return {
    b,
    op,
    norm: (x) => x,
    app: call,
    N,
    Z,
    U,
    V,
    T,
    tt,
    S,
    one,
    two,
    lam,
    pi,
    arr,
    eq,
    refl,
    not,
    sum,
    L,
    R,
    absurd,
    cases,
    sigma,
    pair,
    split,
    and,
    both,
    ind,
    rec,
    J,
    transport,
    def,
  };
}
export function renderModule() {
  // Recover applications of already declared predicates from the combinators'
  // reconstructed bodies. Match bound variables by scope, never by their names;
  // free parameters become arguments. Only earlier declarations are eligible,
  // preventing recursive definitions and references to later declarations.
  const predicates = declarations
    .flatMap((d, index) => {
      if (!["Divides", "Prime"].includes(d.name)) return [];
      let pattern = d.body;
      const params = [];
      while (pattern.kind === "fun") {
        params.push(pattern.x.id);
        pattern = pattern.body;
      }
      return [{ ...d, index, pattern, params }];
    })
    .reverse();
  function matches(p, n, params, captures, bound = new Map()) {
    if (
      !n ||
      (p.kind !== n.kind && !(p.kind === "var" && params.includes(p.id)))
    )
      return false;
    if (p.kind === "var") {
      if (bound.has(p.id)) return n.kind === "var" && n.id === bound.get(p.id);
      if (params.includes(p.id)) {
        if (captures.has(p.id))
          return matches(captures.get(p.id), n, [], new Map());
        captures.set(p.id, n);
        return true;
      }
      return n.kind === "var" && p.id === n.id;
    }
    if (["fun", "forall", "exists"].includes(p.kind))
      return (
        matches(p.A, n.A, params, captures, bound) &&
        matches(
          p.body,
          n.body,
          params,
          captures,
          new Map(bound).set(p.x.id, n.x.id),
        )
      );
    return Object.entries(p).every(([key, value]) => {
      if (key === "kind") return true;
      if (Array.isArray(value))
        return (
          Array.isArray(n[key]) &&
          value.length === n[key].length &&
          value.every((v, i) => matches(v, n[key][i], params, captures, bound))
        );
      if (value && typeof value === "object")
        return matches(value, n[key], params, captures, bound);
      return value === n[key];
    });
  }

  function render(n, env = new Map(), root = null, level = 0) {
    const currentIndex = declarations.findIndex((d) => d.body === root);
    for (const predicate of predicates) {
      if (predicate.index >= currentIndex) continue;
      const captures = new Map();
      if (
        matches(predicate.pattern, n, predicate.params, captures) &&
        predicate.params.every((id) => captures.has(id))
      ) {
        const args = predicate.params.map((id) =>
          render(captures.get(id), env, root, level),
        );
        return predicate.name + (args.length ? `(${args.join(", ")})` : "");
      }
    }
    if (names.has(n) && n !== root)
      return aliases[names.get(n)] ?? names.get(n);
    if (n.kind === "name") return aliases[n.name] ?? n.name;
    if (n.kind === "number") return String(n.value);
    if (n.kind === "var") {
      if (!env.has(n.id))
        throw new Error("Unbound mathematical variable " + n.hint);
      return env.get(n.id);
    }
    const r = (x) => render(x, env, root, level);
    if (n.kind === "binary")
      return `(${r(n.left)} ${n.operator} ${r(n.right)})`;
    if (n.kind === "pair") return `(${r(n.left)}, ${r(n.right)})`;
    if (["fun", "forall", "exists"].includes(n.kind)) {
      let h = /^[A-Za-z][A-Za-z0-9_]*$/.test(n.x.hint) ? n.x.hint : "ignored";
      const base = h;
      let i = 1;
      while ([...env.values()].includes(h)) h = base + ++i;
      const scope = new Map(env).set(n.x.id, h),
        body = render(n.body, scope, root, level);
      return n.kind === "fun"
        ? `(fun (${h} : ${r(n.A)}) => ${body})`
        : `(${n.kind} ${h} : ${r(n.A)}, ${body})`;
    }
    if (n.kind === "call") {
      const f = r(n.fn),
        args = n.args.map(r);
      if (["add", "mul", "le"].includes(f) && args.length === 2)
        return `(${args[0]} ${{ add: "+", mul: "*", le: "<=" }[f]} ${args[1]})`;
      const pad = "  ".repeat(level + 1),
        end = "  ".repeat(level);
      const fresh = (hint, scope) => {
        let h = /^[A-Za-z][A-Za-z0-9_]*$/.test(hint) ? hint : "ignored";
        const base = h;
        let i = 1;
        while ([...scope.values()].includes(h)) h = base + ++i;
        return h;
      };
      if (f === "induct") {
        const [value, motive, base, step] = n.args;
        const k = fresh(step.x.hint, env),
          scope = new Map(env).set(step.x.id, k),
          h = fresh(step.body.x.hint, scope);
        scope.set(step.body.x.id, h);
        const family = render(
          motive.body,
          new Map(env).set(motive.x.id, k),
          root,
          level,
        );
        return `induction ${render(value, env, root, level)} as ${k} return ${family} {\n${pad}zero => ${render(base, env, root, level + 1)};\n${pad}succ ${h} => ${render(step.body.body, scope, root, level + 1)};\n${end}}`;
      }
      if (f === "cases") {
        const [value, C, l, r] = n.args,
          x = fresh(l.x.hint, env),
          y = fresh(r.x.hint, env);
        return `match ${render(value, env, root, level)} return ${render(C, env, root, level)} {\n${pad}left ${x} => ${render(l.body, new Map(env).set(l.x.id, x), root, level + 1)};\n${pad}right ${y} => ${render(r.body, new Map(env).set(r.x.id, y), root, level + 1)};\n${end}}`;
      }
      if (f === "unpack") {
        const [value, C, fn] = n.args,
          x = fresh(fn.x.hint, env),
          scope = new Map(env).set(fn.x.id, x),
          y = fresh(fn.body.x.hint, scope);
        scope.set(fn.body.x.id, y);
        return `unpack ${render(value, env, root, level)} as (${x}, ${y}) return ${render(C, env, root, level)} {\n${pad}${render(fn.body.body, scope, root, level + 1)};\n${end}}`;
      }
      if (["path_induction"].includes(f)) {
        const pad = "  ".repeat(level + 1),
          end = "  ".repeat(level);
        return `${f}(\n${n.args.map((a) => pad + render(a, env, root, level + 1)).join(",\n")}\n${end})`;
      }
      return `${f}(${args.join(", ")})`;
    }
    throw new Error("Unknown mathematical node " + n.kind);
  }
  const header =
    "// Constructive arithmetic and prime numbers. Every definition below is checked from source.\n// No axioms and no imported instruction snapshots.\n\n";
  return (
    header +
    declarations
      // Euclid's statement and proof belong to euclid.proof. This module
      // supplies only the reusable arithmetic and prime-number dependencies.
      .filter(
        (d) =>
          !["InfinitelyManyPrimes", "infinitely_many_primes"].includes(d.name),
      )
      .map((d) => {
        let body = d.body,
          scope = new Map(),
          params = [];
        while (body.kind === "fun") {
          let h = /^[A-Za-z][A-Za-z0-9_]*$/.test(body.x.hint)
            ? body.x.hint
            : "ignored";
          const base = h;
          let i = 1;
          while ([...scope.values()].includes(h)) h = base + ++i;
          params.push(`${h} : ${render(body.A, scope, d.body, 1)}`);
          scope.set(body.x.id, h);
          body = body.body;
        }
        return `${d.theorem ? "theorem" : "def"} ${aliases[d.name] ?? d.name}${params.length ? "(" + params.join(", ") + ")" : ""} =\n  ${render(body, scope, d.body, 1)};\n`;
      })
      .join("\n") +
    "\ndef isLt(n : Nat, p : Nat) = le(succ(n), p);\n"
  );
}
