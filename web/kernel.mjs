// Versioned scalar ABI. No JS views into growable WASM memory are retained.
export class Kernel {
  constructor(module, allowAxioms = false) {
    this.module = module;
    this.handle = module._wb_new(Number(allowAxioms));
    if (!this.handle) throw new Error("Unable to allocate a proof engine.");
    this.bindings = new Map();
    this.steps = [];
    this.metadata = catalogue(module);
  }
  dispose() {
    if (this.handle) this.module._wb_free(this.handle);
    this.handle = 0;
  }
  resolve(name, kind, optional = false) {
    if (optional && name === null) return 0;
    const binding = this.bindings.get(name);
    if (!binding || binding.kind !== kind)
      throw new Error(`Expected ${kind} binding: ${String(name)}`);
    return binding.id;
  }
  apply(input) {
    const step = validateStep(input, this.metadata);
    if (this.bindings.has(step.name))
      throw new Error(`Name already exists: ${step.name}`);
    const meta = this.metadata.find((m) => m.name === step.op);
    const js = step.args.map((n) => this.resolve(n, "judgement"));
    const ctx = meta.context ? this.resolve(step.context, "context") : 0;
    if (step.fresh) {
      const type = this.module._wb_view(this.handle, 0, js[0], 0);
      let previous = null,
        counter = -1;
      for (const [name, b] of this.bindings)
        if (b.kind === "context") {
          if (this.module._wb_view(this.handle, 1, b.id, 0) === type) {
            const n = this.module._wb_view(this.handle, 1, b.id, 2);
            if (n > counter) {
              previous = name;
              counter = n;
            }
          }
        }
      step.free = [previous];
      delete step.fresh;
    }
    const fs = step.free.map((n) => this.resolve(n, "context", true));
    const status = this.module._wb_apply(
      this.handle,
      meta.code,
      ...Array.from({ length: 5 }, (_, i) => js[i] || 0),
      ctx,
      ...Array.from({ length: 4 }, (_, i) => fs[i] || 0),
    );
    if (status) {
      const reason =
        [
          "OK",
          "The rule premises do not satisfy the kernel checks.",
          "The engine resource limit was reached.",
          "The engine ran out of memory.",
        ][status] || "Kernel failure.";
      const err = new Error(`${step.name}: ${meta.name} rejected. ${reason}`);
      err.details = {
        status,
        operation: meta.name,
        line: step.line,
        premises: step.args.map((name) => ({ name, ...this.inspect(name) })),
        contexts: [step.context, ...step.free].filter(Boolean),
      };
      throw err;
    }
    this.bindings.set(step.name, {
      id: this.module._wb_result(this.handle),
      kind: meta.returnsContext ? "context" : "judgement",
      hidden: step.hidden,
    });
    this.steps.push(step);
    return step;
  }
  node(id) {
    const m = this.module,
      h = this.handle;
    return {
      id,
      kind: m.UTF8ToString(m._wb_node_name(h, id)),
      parameter: m._wb_node(h, id, 1),
      size: m._wb_node(h, id, 3),
      depth: m._wb_node(h, id, 4),
      children: Array.from({ length: m._wb_node(h, id, 2) }, (_, i) =>
        m._wb_node(h, id, 5 + i),
      ),
      reducible: !!m._wb_node(h, id, 9),
      unfoldable: !!m._wb_node(h, id, 10),
    };
  }
  tree(id, budget = { left: 350 }, depth = 0) {
    if (!id) return null;
    if (--budget.left < 0 || depth > 40)
      return { id, kind: "…", children: [], truncated: true };
    const n = this.node(id);
    return {
      ...n,
      children: n.children.map((c) => this.tree(c, budget, depth + 1)),
    };
  }
  list(id, path = false) {
    const result = [];
    for (let n = id; n && result.length < 1024; ) {
      const item = this.node(n);
      result.push(item.parameter);
      n = item.children[0];
    }
    return path
      ? result
      : result.map((c) => {
          const names = [...this.bindings]
            .filter(([, b]) => b.kind === "context" && b.id === c)
            .map(([name]) => name);
          return { id: c, names };
        });
  }
  inspect(name) {
    const b = this.bindings.get(name);
    if (!b) throw new Error(`Unknown binding: ${name}`);
    const context = b.kind === "context",
      get = (f) => this.module._wb_view(this.handle, Number(context), b.id, f);
    return {
      name,
      ...b,
      contextNames: Object.fromEntries(
        [...this.bindings]
          .filter(([, value]) => value.kind === "context")
          .map(([label, value]) => [value.id, label]),
      ),
      expression: context ? null : this.tree(get(0)),
      type: this.tree(get(context ? 0 : 1)),
      assumptions: this.list(get(context ? 1 : 2)),
      counter: context ? get(2) : null,
      focus: context
        ? null
        : {
            side: get(4) === 1 ? "expression" : get(4) === 2 ? "type" : null,
            path: this.list(get(3), true),
          },
    };
  }
  stats() {
    return Object.fromEntries(
      ["calls", "cacheHits", "nodes", "judgements", "contexts", "bytes"].map(
        (key, i) => [key, this.module._wb_stats(this.handle, i)],
      ),
    );
  }
  verify(proposition, proof) {
    return !!this.module._wb_verify(
      this.handle,
      this.resolve(proposition, "judgement"),
      this.resolve(proof, "judgement"),
    );
  }
}
export function catalogue(module) {
  const result = [];
  for (let code = 0; code < 204; code++) {
    const count = module._wb_meta(code, 0);
    if (count >= 0)
      result.push({
        code,
        name: module.UTF8ToString(module._wb_name(code)),
        judgements: count,
        context: !!module._wb_meta(code, 1),
        free: module._wb_meta(code, 2),
        returnsContext: !!module._wb_meta(code, 3),
      });
  }
  return result;
}
export function validateStep(s, metadata) {
  if (
    !s ||
    typeof s !== "object" ||
    !/^[A-Za-z][A-Za-z0-9_]*$/.test(s.name || "") ||
    typeof s.name !== "string"
  )
    throw new Error("Each instruction needs a valid result name.");
  const meta = metadata.find((m) => m.name === s.op);
  if (!meta) throw new Error(`Unknown operation: ${String(s.op)}`);
  const ref = (x) => typeof x === "string" && /^[A-Za-z][A-Za-z0-9_]*$/.test(x);
  if (
    !Array.isArray(s.args) ||
    s.args.length !== meta.judgements ||
    !s.args.every(ref)
  )
    throw new Error(
      `${meta.name} requires ${meta.judgements} judgement arguments.`,
    );
  const context = s.context ?? null,
    free = s.free ?? Array(meta.free).fill(null);
  if (meta.context ? !ref(context) : context !== null)
    throw new Error(`${meta.name}: incorrect context argument.`);
  if (
    !Array.isArray(free) ||
    free.length !== meta.free ||
    !free.every((x) => x === null || ref(x))
  )
    throw new Error(
      `${meta.name} requires ${meta.free} optional context slots.`,
    );
  if (s.fresh && meta.name !== "CtxExt")
    throw new Error("Only assume can request a fresh context.");
  return {
    name: s.name,
    op: meta.name,
    args: [...s.args],
    context,
    free: [...free],
    hidden: s.hidden === true,
    ...(s.fresh ? { fresh: true } : {}),
    ...(Number.isSafeInteger(s.line) && s.line > 0 ? { line: s.line } : {}),
  };
}
