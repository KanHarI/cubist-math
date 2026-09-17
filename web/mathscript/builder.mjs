import { Kernel } from "../kernel.mjs";
import library from "../proofs/library.mjs";

// A proof-producing metaprogram: every construction and conversion is a public
// checked instruction. JavaScript only chooses premises and fresh names.
export class Builder {
  constructor(module, { loadLibrary = true, allowAxioms = loadLibrary } = {}) {
    this.k = new Kernel(module, allowAxioms);
    if (loadLibrary) for (const s of library.steps) this.k.apply(s);
    this.serial = 0;
    this.normal = new Map();
    this.boxedDefinitions = new Set();
  }
  emit(op, args = [], free = [], context = null, name = null) {
    if (this.maxSteps && this.k.steps.length >= this.maxSteps)
      throw new Error(
        `Compiled mathematical proof exceeds ${this.maxSteps} instructions.`,
      );
    name ??= `p${++this.serial}_${op}`;
    try {
      this.k.apply({ name, op, args, free, context });
    } catch (e) {
      console.error(
        op,
        args.map((n) => ({
          name: n,
          expr: this.view(n, 0),
          type: this.view(n, 1),
        })),
        free,
      );
      throw new Error(e.message);
    }
    if (this.progress && (this.k.steps.length & 1023) === 0) this.progress();
    return name;
  }
  view(name, field) {
    return this.k.module._wb_view(
      this.k.handle,
      0,
      this.k.bindings.get(name).id,
      field,
    );
  }
  norm(a) {
    const key = `${this.opaque ? "beta" : "defs"}:${this.k.bindings.get(a).id}`;
    if (this.normal.has(key)) return this.normal.get(key);
    for (let i = 0; i < 100; i++) {
      const b = this.emit(
        this.opaque ? "BetaReduceGrossKnuth" : "DefBetaReduceGrossKnuth",
        [a],
      );
      if (
        this.view(a, 0) === this.view(b, 0) &&
        this.view(a, 1) === this.view(b, 1)
      ) {
        this.normal.set(key, b);
        return b;
      }
      a = b;
    }
    throw new Error("Normalization did not converge");
  }
  fresh(A, name = null) {
    const c = name ? name + "_context" : `p${++this.serial}_context`;
    this.k.apply({
      name: c,
      op: "CtxExt",
      args: [A],
      free: [null],
      context: null,
      fresh: true,
    });
    return { A, c, v: this.emit("Vble", [], [], c, name) };
  }
  lam(A, fn) {
    const x = this.fresh(A);
    return this.emit("PiIntro", [A, fn(x.v)], [x.c]);
  }
  pi(A, fn) {
    const x = this.fresh(A);
    return this.emit("PiForm", [A, fn(x.v)], [x.c]);
  }
  arrow(A, B) {
    return this.emit("PiForm", [A, B], [null]);
  }
  app(f, ...args) {
    for (const a of args)
      f = this.norm(this.emit("PiElim", [this.norm(f), this.norm(a)]));
    return f;
  }
  eq(A, x, y) {
    return this.emit("EqForm", [A, x, y]);
  }
  refl(x) {
    return this.emit("EqIntro", [x]);
  }
  // Conversion is explicit: retain target === normal(target), then rewrite the
  // already normalized term's type back to the requested (possibly redex) type.
  coerce(term, T) {
    term = this.norm(term);
    if (this.view(term, 1) === this.view(T, 0)) return term;
    const tn = this.norm(T);
    if (this.view(term, 1) !== this.view(tn, 0)) {
      throw new Error("Conversion types differ");
    }
    let witness = this.emit("HighExp", [this.emit("DefEqRefl", [T])]);
    witness = this.emit("High1", [witness]);
    for (let i = 0; i < 100; i++) {
      const b = this.emit(
        this.opaque ? "BetaReduceGrossKnuth" : "DefBetaReduceGrossKnuth",
        [witness],
      );
      if (this.view(b, 0) === this.view(witness, 0)) {
        witness = b;
        break;
      }
      witness = b;
    }
    witness = this.emit("DefEqSwp", [witness]);
    return this.emit("UnHigh", [
      this.emit("HighSubs", [this.emit("HighType", [term]), witness]),
    ]);
  }
  // Definition-aware conversion reduces the TYPE of the proof, never the
  // proof body itself. A highlighted equality witness restores the original
  // named target type after comparison, preserving boxed theorem terms.
  coerceDefinitions(term, T) {
    if (!this.boxedDefinitions.size) throw new Error("Conversion types differ");
    const findDefinition = (id, seen = new Set()) => {
      if (this.boxedDefinitions.has(id)) return [];
      if (seen.has(id)) return null;
      seen.add(id);
      const node = this.k.node(id);
      for (let i = 0; i < node.children.length; i++) {
        const path = findDefinition(node.children[i], seen);
        if (path) return [i, ...path];
      }
      return null;
    };
    const reduceAt = (binding, side, path = []) => {
      let current = binding;
      for (let i = 0; i < 4096; i++) {
        current = this.emit(side ? "HighType" : "HighExp", [current]);
        for (const child of path) current = this.emit(`High${child}`, [current]);
        const beta = this.emit("BetaReduceGrossKnuth", [current]);
        if (this.view(beta, side) !== this.view(current, side)) {
          current = beta;
          continue;
        }
        current = beta;
        let root = this.view(current, side);
        for (const child of path) root = this.k.node(root).children[child];
        const next = findDefinition(root);
        if (!next) return this.emit("UnHigh", [current]);
        for (const child of next) current = this.emit(`High${child}`, [current]);
        current = this.emit("DefReducePointed", [current]);
      }
      throw new Error("Definition conversion did not converge");
    };
    const converted = reduceAt(term, 1),
      target = reduceAt(T, 0);
    if (this.view(converted, 1) !== this.view(target, 0))
      throw new Error("Conversion types differ");
    const witness = reduceAt(this.emit("DefEqRefl", [T]), 0, [1]);
    return this.emit("UnHigh", [
      this.emit("HighSubs", [
        this.emit("HighType", [converted]),
        this.emit("DefEqSwp", [witness]),
      ]),
    ]);
  }
  subst(body, x, value) {
    return this.emit("DefEqExtR", [this.emit("PiComp", [body, value], [x.c])]);
  }
  named(a, name) {
    return this.emit(
      "DefEqExtR",
      [this.emit("DefEqRefl", [a])],
      [],
      null,
      name,
    );
  }
}
