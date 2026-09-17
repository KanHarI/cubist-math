import { Kernel } from "../../web/kernel.mjs";
import library from "../../web/proofs/library.mjs";

// A proof-producing metaprogram: every construction and conversion is a public
// checked instruction. JavaScript only chooses premises and fresh names.
export class Builder {
  constructor(module) {
    this.k = new Kernel(module, true);
    for (const s of library.steps) this.k.apply(s);
    this.serial = 0;
    this.normal = new Map();
  }
  emit(op, args = [], free = [], context = null, name = null) {
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
      const diff = (x, y, path = []) => {
        if (x === y) return null;
        const a = this.k.node(x),
          c = this.k.node(y);
        if (a.kind !== c.kind || a.parameter !== c.parameter)
          return {
            path,
            a: { kind: a.kind, param: a.parameter, id: x },
            b: { kind: c.kind, param: c.parameter, id: y },
          };
        for (let i = 0; i < a.children.length; i++) {
          const d = diff(a.children[i], c.children[i], [...path, i]);
          if (d) return d;
        }
      };
      console.error(
        "CONVERSION",
        term,
        T,
        diff(this.view(term, 1), this.view(tn, 0)),
      );
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
