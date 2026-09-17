import { Kernel, catalogue } from "./kernel.mjs";
import { parse, formatStep, demo } from "./language.mjs";

// Accepted actions form a revision tree. Preview uses a separate replayed engine.
// No kernel cloning, unchecked publication, or accepted-node rollback is assumed.
export class Session {
  constructor(module, allowAxioms = false) {
    this.allowAxioms = allowAxioms;
    this.module = module;
    this.metadata = catalogue(module);
    this.serial = 0;
    this.revision = 0;
    this.revisions = new Map([
      [0, { id: 0, parent: null, title: "Empty proof", steps: [] }],
    ]);
    this.engine = new Kernel(module, allowAxioms);
    this.draft = null;
    this.events = [];
  }
  dispose() {
    this.discard();
    this.engine.dispose();
  }
  discard() {
    if (this.draft) this.draft.engine.dispose();
    this.draft = null;
  }
  program(revision = this.revision) {
    const chain = [];
    let r = this.revisions.get(revision);
    if (!r) throw new Error("Unknown history revision.");
    while (r) {
      chain.push(r.steps);
      r = r.parent === null ? null : this.revisions.get(r.parent);
    }
    return chain.reverse().flat();
  }
  replay(steps, allowAxioms = this.allowAxioms) {
    const engine = new Kernel(this.module, allowAxioms);
    try {
      for (const step of steps) engine.apply(step);
      return engine;
    } catch (e) {
      engine.dispose();
      throw e;
    }
  }
  event(type, info = {}) {
    this.events.push({
      type,
      revision: this.revision,
      time: new Date().toISOString(),
      ...info,
    });
    if (this.events.length > 100) this.events.shift();
  }
  preview(steps, title = "Proof action") {
    this.discard();
    if (!Array.isArray(steps) || !steps.length)
      throw new Error("Enter at least one instruction.");
    const accepted = this.program();
    if (accepted.length + steps.length > 4096)
      throw new Error("Session limit: 4096 instructions.");
    const start = performance.now(),
      engine = this.replay(accepted),
      normalized = [];
    try {
      for (const step of steps) normalized.push(engine.apply(step));
      const token = ++this.serial,
        result = engine.inspect(normalized.at(-1).name);
      this.draft = {
        token,
        base: this.revision,
        engine,
        steps: normalized,
        title,
      };
      const preview = {
        token,
        result,
        steps: normalized,
        source: normalized.map(formatStep).join("\n"),
        milliseconds: performance.now() - start,
        stats: engine.stats(),
      };
      this.event("preview", {
        operation: normalized.at(-1).op,
        accepted: true,
      });
      return preview;
    } catch (e) {
      engine.dispose();
      this.event("preview", { accepted: false, message: e.message });
      throw e;
    }
  }
  previewSource(source, title = "Source instructions") {
    this.discard();
    return this.preview(parse(source, this.metadata), title);
  }
  previewFocus({ name, side, path, operation, witness, resultName }) {
    this.discard();
    const binding = this.engine.bindings.get(name);
    if (!binding || binding.kind !== "judgement")
      throw new Error("Select a judgement first.");
    if (
      !["expression", "type"].includes(side) ||
      !Array.isArray(path) ||
      path.length > 256 ||
      !path.every((n) => Number.isInteger(n) && n >= 0 && n <= 3)
    )
      throw new Error("Invalid selection path.");
    if (
      ![
        "BetaReducePointed",
        "DefReducePointed",
        "BetaReduceGrossKnuth",
        "HighSubs",
      ].includes(operation)
    )
      throw new Error("Unsupported focused action.");
    const steps = [];
    let counter = 1;
    const fresh = () => {
      let s;
      do {
        s = `focus_${counter++}`;
      } while (
        this.engine.bindings.has(s) ||
        steps.some((x) => x.name === s) ||
        s === resultName
      );
      return s;
    };
    const add = (op, args) => {
      const n = fresh();
      steps.push({ name: n, op, args, context: null, free: [], hidden: true });
      return n;
    };
    let current = add(side === "type" ? "HighType" : "HighExp", [name]);
    for (const child of path) current = add(`High${child}`, [current]);
    current = add(
      operation,
      operation === "HighSubs" ? [current, witness] : [current],
    );
    const output = resultName || fresh();
    steps.push({
      name: output,
      op: "UnHigh",
      args: [current],
      context: null,
      free: [],
      hidden: false,
    });
    return this.preview(
      steps,
      `${operation} on ${name}.${side}${path.map((x) => "." + x).join("")}`,
    );
  }
  accept(token) {
    if (
      !this.draft ||
      this.draft.token !== token ||
      this.draft.base !== this.revision
    )
      throw new Error("This preview is stale. Preview the action again.");
    if (this.revisions.size >= 257)
      throw new Error(
        "History limit: export the current proof and start a new session.",
      );
    const d = this.draft;
    this.draft = null;
    this.engine.dispose();
    this.engine = d.engine;
    const id = ++this.serial;
    this.revisions.set(id, {
      id,
      parent: this.revision,
      title: d.title,
      steps: d.steps,
    });
    this.revision = id;
    this.event("accept", { steps: d.steps.length });
    return this.snapshot();
  }
  checkout(id) {
    const engine = this.replay(this.program(id));
    this.discard();
    this.engine.dispose();
    this.engine = engine;
    this.revision = id;
    this.event("checkout");
    return this.snapshot();
  }
  undo() {
    const parent = this.revisions.get(this.revision).parent;
    return parent === null ? this.snapshot() : this.checkout(parent);
  }
  snapshot() {
    return {
      revision: this.revision,
      allowAxioms: this.allowAxioms,
      bindings: [...this.engine.bindings].map(([name, b]) => ({ name, ...b })),
      stats: this.engine.stats(),
      history: [...this.revisions.values()].map(
        ({ id, parent, title, steps }) => ({
          id,
          parent,
          title,
          count: steps.length,
        }),
      ),
      source: this.program().map(formatStep).join("\n"),
      events: [...this.events],
    };
  }
  inspect(name, options) {
    return this.engine.inspect(name, options);
  }
  verify(proposition, proof) {
    return this.engine.verify(proposition, proof);
  }
  export() {
    return {
      format: "thth-workbench",
      version: 1,
      policy: { allowAxioms: this.allowAxioms },
      steps: this.program(),
    };
  }
  // Bundled Open actions may adopt the displayed policy. Ordinary imports
  // require a matching policy; neither path publishes before replay succeeds.
  import(document, adoptPolicy = false) {
    if (
      !document ||
      document.format !== "thth-workbench" ||
      document.version !== 1 ||
      typeof document.policy?.allowAxioms !== "boolean" ||
      (!adoptPolicy && document.policy.allowAxioms !== this.allowAxioms) ||
      !Array.isArray(document.steps) ||
      document.steps.length > 4096
    )
      throw new Error(
        "Unsupported proof file or axiom policy. Enable axioms explicitly before importing a proof that uses them.",
      );
    // Validate fully before replacing the live proof, including failed imports.
    const engine = this.replay(document.steps, document.policy.allowAxioms);
    this.discard();
    this.engine.dispose();
    this.engine = engine;
    this.allowAxioms = document.policy.allowAxioms;
    this.revision = ++this.serial;
    this.revisions = new Map([
      [0, { id: 0, parent: null, title: "Empty proof", steps: [] }],
      [
        this.revision,
        {
          id: this.revision,
          parent: 0,
          title: "Imported proof",
          steps: engine.steps,
        },
      ],
    ]);
    this.events = [];
    this.event("import");
    return this.snapshot();
  }
  setPolicy(allowAxioms) {
    if (typeof allowAxioms !== "boolean")
      throw new Error("Invalid axiom policy.");
    const engine = new Kernel(this.module, allowAxioms);
    try {
      for (const step of this.program()) engine.apply(step);
    } catch (e) {
      engine.dispose();
      throw e;
    }
    this.discard();
    this.engine.dispose();
    this.engine = engine;
    this.allowAxioms = allowAxioms;
    this.event("policy", { allowAxioms });
    return this.snapshot();
  }
  loadDemo() {
    const p = this.previewSource(demo, "Identity and nested application");
    return this.accept(p.token);
  }
}
