// Observations belong to elaboration attempts, independently of fuel/work
// accounting. A selected child still belongs to its pending parent: rejecting
// that parent drops every nested reference, proof step and scope point.
const kinds = new Set(["reference", "step", "scope"]);

export class ObservationFrame {
  #sinks;
  #parent;
  #state;
  #events = [];
  #next = 0;
  #visible;

  constructor(sinks = {}, parent = null, path = [], visible = true) {
    this.#sinks = parent ? parent.#sinks : Object.freeze({...sinks});
    this.#parent = parent;
    this.#state = parent ? "pending" : "selected";
    this.#visible = visible;
    this.path = Object.freeze(path);
    Object.freeze(this);
  }

  get outcome() {
    const enclosing = this.#parent?.outcome;
    if (enclosing === "discarded" || this.#state === "discarded") return "discarded";
    if (enclosing === "pending") return "pending";
    return this.#state;
  }

  #live() {
    if (this.outcome === "discarded") throw Error("Cannot observe a discarded elaboration attempt.");
  }

  enabled(kind, sink = this.#sinks[kind]) {
    if (!kinds.has(kind)) throw Error(`Unknown elaboration observation: ${kind}.`);
    return this.#visible && (this.#parent ? this.#parent.enabled(kind,sink) : typeof sink === "function");
  }

  record(kind, ...values) {
    this.recordTo(kind,this.#sinks[kind],...values);
  }

  // A derived source unit can mask or replace a consumer without changing
  // the attempt that owns its effects. Keep that consumer with the event.
  recordTo(kind, sink, ...values) {
    this.#live();
    if (!this.enabled(kind,sink)) return;
    if (this.#state === "pending") this.#events.push({kind, sink, values});
    else if (this.#parent) this.#parent.recordTo(kind,sink,...values);
    else sink(...values);
  }

  // Allocate paths even with collection disabled. Turning an observer on must
  // not change the identity of the elaboration instance it observes.
  fork(kind, {visible = true} = {}) {
    this.#live();
    return new ObservationFrame({}, this, [...this.path, Object.freeze({kind, index:this.#next++})], visible);
  }

  select() {
    this.#live();
    if (this.#state !== "pending") throw Error("An elaboration attempt can be selected only once.");
    this.#state = "selected";
    const events = this.#events;
    this.#events = [];
    for (const {kind, sink, values} of events) this.#parent.recordTo(kind,sink,...values);
  }

  discard() {
    if (this.#state !== "pending") throw Error("Only a pending elaboration attempt can be discarded.");
    this.#state = "discarded";
    this.#events = [];
  }

  // A declaration has its own attempt numbering but shares the module's
  // observation consumers. The declaration owner qualifies these paths.
  declaration() {
    if (this.#parent) throw Error("A declaration must start at the module observation root.");
    return new ObservationFrame(this.#sinks);
  }
}
