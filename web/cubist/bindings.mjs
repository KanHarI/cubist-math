// Frontend identities are data, separate from both public labels and live
// elaboration values. A revision is supplied by the compilation which owns
// the source/import snapshot; replay uses that same revision and owner path.
const roles = new Set(["declaration", "local", "parameter", "universe", "dimension", "field", "helper", "pattern"]);
const string = (value, description) => {
  if (typeof value !== "string" || !value.length) throw new TypeError(`Expected ${description}.`);
  return value;
};
const path = owner => {
  if (!Array.isArray(owner) || !owner.length) throw new TypeError("Expected a nonempty binding owner path.");
  return Object.freeze(owner.map(part => string(part, "an owner path component")));
};

// An expansion frame names a site, not another origin graph. Authored spans
// remain source-qualified even when several modules contribute an expansion.
export function sourceOrigin({revision, module, start, end, expansion = []}) {
  string(revision, "a source revision"); string(module, "a module name");
  if (!Number.isSafeInteger(start) || !Number.isSafeInteger(end) || start < 0 || end < start)
    throw new TypeError("Invalid source origin span.");
  return Object.freeze({revision, module, start, end, expansion: Object.freeze(expansion.map(frame => {
    const {kind, site} = frame;
    string(kind, "an expansion kind");
    if (site?.expansion?.length) throw new TypeError("An expansion site cannot contain an origin graph.");
    return Object.freeze({kind, site: sourceOrigin(site)});
  }))});
}

export class BindingTable {
  #bindings = new Map();
  #next = new Map();
  constructor(revision) {
    this.revision = string(revision, "a compilation revision");
    Object.freeze(this);
  }
  allocate(owner, {role, label, origin, original = null}) {
    owner = path(owner);
    if (!roles.has(role)) throw new TypeError(`Unknown binding role: ${role}`);
    string(label, "a public binding label");
    if (original !== null) this.get(original);
    const key = JSON.stringify(owner), index = this.#next.get(key) ?? 0;
    const id = JSON.stringify([this.revision, owner, index]);
    const record = Object.freeze({id, owner, role, label, origin: sourceOrigin(origin), original});
    this.#next.set(key, index + 1);
    this.#bindings.set(id, record);
    return record;
  }
  get(id) {
    const record = this.#bindings.get(id);
    if (!record) throw new TypeError(`Unknown binding identity: ${id}`);
    return record;
  }
  // A clone's correspondence is explicit. External identities are omitted
  // from `owned` and remain shared. Merely walking a tree never allocates.
  freshen(owned, owner) {
    owned = [...owned]; owner = path(owner);
    const records = owned.map(id => this.get(id));
    if (new Set(owned).size !== records.length) throw new TypeError("A binding is owned twice.");
    const correspondence = new Map();
    for (const record of records) correspondence.set(record.id,
      this.allocate(owner, {...record, original: record.original ?? record.id}).id);
    return correspondence;
  }
  snapshot() {
    return Object.freeze({version: 1, revision: this.revision, bindings: Object.freeze([...this.#bindings.values()])});
  }
  static restore(snapshot) {
    if (snapshot?.version !== 1 || !Array.isArray(snapshot.bindings)) throw new TypeError("Invalid binding snapshot.");
    const table = new BindingTable(snapshot.revision);
    // Allocation order validates the owner/counter correspondence, including
    // provenance references, instead of accepting arbitrary aliased IDs.
    for (const record of snapshot.bindings) {
      const restored = table.allocate(record.owner, record);
      if (restored.id !== record.id) throw new TypeError("Invalid binding snapshot correspondence.");
    }
    return table;
  }
}

// Resolutions contain only inert data. A deferred slot carries its original
// enclosing resolution, including missing, independently for each occurrence.
export const bindingResolution = id => Object.freeze({tag: "binding", id: string(id, "a binding identity")});
export const missingResolution = label => Object.freeze({tag: "missing", label: string(label, "a missing label")});
export const reservedResolution = label => Object.freeze({tag: "reserved", label: string(label, "a reserved label")});
export const slotResolution = (id, enclosing) => Object.freeze({tag: "slot", id: string(id, "a slot identity"), enclosing: resolution(enclosing)});
export function resolution(value) {
  switch (value?.tag) {
    case "binding": return bindingResolution(value.id);
    case "missing": return missingResolution(value.label);
    case "reserved": return reservedResolution(value.label);
    case "slot": return slotResolution(value.id, value.enclosing);
    default: throw new TypeError("Invalid lexical resolution.");
  }
}

// Immutable ordered source scope. Live terms, checker maps, native handles
// and constructor tables never belong in this description.
export class LexicalContext {
  #head = null;
  constructor(entries = []) {
    for (const [label, value] of entries) this.#head = Object.freeze({
      label: string(label, "a lexical label"), value: resolution(value), parent: this.#head});
    Object.freeze(this);
  }
  lookup(label) {
    for (let entry = this.#head; entry; entry = entry.parent)
      if (entry.label === label) return entry.value;
    return missingResolution(label);
  }
  qualified(name) {
    // Ordered shadowing applies to a receiver too: a later local T hides
    // an earlier declaration T.f. Member labels are resolved on that receiver.
    for (let entry = this.#head; entry; entry = entry.parent) {
      if (entry.label === name) return {value: entry.value, fields: []};
      if (name.startsWith(entry.label + "."))
        return {value: entry.value, fields: name.slice(entry.label.length + 1).split(".")};
    }
    return {value: missingResolution(name), fields: []};
  }
  bind(label, value) {
    const context = new LexicalContext();
    context.#head = Object.freeze({label: string(label, "a lexical label"), value: resolution(value), parent: this.#head});
    return context;
  }
  defer(label, id) {return this.bind(label, slotResolution(id, this.lookup(label)));}
  snapshot() {
    const entries = [];
    for (let entry = this.#head; entry; entry = entry.parent) entries.push(Object.freeze([entry.label, entry.value]));
    return Object.freeze(entries.reverse());
  }
}

// Slot outcomes are per elaboration branch. Resolving a constructor removes
// its candidate binder and selects the saved enclosing resolution. A value
// inserted by substitution has its own resolution, with no such slot edge.
export class SlotOutcomes {
  #entries;
  constructor(entries = []) {
    this.#entries = new Map();
    for (const [id, outcome] of entries) {
      string(id, "a slot identity");
      if (!["variable", "constructor"].includes(outcome) || this.#entries.has(id))
        throw new TypeError("Invalid or repeated slot outcome.");
      this.#entries.set(id, outcome);
    }
    Object.freeze(this);
  }
  decide(id, outcome) {
    if (this.#entries.has(id)) throw new TypeError("A slot has already been decided in this branch.");
    return new SlotOutcomes([...this.#entries, [id, outcome]]);
  }
  resolve(value) {
    if (value.tag !== "slot") return value;
    const outcome = this.#entries.get(value.id);
    if (!outcome) return value;
    return outcome === "variable" ? bindingResolution(value.id) : this.resolve(value.enclosing);
  }
  snapshot() {return Object.freeze([...this.#entries].map(pair => Object.freeze(pair)));}
}

// The only bridge from the new identity representation to the translator's
// private environment keys. It never accepts an ambient spelling resolver.
export class BindingAdapter {
  #table;
  #reserved;
  constructor(table, {reserved = []} = {}) {
    this.#table = table;
    this.#reserved = new Set(reserved);
    Object.freeze(this);
  }
  key(id) {this.#table.get(id); return `\u0000id ${id}`;}
  // Inverse of the adapter's private key, for consumers recording the live
  // context. Public spellings are never interpreted as binding identities.
  bindingForKey(key) {return key.startsWith("\u0000id ")?this.#table.get(key.slice(4)):null;}
  resolve(value, outcomes = new SlotOutcomes()) {
    value = resolution(value);
    for (let at = value; at; at = at.tag === "slot" ? at.enclosing : null) {
      if (at.tag === "binding" || at.tag === "slot") {
        const record = this.#table.get(at.id);
        if (at.tag === "slot" && record.role !== "pattern") throw new TypeError("A slot must name a candidate pattern binding.");
      }
    }
    return outcomes.resolve(value);
  }
  lower(value, outcomes = new SlotOutcomes(), {deferMissing = false} = {}) {
    value = this.resolve(value, outcomes);
    if (value.tag === "slot") return null; // Must wait for the role's type.
    if (value.tag === "missing" && deferMissing) return null;
    if (value.tag === "binding") return this.key(value.id);
    if (value.tag === "reserved" && this.#reserved.has(value.label)) return value.label;
    if (value.tag === "missing") throw Error(`Untranslated name: ${value.label}`);
    throw new TypeError(`A late lookup is not allowed: ${value.label}`);
  }
}
