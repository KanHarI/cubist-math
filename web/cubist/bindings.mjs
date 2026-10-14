// Frontend identities are data, separate from both public labels and live
// elaboration values. A revision is supplied by the compilation which owns
// the source/import snapshot; replay uses that same revision and owner path.
const roles = new Set(["declaration", "local", "parameter", "universe", "dimension", "field", "helper", "pattern", "activation", "capture"]);
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
    const {kind, site, binding} = frame;
    string(kind, "an expansion kind");
    if (site?.expansion?.length) throw new TypeError("An expansion site cannot contain an origin graph.");
    return Object.freeze({kind, site: sourceOrigin(site),
      ...(binding===undefined?{}:{binding:string(binding,"an expansion binding identity")})});
  }))});
}

// Expansion frames are ordered from the authored definition out to the
// written request. Keep an already-expanded site's path as the outer path,
// without embedding a recursive origin graph in a frame.
export function expandedOrigin(origin,{kind,site,binding}) {
  return sourceOrigin({...origin,expansion:[...origin.expansion,
    {kind,site:sourceOrigin({...site,expansion:[]}),...(binding===undefined?{}:{binding})},...site.expansion]});
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
  freshen(owned, owner, {expansion}={}) {
    owned = [...owned]; owner = path(owner);
    const records = owned.map(id => this.get(id));
    if (new Set(owned).size !== records.length) throw new TypeError("A binding is owned twice.");
    const correspondence = new Map();
    for (const record of records) correspondence.set(record.id,
      this.allocate(owner, {...record, original: record.original ?? record.id,
        ...(expansion?{origin:expandedOrigin(record.origin,expansion)}:{})}).id);
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
export const slotResolution = (id, enclosing,fields=[]) => Object.freeze({tag: "slot", id: string(id, "a slot identity"), enclosing: resolution(enclosing),
  ...(fields.length?{fields:Object.freeze(fields.map(label=>string(label,"a slot member label")))}:{})});
export const memberResolution=(receiver,fields)=>fields.length?Object.freeze({tag:"member",receiver:resolution(receiver),
  fields:Object.freeze(fields.map(label=>string(label,"a member label")))}):resolution(receiver);
export const openingResolution=(id,label,enclosing,candidates=[])=>Object.freeze({tag:"opening",id:string(id,"an activation identity"),
  label:string(label,"an opened occurrence"),enclosing:resolution(enclosing),
  ...(candidates.length?{candidates:Object.freeze(candidates.map(resolution))}:{})});
export const projectedResolution=(projection,receiver)=>Object.freeze({tag:"projected",
  projection:string(projection,"a projection identity"),receiver:string(receiver,"a receiver identity")});
export const failedResolution=({message,namespace,member,description,origin})=>Object.freeze({tag:"failure",
  message:string(message,"a resolution failure"),...(namespace===undefined?{}:{namespace,member,description}),
  ...(origin?{origin:sourceOrigin(origin)}:{})});
const openingFrame=(id,candidates=[])=>Object.freeze({tag:"opening-frame",id:string(id,"an activation identity"),
  ...(candidates.length?{candidates:Object.freeze(candidates.map(([label,value])=>
    Object.freeze([string(label,"an interface candidate"),resolution(value)])))}:{})});
// A qualified namespace closes its member table. Its bare label can keep
// an enclosing value, but an absent member never searches that value's
// ambient namespace. Ordinary later bindings still shadow the whole entry.
export const namespaceResolution=(members,fallback,description)=>Object.freeze({tag:"namespace",
  members:Object.freeze([...members].map(([label,value])=>Object.freeze([string(label,"an interface member"),resolution(value)]))),
  fallback:resolution(fallback),description:string(description,"an interface description")});
// After source resolution the occurrences carry their own candidates. The
// selector only needs to decide that this branch selected that namespace.
export const namespaceSelectorResolution=()=>Object.freeze({tag:"namespace-selector"});
export class UnknownNamespaceMember extends TypeError {
  constructor(namespace,member,description,message="Unknown member of a resolved interface namespace.") {
    super(message);
    Object.assign(this,{namespace,member,description});
  }
}
export function resolutionError(value) {
  const error=value.namespace===undefined?Error(value.message)
    :new UnknownNamespaceMember(value.namespace,value.member,value.description,value.message);
  if(value.origin)Object.assign(error,{origin:value.origin,offset:value.origin.start,sourceEnd:value.origin.end});
  return error;
}
export function resolution(value) {
  switch (value?.tag) {
    case "binding": return bindingResolution(value.id);
    case "missing": return missingResolution(value.label);
    case "reserved": return reservedResolution(value.label);
    case "slot": return slotResolution(value.id, value.enclosing,value.fields);
    case "opening": return openingResolution(value.id,value.label,value.enclosing,value.candidates);
    case "opening-frame": return openingFrame(value.id,value.candidates);
    case "member": return memberResolution(value.receiver,value.fields);
    case "projected": return projectedResolution(value.projection,value.receiver);
    case "failure": return failedResolution(value);
    case "namespace": return namespaceResolution(value.members,value.fallback,value.description);
    case "namespace-selector":return namespaceSelectorResolution();
    default: throw new TypeError("Invalid lexical resolution.");
  }
}

// One identity traversal covers nested fallbacks, namespaces and structural
// targets. Cloning, correspondence, validation and alpha comparison use it;
// none may silently leave an identity hidden in a new resolution variant.
export function mapResolution(value,identity=id=>id,project=value=>value) {
  const map=value=>mapResolution(value,identity,project);
  let mapped;
  switch(value.tag) {
    case "binding":mapped={...value,id:identity(value.id,value.tag)};break;
    case "opening-frame":mapped={...value,id:identity(value.id,value.tag),
      ...(value.candidates?{candidates:value.candidates.map(([label,value])=>[label,map(value)])}:{})};break;
    case "slot": case "opening":mapped={...value,id:identity(value.id,value.tag),enclosing:map(value.enclosing),
      ...(value.candidates?{candidates:value.candidates.map(map)}:{})};break;
    case "member":mapped={...value,receiver:map(value.receiver)};break;
    case "projected":mapped={...value,projection:identity(value.projection,"projection"),receiver:identity(value.receiver,"receiver")};break;
    case "namespace":mapped={...value,fallback:map(value.fallback),members:value.members.map(([label,value])=>[label,map(value)])};break;
    case "missing": case "reserved": case "failure": case "namespace-selector":mapped=value;break;
    default:throw new TypeError("Invalid lexical resolution.");
  }
  return project(mapped);
}

// Immutable ordered source scope. Live terms, checker maps, native handles
// and constructor tables never belong in this description.
export class LexicalContext {
  #head = null;
  constructor(entries = []) {
    for (const [label, value] of entries) this.#head = Object.freeze({
      label: label===null&&value.tag==="opening-frame"?null:string(label, "a lexical label"), value: resolution(value), parent: this.#head});
    Object.freeze(this);
  }
  lookup(label) {
    for (let entry = this.#head; entry; entry = entry.parent) {
      if(entry.value.tag==="opening-frame")return this.#opened(entry.value,label,this.#lookupAfter(entry.parent,label,false).value);
      if (entry.label === label) return entry.value.tag==="namespace"?entry.value.fallback:entry.value;
    }
    return missingResolution(label);
  }
  qualified(name) {
    return this.#lookupAfter(this.#head,name,true);
  }
  // An explicit selection can name an interface namespace. Its ordinary
  // bare-value fallback has a different meaning, including under a deferred
  // pattern or model opening, so it cannot be reused for this lookup.
  selector(name) {return this.#lookupAfter(this.#head,name,true,true);}
  #opened(frame,name,enclosing) {
    const [root,...fields]=name.split(".");
    const candidates=(frame.candidates??[]).filter(([label])=>label===root)
      .map(([,value])=>memberResolution(value,fields));
    return openingResolution(frame.id,name,enclosing,candidates);
  }
  #lookupAfter(head,name,qualified,selector=false) {
    // Ordered shadowing applies to a receiver too: a later local T hides
    // an earlier declaration T.f. Member labels are resolved on that receiver.
    for (let entry = head; entry; entry = entry.parent) {
      if(entry.value.tag==="opening-frame") {
        let fallback;
        try {fallback=this.#lookupAfter(entry.parent,name,qualified,selector);}
        catch(error) {
          if(!(error instanceof UnknownNamespaceMember))throw error;
          fallback={value:failedResolution(error),fields:[]};
        }
        return {value:this.#opened(entry.value,name,memberResolution(fallback.value,fallback.fields)),fields:[]};
      }
      if (entry.label === name) {
        if(selector&&entry.value.tag==="slot") {
          const fallback=this.#lookupAfter(entry.parent,name,qualified,true);
          return {value:slotResolution(entry.value.id,memberResolution(fallback.value,fallback.fields)),fields:[]};
        }
        return {value:entry.value.tag==="namespace"&&!selector?entry.value.fallback:entry.value,fields:[]};
      }
      if(qualified&&name.startsWith(entry.label+".")&&entry.value.tag==="namespace") {
        const [member,...fields]=name.slice(entry.label.length+1).split(".");
        const found=entry.value.members.find(([label])=>label===member);
        if(!found)throw new UnknownNamespaceMember(entry.label,member,entry.value.description);
        return {value:found[1],fields};
      }
      if(qualified&&name.startsWith(entry.label+".")&&entry.value.tag==="slot") {
        let fallback;
        try {fallback=this.#lookupAfter(entry.parent,name,true,selector);}
        catch(error) {
          if(!(error instanceof UnknownNamespaceMember))throw error;
          fallback={value:failedResolution(error),fields:[]};
        }
        return {value:slotResolution(entry.value.id,memberResolution(fallback.value,fallback.fields),
          name.slice(entry.label.length+1).split(".")),fields:[]};
      }
      if (qualified&&name.startsWith(entry.label + "."))
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
  open(id,{candidates=[]}={}) {
    const context=new LexicalContext();
    context.#head=Object.freeze({label:null,value:openingFrame(id,candidates),parent:this.#head});
    return context;
  }
  namespace(label,members,description) {return this.bind(label,namespaceResolution(members,this.lookup(label),description));}
  introducedAfter(id,boundary) {
    let found=false,entry=this.#head;
    for(;entry&&entry!==boundary.#head;entry=entry.parent)
      if(["binding","slot"].includes(entry.value.tag)&&entry.value.id===id)found=true;
    if(entry!==boundary.#head)throw new TypeError("A namespace scope boundary must enclose the current context.");
    return found;
  }
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
      if ((!['variable','constructor'].includes(outcome)&&!["opening","namespace"].includes(outcome?.kind)) || this.#entries.has(id))
        throw new TypeError("Invalid or repeated slot outcome.");
      const value=outcome?.kind==="opening"?Object.freeze({kind:"opening",members:Object.freeze(outcome.members.map(([label,value])=>
        Object.freeze([string(label,"an opened member"),resolution(value)])))}):outcome?.kind==="namespace"?Object.freeze({kind:"namespace"}):outcome;
      this.#entries.set(id,value);
    }
    Object.freeze(this);
  }
  get(id) {const value=this.#entries.get(id);return typeof value==="string"?value:null;}
  activation(id) {const value=this.#entries.get(id);return ["opening","namespace"].includes(value?.kind)?value:null;}
  activate(id,members) {
    if(this.#entries.has(id))throw new TypeError("An activation has already been resolved in this branch.");
    return new SlotOutcomes([...this.#entries,[id,{kind:"opening",members:[...members]}]]);
  }
  selectNamespace(id) {
    if(this.#entries.has(id))throw new TypeError("An activation has already been resolved in this branch.");
    return new SlotOutcomes([...this.#entries,[id,{kind:"namespace"}]]);
  }
  decide(id, outcome) {
    if (this.#entries.has(id)) throw new TypeError("A slot has already been decided in this branch.");
    return new SlotOutcomes([...this.#entries, [id, outcome]]);
  }
  resolve(value) {
    if(value.tag==="member")return memberResolution(this.resolve(value.receiver),value.fields);
    if(value.tag==="opening") {
      const ready=this.activation(value.id);
      if(!ready)return value;
      if(ready.kind==="namespace") {
        if(value.candidates?.length>1)throw new TypeError("A namespace occurrence needs one unambiguous candidate.");
        return this.resolve(value.candidates?.[0]??value.enclosing);
      }
      const [root,...fields]=value.label.split("."),member=ready.members.find(([label])=>label===root);
      return this.resolve(member?memberResolution(member[1],fields):value.enclosing);
    }
    if (value.tag !== "slot") return value;
    const outcome = this.#entries.get(value.id);
    if (!outcome) return value;
    return outcome === "variable" ? memberResolution(bindingResolution(value.id),value.fields??[]) : this.resolve(value.enclosing);
  }
  snapshot() {return Object.freeze([...this.#entries].map(pair => Object.freeze(pair)));}
}

// Both compiled matches and direct kernel clauses commit through this
// operation. Binding a variable after classifying it is idempotent; an
// inconsistent interpretation in the same branch is an elaborator error.
export function decidePatternSlot(outcomes,token,role) {
  if(token?.bindingRole!=="pattern")return outcomes;
  const previous=outcomes.get(token.bindingId);
  if(previous&&previous!==role)throw new TypeError("A pattern slot changed its interpretation in one branch.");
  return previous?outcomes:outcomes.decide(token.bindingId,role);
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
    mapResolution(value,(id,kind)=>{
      const record=this.#table.get(id);
      if(kind==="slot"&&record.role!=="pattern")throw new TypeError("A slot must name a candidate pattern binding.");
      if(["opening","opening-frame"].includes(kind)&&record.role!=="activation")throw new TypeError("An opening must name a selection activation.");
      return id;
    });
    return outcomes.resolve(value);
  }
  lower(value, outcomes = new SlotOutcomes(), {deferMissing = false} = {}) {
    value = this.resolve(value, outcomes);
    if (["slot","opening","member","projected","namespace","namespace-selector"].includes(value.tag)) return null; // Resolution/selection owns these forms.
    if (value.tag === "missing" && deferMissing) return null;
    if (value.tag === "binding") return this.key(value.id);
    if(value.tag==="failure")throw resolutionError(value);
    if (value.tag === "reserved" && this.#reserved.has(value.label)) return value.label;
    if (value.tag === "missing") throw Error(`Untranslated name: ${value.label}`);
    throw new TypeError(`A late lookup is not allowed: ${value.label}`);
  }
}
