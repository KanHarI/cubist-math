// Explicit migration boundary for ordinary binding-aware syntax. Later
// packages move retained theories and goal-dependent blocks through this
// same representation; an unmigrated family is rejected here, not retried
// through nominal capture on failure.
import {scopeMapped, binderName, bindingRole} from "./scopes.mjs";
import {members} from "./references.mjs";
import {sourceOrigin, bindingResolution, SlotOutcomes} from "./bindings.mjs";
import {declarationTelescope, evidenceTelescope, parameterLambdas} from "./telescopes.mjs";
import {syntaxValue,expandedSource} from "./source-syntax.mjs";

const format = "cubist-bindings-1";
// Opt in only after every binder and reference namespace of a family is
// modelled. New parser kinds cannot silently enter nominal lookup paths.
const migrated = new Set(["name", "number", "lambda", "forall", "exists", "binderGroup",
  "pathLambda", "induction", "match", "clause", "pattern", "unpack", "def", "namedArgument", "call", "binary",
  "unary", "pair", "projection", "member", "pathApply", "transport", "lift", "over", "prop", "set",
  "trunc", "typed", "exact", "let", "matchStatement", "rfl", "calc", "rw", "block", "term", "tactic", "hlevel"]);
const freeze = value => {
  if (!value || typeof value !== "object" || Object.isFrozen(value)) return value;
  for (const child of Object.values(value)) freeze(child);
  return Object.freeze(value);
};
const occurrence = (at, value, spelling, origin) => ({kind: "bindingReference", resolution: value, spelling, origin,
  start: at.start, end: at.end});

export function resolveBindingSyntax(tree, options) {
  return resolveBindings(tree,options);
}

// Transitional generated templates own their binders and explicit holes.
// Resolve those binders once; a hole supplies already retained syntax using
// an explicit interface map. Its contents never enter source resolution.
export function resolveBindingTemplate(tree,options,splices) {
  if(!(splices instanceof Map))throw new TypeError("A binding template needs explicit syntax splices.");
  return resolveBindings(tree,options,splices);
}

function resolveBindings(tree, {table, owner, context, source, constructors = [], self = null,
  evidenceTypes=new Map(["IsSet","IsProp"].map(label=>[label,context.lookup(label)])),
  fixedReferences=new Map(),universeReferences=new Map()},splices=null) {
  const universes=new Map(universeReferences);
  constructors = Object.freeze(constructors.map(({id, label, nullary}) => {
    table.get(id);
    if (typeof label !== "string" || typeof nullary !== "boolean") throw new TypeError("Invalid source constructor inventory.");
    return Object.freeze({id, label, nullary});
  }));
  const canonical = tree.kind === "def" ? declarationTelescope(tree) : {tree, inferred: false};
  const telescope=evidenceTelescope(canonical.tree),resolvedParameters=new Map();
  tree = telescope.tree;
  const declaration=tree;
  if(self) {
    self=table.get(self.id);
    if(tree.kind!=="def"||!["declaration","helper"].includes(self.role))
      throw new TypeError("Structural self must be the identity of a retained declaration.");
  }
  const owned = [];
  let splice=0;
  const origin = at => at.origin??sourceOrigin({...source, start: at.start, end: at.end});
  tree = scopeMapped(tree, {
    deferred: true,
    region: (at,node,key) => self&&node===declaration&&["body","value"].includes(key)
      ?at.bind(self.label,bindingResolution(self.id)):at,
    parameter(mapped,original) {resolvedParameters.set(original,mapped);return mapped;},
    enter(node, at) {
      if(fixedReferences.has(node)) {
        const fixed=fixedReferences.get(node),value=fixed.tag==="universe"?universes.get(fixed.label):fixed;
        if(!value)throw new TypeError(`A fixed universe position has no header universe: ${fixed.label}`);
        return occurrence(node,value,node.name,origin(node));
      }
      if(telescope.evidence.has(node)) {
        const {parameter,builtin}=telescope.evidence.get(node),mapped=resolvedParameters.get(parameter);
        if(!mapped?.name.bindingId)throw new TypeError("Parameter evidence precedes its retained parameter.");
        const token=mapped.name,at=origin(token);
        if(!evidenceTypes.has(builtin))throw new TypeError(`A leveled parameter needs a source resolution for ${builtin}.`);
        return {kind:"call",fn:occurrence(token,evidenceTypes.get(builtin),builtin,at),
          args:[mapped.type,occurrence(token,bindingResolution(token.bindingId),token.text,at)],origin:at};
      }
      if(node.kind==="templateHole"&&splices) {
        const insert=splices.get(node.hole);
        if(!insert)throw new TypeError(`Unknown template syntax hole: ${node.hole}`);
        const {syntax}=cloneBindingSyntax(insert(at),table,[...owner,"splice",String(splice++)]);
        owned.push(...syntax.owned);
        return syntax.tree;
      }
      if (node.kind === "reference" || node.kind === "bindingReference")
        throw new TypeError("Source resolution cannot accept already resolved syntax.");
      if (node.kind && !migrated.has(node.kind)) throw new TypeError(`Binding syntax family has not migrated: ${node.kind}`);
      if(node.kind==="binary"&&(node.qualifier||!["=","->","and","or","++","&","|"].includes(node.operator)))
        throw new TypeError("Binding syntax family has not migrated: notation operator");
      if(node.kind==="name"&&node.name==="_")return {...node,origin:origin(node)};
      if (node.kind !== "name") return node;
      let qualified;
      try {qualified=at.qualified(node.name);}
      catch(error){error.at??=node;throw error;}
      const {value, fields} = qualified;
      const spelling = fields.length ? node.name.slice(0, -(fields.join(".").length + 1)) : node.name;
      const ref = occurrence(node, value, spelling, origin(node));
      return fields.length ? members(node, {...ref, end: node.start + spelling.length}, fields) : ref;
    },
    bind(token, node, scope, at) {
      if (token.bindingId) throw new TypeError("Source resolution cannot allocate an existing binder twice.");
      // Anonymous positions still need identities for forwarding, evidence,
      // cloning and generated applications. They introduce no lexical name.
      const record = table.allocate(owner, {role: bindingRole(node, scope, token), label: binderName(token), origin: origin(token)});
      if(record.role==="universe"&&node===declaration)universes.set(record.label,bindingResolution(record.id));
      owned.push(record.id);
      return {...token, bindingId: record.id, bindingRole: record.role,origin:record.origin,
        ...(record.role === "pattern" ? {constructorInventory: constructors, patternEnclosing: at.lookup(binderName(token))} : {})};
    },
    extend(at, binders) {
      for (const token of binders) {
        if (!token.bindingId||binderName(token)==="_") continue;
        at = token.bindingRole === "pattern" ? at.defer(binderName(token), token.bindingId)
          : at.bind(binderName(token), bindingResolution(token.bindingId));
      }
      return at;
    },
  }, context);
  if(telescope.order)tree={...tree,params:telescope.order.map(({parameter,group})=>({...resolvedParameters.get(parameter),group}))};
  return freeze({format, tree, owned, inferred: canonical.inferred});
}

const requireSyntax = syntax => {
  if (syntax?.format !== format || !Array.isArray(syntax.owned)) throw new TypeError("Expected binding-aware syntax.");
};

// A structural view/composition of already resolved trees. The subtree's
// actual binders determine ownership: removing a telescope opens its IDs,
// while wrapping its body closes exactly those same IDs. This never resolves
// a source label or allocates a new identity.
export function bindingSyntaxView(syntax,tree,{inferred=false}={}) {
  requireSyntax(syntax);
  const owned=new Set();
  const visit=tree=>scopeMapped(tree,{
    deferred:true,
    enter(node) {
      if(node.kind==="bindingReference")for(const [,value] of node.substitutions??[])visit(value);
      return node;
    },
    bind(token) {if(token.bindingId)owned.add(token.bindingId);return token;},
    extend:at=>at,
  },null);
  visit(tree);
  return freeze({...syntax,tree,owned:[...owned],inferred});
}

// Dependency consumers see exact external IDs and explicit unresolved
// decisions. A missing occurrence stays missing; a pending slot is never
// mistaken for an independent term. This is a separate pass over the final
// tree, including retained substitution arguments, not an inliner's callback.
export function bindingUses(syntax,{outcomes=new SlotOutcomes(),conditional=false}={}) {
  requireSyntax(syntax);
  const owned=new Set(syntax.owned),uses=[];
  const visit=(tree,conditions=[])=>scopeMapped(tree,{
    deferred:true,
    enter(node) {
      if(node.kind==="name"&&node.name==="_")uses.push({kind:"hole",origin:node.origin});
      if(node.kind!=="bindingReference")return node;
      const selected=outcomes.resolve(node.resolution);
      if(selected.tag==="binding") {
        const replacement=node.substitutions?.find(([id])=>id===selected.id)?.[1];
        if(replacement)visit(replacement,conditions);
        else if(!owned.has(selected.id))uses.push({kind:"binding",id:selected.id,spelling:node.spelling,origin:node.origin,
          ...(conditions.length?{conditions}:{})});
      } else if(selected.tag==="slot") {
        uses.push({kind:"deferred",slot:selected.id,resolution:selected,spelling:node.spelling,origin:node.origin});
        // The arguments remain conditional, rather than unconditional
        // dependencies of whichever alternative a later type will select.
        if(node.substitutions?.length)uses.at(-1).substitutions=node.substitutions;
        if(conditional) {
          let alternative=selected;
          const required=[...conditions];
          while(alternative.tag==="slot") {
            required.push({slot:alternative.id,outcome:"constructor"});
            alternative=outcomes.resolve(alternative.enclosing);
          }
          visit({...node,resolution:alternative},required);
        }
      } else uses.push({kind:selected.tag,label:selected.label,origin:node.origin});
      return node;
    },
    bind(token) {
      if(token.bindingRole==="pattern"&&binderName(token)!=="_"&&!outcomes.get(token.bindingId))uses.push({kind:"deferred-pattern",
        slot:token.bindingId,spelling:token.label??binderName(token),origin:token.origin,
        enclosing:token.patternEnclosing,constructors:token.constructorInventory});
      return token;
    },
    extend:at=>at,
  },null);
  visit(syntax.tree);
  return uses;
}

// Every unresolved interpretation is an obligation, including inferred
// holes. Only an exact ID or an explicit reserved reference is decided.
export const unresolvedBindingUse=use=>!["binding","reserved"].includes(use.kind);

// Structural equality for retained interfaces, up to their local binders
// and an explicit correspondence of external fields/parameters. Public
// labels and authored locations cannot decide inheritance sharing. Pending
// pattern spellings are different: they still select a constructor, so they
// remain semantic until their slots have been resolved.
export function sameBindingSyntax(left,right,correspondence=new Map()) {
  requireSyntax(left);requireSyntax(right);
  const canonical=(syntax,external)=>{
    const locals=new Map();
    const collect=tree=>scopeMapped(tree,{
      deferred:true,
      enter(node) {
        if(node.kind==="bindingReference")for(const [,value] of node.substitutions??[])collect(value);
        return node;
      },
      bind(token) {
        if(token.bindingId&&!locals.has(token.bindingId))locals.set(token.bindingId,locals.size);
        return token;
      },
      extend:at=>at,
    },null);
    collect(syntax.tree);
    const identity=id=>locals.has(id)?["local",locals.get(id)]:["external",external.get(id)??id];
    const resolution=value=>value.tag==="binding"?{tag:"binding",id:identity(value.id)}
      :value.tag==="slot"?{tag:"slot",id:identity(value.id),enclosing:resolution(value.enclosing)}:value;
    const map=tree=>scopeMapped(tree,{
      deferred:true,
      enter(node) {
        if(node.kind!=="bindingReference")return node;
        const {spelling,...reference}=node;
        return {...reference,resolution:resolution(node.resolution),
          ...(node.substitutions?{substitutions:node.substitutions.map(([id,value])=>[identity(id),map(value)])}:{})};
      },
      bind(token) {
        if(!token.bindingId)return token;
        const {text,name,label,...rest}=token;
        return {...rest,bindingId:identity(token.bindingId),
          ...(token.bindingRole==="pattern"?{patternLabel:label??text??name}:{}),
          ...(token.patternEnclosing?{patternEnclosing:resolution(token.patternEnclosing)}:{}),
          ...(token.constructorInventory?{constructorInventory:token.constructorInventory.map(entry=>({...entry,id:identity(entry.id)}))}:{})};
      },
      extend:at=>at,
    },null);
    return syntaxValue(map(syntax.tree),(key,value)=>{
      if(key==="synthetic"
        ||typeof value==="number"&&/^(start|end|group)$|Start$|End$/.test(key))return undefined;
      // Serialization order of object properties carries no syntax meaning.
      return value&&typeof value==="object"&&!Array.isArray(value)
        ?Object.fromEntries(Object.entries(value).sort(([a],[b])=>a<b?-1:a>b?1:0)):value;
    });
  };
  return canonical(left,correspondence)===canonical(right,new Map());
}
const mappedResolution = (value, ids) => value.tag === "binding" ? {...value, id: ids.get(value.id) ?? value.id}
  : value.tag === "slot" ? {...value, id: ids.get(value.id) ?? value.id, enclosing: mappedResolution(value.enclosing, ids)} : value;

// Apply an explicit interface correspondence without any source lookup.
// Open parent fields may share a child identity. This public operation may
// never change or target a local binder. Only cloning can rename locals,
// using fresh identities allocated by the table itself.
export function remapBindingSyntax(syntax,table,correspondence) {
  requireSyntax(syntax);
  const locals=new Set(syntax.owned);
  for(const [before,after] of correspondence) {
    table.get(before);table.get(after);
    if(locals.has(before)||locals.has(after))throw new TypeError("An open interface correspondence cannot change or capture local binders.");
  }
  return mappedBindingSyntax(syntax,correspondence);
}
function mappedBindingSyntax(syntax,correspondence) {
  const owned=syntax.owned.map(id=>correspondence.get(id)??id);
  if(new Set(owned).size!==owned.length)throw new TypeError("An interface correspondence cannot merge local binders.");
  const map = tree => scopeMapped(tree, {
    deferred: true,
    enter: node => node.kind === "bindingReference" ? {...node, resolution: mappedResolution(node.resolution, correspondence),
      ...(node.substitutions ? {substitutions: node.substitutions.map(([id, value]) => [correspondence.get(id) ?? id, map(value)])} : {})} : node,
    bind: token => token.bindingId ? {...token, bindingId: correspondence.get(token.bindingId) ?? token.bindingId,
      ...(token.patternEnclosing ? {patternEnclosing: mappedResolution(token.patternEnclosing, correspondence)} : {}),
      ...(token.constructorInventory?{constructorInventory:token.constructorInventory.map(entry=>({...entry,id:correspondence.get(entry.id)??entry.id}))}:{})} : token,
    extend: at => at,
  }, null);
  const tree = map(syntax.tree);
  return freeze({...syntax,tree,owned});
}

export function cloneBindingSyntax(syntax, table, owner, {expansion}={}) {
  requireSyntax(syntax);
  const correspondence = table.freshen(syntax.owned, owner,{expansion});
  const copy=mappedBindingSyntax(syntax,correspondence);
  return {syntax:expansion?freeze({...copy,tree:expandedSource(copy.tree,expansion)}):copy,correspondence};
}

// Simultaneous substitution for an explicit open interface. An inserted
// argument keeps its own references; it never passes through source name
// resolution again. Under a pending slot its enclosing alternative may need
// substitution, so retain that argument until the slot's role is known.
export function substituteBindingSyntax(syntax, replacements, table, owner, {kind="substitution"}={}) {
  requireSyntax(syntax);
  const owned = [...syntax.owned];
  for (const [id, replacement] of replacements) {
    table.get(id); requireSyntax(replacement);
    if (owned.includes(id)) throw new TypeError("Substitution requires an open binding, not an owned binder.");
  }
  let insertion = 0;
  const insert = (replacement,node,id) => {
    const {syntax: copy} = cloneBindingSyntax(replacement, table, [...owner, "argument", String(insertion++)],
      {expansion:{kind,site:node.origin,binding:id}});
    owned.push(...copy.owned);
    return copy.tree;
  };
  const map = tree => scopeMapped(tree, {
    deferred: true,
    enter(node) {
      if (node.kind !== "bindingReference") return node;
      if (node.resolution.tag === "binding" && replacements.has(node.resolution.id))
        return insert(replacements.get(node.resolution.id),node,node.resolution.id);
      const pending = new Map((node.substitutions ?? []).map(([id, value]) => [id, map(value)]));
      for (let value = node.resolution; value; value = value.tag === "slot" ? value.enclosing : null) {
        if (value.tag === "binding" && !pending.has(value.id) && replacements.has(value.id))
          pending.set(value.id, insert(replacements.get(value.id),node,value.id));
      }
      return pending.size ? {...node, substitutions: [...pending]} : node;
    },
    extend: at => at,
  }, null);
  return freeze({...syntax, tree: map(syntax.tree), owned});
}

// Entry lowering handles decided references and ordinary binder tokens. A
// candidate pattern's token keeps its spelling for the matched constructor
// table. Its body occurrences keep their slots until resolution time.
export function lowerBindingSyntax(syntax, adapter, outcomes = new SlotOutcomes()) {
  requireSyntax(syntax);
  const tree = scopeMapped(syntax.tree, {
    deferred: true,
    enter: node => node.kind === "bindingReference" ? lowerBindingReference(node, adapter, outcomes, {deferMissing: true}) : node,
    bind: token => token.bindingId && token.bindingRole !== "pattern"
      ? {...token, text: adapter.key(token.bindingId), label: token.label ?? binderName(token)} : token,
    extend: at => at,
  }, null);
  return syntax.inferred ? {...tree, value: parameterLambdas(tree.params, tree.value), valueParameters: tree.params, params: []} : tree;
}

// Structural consumers (for example recursion's fixed-argument checks)
// inspect source nodes before calling term elaboration. Resolve the slots
// decided by this branch there too, through the same adapter. Binders and
// still-pending nested slots are unchanged.
export function lowerBindingReferences(tree,adapter,outcomes=new SlotOutcomes()) {
  return scopeMapped(tree,{
    deferred:true,
    enter:node=>node.kind==="bindingReference"?lowerBindingReference(node,adapter,outcomes,{deferMissing:true}):node,
    extend:at=>at,
  },null);
}

export function lowerBindingReference(node, adapter, outcomes = new SlotOutcomes(), options = {}) {
  const resolved = adapter.resolve(node.resolution, outcomes);
  if (resolved.tag === "binding") {
    const replacement = node.substitutions?.find(([id]) => id === resolved.id)?.[1];
    if (replacement) return lowerBindingSyntax({format, tree: replacement, owned: []}, adapter, outcomes);
  }
  const name = adapter.lower(node.resolution, outcomes, options);
  return name === null ? node : {...node, kind: "name", name};
}
