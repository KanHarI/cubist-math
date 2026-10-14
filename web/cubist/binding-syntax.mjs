// Explicit migration boundary for ordinary binding-aware syntax. Later
// packages move retained theories and goal-dependent blocks through this
// same representation; an unmigrated family is rejected here, not retried
// through nominal capture on failure.
import {scopeMapped, binderName, bindingRole,selectionEffects} from "./scopes.mjs";
import {members} from "./references.mjs";
import {sourceOrigin, bindingResolution, SlotOutcomes,mapResolution,memberResolution,namespaceResolution,slotResolution,
  failedResolution,resolutionError,UnknownNamespaceMember,namespaceSelectorResolution} from "./bindings.mjs";
import {declarationTelescope, evidenceTelescope, parameterLambdas} from "./telescopes.mjs";
import {syntaxValue,expandedSource} from "./source-syntax.mjs";
import {mapSyntax} from "../translator/syntax-graph.mjs";
import {notationAlternative} from "./theory-notation.mjs";

const format = "cubist-bindings-1";
// Opt in only after every binder and reference namespace of a family is
// modelled. New parser kinds cannot silently enter nominal lookup paths.
const migrated = new Set(["name", "number", "lambda", "forall", "exists", "binderGroup",
  "pathLambda", "induction", "match", "clause", "pattern", "unpack", "def", "namedArgument", "call", "binary",
  "unary", "pair", "projection", "member", "pathApply", "transport", "lift", "over", "prop", "set",
  "trunc", "typed", "exact", "let", "matchStatement", "rfl", "calc", "rw", "block", "term", "tactic", "hlevel","select","use"]);
const freeze = value => {
  if (!value || typeof value !== "object" || Object.isFrozen(value)) return value;
  for (const child of Object.values(value)) freeze(child);
  return Object.freeze(value);
};
const occurrence = (at, value, spelling, origin) => ({kind: "bindingReference", resolution: value, spelling, origin,
  start: at.start, end: at.end});

// Parent-interface selections reinterpret free field labels, preserving
// lexical binders. Model openings are different: they shadow preceding
// locals. A pending pattern keeps its variable alternative and replaces only
// the constructor branch's enclosing interpretation with the selected field.
function namespaceSelector(value,context,table,boundary) {
  const localRoles=new Set(["parameter","universe","local","dimension","pattern"]);
  const localBinding=id=>localRoles.has(table.get(id).role)&&(!boundary||context.introducedAfter(id,boundary));
  const protect=(local,target)=>local.tag==="binding"&&localBinding(local.id)?local
    :local.tag==="slot"&&localBinding(local.id)?slotResolution(local.id,protect(local.enclosing,target))
    :local.tag==="opening"?protect(local.enclosing,target)
    :local.tag==="namespace"?protect(local.fallback,target):target;
  if(value.tag==="namespace")return namespaceResolution(value.members.map(([label,target])=>
    [label,protect(context.lookup(label),target)]),value.fallback,value.description,value.receiver);
  if(["slot","opening"].includes(value.tag))return {...value,enclosing:namespaceSelector(value.enclosing,context,table,boundary)};
  return value;
}
const namespaceCandidates=value=>value?.tag==="namespace"?value.members
  :["slot","opening"].includes(value?.tag)?namespaceCandidates(value.enclosing):[];

export function resolveBindingSyntax(tree, options) {
  return resolveBindings(tree,options);
}

// A selected receiver uses the selection namespace at its root. A parent's
// abstract model is explicit syntax over its interface, never its bare-name
// fallback to an unrelated declaration. Operand recipes use this entry.
export function resolveBindingReceiver(tree,options) {
  if(options.context.notations()===null)
    throw new TypeError("A retained selection receiver requires the complete source notation inventory.");
  return resolveBindings(tree,{...options,selectionReceiver:true});
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
  fixedReferences=new Map(),universeReferences=new Map(),namespaceBoundary=null,namespaceFailure=null,selectionReceiver=false,
  notation=null},splices=null) {
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
  const selectors=new Map();
  let namespaces=false;
  let splice=0;
  const origin = at => at.origin??sourceOrigin({...source, start: at.start, end: at.end});
  const resolvedAt=(value,node)=>mapResolution(value,undefined,value=>value.tag==="failure"?failedResolution({...value,
    ...(value.namespace!==undefined&&namespaceFailure?{message:namespaceFailure(value)}:{}),origin:origin(node)}):value);
  const lookup=(at,name,node,selector=false)=>{
    let found;
    try {found=selector?at.lexical.selector(name):at.lexical.qualified(name);}
    catch(error) {
      if(!(error instanceof UnknownNamespaceMember))throw error;
      throw resolutionError(resolvedAt(failedResolution(error),node));
    }
    const value=resolvedAt(found.value,node);
    if(value.tag==="failure")throw resolutionError(value);
    return {...found,value};
  };
  tree = scopeMapped(tree, {
    deferred: true,
    prepare(node,at) {
      if(!["select","use"].includes(node.kind))return node;
      if(node.activation)throw new TypeError("Source resolution cannot allocate an existing activation twice.");
      let model=node.model,selector;
      if(node.kind==="select"&&model.kind==="name") {
        const found=lookup(at,model.name,model,true);
        if(model.name!=="_"||found.value.tag==="namespace") {
          selector=memberResolution(namespaceSelector(found.value,at.lexical,table,namespaceBoundary),found.fields);
          if(selector.tag==="namespace"||namespaceCandidates(selector).length)namespaces=true;
          model={...model};selectors.set(model,selector);
        }
      }
      return {...node,model,activation:{text:"selection",start:node.model.start,end:node.model.end,origin:origin(node.model),
        ...(selector?.tag==="namespace"?{activationMode:"namespace"}:{})}};
    },
    region(at,node,key) {
      if(self&&node===declaration&&["body","value"].includes(key))
        at={...at,lexical:at.lexical.bind(self.label,bindingResolution(self.id))};
      // An explicitly selected notation is complete; the surrounding
      // theory's operator table cannot rewrite its body. Its deferred rules
      // enter through their own migration boundary.
      if(node.kind==="select"&&key==="body"&&(node.effects??selectionEffects.all).notation)
        at={...at,notation:null};
      return at;
    },
    parameter(mapped,original) {resolvedParameters.set(original,mapped);return mapped;},
    enter(node, at, descend) {
      if(selectors.has(node))return occurrence(node,selectors.get(node),node.name,origin(node));
      if(fixedReferences.has(node)) {
        const fixed=fixedReferences.get(node);
        if(fixed.tag==="universe"&&fixed.label==="_")
          throw Object.assign(Error("An anonymous universe has no name: name the header universe to refer to it here."),
            {offset:node.start,sourceEnd:node.end});
        const value=fixed.tag==="universe"?universes.get(fixed.label):fixed;
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
        const {syntax}=cloneBindingSyntax(insert(at.lexical),table,[...owner,"splice",String(splice++)]);
        owned.push(...syntax.owned);
        return syntax.tree;
      }
      const key=node.kind==="negation"&&!node.qualifier?"unary -":node.kind==="binary"&&!node.qualifier
        ?node.operator===">"?"<":node.operator===">="?"<=":node.operator:null;
      if(key&&at.notation) {
        const ambiguous=at.notation.ambiguous?.[key];
        if(ambiguous)throw Object.assign(Error(`${key} is ambiguous in ${at.notation.name}: it is ${
          ambiguous.map(e=>`${e.label}'s ${e.parentField}`).join(" and ")}. Write ${
          ambiguous.map(e=>notationAlternative("",key,e)).join(" or ")}, or give one another notation in extends.`),
          {offset:node.start,sourceEnd:node.end,origin:origin(node)});
        const rule=at.notation.bindings[key];
        if(rule) {
          const operand=(child,recipe)=>{
            if(!recipe)return descend(child);
            const {syntax}=cloneBindingSyntax(recipe,table,[...owner,"operand",String(splice++)],
              {expansion:{kind:"notation",site:origin(child)}});
            owned.push(...syntax.owned);
            const activation=table.allocate(owner,{role:"activation",label:"selection",origin:origin(child)});
            owned.push(activation.id);
            return {kind:"select",effects:selectionEffects.notation,model:syntax.tree,
              activation:{text:activation.label,bindingId:activation.id,bindingRole:activation.role,origin:activation.origin,
                start:child.start,end:child.end},
              body:descend(child,{...at,notation:null}),origin:origin(child),start:child.start,end:child.end};
          };
          const reverse=node.operator===">"||node.operator===">=";
          const args=key==="unary -"?[operand(node.operand,rule.recipe.left)]
            :[operand(reverse?node.right:node.left,rule.recipe.left),operand(reverse?node.left:node.right,rule.recipe.right)];
          const site={...node,start:node.operatorStart??node.start,end:node.operatorEnd??node.end};
          return {kind:"call",fn:occurrence(site,bindingResolution(rule.field),table.get(rule.field).label,origin(site)),
            args,origin:origin(node),start:node.start,end:node.end};
        }
      }
      if (node.kind === "reference" || node.kind === "bindingReference")
        throw new TypeError("Source resolution cannot accept already resolved syntax.");
      if (node.kind && !migrated.has(node.kind)) throw new TypeError(`Binding syntax family has not migrated: ${node.kind}`);
      if(node.kind==="binary"&&(node.qualifier||!["=","->","and","or","++","&","|"].includes(node.operator)))
        throw new TypeError("Binding syntax family has not migrated: notation operator");
      if(node.kind==="name"&&node.name==="_")return {...node,origin:origin(node)};
      if (node.kind !== "name") return node;
      let {value, fields} = lookup(at,node.name,node,selectionReceiver&&node===declaration);
      if(selectionReceiver&&node===declaration&&value.tag==="missing")
        throw resolutionError(failedResolution({message:`Untranslated name: ${value.label}`,origin:origin(node)}));
      if(selectionReceiver&&node===declaration)value=mapResolution(value,undefined,value=>{
        if(value.tag!=="namespace")return value;
        if(!value.receiver)throw new TypeError("A namespace notation receiver needs its explicit model interface.");
        return value.receiver;
      });
      const spelling = fields.length ? node.name.slice(0, -(fields.join(".").length + 1)) : node.name;
      const ref = occurrence(node, value, spelling, origin(node));
      return fields.length ? members(node, {...ref, end: node.start + spelling.length}, fields) : ref;
    },
    bind(token, node, scope, at) {
      if (token.bindingId) throw new TypeError("Source resolution cannot allocate an existing binder twice.");
      // Anonymous positions still need identities for forwarding, evidence,
      // cloning and generated applications. They introduce no lexical name.
      const record = table.allocate(owner, {role: bindingRole(node, scope, token), label: binderName(token), origin: origin(token)});
      if(record.role==="universe"&&record.label!=="_"&&node===declaration)universes.set(record.label,bindingResolution(record.id));
      owned.push(record.id);
      return {...token, bindingId: record.id, bindingRole: record.role,origin:record.origin,
        ...(record.role === "pattern" ? {constructorInventory: constructors, patternEnclosing: at.lexical.lookup(binderName(token))} : {})};
    },
    extend(at, binders,node,scope) {
      if(scope.role==="activation") {
        if(scope.effects.notation)at={...at,notation:null};
        if(!scope.effects.labels)return at;
        const selector=selectors.get(node.model),candidates=namespaceCandidates(selector);
        if(selector?.tag==="namespace") {
          for(const [label,value] of selector.members)at={...at,lexical:at.lexical.bind(label,value)};
          return at;
        }
        return {...at,lexical:at.lexical.open(binders[0].bindingId,{candidates})};
      }
      for (const token of binders) {
        if (!token.bindingId||binderName(token)==="_") continue;
        at={...at,lexical:token.bindingRole==="pattern"?at.lexical.defer(binderName(token),token.bindingId)
          :at.lexical.bind(binderName(token),bindingResolution(token.bindingId))};
      }
      return at;
    },
  }, {lexical:context,notation});
  if(telescope.order)tree={...tree,params:telescope.order.map(({parameter,group})=>({...resolvedParameters.get(parameter),group}))};
  const syntax=freeze({format, tree, owned, inferred: canonical.inferred});
  if(!namespaces)return syntax;
  // A statically selected interface is a lexical scope, not a runtime model.
  // Its body is now resolved, so discard that scope descriptor. Keeping its
  // unused member table would invent dependencies and affect alpha equality.
  const erase=tree=>mapSyntax(tree,node=>{
    if(node.kind==="select"&&node.activation?.activationMode==="namespace")return erase(node.body);
    // A deferred selector carries only the decision, not the entire source
    // namespace. Each body occurrence already retained its needed candidate.
    if(node.tag==="namespace")return namespaceSelectorResolution();
  });
  return bindingSyntaxView(syntax,erase(tree),{inferred:canonical.inferred});
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
      const structural=resolutionExpression(node,selected);
      if(structural!==node) {visit(structural,conditions);return node;}
      if(selected.tag==="binding") {
        const replacement=node.substitutions?.find(([id])=>id===selected.id)?.[1];
        if(replacement)visit(replacement,conditions);
        else if(!owned.has(selected.id))uses.push({kind:"binding",id:selected.id,spelling:node.spelling,origin:node.origin,
          ...(conditions.length?{conditions}:{})});
      } else if(selected.tag==="slot"||selected.tag==="opening") {
        uses.push({kind:selected.tag==="slot"?"deferred":"deferred-opening",slot:selected.id,resolution:selected,spelling:node.spelling,origin:node.origin});
        // The arguments remain conditional, rather than unconditional
        // dependencies of whichever alternative a later type will select.
        if(node.substitutions?.length)uses.at(-1).substitutions=node.substitutions;
        if(conditional) {
          let alternative=selected;
          const required=[...conditions];
          while(alternative.tag==="slot"||alternative.tag==="opening") {
            for(const candidate of alternative.candidates??[])
              visit({...node,resolution:candidate},[...required,{activation:alternative.id,label:alternative.label.split(".")[0],outcome:"provided"}]);
            required.push(alternative.tag==="slot"?{slot:alternative.id,outcome:"constructor"}
              :{activation:alternative.id,label:alternative.label.split(".")[0],outcome:"absent"});
            alternative=outcomes.resolve(alternative.enclosing);
          }
          visit({...node,resolution:alternative},required);
        }
      } else if(!["namespace","namespace-selector"].includes(selected.tag))uses.push({kind:selected.tag,label:selected.label,origin:node.origin});
      // A namespace selector describes alternatives; it evaluates no member.
      // Its body carries the actual (possibly conditional) dependencies.
      return node;
    },
    bind(token) {
      if(token.bindingRole==="activation"&&token.activationMode!=="namespace"&&!outcomes.activation(token.bindingId))uses.push({kind:"deferred-activation",
        activation:token.bindingId,origin:token.origin});
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
    const resolution=value=>mapResolution(value,identity);
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
const mappedResolution = (value, ids) => mapResolution(value,id=>ids.get(id)??id);

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
      mapResolution(node.resolution,id=>{
        if(!pending.has(id)&&replacements.has(id))pending.set(id,insert(replacements.get(id),node,id));
        return id;
      });
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
    bind: token => token.bindingId && !["pattern","activation"].includes(token.bindingRole)
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
  const structural=resolutionExpression(node,resolved);
  if(structural!==node)return lowerBindingSyntax({format,tree:structural,owned:[]},adapter,outcomes);
  if (resolved.tag === "binding") {
    const replacement = node.substitutions?.find(([id]) => id === resolved.id)?.[1];
    if (replacement) return lowerBindingSyntax({format, tree: replacement, owned: []}, adapter, outcomes);
  }
  const name = adapter.lower(node.resolution, outcomes, options);
  return name === null ? node : {...node, kind: "name", name};
}

// Structural targets are syntax over exact IDs, never a dotted global name.
// Keep substitutions attached until every opening/slot on the path resolves.
function resolutionExpression(node,value) {
  const reference=resolution=>({...node,resolution});
  if(value.tag==="member")return members(node,reference(value.receiver),value.fields);
  if(value.tag==="projected")return {kind:"call",fn:reference(bindingResolution(value.projection)),
    args:[reference(bindingResolution(value.receiver))],start:node.start,end:node.end,origin:node.origin};
  if(value.tag==="application")return {kind:"call",fn:reference(value.fn),args:value.args.map(reference),
    start:node.start,end:node.end,origin:node.origin};
  return node;
}
