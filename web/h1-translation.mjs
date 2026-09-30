// K2.4a, τ (H1 specification 7.2). Surface elaboration supplies native
// syntax and the universes read by its derivation. The image is admitted in
// a separate instruction kernel, with declared counterparts. No conversion
// equates native and declared types. A mixed-tier call fails in that kernel.
import { CubicalKernel } from "./cubical-kernel.mjs";
import { NativeCubicalElaborator } from "./cubical-elaborator.mjs";
import { T } from "./dist/cubical-runtime/core.mjs";
import { levelNormal } from "./cubical-levels.mjs";
import { bindDimensions } from "./dist/cubical-runtime/dimension-slots.mjs";
import { CubicalDeclarationTransaction } from "./cubical-transaction.mjs";

const N = "__tau_N", PLUS = "__tau_Plus", TREE = "__tau_Tree", PUSH = "__tau_Push";
const variable = T.variable;
const universe = level => ({tag:"U",level});
const maximum = (a,b) => ({tag:"LMax",left:variable(a),right:variable(b)});
const generic = names => names.map(name => ({name,recorded:false}));
const pi = T.pi, app = T.app;

export function counterpartSpecifications() {
  const s = variable("__tau_sort"), A = variable("__tau_A"), B = variable("__tau_B"), C = variable("__tau_C");
  const u = "__tau_u", v = "__tau_v", w = "__tau_w";
  const maps = variable("__tau_maps"), c = variable("__tau_c"), l = variable("__tau_label");
  return [
    {name:N,sort:"__tau_sort",level:0,constructors:[
      {name:"__tau_zero",display:"zero",type:s},
      {name:"__tau_succ",display:"succ",type:pi("__tau_n",s,s)}]},
    {name:PLUS,sort:"__tau_sort",levels:generic([u,v]),level:maximum(u,v),
      parameters:[{name:"__tau_A",type:universe(variable(u))},{name:"__tau_B",type:universe(variable(v))}],
      constructors:[{name:"__tau_inl",display:"inl",type:pi("__tau_a",A,s)},
        {name:"__tau_inr",display:"inr",type:pi("__tau_b",B,s)}]},
    {name:TREE,sort:"__tau_sort",levels:generic([u,v]),level:maximum(u,v),
      parameters:[{name:"__tau_A",type:universe(variable(u))},
        {name:"__tau_B",type:pi("__tau_label",A,universe(variable(v)))}],
      constructors:[{name:"__tau_sup",display:"sup",type:pi("__tau_label",A,
        pi("__tau_children",pi("__tau_index",app(B,l),s),s))}]},
    {name:PUSH,sort:"__tau_sort",levels:generic([u,v,w]),
      level:{tag:"LMax",left:maximum(u,v),right:variable(w)},
      parameters:[{name:"__tau_C",type:universe(variable(u))},{name:"__tau_A",type:universe(variable(v))},
        {name:"__tau_B",type:universe(variable(w))},{name:"__tau_maps",type:T.sigma("__tau_left_map",
          pi("__tau_c",C,A),pi("__tau_c",C,B))}],
      constructors:[{name:"__tau_left",display:"inl",type:pi("__tau_a",A,s)},
        {name:"__tau_right",display:"inr",type:pi("__tau_b",B,s)},
        {name:"__tau_bridge",display:"push",type:pi("__tau_c",C,T.path("__tau_i",s,
          app(variable("__tau_left"),app(T.first(maps),c)),app(variable("__tau_right"),app(T.second(maps),c))))}]},
  ];
}

export class H1Translation {
  constructor(module, sourceChecker) {
    this.source = sourceChecker;
    this.kernel = new CubicalKernel(module);
    this.kernel.setOptimizations(sourceChecker.kernel.optimizations ?? {});
    this.kernel.setExtensions({h1:true});
    this.checker = new NativeCubicalElaborator(this.kernel);
    this.rootContext = new Map(); this.rootDimensions = new Map();
    this.memo = new WeakMap(); this.scopeKeys = new WeakMap(); this.tiers = new WeakMap();
    this.activeDefinitions = new Set(); this.activeSignatures = new Set();
    this.failures = []; this.keptNative = new Set(); this.evaluations = [];
    for (const spec of counterpartSpecifications()) this.checker.admitSignature(spec);
  }
  dispose() { this.kernel.dispose(); }
  scopeKey(context, dimensions) {
    let keys = this.scopeKeys.get(context);
    if (!keys) this.scopeKeys.set(context,keys=new Map());
    const dims = JSON.stringify([...dimensions]);
    if (!keys.has(dims)) keys.set(dims,JSON.stringify([...context].map(([name,type]) =>
      [name,this.source.syntax.encode(type,dimensions)])) + dims);
    return keys.get(dims);
  }
  finite(type, context, dimensions) {
    let cache = this.tiers.get(type);
    if (!cache) this.tiers.set(type,cache=new Map());
    const key = this.scopeKey(context,dimensions);
    if (!cache.has(key)) {
      const sort = this.source.nf(this.source.infer(type,context,dimensions).type,dimensions);
      if (sort.tag !== "U") throw Error("τ needs a type former's universe in its derivation.");
      const level = this.source.syntax.encodeLevel(sort.level);
      cache.set(key,levelNormal(id => this.source.kernel.node(id),level).tier === 0);
    }
    return cache.get(key);
  }
  // The native annotation, exposed in the native derivation, maps to a
  // literal instance for a constructor or eliminator in the image.
  former(type,context,dimensions) {
    return this.map(this.source.nf(type,dimensions),context,dimensions);
  }
  map(term, context=this.rootContext, dimensions=this.rootDimensions) {
    if (!term || typeof term !== "object") return term;
    const key = this.scopeKey(context,dimensions);
    let cache = this.memo.get(term);
    if (!cache) this.memo.set(term,cache=new Map());
    if (cache.has(key)) return cache.get(key);
    const mapped = this.node(term,context,dimensions);
    cache.set(key,mapped); return mapped;
  }
  node(term,context,dimensions) {
    const at = child => this.map(child,context,dimensions);
    const constructor = (sort,index,...args) => args.reduce(app,T.constructor(index,sort));
    switch (term.tag) {
      case "Nat": return T.sort(N);
      case "Zero": return constructor(T.sort(N),0);
      case "Succ": return constructor(T.sort(N),1,at(term.value));
      case "DefRef": this.copyDefinition(term.name); return term;
      case "Sort": case "Elim": this.copySignature(term.signature); break;
      case "Sum":
        if (this.finite(term,context,dimensions)) return T.sort(PLUS,[at(term.left),at(term.right)]);
        this.keptNative.add("Sum"); break;
      case "W": {
        const inner = new Map(context).set(term.name,term.domain);
        const domain = at(term.domain), body = this.map(term.body,inner,dimensions);
        if (this.finite(term,context,dimensions)) return T.sort(TREE,[domain,T.lam(term.name,domain,body)]);
        this.keptNative.add("W"); return {...term,domain,body};
      }
      case "Pushout":
        if (this.finite(term,context,dimensions)) return T.sort(PUSH,[at(term.center),at(term.left),at(term.right),at(term.maps)]);
        this.keptNative.add("Pushout"); break;
      case "Inl": case "Inr": {
        const sort = this.former(term.as,context,dimensions), value = at(term.value);
        return sort.tag === "Sort" && sort.signature === PLUS ? constructor(sort,term.tag === "Inr" ? 1 : 0,value)
          : {...term,as:sort,value};
      }
      case "Sup": {
        const sort = this.former(term.as,context,dimensions), label = at(term.label), children = at(term.children);
        return sort.tag === "Sort" && sort.signature === TREE ? constructor(sort,0,label,children) : {...term,as:sort,label,children};
      }
      case "PushLeft": case "PushRight": case "PushPath": {
        const sort = this.former(term.as,context,dimensions), value = at(term.value);
        if (sort.tag !== "Sort" || sort.signature !== PUSH) return {...term,as:sort,value};
        const index = {PushLeft:0,PushRight:1,PushPath:2}[term.tag];
        const built = constructor(sort,index,value);
        return term.tag === "PushPath" ? T.at(built,term.arg) : built;
      }
      case "NatRec": return app(T.eliminator(N,at(term.motive),[at(term.zero),at(term.step)]),at(term.value));
      case "SumRec": case "WRec": {
        const sort = this.former(this.source.infer(term.value,context,dimensions).type,context,dimensions);
        const signature = term.tag === "SumRec" ? PLUS : TREE;
        if (sort.tag === "Sort" && sort.signature === signature)
          return app(T.eliminator(signature,at(term.motive),term.tag === "SumRec" ? [at(term.left),at(term.right)] : [at(term.step)]),at(term.value));
        break;
      }
      case "PushElim": {
        const motiveType = this.source.nf(this.source.infer(term.motive,context,dimensions).type,dimensions);
        const sort = this.former(motiveType.domain,context,dimensions);
        if (sort.tag === "Sort" && sort.signature === PUSH) {
          let name = "__tau_value";
          while (context.has(name)) name += "_";
          const eliminator = T.eliminator(PUSH,at(term.motive),[at(term.left),at(term.right),at(term.bridge)]);
          return T.lam(name,sort,app(eliminator,variable(name)));
        }
        break;
      }
      case "Pi": case "Lam": case "Sigma": {
        const domain = at(term.domain), inner = new Map(context).set(term.name,term.domain);
        return {...term,domain,body:this.map(term.body,inner,dimensions)};
      }
      case "LPi": case "LLam": {
        const inner = new Map(context).set(term.name,{tag:"LBound",tier:1});
        return {...term,body:this.map(term.body,inner,dimensions)};
      }
      case "Path": case "PLam": case "Comp": case "HComp": case "Trans": {
        const {inner} = bindDimensions(term,dimensions);
        const family = this.map(term.family,context,term.tag === "HComp" ? dimensions : inner);
        if (term.tag === "Path") return {...term,family,left:at(term.left),right:at(term.right)};
        if (term.tag === "PLam") return {...term,family,body:this.map(term.body,context,inner)};
        if (term.tag === "Trans") return {...term,family,base:at(term.base)};
        return {...term,family,base:at(term.base),system:term.system.map(part =>
          ({...part,term:this.map(part.term,context,inner)}))};
      }
    }
    // τ is the identity on every other node and every level/formula.
    if (Array.isArray(term)) return term.map(at);
    return Object.fromEntries(Object.entries(term).map(([field,value]) =>
      [field,field === "face" || field === "arg" && term.tag === "PApp" || field === "level" || field === "levels"
        ? value : at(value)]));
  }
  copySignature(name) {
    if (this.kernel.signatures.has(name)) return;
    if (this.activeSignatures.has(name)) throw Error(`Cyclic signature dependency in τ: ${name}.`);
    const original = this.source.kernel.signatures.get(name);
    if (!original) throw Error(`Unknown source signature in τ: ${name}.`);
    this.activeSignatures.add(name);
    try {
      const spec = original.spec, context = new Map();
      for (const level of spec.levels ?? []) context.set(level.name,{tag:"LBound",tier:1});
      const parameters = (spec.parameters ?? []).map(parameter => {
        const type = this.map(parameter.type,context);
        context.set(parameter.name,parameter.type); return {...parameter,type};
      });
      context.set(spec.sort ?? spec.name,universe(spec.level ?? 0));
      const constructors = spec.constructors.map(constructor => {
        const type = this.map(constructor.type,context);
        context.set(constructor.name,constructor.type); return {...constructor,type};
      });
      this.checker.admitSignature({...spec,parameters,constructors});
    } finally { this.activeSignatures.delete(name); }
  }
  copyDefinition(name) {
    if (this.kernel.definitions.has(name)) return;
    if (this.activeDefinitions.has(name)) throw Error(`Cyclic definition dependency in τ: ${name}.`);
    const reference = this.source.kernel.definitions.get(name);
    if (!reference) throw Error(`Unknown source definition in τ: ${name}.`);
    this.activeDefinitions.add(name);
    try {
      const original = this.source.kernel.definition(reference);
      const value = this.source.syntax.decode(original.value), type = this.source.syntax.decode(original.type);
      this.checker.define(name,this.map(value),this.map(type));
    } finally { this.activeDefinitions.delete(name); }
  }
  checkDeclaration(name,kind="def") {
    const transaction = new CubicalDeclarationTransaction(this.kernel,this.checker);
    try {
      if (kind === "inductive") this.copySignature(name); else this.copyDefinition(name);
      transaction.finish(true);
      return {extensions:kind === "inductive" ? ["H1"] : this.checker.definitionExtensions.get(name) ?? []};
    } catch (error) {
      transaction.finish(false);
      // Source-keyed memoized images may mention definitions rolled back.
      this.memo = new WeakMap(); this.tiers = new WeakMap(); this.scopeKeys = new WeakMap();
      this.failures.push({name,reason:error.message});
      throw Object.assign(Error(`τ has no checked image for ${name}: ${error.message}`),{kind:error.kind ?? "mismatch"});
    }
  }
  checkEvaluation(directive,result,expected) {
    const transaction=new CubicalDeclarationTransaction(this.kernel,this.checker);
    let accepted=false;
    try {
      const image=this.checker.verify(this.map(result.term)), value=this.checker.verify(this.map(expected.term));
      if(!this.checker.equal(image.type,value.type) || !this.checker.equal(image.normal,value.normal)
        || !this.checker.equal(image.normal,this.map(result.normal)))
        throw Error(`τ evaluation disagrees with the native result for ${directive.name ?? "evaluate"}.`);
      this.evaluations.push({name:directive.name,normal:image.normal}); accepted=true;
    } finally {
      transaction.finish(accepted);
      if(!accepted) { this.memo=new WeakMap(); this.tiers=new WeakMap(); this.scopeKeys=new WeakMap(); }
    }
  }
}
