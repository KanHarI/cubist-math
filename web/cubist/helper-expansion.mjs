// Helpers are values over complete retained telescopes. Substitution carries
// their references and freshens local identities; it does not reinterpret a
// label at the use site. Keep applications intact for the checker, including
// unused arguments whose domains must still be checked.
import {bindingSyntaxView,substituteBindingSyntax,unresolvedBindingUse} from "./binding-syntax.mjs";
import {parameterLambdas} from "./telescopes.mjs";
import {DependencyAnalysis} from "./dependencies.mjs";
import {interfaceSignature,interfaceType} from "./retained-interfaces.mjs";
import {reservedResolution} from "./bindings.mjs";
import {scopeMapped} from "./scopes.mjs";
import {assignArguments} from "./call-arguments.mjs";

function helperValue(entry) {
  const {params,type,value,body}=entry.syntax.tree;
  const expression=value??(body?.length===1&&body[0].kind==="exact"?body[0].value:null);
  if(!expression)throw new TypeError("A retained helper needs an expression body.");
  // The result annotation remains inside the telescope, where its parameter
  // IDs are bound. An incorrect helper result must not become valid merely
  // because an inlining consumer expects another type.
  const checked=type?{kind:"call",fn:{kind:"bindingReference",resolution:reservedResolution("typed"),
    spelling:"typed",origin:entry.binding.origin},args:[type,expression]}:expression;
  return bindingSyntaxView(entry.syntax,parameterLambdas(params,checked));
}

export class HelperExpansion {
  #values=new Map();
  #serial=0;
  constructor(entries,{table,owner}) {
    this.analysis=new DependencyAnalysis(entries);
    this.table=table;this.owner=owner;
    // Validate the complete dependency graph before recursively expanding
    // any value. A structural recursive helper is a checked value, not an
    // inline definition. Pending alternatives stay in the resulting trees.
    this.pending=this.analysis.validateHelpers().pending;
    const value=entry=>{
      if(this.#values.has(entry.id))return this.#values.get(entry.id);
      const replacements=new Map();
      for(const use of this.analysis.references(entry.syntax,{conditional:true})) {
        const dependency=use.kind==="binding"?this.analysis.byIdentity.get(use.id):null;
        if(dependency?.kind==="derived"&&!dependency.recursive)replacements.set(use.id,value(dependency));
      }
      // Conditional graph edges need the same expansion order as ordinary
      // references. Substitution retains them under the slot; a variable
      // outcome later discards the enclosing alternative.
      const expanded=substituteBindingSyntax(this.#calls(helperValue(entry)),replacements,table,
        [...owner,"definition",String(this.#serial++)],{kind:"helper"});
      this.#values.set(entry.id,expanded);
      return expanded;
    };
    for(const entry of this.analysis.byIdentity.values())
      if(entry.kind==="derived"&&!entry.recursive)value(entry);
  }
  #calls(syntax) {
    const signature=node=>{
      if(node.kind==="bindingReference"&&node.resolution.tag==="binding") {
        const entry=this.analysis.byIdentity.get(node.resolution.id);
        if(entry?.kind==="derived"&&!entry.recursive)return {entry,parameters:entry.syntax.tree.params.map(p=>({
          name:p.label??p.name.label??p.name.text,implicit:!!p.implicit}))};
      }
      if(node.kind==="call") {
        const previous=signature(node.fn);
        if(previous)return {...previous,parameters:previous.parameters.slice(argumentsOf(node,previous).length)};
      }
      return null;
    };
    const argumentsOf=(node,{entry,parameters})=>{
      const unit={locate:(error,at)=>Object.assign(error,{offset:at.start,sourceEnd:at.end})};
      const given=assignArguments(node,parameters,unit,entry.label),args=[];
      for(let index=0;given(index)!==undefined;index++)args.push(given(index)??{
        kind:"name",name:"_",start:node.start,end:node.end});
      return args;
    };
    const map=tree=>scopeMapped(tree,{
      deferred:true,
      enter(node) {
        if(node.kind!=="call")return node;
        const target=signature(node.fn);
        if(!target)return node;
        const {implicitArgs,...rest}=node;
        return {...rest,fn:map(node.fn),args:argumentsOf(node,target).map(map)};
      },
      extend:at=>at,
    },null);
    return bindingSyntaxView(syntax,map(syntax.tree),{inferred:syntax.inferred});
  }
  expand(syntax) {
    return substituteBindingSyntax(this.#calls(syntax),this.#values,this.table,[...this.owner,"use",String(this.#serial++)],{kind:"helper"});
  }
  signature(entry) {
    const syntax=this.expand(interfaceSignature(entry));
    // This separate complete walk sees replacement trees as well as the
    // original interface. Both bare and applied recursive values are facts.
    const dependencies=this.analysis.dependencies(syntax);
    return {syntax,dependencies,recursive:dependencies.find(use=>use.category==="recursive-helper")??null,
      pending:dependencies.filter(unresolvedBindingUse)};
  }
  // A support planner needs the beta-expanded shape; admission needs every
  // application, domain and result annotation. The analysis view is valid
  // only under the accompanying complete-interface checking obligation.
  type(entry) {
    const checking=this.expand(interfaceType(entry));
    let index=0;
    const view=tree=>bindingSyntaxView(checking,tree);
    const normalize=tree=>scopeMapped(tree,{deferred:true,extend:at=>at,enter:node=>{
      if(node.kind!=="call")return node;
      let fn=normalize(node.fn),args=node.args.map(normalize);
      if(fn.kind==="bindingReference"&&fn.resolution.tag==="reserved"&&fn.resolution.label==="typed"
        &&args.length===2&&!node.implicitArgs)return args[1];
      if(node.implicitArgs||args.some(arg=>arg.kind==="namedArgument"))return {...node,fn,args};
      let reduced=false;
      while(args.length&&(fn.kind==="lambda"||fn.kind==="binderGroup"&&fn.binderKind==="lambda")) {
        // Shared domains belong outside all binders in the group. A
        // partially applied group keeps its remaining telescope intact.
        const names=fn.kind==="lambda"?[fn.name]:fn.names,count=Math.min(names.length,args.length);
        if(names.some(name=>!name.bindingId))return {...node,fn,args};
        const body=count===names.length?fn.body:{...fn,names:names.slice(count)};
        const replacements=new Map(names.slice(0,count).map((name,k)=>[name.bindingId,view(args[k])]));
        fn=normalize(substituteBindingSyntax(view(body),replacements,this.table,
          [...this.owner,"analysis",String(this.#serial++),String(index++)]).tree);
        args=args.slice(count);
        reduced=true;
      }
      return args.length||!reduced?{...node,fn,args}:fn;
    }},null);
    return {checking,analysis:view(normalize(checking.tree)),
      obligations:[{kind:"interface-check",entry:entry.id,origin:entry.binding.origin}]};
  }
}
