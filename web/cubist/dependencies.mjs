// Retained interfaces supply already resolved occurrences. Display labels
// are used in explanations only; an eventual field cannot retarget an
// occurrence that resolved to an earlier parameter, helper or missing name.
import {bindingUses} from "./binding-syntax.mjs";

// Pattern and activation tokens introduce decisions, not dependencies. Their
// receiver expressions and body occurrences carry the actual uses. Patterns retain
// both interpretations: the owned variable or the source enclosing binding.
// Support may be conditional on the eventual pattern check when every such
// interpretation is known. Openings still require their interface; a missing
// conditional branch must fail elaboration, never acquire a destination name.
export function dependencyUses(syntax) {
  return bindingUses(syntax,{conditional:true}).filter(use=>{
    if(["deferred-pattern","deferred-activation"].includes(use.kind))return false;
    if(use.kind==="deferred") {
      let value=use.resolution;
      while(value.tag==="slot")value=value.enclosing;
      return value.tag==="opening";
    }
    return !(use.kind==="missing"&&use.conditions?.length);
  });
}

const category=entry=>entry.kind==="sort"?"carrier"
  :entry.kind==="derived"?entry.recursive?"recursive-helper":"helper":entry.kind;

const requestOrigin=use=>{
  const frames=use.origin?.expansion??[];
  return frames.length?{...use,origin:frames.at(-1).site,definitionOrigin:use.origin,
    via:frames.filter(frame=>frame.kind==="helper").map(frame=>frame.binding).reverse()}:use;
};

export class DependencyAnalysis {
  constructor(entries) {
    this.byIdentity=new Map();
    for(const entry of entries) {
      if(typeof entry.id!=="string"||this.byIdentity.has(entry.id))
        throw new TypeError("A retained dependency interface needs distinct binding identities.");
      this.byIdentity.set(entry.id,entry);
    }
  }
  references(syntax,options) {
    return bindingUses(syntax,options).map(use=>requestOrigin(use.kind!=="binding"?{...use,category:use.kind}
      :{...use,category:category(this.byIdentity.get(use.id)??{kind:"external"})}));
  }
  dependencies(syntax,options) {
    const queue=this.references(syntax,options).map(use=>({via:[],...use})),found=[],seen=new Set();
    for(let index=0;index<queue.length;index++) {
      const use=queue[index];
      if(use.kind!=="binding") {found.push(use);continue;}
      if(seen.has(use.id))continue;
      seen.add(use.id);found.push(use);
      const entry=this.byIdentity.get(use.id);
      if(!entry?.syntax)continue;
      for(const dependency of this.references(entry.syntax,options))
        queue.push({...dependency,origin:use.origin,definitionOrigin:dependency.definitionOrigin??dependency.origin,
          via:[...use.via,use.id,...(dependency.via??[])]});
    }
    return found;
  }
  first(syntax,categories,options) {
    return this.dependencies(syntax,options).find(use=>categories.includes(use.category))??null;
  }
  // Structural self-recursion is a separate elaborator mechanism. A cycle
  // among helpers which promise to inline must fail before expansion starts.
  validateHelperCycles() {
    const visiting=new Set(),done=new Set(),path=[];
    const visit=entry=>{
      if(category(entry)!=="helper"||done.has(entry.id))return;
      if(visiting.has(entry.id)) {
        const cycle=path.slice(path.indexOf(entry.id)).concat(entry.id);
        throw new Error(`Cycle among helper definitions: ${cycle.map(id=>this.byIdentity.get(id).label??id).join(" -> ")}`);
      }
      visiting.add(entry.id);path.push(entry.id);
      for(const use of this.references(entry.syntax,{conditional:true}))
        if(use.kind==="binding") {
          const dependency=this.byIdentity.get(use.id);
          if(dependency)visit(dependency);
        }
      path.pop();visiting.delete(entry.id);done.add(entry.id);
    };
    for(const entry of this.byIdentity.values())visit(entry);
  }
}
