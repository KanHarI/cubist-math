// Retained interfaces supply already resolved occurrences. Display labels
// are used in explanations only; an eventual field cannot retarget an
// occurrence that resolved to an earlier parameter, helper or missing name.
import {bindingUses} from "./binding-syntax.mjs";

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
  validateHelpers() {
    const visiting=new Set(),done=new Set(),path=[],pending=[];
    const visit=entry=>{
      if(category(entry)!=="helper"||done.has(entry.id))return;
      if(visiting.has(entry.id)) {
        const cycle=path.slice(path.indexOf(entry.id)).concat(entry.id);
        throw new TypeError(`Cycle among nonrecursive helpers: ${cycle.map(id=>this.byIdentity.get(id).label??id).join(" -> ")}`);
      }
      visiting.add(entry.id);path.push(entry.id);
      for(const use of this.references(entry.syntax,{conditional:true}))
        if(use.kind==="binding") {
          const dependency=this.byIdentity.get(use.id);
          if(dependency)visit(dependency);
        } else if(use.kind==="deferred"||use.kind==="deferred-pattern")pending.push({owner:entry.id,...use});
      path.pop();visiting.delete(entry.id);done.add(entry.id);
    };
    for(const entry of this.byIdentity.values())visit(entry);
    // An acyclic known graph is not a claim about unresolved alternatives.
    return {pending};
  }
}
