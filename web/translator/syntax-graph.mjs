// Shared, bounded operations on inert cubical syntax DAGs. These utilities
// preserve object identity; they do not decide typing or proof equality.
// The work is counted, never timed, so the same construction succeeds or
// fails the same way on every machine; `checkDeadline` polls the
// declaration's safety timeout, when one is set.
export function syntaxGraphBudget({checkDeadline,maxVisits=500000}={}) {
  let visits=0;
  return {tick() {
    if(++visits>maxVisits)throw Object.assign(Error('Cubical syntax construction term-size budget exceeded.'),{kind:"budget"});
    if((visits&255)===1)checkDeadline?.();
  }};
}

// Cache by the dimension assignment, not by a Map object's identity or
// insertion order. Callers may pass mutable maps, so compute this afresh.
export function dimensionContextKey(dimensions) {
  if(!dimensions.size)return "[]";
  return JSON.stringify([...dimensions].sort(([left],[right])=>
    left<right?-1:left>right?1:0));
}

export function visitSyntax(root,visit,{budget=syntaxGraphBudget(),children=Object.values}={}) {
  const seen=new WeakSet(),pending=[root];
  while(pending.length) {
    const value=pending.pop();
    budget.tick();
    if(value&&typeof value==='object') {
      if(seen.has(value))continue;
      seen.add(value);
    }
    visit(value);
    if(value&&typeof value==='object')
      for(const child of children(value))pending.push(child);
  }
}

export function syntaxNames(root,{budget,...options}={}) {
  const used=new Set();
  visitSyntax(root,value=>{
    if(typeof value==='string')used.add(value.replace(/:[01]$/,''));
  },{budget:budget??syntaxGraphBudget({maxVisits:250000,...options})});
  return used;
}

// `replace` returns undefined to copy a node, or an explicit replacement.
// Object and array children are copied once, including under multiple parents.
export function mapSyntax(root,replace,{budget=syntaxGraphBudget()}={}) {
  const memo=new WeakMap(),pending=[];
  const copy=value=>{
    if(!value||typeof value!=='object')return value;
    if(memo.has(value))return memo.get(value);
    budget.tick();
    const replacement=replace(value);
    if(replacement!==undefined) {
      memo.set(value,replacement);
      return replacement;
    }
    const result=Array.isArray(value)?[]:{};
    memo.set(value,result);
    pending.push([value,result]);
    return result;
  };
  const result=copy(root);
  while(pending.length) {
    const [source,target]=pending.pop();
    for(const [key,value] of Object.entries(source)) {
      budget.tick();
      target[key]=copy(value);
    }
  }
  return result;
}

// A compact, immutable description for transport/inspection. Every shared
// object is written once; JSON serialization cannot expand a small DAG into
// an exponential tree. This is data only, never an exported kernel artifact.
// Non-enumerable annotations (including checked PApp caches) confer no
// authority here. Live maps, class instances, accessors and functions cannot
// accidentally become persistent context state.
export const snapshotTextLimit=4000000;
export function snapshotSyntax(root,{budget=syntaxGraphBudget(),maxText=snapshotTextLimit}={}) {
  const indices=new WeakMap(),pending=[],nodes=[];
  let text=0;
  const string=value=>{
    text+=value.length;
    if(text>maxText)throw new TypeError("Syntax snapshot text budget exceeded.");
    return value;
  };
  const encode=value=>{
    budget.tick();
    if(value===undefined)return Object.freeze({undefined:true});
    if(value===null||typeof value==="boolean")return value;
    if(typeof value==="string")return string(value);
    if(typeof value==="number"&&Number.isFinite(value))return value;
    if(typeof value!=="object")throw new TypeError("A syntax snapshot contains non-data values.");
    if(indices.has(value))return Object.freeze({node:indices.get(value)});
    const prototype=Object.getPrototypeOf(value);
    if(!Array.isArray(value)&&prototype!==Object.prototype&&prototype!==null)
      throw new TypeError("A syntax snapshot cannot retain a live object.");
    const index=nodes.length;
    indices.set(value,index);nodes.push(null);pending.push([index,value]);
    return Object.freeze({node:index});
  };
  const entry=encode(root);
  while(pending.length) {
    const [index,value]=pending.pop(),descriptors=Object.getOwnPropertyDescriptors(value);
    const fields=[];
    for(const [key,descriptor] of Object.entries(descriptors)) {
      budget.tick();
      if(!descriptor.enumerable)continue;
      if(!Object.hasOwn(descriptor,"value"))throw new TypeError("A syntax snapshot cannot evaluate accessors.");
      fields.push(Object.freeze([string(key),encode(descriptor.value)]));
    }
    nodes[index]=Object.freeze({array:Array.isArray(value),
      ...(Array.isArray(value)?{length:value.length}:{nullPrototype:Object.getPrototypeOf(value)===null}),
      fields:Object.freeze(fields)});
  }
  // Reject cycles, while counting each edge once. The source visitor's memo
  // is deliberately not a proof of acyclicity (mapSyntax can copy cycles).
  const degrees=nodes.map(()=>0),edges=nodes.map(node=>node.fields.flatMap(([,value])=>
    value&&typeof value==="object"&&Object.hasOwn(value,"node")?[value.node]:[]));
  for(const children of edges)for(const child of children)degrees[child]++;
  const ready=[];
  degrees.forEach((degree,index)=>{if(!degree)ready.push(index);});
  let visited=0;
  while(ready.length) {
    const index=ready.pop();visited++;budget.tick();
    for(const child of edges[index])if(--degrees[child]===0)ready.push(child);
  }
  if(visited!==nodes.length)throw new TypeError("A syntax snapshot must be acyclic.");
  return Object.freeze({version:1,root:entry,nodes:Object.freeze(nodes)});
}
