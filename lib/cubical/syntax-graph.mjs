// Shared, bounded operations on inert cubical syntax DAGs. These utilities
// preserve object identity; they do not decide typing or proof equality.
export function syntaxGraphBudget({deadline=performance.now()+1000,
  checkDeadline,maxVisits=500000}={}) {
  let visits=0;
  return {tick() {
    if(++visits>maxVisits)throw Error('Cubical syntax construction term-size budget exceeded.');
    if((visits&255)===1) {
      if(performance.now()>deadline)throw Error('Cubical syntax construction elapsed-work budget exceeded.');
      checkDeadline?.();
    }
  }};
}

// Cache by the dimension assignment, not by a Map object's identity or
// insertion order. Callers may pass mutable maps, so compute this afresh.
export function dimensionContextKey(dimensions) {
  return JSON.stringify([...dimensions].sort(([left],[right])=>
    left<right?-1:left>right?1:0));
}

export function visitSyntax(root,visit,{budget=syntaxGraphBudget()}={}) {
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
      for(const child of Object.values(value))pending.push(child);
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
