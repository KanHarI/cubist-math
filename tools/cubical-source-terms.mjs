// Print derived cubical syntax as explicit, independently checkable MathScript.
// Used only when migrating source proofs, never as a verification shortcut.
export function cubicalSource(term) {
  const reserved=new Set(), dimensions=new Map();
  const collect=t=>{if(t&&typeof t==='object'){if(t.name)reserved.add(t.name);Object.values(t).forEach(collect);}};
  collect(term);
  const dim=name=>{if(!dimensions.has(name)){let fresh=`interval_${name}`;while(reserved.has(fresh))fresh+='_';reserved.add(fresh);dimensions.set(name,fresh);}return dimensions.get(name);};
  const interval=formula=>formula.length?formula.map(clause=>clause.length?clause.map(lit=>lit.endsWith(':1')?dim(lit.slice(0,-2)):`flip(${dim(lit.slice(0,-2))})`).reduce((a,b)=>`meet(${a}, ${b})`):'1').reduce((a,b)=>`join(${a}, ${b})`):'0';
  const face=formula=>formula.length?formula.map(clause=>clause.length?`(${clause.map(lit=>`on(${dim(lit.slice(0,-2))}, ${lit.slice(-1)})`).join(' and ')})`:'1').join(' or '):'0';
  const s=t=>{
    switch(t.tag) {
      case 'Var':case 'DefRef':return t.name;
      case 'U':return `U${t.level}`;
      case 'Nat':case 'Unit':case 'Void':return t.tag;
      case 'Point':return 'tt';case 'Zero':return '0';case 'Succ':return `succ(${s(t.value)})`;
      case 'Pi':return `(forall ${t.name} : ${s(t.domain)}, ${s(t.body)})`;
      case 'Sigma':return `(exists ${t.name} : ${s(t.domain)}, ${s(t.body)})`;
      case 'Lam':return `(fun (${t.name} : ${s(t.domain)}) => ${s(t.body)})`;
      case 'App':{const args=[];let fn=t;while(fn.tag==='App'){args.unshift(s(fn.arg));fn=fn.fn;}return `${s(fn)}(${args.join(', ')})`;}
      case 'Path':return `PathP(fun (${dim(t.dim)} : Interval) => ${s(t.family)}, ${s(t.left)}, ${s(t.right)})`;
      case 'PLam':return `path(fun (${dim(t.dim)} : Interval) => ${s(t.family)}, fun (${dim(t.dim)} : Interval) => ${s(t.body)})`;
      case 'PApp':return `at(${s(t.path)}, ${interval(t.arg)})`;
      case 'Comp':return `comp(fun (${dim(t.dim)} : Interval) => ${s(t.family)}, ${s(t.base)}${t.system.map(part=>`, face_when(${face(part.face)}, fun (${dim(t.dim)} : Interval) => ${s(part.term)})`).join('')})`;
      case 'Pair':return `typed(${s(t.as)}, (${s(t.first)}, ${s(t.second)}))`;
      default:throw Error(`No source notation for ${t.tag}`);
    }
  };return s(term);
}
