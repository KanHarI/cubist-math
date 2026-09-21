// Alpha-renaming for inert syntax transport, not a typing rule. Dimension
// slots belong to live names, not every syntactic ancestor binder. Native
// checking separately accounts for dimensions hidden in local-variable types.
const children={
  U:[],Var:[],Ref:[],DefRef:[],Nat:[],Zero:[],Unit:[],Point:[],Void:[],
  Pi:['domain','body'],Lam:['domain','body'],Sigma:['domain','body'],W:['domain','body'],
  App:['fn','arg'],Pair:['as','first','second'],Fst:['pair'],Snd:['pair'],Succ:['value'],
  NatRec:['motive','zero','step','value'],Abort:['as','impossible'],Sup:['as','label','children'],
  WRec:['motive','step','value'],Sum:['left','right'],Inl:['as','value'],Inr:['as','value'],
  SumRec:['motive','left','right','value'],UnitRec:['motive','point','value'],
  PApp:['path','pathType'],Pushout:['center','left','right','maps'],
  PushLeft:['as','value'],PushRight:['as','value'],PushPath:['as','value'],
  PushElim:['motive','left','right','bridge'],Unglue:['as','value'],
};
const cache=new WeakMap();
const add=(target,source)=>{for(const name of source)target.add(name);};
function formulaNames(formula) {
  const names=new Set();
  for(const clause of formula)for(const literal of clause) {
    if(typeof literal!=='string'||!/:[01]$/.test(literal))throw Error('Invalid dimension literal.');
    names.add(literal.slice(0,-2));
  }
  formula.forEach(Object.freeze);
  Object.freeze(formula);
  return names;
}
function boundNames(term) {
  const result=new Set();
  if(term.tag!=='HComp')add(result,freeDimensions(term.family));
  if(term.tag==='PLam')add(result,freeDimensions(term.body));
  if(['Comp','HComp'].includes(term.tag))for(const piece of term.system)
    add(result,freeDimensions(piece.term));
  result.delete(term.dim);
  return result;
}
export function freeDimensions(term) {
  if(!term||typeof term!=='object')throw Error('Expected cubical syntax.');
  const cached=cache.get(term);
  if(cached)return new Set(cached);
  const result=new Set(),tag=term.tag;
  if(['Path','PLam','Comp','HComp','Trans'].includes(tag)) {
    add(result,boundNames(term));
    if(tag==='Path') {
      add(result,freeDimensions(term.left));
      add(result,freeDimensions(term.right));
    }
    if(['Comp','HComp','Trans'].includes(tag))add(result,freeDimensions(term.base));
    if(tag==='HComp')add(result,freeDimensions(term.family));
    if(['Comp','HComp'].includes(tag))for(const piece of term.system)add(result,formulaNames(piece.face));
    if(tag==='Trans')add(result,formulaNames(term.face));
  } else if(['Glue','GlueTerm'].includes(tag)) {
    add(result,freeDimensions(term.base));
    if(tag==='GlueTerm')add(result,freeDimensions(term.as));
    for(const piece of term.system) {
      add(result,formulaNames(piece.face));
      for(const key of tag==='Glue'?['type','equiv']:['term'])add(result,freeDimensions(piece[key]));
    }
  } else {
    if(!children[tag])throw Error(`Unsupported cubical syntax: ${tag}`);
    for(const key of children[tag])if(term[key])add(result,freeDimensions(term[key]));
    if(['PApp','PushPath'].includes(tag))add(result,formulaNames(term.arg));
  }
  // Like the checked codec, this analysis consumes immutable syntax. Freeze
  // every inspected child before memoizing, so shared DAGs are visited once
  // without allowing later mutation to invalidate a liveness decision.
  if(term.system) {
    term.system.forEach(Object.freeze);
    Object.freeze(term.system);
  }
  Object.freeze(term);
  cache.set(term,result);
  return new Set(result);
}

export function bindDimensions(term,dimensions=new Map()) {
  if(!['Path','PLam','Comp','HComp','Trans'].includes(term.tag))throw Error('Expected a dimension binder.');
  const live=boundNames(term),inner=new Map();
  for(const [name,slot]of dimensions)if(live.has(name))inner.set(name,slot);
  const occupied=new Set(inner.values());
  let dim=0;
  while(occupied.has(dim))dim++;
  if(dim>=64)throw Error('Cubical prototype supports 64 simultaneously live dimensions.');
  inner.set(term.dim,dim);
  return {dim,inner};
}
