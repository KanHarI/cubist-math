// Ordinary declaration telescopes keep each written group's shared domain
// outside every binder in that group. Both scoping and lambda construction
// use these groups, including inferred declarations' parameter metadata.
export function parameterGroups(params) {
  const groups = [];
  for (let k = 0; k < params.length;) {
    const first = params[k++], parameters = [first];
    while (first.group !== undefined && k < params.length && params[k].group === first.group) parameters.push(params[k++]);
    groups.push({parameters, after: k, ...(first.bound ? {bound: first.bound} : {domain: first.type})});
  }
  return groups;
}

// The public argument convention interleaves each leveled parameter and
// its evidence. Both telescope construction and implicit call completion
// consume this layout, rather than deriving separate argument orders.
export const evidenceLayout=params=>params.flatMap((p,index)=>[
  {index,kind:"argument"},...(p.level?[{index,kind:"evidence",level:p.level}]:[])]);

// Resolve a written group's shared domain before any of its binders. Only
// after resolution, reorder its explicit evidence into the public layout;
// the shared domain then carries IDs and cannot be captured by that order.
export function evidenceTelescope(tree) {
  const evidence=new Map();
  if(!tree.params?.some(p=>p.level))return {tree,evidence};
  const params=[],order=[];
  for(const {parameters} of parameterGroups(tree.params)) {
    const group=params.length;
    const originals=parameters.map(p=>({...p,group})),witnesses=new Map();
    params.push(...originals);
    for(const [index,p] of originals.entries())if(p.level) {
      if(!["set","prop"].includes(p.level)||p.bound||p.name.text==="_")
        throw new TypeError("A leveled parameter needs a named type and set or prop evidence.");
      const type={kind:"call"}; // private marker, consumed before traversal
      evidence.set(type,{parameter:p,builtin:p.level==="set"?"IsSet":"IsProp"});
      const witness={name:{...p.name,text:`${p.name.text}_is_${p.level}`,synthetic:true},type,group:params.length};
      witnesses.set(index,witness);params.push(witness);
    }
    const first=order.length;
    for(const {index,kind} of evidenceLayout(originals))order.push({parameter:kind==="argument"?originals[index]:witnesses.get(index),
      group:witnesses.size?order.length:first});
  }
  return {tree:{...tree,params},evidence,order};
}

function parameterBinders(kind,params,body) {
  for (const group of parameterGroups(params).reverse()) {
    const {parameters, bound, domain} = group;
    const binder = bound ? {bound} : {domain};
    body = parameters.length === 1
      ? {kind, name: parameters[0].name, ...binder, body}
      : {kind: "binderGroup", binderKind: kind, names: parameters.map(p => p.name), ...binder, body};
  }
  return body;
}
export const parameterLambdas=(params,body)=>parameterBinders("lambda",params,body);
export const parameterForalls=(params,body)=>parameterBinders("forall",params,body);

// The native clause telescope introduces fields, recursive hypotheses and
// then dimensions. Fields and dimensions name distinct variables; hypotheses
// deliberately may shadow fields. Deferred patterns enforce distinctness
// only when their types have decided which tokens introduce variables.
export function clauseTelescope(clause,{args=clause.args??[],hypotheses=clause.hypotheses??[]}={}) {
  return [
    {field:"args",tokens:args,role:"pattern",distinct:true},
    {field:"binders",tokens:clause.binders??[],role:"local",distinct:true},
    {field:"hypotheses",tokens:hypotheses,role:"local",distinct:false},
    {field:"coordinates",tokens:clause.coordinates??[],role:"dimension",distinct:true},
  ];
}

// One clause-wide policy for direct and compiled clauses. A lowered key is
// never a public variable name, and a constructor decision never calls this.
export function bindClauseName(bound,token,locate=error=>error) {
  const label=token.label??token.text;
  if(label==="_")return bound;
  if(bound.has(label))throw locate(Error(`${label} is bound twice in this clause: name each variable once.`),token);
  return new Set(bound).add(label);
}

// The parser's inferred-declaration form repeats its header as lambdas and
// metadata. Canonicalize before assigning identities, then rebuild both
// views from the same resolved parameter tokens at the adapter boundary.
export function declarationTelescope(declaration) {
  const params = declaration.valueParameters;
  if (!params?.length) return {tree: declaration, inferred: false};
  if (declaration.params?.length) throw new TypeError("A declaration has two parameter telescopes.");
  let value = declaration.value;
  for (const {parameters} of parameterGroups(params)) {
    const names = value?.kind === "lambda" ? [value.name] : value?.kind === "binderGroup" && value.binderKind === "lambda" ? value.names : [];
    if (names.length !== parameters.length || names.some((name, k) => name !== parameters[k].name))
      throw new TypeError("Inferred declaration metadata does not describe its parameter lambdas.");
    value = value.body;
  }
  return {tree: {...declaration, params, valueParameters: [], value}, inferred: true};
}
