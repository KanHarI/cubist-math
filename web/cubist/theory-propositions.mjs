// Classify laws over retained field identities and their carrier evidence.
// Display labels are used only to explain a refusal.
const reference=node=>node?.kind==="bindingReference"&&node.resolution.tag==="binding"?node.resolution.id:null;
const builtin=(node,label)=>node.kind==="bindingReference"&&node.resolution.tag==="reserved"&&node.resolution.label===label;

export function notAProposition(statement,fields,proposition=()=>false,header=[]) {
  const key=reference;
  const sortNamed=(node,bound)=>{
    const id=key(node?.kind==="call"?node.fn:node);
    return id!==null&&!bound.has(id)&&fields.get(id)?.kind==="sort"?id:null;
  };
  const returns=field=>{
    if(field?.kind!=="operation")return null;
    let type=field.type;
    while(type.kind==="forall"||type.kind==="binderGroup")type=type.body;
    return sortNamed(type,new Map());
  };
  const sortOf=(term,bound)=>{
    const id=key(term),head=key(term.kind==="call"?term.fn:term);
    return id!==null?(bound.has(id)?bound.get(id):returns(fields.get(id)))
      :head!==null&&!bound.has(head)?returns(fields.get(head)):null;
  };
  const propositionSort=id=>fields.get(id)?.kind==="sort"
    &&[...fields.values()].some(field=>field.kind==="evidence"&&field.of===id&&field.evidence==="IsProp");
  const check=(node,bound)=>{
    if(node.kind==="forall"||node.kind==="binderGroup"&&node.binderKind==="forall") {
      const sort=sortNamed(node.domain,bound),inner=new Map(bound);
      for(const binder of node.kind==="forall"?[node.name]:node.names)inner.set(binder.bindingId,sort);
      return check(node.body,inner);
    }
    if(node.kind==="binary"&&node.operator==="->")return check(node.right,bound);
    if(node.kind==="binary"&&node.operator==="and")return check(node.left,bound)??check(node.right,bound);
    if(node.kind==="binary"&&node.operator==="=") {
      const sort=node.carrier?sortNamed(node.carrier,bound):sortOf(node.left,bound)??sortOf(node.right,bound);
      if(sort===null)return {node,why:"the sides of an equation in it are not elements of one of the theory's sorts"};
      return [...fields.values()].some(field=>field.kind==="evidence"&&field.of===sort)?null
        :{node,why:`${fields.get(sort).name} has no h-level, so an equation between its elements is not a proposition`};
    }
    const id=key(node);
    if(!bound.has(id)&&(["Void","Unit"].some(label=>builtin(node,label))&&!fields.has(id)||propositionSort(id)))return null;
    if(node.kind==="call"&&sortNamed(node,bound)!==null&&propositionSort(key(node.fn)))return null;
    const head=node.kind==="call"?node.fn:node,declaration=reference(head);
    if(declaration!==null&&!bound.has(declaration)&&!fields.has(declaration)&&proposition(declaration))return null;
    return {node,why:fields.get(id)?.kind==="sort"?`${fields.get(id).name} is a sort, whose elements are data`:"its statement is none of these"};
  };
  return check(statement,new Map(header.map(id=>[id,null])));
}
