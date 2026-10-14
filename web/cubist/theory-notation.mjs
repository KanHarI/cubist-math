// The public shape of a field's notation is independent of the reference
// representation. Consumers supply the carrier test in their own interface.
const located=(error,node)=>Object.assign(error,{offset:node.start,sourceEnd:node.end});
export const notationKey=notation=>notation.numeral?"numeral":notation.unary?"unary -":notation.operator;
export const notationViews=notation=>Object.freeze({left:notation.leftView??null,right:notation.rightView??null});
export const notationAlternative=(model,operator,entry,{applied=true}={})=>{
  const receiver=`${model?`${model}.`:""}${entry.label}`;
  return entry.call?`${receiver}.${entry.parentField}(${operator==="unary -"?"x":"x, y"})`
    :applied?operator==="unary -"?`${receiver}.(-) x`:`x ${receiver}.(${operator}) y`:`${receiver}.(${operator})`;
};

export function validateFieldNotation(item,{theory:T,isCarrier}) {
  if(!item.notation)return null;
  const {operator,left,right,unary,leftView,rightView,numeral}=item.notation;
  if(item.kind==="sort") {
    if(unary||item.params.length!==2||left?.text!==item.params[0].name.text||right?.text!==item.params[1].name.text)
      throw located(Error(`A notation names a family's two indices in order, as in le(x, y : M) : prop U notation x <= y.`),item.notation);
  } else if(numeral) {
    if(item.kind!=="derived"||item.params.length!==1||!(item.params[0].type.kind==="name"&&item.params[0].type.name==="Nat"))
      throw located(Error(`notation numeral reads a plain numeral: it marks a derived operation of one natural number, as def of_nat(n : Nat) : R := … notation numeral.`),item.notation);
  } else {
    if(unary) {
      if(!["operation","derived"].includes(item.kind)||item.params.length!==1||left.text!==item.params[0].name.text)
        throw located(Error(`-x names an operation's one argument, as in neg(x : M) : M notation -x.`),item.notation);
    } else {
      if(!["operation","derived"].includes(item.kind)||item.params.length!==2)
        throw located(Error(`A notation names an operation's two arguments, as in mul(x, y : M) : M notation x * y; ${item.name.text} has ${["none","one"][item.params.length]??item.params.length}.`),item.notation);
      if(left.text!==item.params[0].name.text||right.text!==item.params[1].name.text)
        throw located(Error(`The notation of ${item.name.text} writes its arguments in order: ${item.params[0].name.text} ${operator} ${item.params[1].name.text}.`),item.notation);
    }
    for(const [k,token,view] of unary?[[0,left,leftView]]:[[0,left,leftView],[1,right,rightView]])
      if(!view&&!isCarrier(k))
        throw located(Error(`The notation of ${item.name.text} reads ${token.text} in the notation selected where it is used, which is ${T}'s; ${token.text} is no carrier's element: name the notation it is read in, as ${token.text===left?.text&&!unary?`nat.(${token.text}) ^ y`:`x ^ nat.(${token.text})`}.`),token);
  }
  return Object.freeze({key:notationKey(item.notation),views:notationViews(item.notation)});
}
