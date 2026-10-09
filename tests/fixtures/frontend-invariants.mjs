// Bounded source generation, independent client equations and shrink steps.
// No expected term is obtained from the compiler's theory generator.
export const ciSeeds=[0,1,2,3,4,5,6,7];
export const caseLimit=64;
export function configuration(seed) {
  if(!Number.isSafeInteger(seed)||seed<0||seed>=caseLimit)throw Error("seed must be 0..63");
  return {seed,imported:!!(seed&1),inherited:!!(seed&2),renamed:!!(seed&4),
    depth:1+Math.floor(seed/8)+(seed%3),binder:["c","S","x","point"][seed%4],noise:!!(seed&1),recursive:true,paths:true};
}
export function generate(config) {
  const {imported,inherited,renamed,depth,binder,noise,recursive,paths}=config;
  const names=renamed&&inherited?{M:"Carrier",c:"point",op:"combine"}:{M:"M",c:"c",op:"op"};
  const {M,c,op}=names, model=inherited?"Child":"T";
  const header=`import hlevels; import nat;
notation lexical { numeral(n : Nat) := n; }
use lexical;
${noise?"def f : Unit := tt; def result : Unit := tt; def c1 : Unit := tt;":""}`;
  const helpers=Array.from({length:depth},(_,i)=>`def helper${i}(x : M) : M := ${i?`helper${i-1}(x)`:"op(0,x,c)"};`).join("\n");
  const parent=`${header}
theory T(U < UU0) { M : set U; c : M; op(n : Nat, x, y : M) : M;
  ${helpers}
  def wrapped(${binder} : M, proof_ : ${binder} = ${binder}) : M := helper${depth-1}(${binder});
  law same(c : M) : helper${depth-1}(c) = op(0,c,c);
  ${recursive?"def iter(n : Nat) : M := match n { zero => c; succ(k) => op(0,iter(k),c); };\ndef twice(n : Nat) : M := op(0,iter(n),c);":""}
}`;
  const shifted=`notation shifted { numeral(n : Nat) := succ(n); }
use shifted;`;
  const child=inherited?`theory Child(U < UU0) extends T${renamed?"(M := Carrier, c := point, op := combine)":""} {
  def fresh(x : ${M}) : ${M} := ${op}(0,x,${c});
}`:"";
  const setup=`${imported?"import fixture;":parent}\n${shifted}\n${child}`;
  const clients=`
def intended(S : ${model}(U0), x : S.${M}) : S.wrapped(x,refl(x)) = S.${op}(zero,x,S.${c}) := refl(S.${op}(zero,x,S.${c}));
def captured(S : ${model}(U0), x : S.${M}) : S.wrapped(x,refl(x)) = S.${op}(zero,x,x) := refl(S.${op}(zero,x,x));
def law_meaning(S : ${model}(U0), x : S.${M}) : S.${op}(zero,x,S.${c}) = S.${op}(zero,x,x) := S.same(x);
def identity(S : ${model}(U0), x : S.${M}) : ${model}.Hom.compose(${model}.Hom.id(S),${model}.Hom.id(S)).map(x) = x { rfl; }
${inherited?`def child_selection(S : ${model}(U0), x : S.${M}) : S.fresh(x) = S.${op}(succ(zero),x,S.${c}) { rfl; }`:""}
${recursive?`def earlier_call(S : ${model}(U0)) : S.twice(zero) = S.${op}(zero,S.${c},S.${c}) { rfl; }`:""}
initial N : ${model}(U0);
def generated(x : N) : N.model.wrapped(x,refl(x)) = N.${op}(zero,x,N.${c}) { rfl; }
def forget(x : N) : Unit := match x { N.${c} => tt; _ => tt; };
def forgotten : forget(N.${op}(zero,N.${c},N.${c})) = tt { rfl; }
free W(A : U0) : ${model}(U0) on A;
def fold_computes(S : ${model}(U0), x : S.${M}) : W.fold(S.${M},S,fun (a : S.${M}) => a).map(W.gen(x)) = x { rfl; }
def ordinary : U0 := forall unused : Unit. Unit;
${paths?`inductive Boundary : set U0 { left_; right_; path_ : left_ = right_; }
def mismatch(x : Boundary) : Boundary := match x { left_ => left_; _ => right_; };`:""}`;
  return {source:setup+clients,fixtures:imported?{fixture:parent}:{},parent,model,names,
    accepted:["intended","law_meaning","identity","generated","forgotten","fold_computes",...(inherited?["child_selection"]:[]),...(recursive?["earlier_call"]:[])],
    expectedGaps:["captured",...(paths?["mismatch"]:[])],
    labelScope:`law same(c : M) : helper${depth-1}(c) = op(0,c,c);`};
}

// Greedy, dependency-aware reduction: each candidate is another well-formed
// configuration. Keep only candidates reproducing the same assertion code.
// The fixed order and bounded attempts make a failure replayable.
export async function minimize(config,fails,maxAttempts=12) {
  let current={...config},attempts=0;
  for(const key of ["noise","paths","recursive","renamed","imported","inherited","depth","binder"]) {
    const value=key==="depth"?1:key==="binder"?"x":false;
    if(current[key]===value||attempts>=maxAttempts)continue;
    const next={...current,[key]:value};attempts++;
    if(await fails(next))current=next;
  }
  return {config:current,attempts};
}
