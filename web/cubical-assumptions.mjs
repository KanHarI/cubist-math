// Explicit logical assumptions, represented as an ordinary context: the
// axioms that definitions state, `def Name := axiom F;`. The C kernel checks
// proofs abstracted over that context; it is never asked to trust a new
// inference rule or a theorem-specific axiom.
import {stem} from './translator/names.mjs';
const V=name=>({tag:'Var',name});
const pi=(name,domain,body)=>({tag:'Pi',name,domain,body});
const app=(fn,...args)=>args.reduce((fn,arg)=>({tag:'App',fn,arg}),fn);
// The library's axioms keep their names as labels, as LEM and Choice do; any
// other axiom is labelled by its module's name and its own, module::Name
// (the user's decision of 2026-10-26). A bare label needs a library module
// itself, read from library/ (`library`): a module of the same name
// elsewhere, or edited, is labelled as any other. tests/library.test.mjs
// keeps the library's axiom names distinct.
// `def Name := axiom F;` (docs/roadmaps/hott/h1-truncation-migration.md,
// "Axioms as definitions"). F, already elaborated in `scope`, is a type, or
// a family of types: a telescope of universe and ordinary parameters with a
// type-valued body. The assumption's type closes that body over the
// telescope, which F's own type gives: F is applied to a fresh variable for
// each parameter, and the weak head of the application is the body. So
// `axiom ExcludedMiddle` has type forall U < UU0. forall A : U. …, not
// ExcludedMiddle's own type. The checker adds one context entry of that
// type, named by the definition, module__Name, and every use, alias and
// application shares it. Like any assumption it computes nothing, and is
// listed by its label wherever a result depends on it.
export function axiomAssumption(checker,{module,declaration,binding,library=false},statement,scope) {
  const binders=[];
  let inner=scope,applied=statement,type=scope.nf(scope.infer(statement).type);
  while(type.tag==='LPi'||type.tag==='Pi') {
    const name=inner.fresh(stem(type.name)),variable=V(name);
    if(type.tag==='LPi') {
      inner=inner.bind(name,{tag:'LBound',tier:1});
      applied={tag:'LApp',fn:applied,level:variable};
      binders.push({name});
    } else {
      inner=inner.bind(name,type.domain);
      applied=app(applied,variable);
      binders.push({name,domain:type.domain});
    }
    type=inner.nf(inner.infer(applied).type);
  }
  if(type.tag!=='U')throw Error('An axiom states a type, or a family of types: axiom T; or axiom F; where F(x) is a type.');
  const body=binders.length ? inner.nf(applied) : statement;
  const closed=binders.reduceRight((body,binder)=>binder.domain ? pi(binder.name,binder.domain,body)
    : {tag:'LPi',name:binder.name,body},body);
  scope.spend('queries');
  // The assumption is named by the definition's identity with the
  // assumption mark, which no declaration, binder or generated name holds
  // (names.mjs, assumptionMark). `axioms` maps the identity to it.
  const label=library ? declaration : `${module}::${declaration}`;
  const value=checker.assume(binding,closed);
  checker.axioms.set(binding,value.name);
  checker.assumptionOrigins.set(value.name,{kind:'axiom',module,declaration,binding});
  checker.libraryAssumptions.set(label,value);
  checker.assumptionLabels.set(value.name,label);
  return value;
}
