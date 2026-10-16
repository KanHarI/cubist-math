import "./fresh-build.mjs";
import test from "node:test";
import assert from "node:assert/strict";
import create from "../web/dist/cubical.mjs";
import {CubicalProgram} from "../web/cubical-program.mjs";
import {Translator} from "../web/translator/translate.mjs";
import {Scope} from "../web/translator/elaboration.mjs";
import {bindingInputs} from "../web/translator/binding-module.mjs";
import {parse} from "../web/cubist/parser.mjs";
import {ArtifactBuilder,at,token,reference,builtin} from "../web/cubist/artifact-builder.mjs";
import {parameterLambdas} from "../web/cubist/telescopes.mjs";
import {RetainedInterfaces} from "../web/cubist/retained-interfaces.mjs";
import {resolveBindingSyntax,bindingSyntaxView,lowerBindingSyntax,bindingUses}
  from "../web/cubist/binding-syntax.mjs";

test("artifact binders compose with retained syntax through explicit ID maps",async t=>{
  const program=new CubicalProgram(await create(),async()=>"");t.after(()=>program.dispose());
  assert.deepEqual((await program.check("inductive Two { left_; right_; }","base")).gaps,[]);
  const registry=program.compilationBindings,table=registry.table,values=new Map();
  for(const [label,value] of program.modules.get("base"))if(/^[A-Za-z_][A-Za-z0-9_]*$/.test(label)) {
    const record=registry.ofValue(value);if(record)values.set(record.id,value);
  }
  const inputs=bindingInputs(table,values,{reserved:["U0","Unit","tt"]});
  const source={revision:"source",module:"parent"};
  const retained=new RetainedInterfaces({table,owner:["parent"],source,context:inputs.context});
  const header=parse("def P(A : U0) : Unit := tt;").declarations[0];
  const h=retained.parameters(header.name,header.params);
  const field=retained.retain(parse("def c : A := tt;").declarations[0],{kind:"operation"});
  const helper=retained.retain(parse("def get(x : A) : A := c;").declarations[0],{kind:"derived"});
  const value=bindingSyntaxView(helper.syntax,parameterLambdas(helper.syntax.tree.params,helper.syntax.tree.body[0].value));
  const origin=field.binding.origin,builder=new ArtifactBuilder(h,{table,owner:["generated"],origin});
  const B=builder.local("B"),c=builder.local("c"),x=builder.local("x");
  const inserted=builder.substitute(value,new Map([
    [h.tree.params[0].name.bindingId,bindingSyntaxView(value,reference(B))],
    [field.id,bindingSyntaxView(value,reference(c))],
  ]));
  const binding=builder.reserve("generated"),params=[
    {name:token(B),type:builtin("U0",origin),group:0},
    {name:token(c),type:reference(B),group:1},{name:token(x),type:reference(B),group:2},
  ];
  builder.emit(binding,{kind:"def",name:token(binding),params,type:reference(B),
    body:[{kind:"exact",value:{kind:"call",fn:inserted.tree,args:[reference(x)],...at(origin)},...at(origin)}],
    ...at(origin)},{role:"test"});
  const emitted=builder.artifacts[0].syntax,tree=emitted.tree;
  assert.equal(tree.body[0].value.fn.body.resolution.id,tree.params[1].name.bindingId);
  assert.notEqual(tree.body[0].value.fn.name.bindingId,tree.params[2].name.bindingId);
  assert.notEqual(tree.params[0].name.bindingId,B.id,"emission freshens owned identities");
  assert.ok(!bindingUses(emitted).some(use=>[field.id,h.tree.params[0].name.bindingId].includes(use.id)));
  const syntax=bindingSyntaxView(emitted,parameterLambdas(tree.params,tree.body[0].value));
  const translator=new Translator({checker:program.checker,compilationBindings:registry,normalize:false});
  const scope=new Scope(translator.unit({bindingAdapter:inputs.adapter}),new Map(),inputs.env);
  const args=resolveBindingSyntax(parse("f(Two, left_, right_)",true),{table,owner:["arguments"],context:inputs.context,source});
  const applied=bindingSyntaxView(syntax,{kind:"call",fn:syntax.tree,args:args.tree.args});
  const actual=translator.term(lowerBindingSyntax(applied,inputs.adapter),scope);
  scope.infer(actual);
  const expected=label=>translator.term(lowerBindingSyntax(resolveBindingSyntax(parse(label,true),{
    table,owner:["expected",label],context:inputs.context,source}),inputs.adapter),scope);
  assert.equal(scope.equal(actual,expected("left_")),true);
  assert.equal(scope.equal(actual,expected("right_")),false);
});
