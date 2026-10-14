import "./fresh-build.mjs";
import test from "node:test";
import assert from "node:assert/strict";
import create from "../web/dist/cubical.mjs";
import {CubicalProgram} from "../web/cubical-program.mjs";
import {Translator} from "../web/translator/translate.mjs";
import {Scope} from "../web/translator/elaboration.mjs";
import {bindingInputs} from "../web/translator/binding-module.mjs";
import {parse} from "../web/cubist/parser.mjs";
import {rewritten} from "../web/cubist/scopes.mjs";
import {parameterLambdas} from "../web/cubist/telescopes.mjs";
import {RetainedInterfaces} from "../web/cubist/retained-interfaces.mjs";
import {resolveBindingSyntax,resolveBindingTemplate,bindingSyntaxView,substituteBindingSyntax,lowerBindingSyntax,bindingUses}
  from "../web/cubist/binding-syntax.mjs";

test("generated template binders compose with retained syntax through explicit ID maps",async t=>{
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
  const generated="fun (B : U0) => fun (c, x : B) => __body(x)";
  const template=rewritten(parse(generated,true),n=>n.kind==="name"&&n.name==="__body"?{kind:"templateHole",hole:"body",start:n.start,end:n.end}:n);
  const reference=(context,label)=>{
    const resolution=context.lookup(label);
    assert.equal(resolution.tag,"binding");
    return bindingSyntaxView(value,{kind:"bindingReference",resolution,spelling:label,origin:field.binding.origin});
  };
  const splices=new Map([["body",context=>substituteBindingSyntax(value,new Map([
    [h.tree.params[0].name.bindingId,reference(context,"B")],
    [field.id,reference(context,"c")],
  ]),table,["instantiate"])] ]);
  const syntax=resolveBindingTemplate(template,{table,owner:["generated"],context:inputs.context,
    source:{revision:"generated",module:"artifact"}},splices);
  const own=syntax.tree.body.names;
  assert.equal(syntax.tree.body.body.fn.body.resolution.id,own[0].bindingId);
  assert.notEqual(syntax.tree.body.body.fn.name.bindingId,own[1].bindingId);
  assert.ok(!bindingUses(syntax).some(use=>[field.id,h.tree.params[0].name.bindingId].includes(use.id)));
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
  assert.throws(()=>resolveBindingSyntax(template,{table,owner:["source"],context:inputs.context,source}),/family has not migrated: templateHole/);
  assert.throws(()=>resolveBindingTemplate(template,{table,owner:["missing"],context:inputs.context,source},new Map()),/Unknown template syntax hole/);
});
