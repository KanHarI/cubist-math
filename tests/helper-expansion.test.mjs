import "./fresh-build.mjs";
import test from "node:test";
import assert from "node:assert/strict";
import create from "../web/dist/cubical.mjs";
import {CubicalProgram} from "../web/cubical-program.mjs";
import {Translator} from "../web/translator/translate.mjs";
import {Scope} from "../web/translator/elaboration.mjs";
import {bindingInputs} from "../web/translator/binding-module.mjs";
import {parse} from "../web/cubist/parser.mjs";
import {RetainedInterfaces} from "../web/cubist/retained-interfaces.mjs";
import {HelperExpansion} from "../web/cubist/helper-expansion.mjs";
import {resolveBindingSyntax,lowerBindingSyntax,bindingUses} from "../web/cubist/binding-syntax.mjs";

const wasm=await create();
async function setup(t) {
  const program=new CubicalProgram(wasm,async()=>"");t.after(()=>program.dispose());
  assert.deepEqual((await program.check("inductive Two { left_; right_; }","base")).gaps,[]);
  const registry=program.compilationBindings,table=registry.table,values=new Map();
  for(const [label,value] of program.modules.get("base")) {
    if(!/^[A-Za-z_][A-Za-z0-9_]*$/.test(label))continue;
    const binding=registry.ofValue(value);
    if(binding)values.set(binding.id,value);
  }
  const inputs=bindingInputs(table,values,{reserved:["U0","UU0","Unit","tt","typed","refl"]});
  const source={revision:"source",module:"theory"};
  const interfaces=new RetainedInterfaces({table,owner:["theory"],source,context:inputs.context,constructors:inputs.constructors});
  const retain=(text,options={kind:"derived"})=>interfaces.retain(parse(text).declarations[0],options);
  const translator=new Translator({checker:program.checker,compilationBindings:registry,normalize:false});
  let serial=0;
  const resolve=text=>resolveBindingSyntax(parse(text,true),{table,context:interfaces.context,source,
    owner:["request",String(serial++)],constructors:inputs.constructors});
  const scope=new Scope(translator.unit({bindingAdapter:inputs.adapter}),new Map(),inputs.env);
  const elaborate=syntax=>{
    const term=translator.term(lowerBindingSyntax(syntax,inputs.adapter),scope);
    scope.infer(term);return term;
  };
  return {table,inputs,interfaces,retain,resolve,scope,elaborate,program};
}

test("helper expansion preserves field identity through complete grouped telescopes and named calls",async t=>{
  const p=await setup(t),{table,inputs,interfaces,retain,resolve,scope,elaborate,program}=p;
  const field=retain("def c : Two := left_;",{kind:"operation"});
  inputs.env.set(inputs.adapter.key(field.id),program.modules.get("base").get("left_"));
  retain("def first(x, y : Two) : Two := c;");
  retain("def dependent(c, other : Two, p : c = other) : Two := first(y := other, x := c);");
  const expansion=new HelperExpansion(interfaces.entries,{table,owner:["expand"]});
  for(const source of ["dependent(other := right_, p := refl(right_), c := right_)",
    "(fun (c : Two) => first(c)(y := c))(right_)","first(y := right_, x := right_)"]) {
    const expanded=expansion.expand(resolve(source));
    const actual=elaborate(expanded);
    assert.equal(scope.equal(actual,elaborate(resolve("left_"))),true,source);
    assert.equal(scope.equal(actual,elaborate(resolve("right_"))),false,source);
    assert.ok(bindingUses(expanded).some(use=>use.id===field.id));
  }
});

test("inlining retains unused argument domains and the declared result check",async t=>{
  const {table,interfaces,retain,resolve,scope,elaborate}=await setup(t);
  retain("def keep(x : Unit) : Unit := tt;");
  retain("def invalid(x : Unit) : Unit := left_;");
  const expansion=new HelperExpansion(interfaces.entries,{table,owner:["expand"]});
  assert.equal(scope.equal(elaborate(expansion.expand(resolve("keep(tt)"))),elaborate(resolve("tt"))),true);
  assert.throws(()=>elaborate(expansion.expand(resolve("keep(left_)"))));
  assert.throws(()=>elaborate(expansion.expand(resolve("invalid(tt)"))));
});

test("retained helper calls assign implicit and partial named arguments through their declared telescope",async t=>{
  const {table,interfaces,retain,resolve,scope,elaborate}=await setup(t);
  retain("def choose{{A : U0}}(x, y : A) : A := x;");
  retain("def inferred{{A : U0}}(x, y : A) := x;");
  const expansion=new HelperExpansion(interfaces.entries,{table,owner:["expand"]});
  for(const source of ["choose{{A := Two}}(y := left_, x := right_)",
    "choose(y := left_, x := right_)","choose{{Two}}(right_)(y := left_)",
    "inferred(y := left_, x := right_)"]) {
    const actual=elaborate(expansion.expand(resolve(source)));
    assert.equal(scope.equal(actual,elaborate(resolve("right_"))),true,source);
    assert.equal(scope.equal(actual,elaborate(resolve("left_"))),false,source);
  }
  assert.throws(()=>expansion.expand(resolve("choose(A := Two, x := right_)")),/implicit parameter/);
  assert.throws(()=>expansion.expand(resolve("choose(x := right_, x := left_)")),/given twice/);
});

test("family domains expand the helper captured at source entry despite an ambient same-named value",async t=>{
  const {table,inputs,interfaces,retain,resolve,scope,elaborate}=await setup(t);
  // A destination spelling deliberately denotes a different type. The
  // retained family's complete telescope already names the helper's ID.
  inputs.env.set("Index",elaborate(resolve("Unit")));
  retain("def Index : U0 := Two;");
  const family=retain("def F(index : Index) : Unit := tt;",{kind:"sort"});
  const expansion=new HelperExpansion(interfaces.entries,{table,owner:["expand"]});
  const signature=expansion.signature(family);
  const domain=signature.syntax.tree.params[0].type;
  const actual=elaborate({...signature.syntax,tree:domain,owned:[]});
  assert.equal(scope.equal(actual,elaborate(resolve("Two"))),true);
  assert.equal(scope.equal(actual,elaborate(resolve("Unit"))),false);
});

test("expanded signature validation finds recursive dependencies inside helper replacements and bare values",async t=>{
  const {table,interfaces,retain}=await setup(t);
  const recursive=retain("def loop(x : Unit) : Unit := loop(x);",{kind:"derived",self:true});
  retain("def wrap(x : Unit) : Unit := loop(x);");
  retain("def again(x : Unit) : Unit := wrap(x);");
  const hidden=retain("def hidden : again(tt) = tt := refl(tt);",{kind:"law"});
  const bare=retain("def bare : loop = loop := refl(loop);",{kind:"law"});
  const expansion=new HelperExpansion(interfaces.entries,{table,owner:["expand"]});
  for(const entry of [hidden,bare]) {
    const result=expansion.signature(entry);
    assert.equal(result.recursive.id,recursive.id);
    assert.deepEqual(result.pending,[]);
  }
});
