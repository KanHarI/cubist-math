import "./fresh-build.mjs";
import {naturalSort, numeral} from "../web/translator/numerals.mjs";
import test from "node:test";
import assert from "node:assert/strict";
import {spawnSync} from "node:child_process";
import {readFile} from "node:fs/promises";
import createCubical from "../web/dist/cubical.mjs";
import {CubicalProgram} from "../web/cubical-program.mjs";
import {formatCubist} from "../web/cubist/formatter.mjs";
import {parse} from "../web/cubist/parser.mjs";
import {expandedSyntax} from "../web/cubist/tuples.mjs";
import {budget} from "./timing.mjs";
import {sourceReader} from "../tools/module-sources.mjs";
import {testModulePath} from "../tools/inline-errors.mjs";
import {checkProgram,checkTestModule} from "./check-program.mjs";

// The blowup detectors below. A shared term nested sharedDepth deep has a
// tree of 2^sharedDepth nodes, so a check that expands it cannot finish
// within these limits, while a normal check stays far below them, and so
// does its slowdown under machine load: checkLimit bounds a check,
// childLimit a child process's startup and check together.
const sharedDepth=30, checkLimit=budget(2000), childLimit=budget(15000);

const readLibrary = name => readFile(new URL(`../archive/first-library/${name}.cubist`,import.meta.url),"utf8");
const sample = name => readFile(new URL(`../docs/examples/proof-ergonomics/implemented/${name}.cubist`,import.meta.url),"utf8");
// The Cubist cases are cubist-tests/ergonomics_*.cubist, whose comments
// state each refusal and what each print shows (tests/cubist-tests.test.mjs);
// here, the links, frozen edits and rewrite work a verdict does not show,
// and the cases that are documentation examples, generated or instrumented.
const cases = (t, name) => checkTestModule(t, `ergonomics_${name}`);
// A module's source with its comments blanked, offsets kept.
const uncommented = source => source.replace(/\/\/.*/g, comment => " ".repeat(comment.length));
// A module's source, edited, checked as the module is.
const edited = (t, name, source) => checkProgram(t, source,
  { reader: sourceReader({ path: testModulePath(`ergonomics_${name}`) }), name: `ergonomics_${name}_edited` });

test("short arithmetic, cubical and dependent examples elaborate to native axiom-free proofs",async t=>{
  for(const name of ["arithmetic","cubical","dependent","type-transport"]) {
    const program=new CubicalProgram(await createCubical(),readLibrary);
    t.after(()=>program.dispose());
    const result=await program.check(await sample(name),`ergonomics_${name}`);
    assert.equal(result.complete,true,`${name}: ${JSON.stringify(result.gaps)}`);
    assert.ok(result.outputs.every(d=>d.verified&&d.axioms.length===0),name);
    if(name==="arithmetic") for(const role of ["calculation witness","rewrite witness","simplification witness"]) {
      const link=result.links.find(item=>item.role===role);
      assert.ok(link,role);
      assert.equal(program.inspect(link.binding).type.tag,"Path",role);
    }
    if(name==="arithmetic") {
      const steps=result.links.filter(item=>item.role==="calculation step");
      assert.ok(steps.length>=2);
      assert.equal(new Set(steps.map(item=>item.binding)).size,steps.length);
      for(const step of steps) assert.equal(program.inspect(step.binding).type.tag,"Path");
    }
  }
});

test("generic proof tactics link their checked witnesses from source",async t=>{
  const {source,result,program}=await cases(t,"generic_tactic_links");
  for(const [keyword,role] of [["calc","calculation witness"],["rw","rewrite witness"],
    ["simp","simplification witness"],["by","calculation step"]]) {
    const offset=source.indexOf(`${keyword} `,source.indexOf("{"));
    const link=result.links.find(item=>item.start===offset&&item.role===role);
    assert.ok(link,`${keyword} source link`);
    const view=program.inspect(link.binding);
    assert.equal(view.type.tag,"Path",keyword);
    if(keyword==="simp") {
      // One check covers every level, so a generic proof is offered the same
      // edit as a concrete one.
      assert.equal(link.freeze?.text,"simp only [h];");
      const witness=view.symbols[view.name];
      assert.match(witness.description,/Checked simplification/);
      assert.equal(link.rewriteSteps.length,1);
      assert.equal(program.inspect(link.rewriteSteps[0].binding).type.tag,"Path");
    }
  }
});

test("constant path reversal avoids exponential native interval expansion",async t=>{
  const dimensions=Array.from({length:32},(_,i)=>`d${i}`);
  let terms=Array.from({length:16},(_,i)=>`meet(d${2*i},d${2*i+1})`);
  while(terms.length>1)terms=Array.from({length:Math.ceil(terms.length/2)},(_,i)=>
    terms[2*i+1]?`join(${terms[2*i]},${terms[2*i+1]})`:terms[2*i]);
  const lets=dimensions.map((_,i)=>`let t${i} := ${i?`refl(t${i-1})`:"0"};`).join("\n");
  const source=`def native_interval_budget : 0 = 0 {
    ${lets}
    let h : t31 = t31 {
      exact ${dimensions.map(d=>`path ${d} => `).join("")}sym(refl(0)) @ ${terms[0]};
    }
    rfl;
  }`;
  const program=new CubicalProgram(await createCubical(),()=>{throw Error("Unexpected import.");},
    {collectReferences:false});
  t.after(()=>program.dispose());
  // The deadline covers the let's instruction derivation too: 32 nested
  // path lambdas, each compared with its annotation. An exponential
  // expansion would exceed any budget.
  program.kernel.setDeadline(checkLimit);
  const result=await program.check(source,"constant_path_reverse");
  assert.equal(result.outputs[0].verified,true,result.outputs[0].reason);
  const neutral=source.replace("def native_interval_budget :",
    "def native_interval_budget(p : 0 = 0) :").replace("sym(refl(0))","sym(p)")+
    "\ndef after : 0 = 0 { rfl; }";
  const wasm=new URL("../web/dist/cubical.mjs",import.meta.url).href;
  const programPath=new URL("../web/cubical-program.mjs",import.meta.url).href;
  const script=`import createCubical from ${JSON.stringify(wasm)};
    import {CubicalProgram} from ${JSON.stringify(programPath)};
    const program=new CubicalProgram(await createCubical(),()=>{throw Error("Unexpected import.");},
      {collectReferences:false});
    program.kernel.setDeadline(${checkLimit});
    try { const result=await program.check(process.argv[1],"neutral_path_reverse");
      console.log(JSON.stringify(result.outputs.map(({verified,reason})=>({verified,reason}))));
    } finally { program.dispose(); }`;
  const child=spawnSync(process.execPath,["--max-old-space-size=128","--input-type=module","-e",script,neutral],
    {encoding:"utf8",timeout:childLimit});
  assert.equal(child.error,undefined,child.stderr);
  assert.equal(child.status,0,child.stderr);
  const outputs=JSON.parse(child.stdout.trim());
  assert.deepEqual(outputs.map(output=>output.verified),[false,true]);
  assert.match(outputs[0].reason,/Cubical lattice term-size or work budget exceeded/);
});

test("positive composition faces use only the needed endpoint of a compact interval",async t=>{
  const dimensions=Array.from({length:32},(_,i)=>`d${i}`);
  let terms=Array.from({length:16},(_,i)=>`meet(d${2*i},d${2*i+1})`);
  while(terms.length>1)terms=Array.from({length:Math.ceil(terms.length/2)},(_,i)=>
    terms[2*i+1]?`join(${terms[2*i]},${terms[2*i+1]})`:terms[2*i]);
  const lets=dimensions.map((_,i)=>`let t${i} := ${i?`refl(t${i-1})`:"0"};`).join("\n");
  const source=`def positive_face_budget : 0 = 0 {
    ${lets}
    let h : t31 = t31 {
      exact ${dimensions.map(d=>`path ${d} => `).join("")}
        path(fun (i : Interval) => Nat,
          fun (i : Interval) => comp(fun (j : Interval) => Nat, 0,
            face(i, 1, fun (j : Interval) => 0))) @ ${terms[0]};
    }
    rfl;
  }`;
  const program=new CubicalProgram(await createCubical(),()=>{throw Error("Unexpected import.");},
    {collectReferences:false});
  t.after(()=>program.dispose());
  program.kernel.setDeadline(checkLimit);
  const result=await program.check(source,"positive_face_budget");
  assert.equal(result.outputs[0].verified,true,result.outputs[0].reason);
});

test("a pushout instance visits shared source types within the proof deadline",()=>{
  const wasm=new URL("../web/dist/cubical.mjs",import.meta.url).href;
  const programPath=new URL("../web/cubical-program.mjs",import.meta.url).href;
  let source="import pushout;\ndef shared(F : U0 -> U0 -> U0, A : U0) : 0 = 0 { let T0 := A;";
  for(let i=1;i<=sharedDepth;i++)source+=`let T${i} := F(T${i-1},T${i-1});`;
  source+=`let P := Pushout(U0, U0, U0, T${sharedDepth}, Unit, Unit, fun (x : T${sharedDepth}) => tt, fun (x : T${sharedDepth}) => tt);
    let h : forall x : P. x = x { intro x; exact path i => x; } rfl; }
    def after : 0 = 0 { rfl; }`;
  const sources=new URL("../tools/module-sources.mjs",import.meta.url).href;
  const script=`import createCubical from ${JSON.stringify(wasm)};
    import {CubicalProgram} from ${JSON.stringify(programPath)};
    import {sourceReader} from ${JSON.stringify(sources)};
    const program=new CubicalProgram(await createCubical(),sourceReader(),{collectReferences:false});
    await program.check("import pushout;","imports");
    program.kernel.setDeadline(${checkLimit});
    try { const result=await program.check(process.argv[1],"shared_pushout");
      console.log(JSON.stringify(result.outputs.map(({verified,reason})=>({verified,reason}))));
    } finally {program.dispose();}`;
  const child=spawnSync(process.execPath,["--max-old-space-size=128","--input-type=module","-e",script,source],
    {encoding:"utf8",timeout:childLimit});
  assert.equal(child.error,undefined,child.stderr);
  assert.equal(child.status,0,child.stderr);
  assert.deepEqual(JSON.parse(child.stdout.trim()).map(output=>output.verified),[true,true]);
});

test("new proof syntax survives formatting with the same expanded AST",async()=>{
  for(const name of ["arithmetic","cubical","dependent","type-transport"]) {
    const source=await sample(name),formatted=formatCubist(source);
    assert.equal(formatCubist(formatted),formatted,name);
    assert.equal(expandedSyntax(parse(formatted)),expandedSyntax(parse(source)),name);
  }
});

test("incomplete grouped binders and introductions fail without hanging the parser",()=>{
  const parser=new URL("../web/cubist/parser.mjs",import.meta.url).href;
  for(const source of ["def f(x","def f : forall x","def f := fun (x",
    "def f : Nat { intro x"]) {
    const script=`import {parse} from ${JSON.stringify(parser)}; parse(process.argv[1]);`;
    const child=spawnSync(process.execPath,["--input-type=module","-e",script,source],
      {encoding:"utf8",timeout:childLimit});
    assert.equal(child.error,undefined,source);
    assert.notEqual(child.status,0,source);
    assert.match(child.stderr,/Expected (a name\.|[':;]+(?: or '<')?, found 'EOF')/,source);
  }
});



test("simp size budget interrupts serialization of a compact shared term",()=>{
  const wasm=new URL("../web/dist/cubical.mjs",import.meta.url).href;
  const program=new URL("../web/cubical-program.mjs",import.meta.url).href;
  const script=`import createCubical from ${JSON.stringify(wasm)};
    import {CubicalProgram} from ${JSON.stringify(program)};
    let source="def shared(f : Nat -> Nat -> Nat, n : Nat) : n = n { let t0 := n;";
    for(let i=1;i<=${sharedDepth};i++)source+="let t"+i+" := f(t"+(i-1)+", t"+(i-1)+");";
    source+="let h : t${sharedDepth} = t${sharedDepth} { simp only []; } rfl; }";
    const checker=new CubicalProgram(await createCubical(),()=>{throw Error("No imports");},
      {collectReferences:false});
    try {
      const result=await checker.check(source,"shared_simp_budget");
      console.log(JSON.stringify(result.outputs.map(({verified,reason})=>({verified,reason}))));
    } finally {checker.dispose();}`;
  const child=spawnSync(process.execPath,["--max-old-space-size=96","--input-type=module","-e",script],
    {encoding:"utf8",timeout:childLimit});
  assert.equal(child.error,undefined,child.stderr);
  assert.equal(child.status,0,child.stderr);
  assert.deepEqual(JSON.parse(child.stdout.trim()).map(output=>output.verified),[false]);
  assert.match(child.stdout,/Simplification term-size budget exceeded/);
});

test("simp rule selection and exclusion bound compact shared identities",()=>{
  const wasm=new URL("../web/dist/cubical.mjs",import.meta.url).href;
  const program=new URL("../web/cubical-program.mjs",import.meta.url).href;
  for(const tactic of ["simp only [h]","simp without [h]"]) {
    const script=`import createCubical from ${JSON.stringify(wasm)};
      import {CubicalProgram} from ${JSON.stringify(program)};
      let source="def shared(f : Nat -> Nat -> Nat, n : Nat) : n = n { let t0 := n;";
      for(let i=1;i<=${sharedDepth};i++)source+="let t"+i+" := f(t"+(i-1)+", t"+(i-1)+");";
      source+="let h : t${sharedDepth} = t${sharedDepth} { rfl; } ${tactic}; }";
      const checker=new CubicalProgram(await createCubical(),()=>{throw Error("No imports");},
        {collectReferences:false});
      try {
        const result=await checker.check(source,"shared_rule_budget");
        console.log(JSON.stringify(result.outputs.map(({verified,reason})=>({verified,reason}))));
      } finally {checker.dispose();}`;
    const child=spawnSync(process.execPath,["--max-old-space-size=96","--input-type=module","-e",script],
      {encoding:"utf8",timeout:childLimit});
    assert.equal(child.error,undefined,`${tactic}: ${child.stderr}`);
    assert.equal(child.status,0,`${tactic}: ${child.stderr}`);
    assert.deepEqual(JSON.parse(child.stdout.trim()).map(output=>output.verified),[false]);
    assert.match(child.stdout,/Simplification term-size budget exceeded/,tactic);
  }
});

test("quantified simp rules scan each shared pattern node once",()=>{
  const wasm=new URL("../web/dist/cubical.mjs",import.meta.url).href;
  const program=new URL("../web/cubical-program.mjs",import.meta.url).href;
  for(const tactic of ["simp only [h]","simp without [h]"]) {
    const script=`import createCubical from ${JSON.stringify(wasm)};
      import {CubicalProgram} from ${JSON.stringify(program)};
      let source="def shared(f : Nat -> Nat -> Nat, n : Nat) : n = n { let t0 := n;";
      for(let i=1;i<=${sharedDepth};i++)source+="let t"+i+" := f(t"+(i-1)+", t"+(i-1)+");";
      source+="let helper : (forall k : Nat. f(t${sharedDepth},k) = k) -> n = n { intro h; ${tactic}; } rfl; }";
      const checker=new CubicalProgram(await createCubical(),()=>{throw Error("No imports");},
        {collectReferences:false});
      try {
        const result=await checker.check(source,"shared_pattern_budget");
        console.log(JSON.stringify(result.outputs.map(({verified,reason})=>({verified,reason}))));
      } finally {checker.dispose();}`;
    const child=spawnSync(process.execPath,["--max-old-space-size=96","--input-type=module","-e",script],
      {encoding:"utf8",timeout:childLimit});
    assert.equal(child.error,undefined,`${tactic}: ${child.stderr}`);
    assert.equal(child.status,0,`${tactic}: ${child.stderr}`);
    assert.deepEqual(JSON.parse(child.stdout.trim()).map(output=>output.verified),[true],tactic);
  }
});

test("path reconstruction preserves compact shared terms within the proof deadline",()=>{
  const wasm=new URL("../web/dist/cubical.mjs",import.meta.url).href;
  const program=new URL("../web/cubical-program.mjs",import.meta.url).href;
  const cases=[
    ["rw","def shared(f : Nat -> Nat -> Nat, n : Nat) : n = n { let t0 := n;",
      "f", `let proof : t${sharedDepth} = t${sharedDepth} { rw [refl(t${sharedDepth})] at lhs; } rfl; }`],
    ["calc","def shared(f : Nat -> Nat -> Nat, n : Nat) : n = n { let t0 := n;",
      "f", `let proof : t${sharedDepth} = t${sharedDepth} { calc { t${sharedDepth} = t${sharedDepth} by refl(t${sharedDepth}); _ = t${sharedDepth} by refl(t${sharedDepth}); } } rfl; }`],
    ["simp","def shared(f : Nat -> Nat, g : Nat -> Nat -> Nat, n : Nat, c : forall k : Nat. n = n -> f(k) = k) : f(n) = n { let t0 := n;",
      "g", `let h : n = n := (fun (unused : Nat) => refl(n))(t${sharedDepth}); simp only [c] with [h]; }`],
    ["simpa","def shared(f : Nat -> Nat, g : Nat -> Nat -> Nat, n : Nat, c : forall k : Nat. n = n -> f(k) = k) : f(n) = n { let t0 := n;",
      "g", `let h : n = n := (fun (unused : Nat) => refl(n))(t${sharedDepth}); simpa only [c] with [h] using refl(n); }`],
  ];
  for(const [name,prefix,fn,suffix] of cases) {
    const script=`import createCubical from ${JSON.stringify(wasm)};
      import {CubicalProgram} from ${JSON.stringify(program)};
      let source=${JSON.stringify(prefix)};
      for(let i=1;i<=${sharedDepth};i++)source+="let t"+i+" := ${fn}(t"+(i-1)+",t"+(i-1)+");";
      source+=${JSON.stringify(suffix)};
      const checker=new CubicalProgram(await createCubical(),()=>{throw Error("No imports");},
        {collectReferences:false});
      checker.kernel.setDeadline(${checkLimit});
      try {
        const result=await checker.check(source,"shared_path_reconstruction");
        console.log(JSON.stringify(result.outputs.map(({verified,reason,axioms})=>({verified,reason,axioms}))));
      } finally {checker.dispose();}`;
    const child=spawnSync(process.execPath,["--max-old-space-size=128","--input-type=module","-e",script],
      {encoding:"utf8",timeout:childLimit});
    assert.equal(child.error,undefined,`${name}: ${child.stderr}`);
    assert.equal(child.status,0,`${name}: ${child.stderr}`);
    assert.deepEqual(JSON.parse(child.stdout.trim()),[{verified:true,axioms:[]}],name);
  }
});

test("path abstraction and dependent-path transport keep shared inputs compact",()=>{
  const wasm=new URL("../web/dist/cubical.mjs",import.meta.url).href;
  const program=new URL("../web/cubical-program.mjs",import.meta.url).href;
  for(const mode of ["path","over"]) {
    const script=`import createCubical from ${JSON.stringify(wasm)};
      import {CubicalProgram} from ${JSON.stringify(program)};
      let source;
      if(${JSON.stringify(mode)}==="path") {
        source="def shared(F : U0 -> U0 -> U0, A : U0) : 0 = 0 { let T0 := A;";
        for(let i=1;i<=${sharedDepth};i++)source+="let T"+i+" := F(T"+(i-1)+",T"+(i-1)+");";
        source+="let h : forall x : T${sharedDepth}. x = x { intro x; exact path i => x; } rfl; }";
      } else {
        source="def shared(f : Nat -> Nat -> Nat, n : Nat) : n = n { let t0 := n;";
        for(let i=1;i<=${sharedDepth};i++)source+="let t"+i+" := f(t"+(i-1)+",t"+(i-1)+");";
        source+="let h : (along (fun (n : Nat) => Nat) by refl(0) from t${sharedDepth}) = t${sharedDepth} -> t${sharedDepth} = t${sharedDepth} { intro q; over (fun (n : Nat) => Nat) along refl(0) by { exact q; } } rfl; }";
      }
      const checker=new CubicalProgram(await createCubical(),()=>{throw Error("No imports");},
        {collectReferences:false});
      checker.kernel.setDeadline(${checkLimit});
      try {
        const result=await checker.check(source,"shared_cubical_syntax");
        console.log(JSON.stringify(result.outputs.map(({verified,reason,axioms})=>({verified,reason,axioms}))));
      } finally {checker.dispose();}`;
    const child=spawnSync(process.execPath,["--max-old-space-size=128","--input-type=module","-e",script],
      {encoding:"utf8",timeout:childLimit});
    assert.equal(child.error,undefined,`${mode}: ${child.stderr}`);
    assert.equal(child.status,0,`${mode}: ${child.stderr}`);
    assert.deepEqual(JSON.parse(child.stdout.trim()),[{verified:true,axioms:[]}],mode);
  }
});

test("interval expansion is bounded while later declarations still elaborate",()=>{
  const wasm=new URL("../web/dist/cubical.mjs",import.meta.url).href;
  const program=new URL("../web/cubical-program.mjs",import.meta.url).href;
  const sourceFor=(pairs)=>{
    const dimensions=Array.from({length:2*pairs},(_,i)=>`d${i}`);
    let formula=Array.from({length:pairs},(_,i)=>`join(d${2*i},d${2*i+1})`);
    while(formula.length>1)formula=Array.from({length:Math.ceil(formula.length/2)},(_,i)=>
      formula[2*i+1]?`meet(${formula[2*i]},${formula[2*i+1]})`:formula[2*i]);
    let source="def interval_budget : 0 = 0 { let t0 := 0;";
    for(let i=1;i<dimensions.length;i++)source+=`let t${i} := refl(t${i-1});`;
    source+=`let h : t${dimensions.length-1} = t${dimensions.length-1} { exact `;
    source+=dimensions.map(d=>`path ${d} => `).join("");
    return source+`refl(0) @ ${formula[0]}; } rfl; } def after : 0 = 0 { rfl; }`;
  };
  const script=`import createCubical from ${JSON.stringify(wasm)};
    import {CubicalProgram} from ${JSON.stringify(program)};
    const checker=new CubicalProgram(await createCubical(),()=>{throw Error("No imports");},
      {collectReferences:false});
    checker.kernel.setDeadline(${checkLimit});
    try {
      const result=await checker.check(process.argv[1],"interval_budget");
      console.log(JSON.stringify(result.outputs.map(({verified,reason,axioms})=>({verified,reason,axioms}))));
    } finally {checker.dispose();}`;
  for(const [pairs,expected] of [[8,true],[14,false]]) {
    const child=spawnSync(process.execPath,["--max-old-space-size=128","--input-type=module","-e",script,sourceFor(pairs)],
      {encoding:"utf8",timeout:childLimit});
    assert.equal(child.error,undefined,`${pairs}: ${child.stderr}`);
    assert.equal(child.status,0,`${pairs}: ${child.stderr}`);
    const outputs=JSON.parse(child.stdout.trim());
    assert.deepEqual(outputs.map(output=>output.verified),[expected,true],`${pairs}: ${child.stdout}`);
    assert.deepEqual(outputs.filter(output=>output.verified).map(output=>output.axioms),
      expected?[[],[]]:[[]]);
    if(!expected)assert.match(outputs[0].reason,/Cubical lattice term-size budget exceeded/);
  }
});

test("shared path and transport proofs remain inspectable without expanding raw syntax",()=>{
  const wasm=new URL("../web/dist/cubical.mjs",import.meta.url).href;
  const program=new URL("../web/cubical-program.mjs",import.meta.url).href;
  const json=new URL("../web/cubical-json.mjs",import.meta.url).href;
  for(const mode of ["path","over"]) {
    let source;
    if(mode==="path") {
      source="def shared(F : U0 -> U0 -> U0, A : U0) : 0 = 0 { let T0 := A;";
      for(let i=1;i<=sharedDepth;i++)source+=`let T${i} := F(T${i-1},T${i-1});`;
      source+=`let h : forall x : T${sharedDepth}. x = x { intro x; exact path i => x; } rfl; }`;
    } else {
      source="def shared(f : Nat -> Nat -> Nat, n : Nat) : n = n { let t0 := n;";
      for(let i=1;i<=sharedDepth;i++)source+=`let t${i} := f(t${i-1},t${i-1});`;
      source+=`let h : (along (fun (n : Nat) => Nat) by refl(0) from t${sharedDepth}) = t${sharedDepth} -> t${sharedDepth} = t${sharedDepth} { intro q; over (fun (n : Nat) => Nat) along refl(0) by { exact q; } } rfl; }`;
    }
    const script=`import createCubical from ${JSON.stringify(wasm)};
      import {CubicalProgram} from ${JSON.stringify(program)};
      import {boundedSyntaxJson} from ${JSON.stringify(json)};
      const checker=new CubicalProgram(await createCubical(),()=>{throw Error("No imports");});
      checker.kernel.setDeadline(${checkLimit});
      try {
        const result=await checker.check(process.argv[1],"shared_inspection");
        const h=result.links.find(link=>link.name==="h");
        const view=checker.inspect(h.binding);
        console.log(JSON.stringify({verified:result.outputs[0].verified,
          axioms:result.outputs[0].axioms,inspected:!!view.expressionText,
          rawLimited:boundedSyntaxJson(view.expression)===null}));
      } finally {checker.dispose();}`;
    const child=spawnSync(process.execPath,["--max-old-space-size=128","--input-type=module","-e",script,source],
      {encoding:"utf8",timeout:childLimit});
    assert.equal(child.error,undefined,`${mode}: ${child.stderr}`);
    assert.equal(child.status,0,`${mode}: ${child.stderr}`);
    assert.deepEqual(JSON.parse(child.stdout.trim()),
      {verified:true,axioms:[],inspected:true,rawLimited:true},mode);
  }
});


// Its refusals are ergonomics_type_transport_rejections.
test("simpa transports through checked paths of types without inventing equivalences",async t=>{
  const source=await sample("type-transport");
  const program=new CubicalProgram(await createCubical(),readLibrary);
  t.after(()=>program.dispose());
  const checked=await program.check(source,"type_transport");
  assert.equal(checked.complete,true,JSON.stringify(checked.gaps));
  assert.equal(checked.outputs.length,5);
  assert.ok(checked.outputs.every(output=>output.verified&&output.axioms.length===0));
  const frozen=checked.links.find(link=>link.role==="simplification witness"&&link.freeze);
  assert.equal(frozen?.freeze.text,"simpa only [nat_add_zero] using h;");
  assert.equal(program.inspect(frozen.rewriteSteps[0].binding).type.tag,"Path");
  const replaySource=source.slice(0,frozen.freeze.start)+frozen.freeze.text
    +source.slice(frozen.freeze.end);
  const replay=new CubicalProgram(await createCubical(),readLibrary);
  t.after(()=>replay.dispose());
  assert.equal((await replay.check(replaySource,"type_transport_frozen")).complete,true);
});




test("an imported generic definition that fails is reported in its own module",async t=>{
  const {result}=await cases(t,"imported_failure");
  const [broken]=result.gaps;
  assert.deepEqual([broken.module,broken.name],["ergonomics_imported_failure_rules","broken__rule"]);
  // Its position counts the long line before it.
  const library=await readFile(testModulePath("ergonomics_imported_failure_rules"),"utf8");
  const before=library.slice(0,broken.start);
  assert.ok(broken.reason.endsWith(` at ${before.split("\n").length}:${before.length-before.lastIndexOf("\n")}`),broken.reason);
  assert.equal(library.slice(broken.start,broken.end),"0");
});

test("freeze is withheld when removing a rule changes conditional premise search",async t=>{
  const {result}=await cases(t,"freeze_premise_search");
  const link=result.links.find(item=>item.role==="simplification witness");
  assert.ok(link);
  assert.equal(link.freeze,null);
});

test("freeze withholds a rule name shadowed by a named simplification set",async t=>{
  const {source,result}=await cases(t,"freeze_set_collision");
  assert.equal(result.links.find(item=>item.role==="simplification witness")?.freeze,null);
  // The edit it withholds would name the set.
  const broken=await edited(t,"freeze_set_collision",source.replace("simp;","simp only [nat_add_zero];"));
  assert.equal(broken.result.outputs[0].verified,false);
});

test("freezing a simplified hypothesis preserves its witness for dependent proofs",async t=>{
  const {source,result}=await cases(t,"freeze_witness");
  const links=result.links.filter(item=>item.role==="simplification witness");
  assert.equal(links.length,3);
  assert.equal(links[1].freeze,null);
  assert.equal(links[2].freeze?.text,"simp only [h] at h as h2;");
  const edit=links[2].freeze;
  assert.equal((await edited(t,"freeze_witness",source.slice(0,edit.start)+edit.text+source.slice(edit.end))).result.complete,true);
});

for(const tactic of ["simp","simpa"]) {
  test(`${tactic} freeze preserves a proof later compared with another path`,async t=>{
    const {result}=await cases(t,`${tactic}_freeze_path_identity`);
    const links=result.links.filter(item=>item.role==="simplification witness");
    assert.equal(links.length,2);
    assert.equal(links[1].freeze,null);
  });
}

for(const tactic of ["simp","simpa"]) {
  test(`${tactic} type-path freeze preserves a proof later compared with another`,async t=>{
    const module=`${tactic}_type_freeze_path_identity`,{source,result}=await cases(t,module);
    const links=result.links.filter(item=>item.role==="simplification witness");
    assert.equal(links.length,3);
    assert.equal(links[1].freeze,null);
    assert.equal(links[2].freeze?.text,`${tactic} only [nat_add_zero]${tactic==="simpa"?" using h":""};`);
    const edit=links[2].freeze;
    assert.equal((await edited(t,module,source.slice(0,edit.start)+edit.text+source.slice(edit.end))).result.complete,true);
  });
}

test("a naturality square must preserve its varying right boundary",async t=>{
  const program=new CubicalProgram(await createCubical(),readLibrary);
  t.after(()=>program.dispose());
  const invalid=(await sample("cubical")).replace("H(p @ i) @ j","H(x) @ j");
  const result=await program.check(invalid,"invalid_square");
  const square=result.outputs.find(d=>d.name==="naturality_square");
  assert.equal(square.verified,false);
});


test("a multi-binder fun source link inspects the complete closed function",async t=>{
  const {source,result,program}=await cases(t,"multi_binder_fun");
  assert.equal(expandedSyntax(parse(formatCubist(source))),expandedSyntax(parse(source)));
  for(const name of ["written","grouped","named_fun"]) {
    const start=source.indexOf(":= fun",source.indexOf(`def ${name}`))+3;
    const links=result.links.filter(link=>link.name==="fun"&&link.start===start);
    assert.equal(links.length,1,name);
    const view=program.inspect(links[0].binding);
    assert.deepEqual(view.context,[],name);
    assert.equal(view.type.tag,"Pi",name);
    assert.equal(view.type.body.tag,"Pi",name);
    assert.equal(view.symbols[view.name].name,"fun",name);
  }
});


test("a universe binder in a mixed group links to its universe",async t=>{
  const {source,result,program}=await cases(t,"mixed_universes");
  const binder=result.links.find(item=>item.start===source.indexOf("V, W < UU0"));
  assert.ok(binder);
  const view=program.inspect(binder.binding);
  assert.equal(view.expression.tag,"U");
  assert.equal(view.context.find(entry=>entry.name===view.expression.level.name).label,"V");
});


test("generic calc endpoints stay separate from step witnesses",async t=>{
  const {source,result,program}=await cases(t,"generic_calc");
  const offset=source.indexOf("n + 0 = n by");
  const endpoint=result.links.find(item=>item.start===offset&&item.name==="n");
  assert.ok(endpoint);
  assert.equal(program.inspect(endpoint.binding).type.tag,"Sort");
  // The step's checked path belongs to its `by` keyword, not its left endpoint.
  const byOffset=source.indexOf("by nat_add_zero");
  const step=result.links.find(item=>item.start===byOffset&&item.role==="calculation step");
  assert.ok(step);
  const stepView=program.inspect(step.binding);
  assert.equal(stepView.type.tag,"Path");
  const payload=program.export(step.binding);
  const replay=new CubicalProgram(await createCubical(),name=>payload.sources[name]);
  t.after(()=>replay.dispose());
  await replay.check(payload.source,payload.main);
  const restored=replay.inspect(payload.binding);
  assert.equal(restored.name,step.binding);
  assert.deepEqual(restored.type,stepView.type);
});

test("generic proofs link ext and simplified hypothesis binders and uses",async t=>{
  const {source,result,program}=await cases(t,"generic_proof_locals");
  for(const [snippet,name] of [["ext x","x"],["as h2","h2"],["exact h2","h2"]]) {
    const offset=source.indexOf(snippet)+snippet.lastIndexOf(name);
    const link=result.links.find(item=>item.name===name&&item.start===offset);
    assert.ok(link,`Missing source link for ${snippet}`);
    const view=program.inspect(link.binding);
    assert.equal(view.symbols[view.name].name,name);
    assert.equal(view.type.tag,name==="x"?"Sort":"Path");
    const payload=program.export(view.name);
    const replay=new CubicalProgram(await createCubical(),module=>payload.sources[module]);
    t.after(()=>replay.dispose());
    await replay.check(payload.source,payload.main);
    assert.deepEqual(replay.inspect(payload.binding).type,view.type);
  }
});

test("a failed use of a generic definition leaves the definition in the kernel, and admits nothing of its own",async t=>{
  const {program}=await cases(t,"generic_failure");
  assert.ok(program.kernel.definitions.has("ergonomics_generic_failure__identity"));
  assert.equal(program.kernel.definitions.has("ergonomics_generic_failure__failed"),false);
});

test("a late declaration observer error rolls back its native definition",async t=>{
  let reject=true;
  const program=new CubicalProgram(await createCubical(),readLibrary,{
    onDeclaration() {if(reject){reject=false;throw Error("observer rejected declaration");}}
  });
  t.after(()=>program.dispose());
  await assert.rejects(program.check("def discarded := 0;","observer_failure"),/observer rejected declaration/);
  assert.equal(program.kernel.definitions.has("observer_failure__discarded"),false);
  const recovered=await program.check("def accepted := 1;","observer_recovery");
  assert.equal(recovered.outputs[0].verified,true);
});


test("registered default and named sets retain checked proofs and format stably",async t=>{
  const program=new CubicalProgram(await createCubical(),readLibrary);
  t.after(()=>program.dispose());
  const source=await sample("registered-simp");
  const result=await program.check(source,"registered_simp");
  assert.equal(result.complete,true,JSON.stringify(result.gaps));
  assert.equal(result.outputs.length,9);
  assert.ok(result.outputs.every(d=>d.verified&&d.axioms.length===0));
  const work=result.outputs.find(d=>d.name==="recursive_premise").rewriteWork;
  assert.ok(work.traversals>work.successfulRewrites);
  assert.ok(work.candidateVisits>=work.traversals);
  assert.equal(work.premiseProofs,0);
  const witnesses=result.links.filter(link=>link.role==="simplification witness"&&link.freeze);
  assert.equal(witnesses.length,6);
  const recursive=witnesses.find(witness=>witness.freeze.original==="simp;"
    &&witness.freeze.text.includes("nat_add_zero"));
  assert.ok(recursive);
  assert.doesNotMatch(recursive.freeze.text,/double_zero_if/);
  for(const [index,witness] of witnesses.entries()) {
    assert.ok(witness.rewriteSteps?.length,witness.name);
    for(const step of witness.rewriteSteps)
      assert.equal(program.inspect(step.binding).type.tag,"Path");
    const {start,end,original,text}=witness.freeze;
    assert.equal(source.slice(start,end),original);
    assert.match(text,/^simp(?:a)? only \[/);
    const frozen=source.slice(0,start)+text+source.slice(end);
    const replay=new CubicalProgram(await createCubical(),readLibrary);
    t.after(()=>replay.dispose());
    const checked=await replay.check(frozen,`frozen_simp_${index}`);
    assert.equal(checked.complete,true,JSON.stringify(checked.gaps));
  }
  const formatted=formatCubist(source);
  assert.equal(expandedSyntax(parse(formatted)),expandedSyntax(parse(source)));
  // A set assignment is spaced like one; an equality carrier stays attached.
  assert.equal(formatted,source);
  assert.match(formatted,/simp_set nat_units := \[nat_add_zero\];/);
  assert.match(formatCubist("def t(x : Nat) : x =[Nat] x {\n  rfl;\n}\n"),/x =\[Nat\] x/);
});

// The verdicts are the ergonomics_simp_client_* modules'; here, the rule
// sets they keep.
test("imported simp registrations keep the higher priority, and a shadowed rule is never frozen",async t=>{
  const defaults=async name=>{
    const {program}=await cases(t,`simp_client_${name}`);
    return [...program.simpRegistries.get(`ergonomics_simp_client_${name}`).defaults.values()];
  };
  for(const order of ["conflict","reverse_order"]) {
    const rules=await defaults(order);
    assert.equal(rules.length,1,order);
    assert.equal(rules[0].priority,7,order);
  }
  const {result}=await cases(t,"simp_client_shadowed_rule");
  assert.equal(result.links.find(link=>link.role==="simplification witness")?.freeze,null);
});



test("conditional simp links a reflexive premise's rewrite",async t=>{
  const {result}=await cases(t,"conditional_simp");
  const reflexiveLink=result.links.find(link=>link.role==="simplification witness"&&link.description?.includes("1 rewrites"));
  assert.ok(reflexiveLink);
});

test("conditional premise simplification is bounded and keeps nested witnesses",async t=>{
  const {result,program}=await cases(t,"nested_premises");
  const work=name=>result.outputs.find(d=>d.name===name).rewriteWork;
  assert.ok(work("nested").premiseAttempts>=2);
  assert.ok(work("nested").premiseProofs>=2);
  assert.ok(work("nested").premiseRewriteSteps>=2);
  assert.ok(work("no_base").premiseAttempts>0);
  assert.equal(work("no_base").premiseProofs,0);
  const step=result.links.find(link=>link.role==="simplification step"
    &&link.description.includes("using outer"));
  assert.match(step?.description??"",/Premise simplified using inner, nat_add_zero/);
  assert.equal(program.inspect(step.binding).type.tag,"Path");
});

test("rewrite errors are reported at the rule they name",async t=>{
  const reverseSource="def reverse(n : Nat) : n = n { rw [<- refl(n)] at lhs; }";
  const reverseRule=parse(reverseSource).declarations[0].body[0].rules[0];
  assert.equal(reverseSource.slice(reverseRule.start,reverseRule.end),"<- refl(n)");
  const {source,result}=await cases(t,"rule_diagnostics");
  for(const [name,token] of [["bad_rw","nat_add_zero(n)"],
    ["bad_simp","[0]"],["missing_premise","[zero_if]"]]) {
    const output=result.outputs.find(d=>d.name===name);
    const statementStart=source.indexOf(`def ${name}`);
    const expected=source.indexOf(token,statementStart)+(token.startsWith("[")?1:0);
    assert.equal(output.errorStart,expected,name);
    assert.equal(result.gaps.find(g=>g.name===name).start,expected,name);
  }
  assert.match(result.outputs.find(d=>d.name==="bad_rw").reason,/ at \d+:\d+$/);
  assert.match(result.outputs.find(d=>d.name==="bad_simp").reason,/ at \d+:\d+$/);
});


test("tactic search time limits exclude later statements and calc steps",async t=>{
  // Checking slow_step advances a fake clock by five seconds, as if that
  // later statement were slow. No rewrite search runs while it is checked.
  const name="ergonomics_search_time_scope",path=testModulePath(name);
  const program=new CubicalProgram(await createCubical(),sourceReader({path}));
  t.after(()=>program.dispose());
  const now=performance.now.bind(performance);
  let skew=0;
  performance.now=()=>now()+skew;
  t.after(()=>{delete performance.now;});
  const infer=program.checker.infer;
  program.checker.infer=function(term,...rest) {
    if(term?.tag==="App"&&term.fn?.tag==="DefRef"&&term.fn.name.endsWith("__slow_step"))skew+=5000;
    return infer.call(this,term,...rest);
  };
  const result=await program.check(await readFile(path,"utf8"),name);
  assert.equal(result.complete,true,JSON.stringify(result.gaps));
  assert.ok(skew>=15000,"each slow statement advanced the clock");
});


test("a conditional rule with unprovable premises does not stop simplification",async t=>{
  const program=new CubicalProgram(await createCubical(),readLibrary);
  t.after(()=>program.dispose());
  const goal=count=>{
    const names=Array.from({length:count},(_,index)=>`b${index}`);
    const args=names.map(name=>`c(${name})`).join(", ");
    return {params:`a : Nat, g : ${Array(count+2).fill("Nat").join(" -> ")}, ${names.join(", ")} : Nat`,
      type:`g(${args}, (a + 0) + 0) = g(${args}, a)`};
  };
  const few=goal(20),many=goal(70);
  const result=await program.check(`import primes;
    def c(x : Nat) := x;
    def c_zero(x : Nat, h : x = 0) : c(x) = 0 { rw [h] at lhs; }
    simp_rule c_zero priority 50;
    def few(${few.params}) : ${few.type} { simp [nat_add_zero]; }
    def many(${many.params}) : ${many.type} { simp [nat_add_zero]; }
  `,"premise_budget");
  assert.equal(result.complete,true,JSON.stringify(result.gaps));
  // Each c(b_i) premise is searched once, although it recurs on both sides
  // and in every pass. Past the attempt limit the rule simply does not fire.
  const attempts=name=>result.outputs.find(d=>d.name===name).rewriteWork.premiseAttempts;
  assert.equal(attempts("few"),20);
  assert.equal(attempts("many"),64);
});

test("each calc by keyword links to its checked step in an ordinary declaration",async t=>{
  const {source,result,program}=await cases(t,"calc_step_links");
  const byOffsets=[...uncommented(source).matchAll(/\bby\b/g)].map(match=>match.index);
  const steps=result.links.filter(link=>link.role==="calculation step");
  assert.deepEqual(steps.map(link=>[link.start,link.end]),byOffsets.map(start=>[start,start+2]));
  for(const step of steps) {
    // No other link starts at `by`, so the source view shows this one.
    assert.equal(result.links.filter(link=>link.start===step.start).length,1);
    assert.equal(program.inspect(step.binding).type.tag,"Path");
  }
});

test("concrete and universe-generic declarations link tactics from the parser's keyword sites",async t=>{
  const roles=new Set(["calculation witness","calculation step","rewrite witness","simplification witness"]);
  // Each tactic link, relative to the keyword the parser recorded.
  const sites=async module=>{
    const {source,result}=await cases(t,module);
    const keywords=parse(source).declarations.map(d=>d.body[0].keyword);
    return result.links.filter(link=>roles.has(link.role)).sort((a,b)=>a.start-b.start).map(link=>{
      const keyword=keywords.findLast(keyword=>keyword.start<=link.start);
      return [link.name,link.role,link.start-keyword.start,link.end-link.start];
    });
  };
  const concrete=await sites("tactic_sites");
  assert.deepEqual(concrete.map(site=>site[0]),["calc","calc step 1","rw","simp"]);
  assert.deepEqual(await sites("tactic_sites_generic"),concrete);
});

test("a parenthesized binder links from its keyword like an unparenthesized one",async t=>{
  const {source,result}=await cases(t,"binder_sites");
  const keywords=[...uncommented(source).matchAll(/\b(fun|forall)\b/g)].map(match=>[match[1],match.index,match.index+match[1].length]);
  const links=result.links.filter(link=>link.role==="language expression"&&["fun","forall"].includes(link.name));
  assert.deepEqual(links.map(link=>[link.name,link.start,link.end]).sort((a,b)=>a[1]-b[1]),keywords);
});
