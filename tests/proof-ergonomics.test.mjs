import test from "node:test";
import assert from "node:assert/strict";
import {spawnSync} from "node:child_process";
import {readFile} from "node:fs/promises";
import createCubical from "../web/dist/cubical.mjs";
import {CubicalProgram} from "../web/cubical-program.mjs";
import {formatMathScript} from "../web/mathscript/formatter.mjs";
import {parse} from "../web/mathscript/parser.mjs";
import {expandedSyntax} from "../web/mathscript/tuples.mjs";

const readLibrary = name => readFile(new URL(`../web/proofs/${name}.cubist`,import.meta.url),"utf8");
const sample = name => readFile(new URL(`../docs/examples/proof-ergonomics/implemented/${name}.cubist`,import.meta.url),"utf8");

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

test("generic proof tactics link their checked specialization witnesses from source",async t=>{
  const source=`def generic_calc(U : Universe, x : Nat) : x = x { calc { x = x by refl(x); } }
    def generic_rw(U : Universe, x y : Nat, p : x = y) : x = y { rw [p]; }
    def generic_simp(U : Universe, f : Nat -> Nat, n : Nat, h : f(n) = n) : f(n) = n { simp [h]; }`;
  const program=new CubicalProgram(await createCubical(),()=>{throw Error("Unexpected import.");});
  t.after(()=>program.dispose());
  const result=await program.check(source,"generic_tactic_links");
  assert.ok(result.outputs.every(output=>output.template));
  for(const [keyword,role] of [["calc","calculation witness"],["rw","rewrite witness"],
    ["simp","simplification witness"],["by","calculation step"]]) {
    const offset=source.indexOf(`${keyword} `,source.indexOf("{"));
    const link=result.links.find(item=>item.start===offset&&item.role===role);
    assert.ok(link,`${keyword} source link`);
    const view=program.inspect(link.binding,{universes:[1]});
    assert.equal(view.type.tag,"Path",keyword);
    assert.deepEqual(view.templateInspection.universes,[1]);
    if(keyword==="by") assert.deepEqual(view.templateInspection.expansion,
      {role:"calculation step",index:1});
    if(keyword==="simp") {
      const witness=view.symbols[view.name];
      assert.match(witness.description,/Checked simplification/);
      assert.equal(witness.freeze,null);
      assert.equal(witness.rewriteSteps.length,1);
      assert.equal(program.inspect(witness.rewriteSteps[0].binding).type.tag,"Path");
    }
  }
});

test("a template simplification cannot freeze rules needed at another universe",async t=>{
  const source=`def level_sensitive(U : Universe, f : U2 -> Nat,
    h0 : f(U0) = 0, h1 : f(U1) = 0) : f(U) = 0 { simp [h0, h1]; }
    def at_zero(f : U2 -> Nat, h0 : f(U0) = 0, h1 : f(U1) = 0) : f(U0) = 0 {
      exact level_sensitive(U0, f, h0, h1);
    }
    def at_one(f : U2 -> Nat, h0 : f(U0) = 0, h1 : f(U1) = 0) : f(U1) = 0 {
      exact level_sensitive(U1, f, h0, h1);
    }`;
  const program=new CubicalProgram(await createCubical(),()=>{throw Error("Unexpected import.");});
  t.after(()=>program.dispose());
  const result=await program.check(source,"template_freeze_levels");
  assert.deepEqual(result.outputs.map(output=>output.verified),[false,true,true]);
  const link=result.links.find(item=>item.role==="simplification witness");
  assert.ok(link);
  for(const level of [0,1]) {
    const view=program.inspect(link.binding,{universes:[level]});
    assert.equal(view.type.tag,"Path");
    assert.equal(view.symbols[view.name].freeze,null);
    assert.equal(view.symbols[view.name].rewriteSteps.length,1);
  }
});

test("constant path reversal avoids exponential native interval expansion",async t=>{
  const dimensions=Array.from({length:32},(_,i)=>`d${i}`);
  let terms=Array.from({length:16},(_,i)=>`meet(d${2*i},d${2*i+1})`);
  while(terms.length>1)terms=Array.from({length:Math.ceil(terms.length/2)},(_,i)=>
    terms[2*i+1]?`join(${terms[2*i]},${terms[2*i+1]})`:terms[2*i]);
  const lets=dimensions.map((_,i)=>`let t${i} = ${i?`refl(t${i-1})`:"0"};`).join("\n");
  const source=`def native_interval_budget : 0 = 0 {
    ${lets}
    have h : t31 = t31 {
      exact ${dimensions.map(d=>`path ${d} => `).join("")}sym(refl(0)) @ ${terms[0]};
    }
    rfl;
  }`;
  const program=new CubicalProgram(await createCubical(),()=>{throw Error("Unexpected import.");},
    {collectReferences:false});
  t.after(()=>program.dispose());
  program.kernel.setDeadline(500);
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
    program.kernel.setDeadline(1000);
    try { const result=await program.check(process.argv[1],"neutral_path_reverse");
      console.log(JSON.stringify(result.outputs.map(({verified,reason})=>({verified,reason}))));
    } finally { program.dispose(); }`;
  const child=spawnSync(process.execPath,["--max-old-space-size=128","--input-type=module","-e",script,neutral],
    {encoding:"utf8",timeout:2500});
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
  const lets=dimensions.map((_,i)=>`let t${i} = ${i?`refl(t${i-1})`:"0"};`).join("\n");
  const source=`def positive_face_budget : 0 = 0 {
    ${lets}
    have h : t31 = t31 {
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
  program.kernel.setDeadline(1000);
  const result=await program.check(source,"positive_face_budget");
  assert.equal(result.outputs[0].verified,true,result.outputs[0].reason);
});

test("pushout construction visits shared source types within the proof deadline",()=>{
  const wasm=new URL("../web/dist/cubical.mjs",import.meta.url).href;
  const programPath=new URL("../web/cubical-program.mjs",import.meta.url).href;
  let source="def shared(F : U0 -> U0 -> U0, A : U0) : 0 = 0 { let T0 = A;";
  for(let i=1;i<=26;i++)source+=`let T${i} = F(T${i-1},T${i-1});`;
  source+=`let P = Pushout(T26, Unit, Unit, fun (x : T26) => tt, fun (x : T26) => tt);
    have h : forall x : P, x = x { intro x; exact path i => x; } rfl; }
    def after : 0 = 0 { rfl; }`;
  const script=`import createCubical from ${JSON.stringify(wasm)};
    import {CubicalProgram} from ${JSON.stringify(programPath)};
    const program=new CubicalProgram(await createCubical(),()=>{throw Error("Unexpected import");},
      {collectReferences:false});
    program.kernel.setDeadline(100);
    try { const result=await program.check(process.argv[1],"shared_pushout");
      console.log(JSON.stringify(result.outputs.map(({verified,reason})=>({verified,reason}))));
    } finally {program.dispose();}`;
  const child=spawnSync(process.execPath,["--max-old-space-size=128","--input-type=module","-e",script,source],
    {encoding:"utf8",timeout:2500});
  assert.equal(child.error,undefined,child.stderr);
  assert.equal(child.status,0,child.stderr);
  assert.deepEqual(JSON.parse(child.stdout.trim()).map(output=>output.verified),[true,true]);
});

test("new proof syntax survives formatting with the same expanded AST",async()=>{
  for(const name of ["arithmetic","cubical","dependent","type-transport"]) {
    const source=await sample(name),formatted=formatMathScript(source);
    assert.equal(formatMathScript(formatted),formatted,name);
    assert.equal(expandedSyntax(parse(formatted)),expandedSyntax(parse(source)),name);
  }
});

test("incomplete grouped binders and introductions fail without hanging the parser",()=>{
  const parser=new URL("../web/mathscript/parser.mjs",import.meta.url).href;
  for(const source of ["def f(x","def f : forall x","def f = fun (x",
    "def f : Nat { intro x"]) {
    const script=`import {parse} from ${JSON.stringify(parser)}; parse(process.argv[1]);`;
    const child=spawnSync(process.execPath,["--input-type=module","-e",script,source],
      {encoding:"utf8",timeout:1000});
    assert.equal(child.error,undefined,source);
    assert.notEqual(child.status,0,source);
    assert.match(child.stderr,/Expected a name\./,source);
  }
});

test("rewrites retain occurrence, carrier and dependent-position obligations",async t=>{
  const program=new CubicalProgram(await createCubical(),readLibrary);
  t.after(()=>program.dispose());
  const result=await program.check(`import primes;
    def first(n : Nat) : (n + 0) + (n + 0) = n + (n + 0) {
      rw [nat_add_zero(n)] at lhs occurrence 1;
    }
    def second(n : Nat) : (n + 0) + (n + 0) = (n + 0) + n {
      rw [nat_add_zero(n)] at lhs occurrence 2;
    }
    def reverse(n : Nat) : n = n + 0 { rw [<- nat_add_zero(n)] at lhs; }
    def default_second(n : Nat) : n + 0 = n + 0 {
      rw [nat_add_zero(n)] occurrence 2;
      exact nat_add_zero(n);
    }
    def missing(n : Nat) : n + 0 = n { rw [nat_add_zero(n)] at lhs occurrence 2; }
    def missing_default(n : Nat) : n + 0 = n { rw [nat_add_zero(n)] occurrence 2; }
    def dependent(A : U0, C : A -> U0, f : forall a : A, C(a), x : A, y : A, p : x = y) :
      f(x) = f(x) { rw [p] at lhs; }
    def after : 0 = 0 { rfl; }
  `,"rewrite_rejections");
  assert.deepEqual(result.outputs.map(d=>d.verified),[true,true,true,true,false,false,false,true]);
  assert.match(result.outputs[4].reason,/occurrence 2/);
  assert.match(result.outputs[5].reason,/occurrence 2 was not found \(1 eligible matches\)/);
  assert.match(result.outputs[6].reason,/unsupported dependent position/);
});

test("simp stops on cycles and does not equate a loop with reflexivity",async t=>{
  const program=new CubicalProgram(await createCubical(),readLibrary);
  t.after(()=>program.dispose());
  const result=await program.check(`import primes;
    def cyclic(n : Nat) : n + 0 = n { simp only [nat_add_zero, <- nat_add_zero]; }
    def false_claim : 0 = 1 { simp only []; }
    def loop_claim(A : U0, x : A, p : x = x) : p = refl(x) { simp only []; }
    def good : 0 = 0 { simp only []; }
  `,"simp_rejections");
  assert.deepEqual(result.outputs.map(d=>d.verified),[false,false,false,true]);
  assert.match(result.outputs[0].reason,/cycle|budget/);
  assert.match(result.outputs[1].reason,/unresolved equality/);
  assert.match(result.outputs[2].reason,/unresolved equality/);
});

test("simp size budget interrupts serialization of a compact shared term",()=>{
  const wasm=new URL("../web/dist/cubical.mjs",import.meta.url).href;
  const program=new URL("../web/cubical-program.mjs",import.meta.url).href;
  const script=`import createCubical from ${JSON.stringify(wasm)};
    import {CubicalProgram} from ${JSON.stringify(program)};
    let source="def shared(f : Nat -> Nat -> Nat, n : Nat) : n = n { let t0 = n;";
    for(let i=1;i<=24;i++)source+="let t"+i+" = f(t"+(i-1)+", t"+(i-1)+");";
    source+="have h : t24 = t24 { simp only []; } rfl; }";
    const checker=new CubicalProgram(await createCubical(),()=>{throw Error("No imports");},
      {collectReferences:false});
    try {
      const result=await checker.check(source,"shared_simp_budget");
      console.log(JSON.stringify(result.outputs.map(({verified,reason})=>({verified,reason}))));
    } finally {checker.dispose();}`;
  const child=spawnSync(process.execPath,["--max-old-space-size=96","--input-type=module","-e",script],
    {encoding:"utf8",timeout:1000});
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
      let source="def shared(f : Nat -> Nat -> Nat, n : Nat) : n = n { let t0 = n;";
      for(let i=1;i<=24;i++)source+="let t"+i+" = f(t"+(i-1)+", t"+(i-1)+");";
      source+="have h : t24 = t24 { rfl; } ${tactic}; }";
      const checker=new CubicalProgram(await createCubical(),()=>{throw Error("No imports");},
        {collectReferences:false});
      try {
        const result=await checker.check(source,"shared_rule_budget");
        console.log(JSON.stringify(result.outputs.map(({verified,reason})=>({verified,reason}))));
      } finally {checker.dispose();}`;
    const child=spawnSync(process.execPath,["--max-old-space-size=96","--input-type=module","-e",script],
      {encoding:"utf8",timeout:1500});
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
      let source="def shared(f : Nat -> Nat -> Nat, n : Nat) : n = n { let t0 = n;";
      for(let i=1;i<=28;i++)source+="let t"+i+" = f(t"+(i-1)+", t"+(i-1)+");";
      source+="have helper : (forall k : Nat, f(t28,k) = k) -> n = n { intro h; ${tactic}; } rfl; }";
      const checker=new CubicalProgram(await createCubical(),()=>{throw Error("No imports");},
        {collectReferences:false});
      try {
        const result=await checker.check(source,"shared_pattern_budget");
        console.log(JSON.stringify(result.outputs.map(({verified,reason})=>({verified,reason}))));
      } finally {checker.dispose();}`;
    const child=spawnSync(process.execPath,["--max-old-space-size=96","--input-type=module","-e",script],
      {encoding:"utf8",timeout:1500});
    assert.equal(child.error,undefined,`${tactic}: ${child.stderr}`);
    assert.equal(child.status,0,`${tactic}: ${child.stderr}`);
    assert.deepEqual(JSON.parse(child.stdout.trim()).map(output=>output.verified),[true],tactic);
  }
});

test("path reconstruction preserves compact shared terms within the proof deadline",()=>{
  const wasm=new URL("../web/dist/cubical.mjs",import.meta.url).href;
  const program=new URL("../web/cubical-program.mjs",import.meta.url).href;
  const cases=[
    ["rw","def shared(f : Nat -> Nat -> Nat, n : Nat) : n = n { let t0 = n;",
      "f", "have proof : t24 = t24 { rw [refl(t24)] at lhs; } rfl; }"],
    ["calc","def shared(f : Nat -> Nat -> Nat, n : Nat) : n = n { let t0 = n;",
      "f", "have proof : t24 = t24 { calc { t24 = t24 by refl(t24); _ = t24 by refl(t24); } } rfl; }"],
    ["simp","def shared(f : Nat -> Nat, g : Nat -> Nat -> Nat, n : Nat, c : forall k : Nat, n = n -> f(k) = k) : f(n) = n { let t0 = n;",
      "g", "have h : n = n := (fun (unused : Nat) => refl(n))(t24); simp only [c] with [h]; }"],
    ["simpa","def shared(f : Nat -> Nat, g : Nat -> Nat -> Nat, n : Nat, c : forall k : Nat, n = n -> f(k) = k) : f(n) = n { let t0 = n;",
      "g", "have h : n = n := (fun (unused : Nat) => refl(n))(t24); simpa only [c] with [h] using refl(n); }"],
  ];
  for(const [name,prefix,fn,suffix] of cases) {
    const script=`import createCubical from ${JSON.stringify(wasm)};
      import {CubicalProgram} from ${JSON.stringify(program)};
      let source=${JSON.stringify(prefix)};
      for(let i=1;i<=24;i++)source+="let t"+i+" = ${fn}(t"+(i-1)+",t"+(i-1)+");";
      source+=${JSON.stringify(suffix)};
      const checker=new CubicalProgram(await createCubical(),()=>{throw Error("No imports");},
        {collectReferences:false});
      checker.kernel.setDeadline(100);
      try {
        const result=await checker.check(source,"shared_path_reconstruction");
        console.log(JSON.stringify(result.outputs.map(({verified,reason,axioms})=>({verified,reason,axioms}))));
      } finally {checker.dispose();}`;
    const child=spawnSync(process.execPath,["--max-old-space-size=128","--input-type=module","-e",script],
      {encoding:"utf8",timeout:2500});
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
        source="def shared(F : U0 -> U0 -> U0, A : U0) : 0 = 0 { let T0 = A;";
        for(let i=1;i<=24;i++)source+="let T"+i+" = F(T"+(i-1)+",T"+(i-1)+");";
        source+="have h : forall x : T24, x = x { intro x; exact path i => x; } rfl; }";
      } else {
        source="def shared(f : Nat -> Nat -> Nat, n : Nat) : n = n { let t0 = n;";
        for(let i=1;i<=24;i++)source+="let t"+i+" = f(t"+(i-1)+",t"+(i-1)+");";
        source+="have h : (along (fun (n : Nat) => Nat) by refl(0) from t24) = t24 -> t24 = t24 { intro q; over (fun (n : Nat) => Nat) along refl(0) by { exact q; } } rfl; }";
      }
      const checker=new CubicalProgram(await createCubical(),()=>{throw Error("No imports");},
        {collectReferences:false});
      checker.kernel.setDeadline(100);
      try {
        const result=await checker.check(source,"shared_cubical_syntax");
        console.log(JSON.stringify(result.outputs.map(({verified,reason,axioms})=>({verified,reason,axioms}))));
      } finally {checker.dispose();}`;
    const child=spawnSync(process.execPath,["--max-old-space-size=128","--input-type=module","-e",script],
      {encoding:"utf8",timeout:2500});
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
    let source="def interval_budget : 0 = 0 { let t0 = 0;";
    for(let i=1;i<dimensions.length;i++)source+=`let t${i} = refl(t${i-1});`;
    source+=`have h : t${dimensions.length-1} = t${dimensions.length-1} { exact `;
    source+=dimensions.map(d=>`path ${d} => `).join("");
    return source+`refl(0) @ ${formula[0]}; } rfl; } def after : 0 = 0 { rfl; }`;
  };
  const script=`import createCubical from ${JSON.stringify(wasm)};
    import {CubicalProgram} from ${JSON.stringify(program)};
    const checker=new CubicalProgram(await createCubical(),()=>{throw Error("No imports");},
      {collectReferences:false});
    checker.kernel.setDeadline(1000);
    try {
      const result=await checker.check(process.argv[1],"interval_budget");
      console.log(JSON.stringify(result.outputs.map(({verified,reason,axioms})=>({verified,reason,axioms}))));
    } finally {checker.dispose();}`;
  for(const [pairs,expected] of [[8,true],[14,false]]) {
    const child=spawnSync(process.execPath,["--max-old-space-size=128","--input-type=module","-e",script,sourceFor(pairs)],
      {encoding:"utf8",timeout:2500});
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
      source="def shared(F : U0 -> U0 -> U0, A : U0) : 0 = 0 { let T0 = A;";
      for(let i=1;i<=28;i++)source+=`let T${i} = F(T${i-1},T${i-1});`;
      source+="have h : forall x : T28, x = x { intro x; exact path i => x; } rfl; }";
    } else {
      source="def shared(f : Nat -> Nat -> Nat, n : Nat) : n = n { let t0 = n;";
      for(let i=1;i<=24;i++)source+=`let t${i} = f(t${i-1},t${i-1});`;
      source+="have h : (along (fun (n : Nat) => Nat) by refl(0) from t24) = t24 -> t24 = t24 { intro q; over (fun (n : Nat) => Nat) along refl(0) by { exact q; } } rfl; }";
    }
    const script=`import createCubical from ${JSON.stringify(wasm)};
      import {CubicalProgram} from ${JSON.stringify(program)};
      import {boundedSyntaxJson} from ${JSON.stringify(json)};
      const checker=new CubicalProgram(await createCubical(),()=>{throw Error("No imports");});
      checker.kernel.setDeadline(100);
      try {
        const result=await checker.check(process.argv[1],"shared_inspection");
        const h=result.links.find(link=>link.name==="h");
        const view=checker.inspect(h.binding);
        console.log(JSON.stringify({verified:result.outputs[0].verified,
          axioms:result.outputs[0].axioms,inspected:!!view.expressionText,
          rawLimited:boundedSyntaxJson(view.expression)===null}));
      } finally {checker.dispose();}`;
    const child=spawnSync(process.execPath,["--max-old-space-size=128","--input-type=module","-e",script,source],
      {encoding:"utf8",timeout:2500});
    assert.equal(child.error,undefined,`${mode}: ${child.stderr}`);
    assert.equal(child.status,0,`${mode}: ${child.stderr}`);
    assert.deepEqual(JSON.parse(child.stdout.trim()),
      {verified:true,axioms:[],inspected:true,rawLimited:true},mode);
  }
});

test("simpa reconstructs the original equality and rejects a false supplied term",async t=>{
  const program=new CubicalProgram(await createCubical(),readLibrary);
  t.after(()=>program.dispose());
  const result=await program.check(`import primes;
    def good(n : Nat) : n + 0 = n { simpa only [nat_add_zero] using refl(n); }
    def bad : 0 = 1 { simpa only [] using refl(0); }
  `,"simpa_reconstruction");
  assert.deepEqual(result.outputs.map(d=>d.verified),[true,false]);
  assert.deepEqual(result.outputs[0].axioms,[]);
  assert.match(result.outputs[1].reason,/Type mismatch/);
});

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

  const rejected=new CubicalProgram(await createCubical(),readLibrary);
  t.after(()=>rejected.dispose());
  const bad=await rejected.check(`
    def no_path(A B : U0, a : A) : B { simpa only [] using a; }
    def maps_are_not_type_paths(A B : U0, f : A -> B, g : B -> A, a : A) : B {
      simpa only [f, g] using a;
    }
    def nontrivial_loop(A : U0, p : A = A, a : A) : A {
      simpa only [p] using a;
    }
  `,"type_transport_rejections");
  assert.deepEqual(bad.outputs.map(output=>output.verified),[false,false,false]);
  assert.match(bad.outputs[0].reason,/Type mismatch/);
  assert.match(bad.outputs[1].reason,/homogeneous equality/);
  assert.match(bad.outputs[2].reason,/cycle/);
});

test("simp tries rules at each child before rewriting its parent",async t=>{
  const program=new CubicalProgram(await createCubical(),readLibrary);
  t.after(()=>program.dispose());
  const result=await program.check(`
    def equality(f : Nat -> Nat, a b c d : Nat,
      p : f(a) = c, q : a = b, r : f(b) = d) : f(a) = d {
      simp only [p, q, r];
    }
    def type_goal(P : Nat -> U0, f : Nat -> Nat, a b c d : Nat,
      p : f(a) = c, q : a = b, r : f(b) = d, h : P(d)) : P(f(a)) {
      simpa only [p, q, r] using h;
    }
  `,"simp_child_order");
  assert.equal(result.complete,true,JSON.stringify(result.gaps));
  assert.ok(result.outputs.every(output=>output.axioms.length===0));
});

test("a quantified rule with an incompatible parameter type leaves later rules available",async t=>{
  const program=new CubicalProgram(await createCubical(),readLibrary);
  t.after(()=>program.dispose());
  const result=await program.check(`import primes;
    def through(f : Nat -> Nat, n : Nat) : f(n + 0) = f(n) {
      exact cong(f,nat_add_zero(n));
    }
    def family(P : Nat -> U0, n : Nat) : P(n + 0) = P(n) {
      simp only [through, nat_add_zero];
    }
  `,"simp_incompatible_candidate");
  assert.equal(result.complete,true,JSON.stringify(result.gaps));
  assert.ok(result.outputs.every(output=>output.axioms.length===0));
});

test("universe templates retain their defining simplification sets during use and inspection",async t=>{
  const modules={rules:`import primes;
    simp_set units = [nat_add_zero];
    def generic(U : Universe, n : Nat) : n + 0 = n { simp only [units]; }
  `};
  const program=new CubicalProgram(await createCubical(),
    module=>modules[module]??readLibrary(module));
  t.after(()=>program.dispose());
  const result=await program.check(`import rules;
    simp_set units = [];
    def use(n : Nat) : n + 0 = n { exact generic(U0,n); }
  `,"template_rule_scope");
  assert.equal(result.complete,true,JSON.stringify(result.gaps));
  assert.deepEqual(result.outputs[0].axioms,[]);
  assert.equal(program.inspect("rules__generic",{universes:[0]}).type.tag,"Pi");
});

test("imported template failures select the caller and name the definition site",async t=>{
  const library=`// ${".".repeat(200)}\ndef broken__rule(U : Universe, n : Nat) : n = n {\n simp only [0];\n}`;
  const source="import rules;\ndef use = broken__rule(U0, 0);\ndef good = 0;";
  const program=new CubicalProgram(await createCubical(),name=>{
    if(name==="rules")return library;
    throw Error(`Unexpected import ${name}`);
  });
  t.after(()=>program.dispose());
  const result=await program.check(source,"client");
  assert.deepEqual(result.outputs.map(output=>output.verified),[false,true]);
  const failed=result.outputs[0];
  assert.equal(failed.errorStart,source.indexOf("broken__rule"));
  assert.equal(failed.errorEnd,source.indexOf("broken__rule")+"broken__rule".length);
  assert.match(failed.reason,/In template rules\.broken__rule: .* at 3:13/);
  assert.ok(failed.errorEnd<=source.length);
  assert.equal(result.gaps[0].start,failed.errorStart);
});

test("freeze is withheld when removing a rule changes conditional premise search",async t=>{
  const program=new CubicalProgram(await createCubical(),readLibrary);
  t.after(()=>program.dispose());
  const result=await program.check(`import primes;
    def freeze_case(f g k : Nat -> Nat, a b t : Nat,
      c : forall n : Nat, g(n) = n -> f(n) = k(n),
      divert : g(a) = b, unit : forall n : Nat, g(n) = n,
      fallback : f(a) = t) : f(a) + f(b) = t + k(b) {
      simp [c, divert, unit, fallback];
    }
  `,"simp_freeze_premise_search");
  assert.equal(result.complete,true,JSON.stringify(result.gaps));
  assert.deepEqual(result.outputs[0].axioms,[]);
  const link=result.links.find(item=>item.role==="simplification witness");
  assert.ok(link);
  assert.equal(link.freeze,null);
});

test("freeze withholds a rule name shadowed by a named simplification set",async t=>{
  const source=`import primes;
    simp_rule nat_add_zero;
    simp_set nat_add_zero = [];
    def checked(n : Nat) : n + 0 = n { simp; }
  `;
  const program=new CubicalProgram(await createCubical(),readLibrary);
  t.after(()=>program.dispose());
  const result=await program.check(source,"simp_freeze_set_collision");
  assert.equal(result.complete,true,JSON.stringify(result.gaps));
  assert.equal(result.links.find(item=>item.role==="simplification witness")?.freeze,null);
  const edited=new CubicalProgram(await createCubical(),readLibrary);
  t.after(()=>edited.dispose());
  const broken=await edited.check(source.replace("simp;","simp only [nat_add_zero];"),
    "simp_freeze_set_collision_edited");
  assert.equal(broken.outputs[0].verified,false);
});

test("freezing a simplified hypothesis preserves its witness for dependent proofs",async t=>{
  const program=new CubicalProgram(await createCubical(),readLibrary);
  t.after(()=>program.dispose());
  const source=`import primes;
    def dependent(f g k : Nat -> Nat, a b : Nat,
      c : forall n : Nat, g(n) = n -> f(n) = k(n),
      divert : g(a) = b, unit : forall n : Nat, g(n) = n,
      fallback : f(a) = k(a), h : f(a) + f(b) = k(a) + k(b)) : 0 = 0 {
      simp only [c, divert, unit, fallback] at h as h1;
      simp [c, divert, unit, fallback] at h as h2;
      have stable : h2 = h1 { rfl; }
      rfl;
    }
    def stable(n : Nat, h : n + 0 = n, unused : 2 = 3) : n = n {
      simp [h, unused] at h as h2;
      exact h2;
    }
  `;
  const result=await program.check(source,"simp_freeze_witness");
  assert.equal(result.complete,true,JSON.stringify(result.gaps));
  const links=result.links.filter(item=>item.role==="simplification witness");
  assert.equal(links.length,3);
  assert.equal(links[1].freeze,null);
  assert.equal(links[2].freeze?.text,"simp only [h] at h as h2;");
  const edit=links[2].freeze;
  const replay=new CubicalProgram(await createCubical(),readLibrary);
  t.after(()=>replay.dispose());
  assert.equal((await replay.check(source.slice(0,edit.start)+edit.text+source.slice(edit.end),
    "simp_freeze_witness_replay")).complete,true);
});

for(const tactic of ["simp","simpa"]) {
  test(`${tactic} freeze preserves a proof later compared with another path`,async t=>{
    const program=new CubicalProgram(await createCubical(),readLibrary);
    t.after(()=>program.dispose());
    const using=tactic==="simpa"?" using refl(k(a) + k(b))":"";
    const source=`import primes;
      def dependent(f g k : Nat -> Nat, a b : Nat,
        c : forall n : Nat, g(n) = n -> f(n) = k(n),
        divert : g(a) = b, unit : forall n : Nat, g(n) = n,
        fallback : f(a) = k(a)) : 0 = 0 {
        have h1 : f(a) + f(b) = k(a) + k(b) {
          ${tactic} only [c, divert, unit, fallback]${using};
        }
        have h2 : f(a) + f(b) = k(a) + k(b) {
          ${tactic} [c, divert, unit, fallback]${using};
        }
        have stable : h2 = h1 { rfl; }
        rfl;
      }
    `;
    const result=await program.check(source,`${tactic}_freeze_path_identity`);
    assert.equal(result.complete,true,JSON.stringify(result.gaps));
    assert.deepEqual(result.outputs[0].axioms,[]);
    const links=result.links.filter(item=>item.role==="simplification witness");
    assert.equal(links.length,2);
    assert.equal(links[1].freeze,null);
  });
}

for(const tactic of ["simp","simpa"]) {
  test(`${tactic} type-path freeze preserves a proof later compared with another`,async t=>{
    const program=new CubicalProgram(await createCubical(),readLibrary);
    t.after(()=>program.dispose());
    const using=tactic==="simpa"?" using h":"";
    const finish=tactic==="simp"?"exact h;":"";
    const source=`import primes;
      def dependent(P : Nat -> U0, f g k : Nat -> Nat, a b : Nat,
        c : forall n : Nat, g(n) = n -> f(n) = k(n),
        divert : g(a) = b, unit : forall n : Nat, g(n) = n,
        fallback : f(a) = k(a), h : P(k(a) + k(b))) : 0 = 0 {
        have h1 : P(f(a) + f(b)) {
          ${tactic} only [c, divert, unit, fallback]${using};
          ${finish}
        }
        have h2 : P(f(a) + f(b)) {
          ${tactic} [c, divert, unit, fallback]${using};
          ${finish}
        }
        have stable : h2 = h1 { rfl; }
        rfl;
      }
      def stable(P : Nat -> U0, n : Nat, h : P(n), unused : 2 = 3) : P(n + 0) {
        ${tactic} [nat_add_zero, unused]${using};
        ${finish}
      }
    `;
    const result=await program.check(source,`${tactic}_type_freeze_path_identity`);
    assert.equal(result.complete,true,JSON.stringify(result.gaps));
    assert.ok(result.outputs.every(output=>output.axioms.length===0));
    const links=result.links.filter(item=>item.role==="simplification witness");
    assert.equal(links.length,3);
    assert.equal(links[1].freeze,null);
    assert.equal(links[2].freeze?.text,
      `${tactic} only [nat_add_zero]${using};`);
    const edit=links[2].freeze;
    const replay=new CubicalProgram(await createCubical(),readLibrary);
    t.after(()=>replay.dispose());
    assert.equal((await replay.check(source.slice(0,edit.start)+edit.text+source.slice(edit.end),
      `${tactic}_type_freeze_replay`)).complete,true);
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

test("a grouped binder checks its shared domain before a binder shadows that name",async t=>{
  const program=new CubicalProgram(await createCubical(),readLibrary);
  t.after(()=>program.dispose());
  const result=await program.check(`
    def Carrier = Nat;
    def grouped(Carrier item : Carrier) : item = item { rfl; }
    def applied : grouped(0, 1) = grouped(0, 1) { rfl; }
    def inferred_lambda(A : U0) : A -> A { exact fun x => x; }
    def quantified : forall A B : U0, A -> B -> A { intro A B x y; exact x; }
  `,"group_shadowing");
  assert.deepEqual(result.outputs.map(d=>d.verified),[true,true,true,true,true]);
});

test("a multi-binder fun source link inspects the complete closed function",async t=>{
  for(const expression of ["fun (x : Nat) (y : Nat) => x",
    "fun (x y : Nat) => x", "fun (x : Nat) (fun : Nat) => x"]) {
    const program=new CubicalProgram(await createCubical(),readLibrary);
    t.after(()=>program.dispose());
    const source=`def f = ${expression};`;
    assert.equal(expandedSyntax(parse(formatMathScript(source))),expandedSyntax(parse(source)));
    const result=await program.check(source,"multi_binder_link");
    assert.equal(result.complete,true,JSON.stringify(result.gaps));
    const links=result.links.filter(link=>link.name==="fun"&&link.start===source.indexOf("fun"));
    assert.equal(links.length,1,expression);
    const view=program.inspect(links[0].binding);
    assert.deepEqual(view.context,[],expression);
    assert.equal(view.type.tag,"Pi",expression);
    assert.equal(view.type.body.tag,"Pi",expression);
    assert.equal(view.symbols[view.name].name,"fun",expression);
  }
});

test("grouped universe parameters specialize like separate universe binders",async t=>{
  const program=new CubicalProgram(await createCubical(),readLibrary);
  t.after(()=>program.dispose());
  const result=await program.check(`
    def separate(U : Universe, V : Universe, A : U, B : V, x : A, y : B) = x;
    def grouped(U V : Universe, A : U, B : V, x : A, y : B) = x;
    def use_separate = separate(U0, U1, Nat, U0, 0, Nat);
    def use_grouped = grouped(U0, U1, Nat, U0, 0, Nat);
  `,"grouped_universes");
  assert.equal(result.complete,true,JSON.stringify(result.gaps));
  assert.deepEqual(result.outputs.map(item=>item.template),[true,true,false,false]);
  assert.deepEqual(result.outputs.slice(2).map(item=>item.verified),[true,true]);
  assert.equal(program.inspect("grouped_universes__grouped",{universes:[0,1]}).type.tag,"Pi");
});

test("consecutive mixed universe groups specialize and inspect every parameter",async t=>{
  const program=new CubicalProgram(await createCubical(),readLibrary);
  t.after(()=>program.dispose());
  const source=`
    def mixed(U : Universe, V W : Universe, A : U, B : V, x : A, y : B) = x;
    def multiple(U V : Universe, W X : Universe, A : U, B : W, x : A, y : B) = x;
    def use_mixed = mixed(U0, U0, U0, Nat, Nat, 0, 0);
    def use_multiple = multiple(U0, U0, U0, U0, Nat, Nat, 0, 0);
  `;
  const result=await program.check(source,"mixed_universes");
  assert.equal(result.complete,true,JSON.stringify(result.gaps));
  assert.deepEqual(result.outputs.slice(0,2).map(item=>item.templateParameters),
    [["U","V","W"],["U","V","W","X"]]);
  assert.deepEqual(result.outputs.slice(2).map(item=>item.verified),[true,true]);
  assert.equal(program.inspect("mixed_universes__mixed",{universes:[0,1,2]}).type.tag,"Pi");
  assert.equal(program.inspect("mixed_universes__multiple",{universes:[0,1,2,3]}).type.tag,"Pi");
  const binder=result.links.find(item=>item.role==="template reference"
    &&item.start===source.indexOf("V W : Universe"));
  assert.ok(binder);
  assert.equal(program.inspect(binder.binding,{universes:[0,1,2]}).expression.level,1);
});

test("rw skips an unsupported left occurrence to reach an eligible right one",async t=>{
  const program=new CubicalProgram(await createCubical(),readLibrary);
  t.after(()=>program.dispose());
  const params=`A : U0, C : A -> U0, f : forall a : A, C(a), x y : A,
    k : A -> C(x), p : x = y, h : f(x) = k(y)`;
  const result=await program.check(`
    def default_target(${params}) : f(x) = k(x) { rw [p]; exact h; }
    def explicit_target(${params}) : f(x) = k(x) { rw [p] at rhs; exact h; }
  `,"rewrite_eligible_rhs");
  assert.equal(result.complete,true,JSON.stringify(result.gaps));
  assert.ok(result.outputs.every(item=>item.verified&&item.axioms.length===0));
});

test("template inspection keeps calc endpoints separate from step witnesses",async t=>{
  const program=new CubicalProgram(await createCubical(),readLibrary);
  t.after(()=>program.dispose());
  const source=`import primes;
    def generic(U : Universe, n : Nat) : n + 0 = n {
      calc { n + 0 = n by nat_add_zero(n); }
    }`;
  const result=await program.check(source,"template_calc");
  const offset=source.indexOf("n + 0 = n by");
  const link=result.links.find(item=>item.role==="template reference"&&item.start===offset);
  assert.ok(link);
  assert.equal(program.inspect(link.binding).type.tag,"Nat");
  const step=`template_calc__generic__inspect_U0__local_${offset}_calculation_step_1`;
  const stepView=program.inspect(step);
  assert.equal(stepView.type.tag,"Path");
  const symbol=program.localSymbols[step];
  assert.deepEqual(symbol.templateExpansion,{role:"calculation step",index:1});
  assert.equal(program.inspect(symbol.templateBinding,{universes:symbol.universes,
    offset:symbol.templateOffset,expansion:symbol.templateExpansion}).type.tag,"Path");
  const payload=program.export(step);
  assert.deepEqual(payload.templateInspection.expansion,{role:"calculation step",index:1});
  const replay=new CubicalProgram(await createCubical(),name=>payload.sources[name]);
  t.after(()=>replay.dispose());
  await replay.check(payload.source,payload.main);
  const restored=replay.inspect(payload.templateInspection.binding,payload.templateInspection);
  assert.equal(restored.name,step);
  assert.deepEqual(restored.type,stepView.type);
});

test("template references include ext and simplified hypothesis binders and uses",async t=>{
  const program=new CubicalProgram(await createCubical(),readLibrary);
  t.after(()=>program.dispose());
  const source=`
    def ext_case(U : Universe, f : Nat -> Nat) : f = f {
      ext x; exact refl(f(x));
    }
    def simp_case(U : Universe, x : Nat, h : x = x) : x = x {
      simp only [] at h as h2; exact h2;
    }
  `;
  const result=await program.check(source,"template_proof_locals");
  assert.equal(result.complete,true,JSON.stringify(result.gaps));
  for(const [snippet,name] of [["ext x","x"],["as h2","h2"],["exact h2","h2"]]) {
    const offset=source.indexOf(snippet)+snippet.lastIndexOf(name);
    const link=result.links.find(item=>item.role==="template reference"&&item.start===offset);
    assert.ok(link,`Missing source link for ${snippet}`);
    const view=program.inspect(link.binding);
    assert.equal(view.symbols[view.name].name,name);
    assert.equal(view.type.tag,name==="x"?"Nat":"Path");
    const payload=program.export(view.name);
    const replay=new CubicalProgram(await createCubical(),module=>payload.sources[module]);
    t.after(()=>replay.dispose());
    await replay.check(payload.source,payload.main);
    assert.deepEqual(replay.inspect(payload.templateInspection.binding,payload.templateInspection).type,view.type);
  }
});

test("normal program checking rolls back a failed universe specialization",async t=>{
  const program=new CubicalProgram(await createCubical(),readLibrary);
  t.after(()=>program.dispose());
  const result=await program.check(`
    def identity(U : Universe, A : U, x : A) = x;
    def before = identity(U0, Nat, 0);
    def failed : 0 = 1 { exact identity(U1, U0, Nat); }
    def after = identity(U0, Nat, 1);
  `,"transaction");
  assert.deepEqual(result.outputs.map(d=>d.verified),[false,true,false,true]);
  assert.ok(program.kernel.definitions.has("transaction__identity__U0"));
  assert.equal(program.kernel.definitions.has("transaction__identity__U1"),false);
});

test("a late declaration observer error rolls back its native definition",async t=>{
  let reject=true;
  const program=new CubicalProgram(await createCubical(),readLibrary,{
    onDeclaration() {if(reject){reject=false;throw Error("observer rejected declaration");}}
  });
  t.after(()=>program.dispose());
  await assert.rejects(program.check("def discarded = 0;","observer_failure"),/observer rejected declaration/);
  assert.equal(program.kernel.definitions.has("observer_failure__discarded"),false);
  const recovered=await program.check("def accepted = 1;","observer_recovery");
  assert.equal(recovered.outputs[0].verified,true);
});

test("a quantified simp rule enforces repeated parameter consistency",async t=>{
  const program=new CubicalProgram(await createCubical(),readLibrary);
  t.after(()=>program.dispose());
  const result=await program.check(`import primes;
    def duplicated(n : Nat) : n + n = n + n { rfl; }
    def different : 0 + 1 = 0 + 1 { simp only [duplicated]; }
    def same : 1 + 1 = 1 + 1 { simp only [duplicated]; }
  `,"repeated_match");
  assert.equal(result.outputs[0].verified,true);
  assert.equal(result.outputs[1].verified,true);
  assert.equal(result.outputs[2].verified,false);
  assert.match(result.outputs[2].reason,/cycle/);
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
  const choices=result.links.filter(link=>link.role==="simplification witness"&&link.freeze);
  assert.equal(choices.length,6);
  const recursive=choices.find(choice=>choice.freeze.original==="simp;"
    &&choice.freeze.text.includes("nat_add_zero"));
  assert.ok(recursive);
  assert.doesNotMatch(recursive.freeze.text,/double_zero_if/);
  for(const [index,choice] of choices.entries()) {
    assert.ok(choice.rewriteSteps?.length,choice.name);
    for(const step of choice.rewriteSteps)
      assert.equal(program.inspect(step.binding).type.tag,"Path");
    const {start,end,original,text}=choice.freeze;
    assert.equal(source.slice(start,end),original);
    assert.match(text,/^simp(?:a)? only \[/);
    const frozen=source.slice(0,start)+text+source.slice(end);
    const replay=new CubicalProgram(await createCubical(),readLibrary);
    t.after(()=>replay.dispose());
    const checked=await replay.check(frozen,`frozen_simp_${index}`);
    assert.equal(checked.complete,true,JSON.stringify(checked.gaps));
  }
  const formatted=formatMathScript(source);
  assert.equal(expandedSyntax(parse(formatted)),expandedSyntax(parse(source)));
});

test("imported simp registrations are scoped and conflicting named sets fail only on use",async t=>{
  const sources={
    rules_a:`import primes; simp_rule nat_add_zero; simp_set units = [nat_add_zero];`,
    rules_b:`import primes; simp_rule nat_add_zero priority 7; simp_set units = [nat_add_zero];`,
  };
  const programs=[];
  const check=async(source,name)=>{
    const program=new CubicalProgram(await createCubical(),module=>sources[module]??readLibrary(module));
    programs.push(program);
    t.after(()=>program.dispose());
    return program.check(source,name);
  };
  const a=await check(`import rules_a;
    def good(n : Nat) : n + 0 = n { simp; }
    def named(n : Nat) : n + 0 = n { simp only [units]; }
  `,"client_a");
  assert.equal(a.complete,true,JSON.stringify(a.gaps));
  const isolated=await check(`import primes;
    def absent(n : Nat) : n + 0 = n { simp; }
    def explicit(n : Nat) : n + 0 = n { simp only [nat_add_zero]; }
  `,"client_isolated");
  assert.deepEqual(isolated.outputs.map(d=>d.verified),[false,true]);
  const conflict=await check(`import rules_a; import rules_b;
    def default_ok(n : Nat) : n + 0 = n { simp; }
    def ambiguous(n : Nat) : n + 0 = n { simp only [units]; }
    simp_set units = [nat_add_zero];
    def locally_resolved(n : Nat) : n + 0 = n { simp only [units]; }
  `,"client_conflict");
  assert.deepEqual(conflict.outputs.map(d=>d.verified),[true,false,true]);
  assert.match(conflict.outputs[1].reason,/ambiguous/);
  assert.equal(programs.at(-1).simpRegistries.get("client_conflict").defaults.size,1);
  assert.equal([...programs.at(-1).simpRegistries.get("client_conflict").defaults.values()][0].priority,7);
  const reversed=await check(`import rules_b; import rules_a;
    def works(n : Nat) : n + 0 = n { simp; }
  `,"client_reverse_order");
  assert.equal(reversed.complete,true,JSON.stringify(reversed.gaps));
  assert.equal([...programs.at(-1).simpRegistries.get("client_reverse_order").defaults.values()][0].priority,7);
  const shadowed=await check(`import rules_a;
    def nat_add_zero(n : Nat) = n;
    def proven(n : Nat) : n + 0 = n { simp; }
  `,"client_shadowed_rule");
  assert.equal(shadowed.complete,true,JSON.stringify(shadowed.gaps));
  assert.equal(shadowed.links.find(link=>link.role==="simplification witness")?.freeze,null);
});

test("invalid registrations do not enter the default rule set",async t=>{
  const program=new CubicalProgram(await createCubical(),readLibrary);
  t.after(()=>program.dispose());
  const result=await program.check(`import primes;
    def ordinary(n : Nat) = n;
    def useless(n : Nat) : 0 = 0 { rfl; }
    simp_rule ordinary;
    simp_rule useless;
    simp_set bad = [ordinary];
    def missing(n : Nat) : n + 0 = n { simp; }
    def explicit(n : Nat) : n + 0 = n { simp only [nat_add_zero]; }
  `,"invalid_registry");
  assert.equal(result.complete,false);
  assert.deepEqual(result.outputs.map(d=>d.verified),[true,true,false,true]);
  assert.equal(result.gaps.filter(g=>g.directive).length,3);
  assert.match(result.gaps[0].reason,/homogeneous equality/);
});

test("exclusions remove defaults and hypothesis simplification keeps the source",async t=>{
  const program=new CubicalProgram(await createCubical(),readLibrary);
  t.after(()=>program.dispose());
  const result=await program.check(`import primes;
    simp_rule nat_add_zero;
    simp_set units = [nat_add_zero];
    def removed(n : Nat) : n + 0 = n { simp without [nat_add_zero]; }
    def removed_set(n : Nat) : n + 0 = n { simp [units] without [units]; }
    def retained(n : Nat, h : n + 0 = n) : n + 0 = n {
      simp at h as normalized;
      exact h;
    }
    def normalized(n : Nat, h : n + 0 = n) : n = n {
      simp at h as shorter;
      exact shorter;
    }
    def global_rejected(n : Nat) : n = n {
      simp only [] at nat_add_zero as bad;
      rfl;
    }
  `,"local_simp");
  assert.deepEqual(result.outputs.map(d=>d.verified),[false,false,true,true,false]);
  assert.match(result.outputs[0].reason,/unresolved equality/);
  assert.match(result.outputs[1].reason,/unresolved equality/);
  assert.match(result.outputs[4].reason,/local hypothesis/);
  assert.deepEqual(result.outputs[3].axioms,[]);
});

test("conditional simp retains an explicitly selected or reflexive premise proof",async t=>{
  const program=new CubicalProgram(await createCubical(),readLibrary);
  t.after(()=>program.dispose());
  const result=await program.check(`import primes;
    def zero_if(n : Nat, h : n = 0) : n + 0 = 0 {
      calc {
        n + 0 = n by nat_add_zero(n);
        _ = 0 by h;
      }
    }
    simp_rule zero_if;
    def selected(n : Nat, h : n = 0) : n + 0 = 0 {
      simp with [h];
    }
    def missing(n : Nat) : n + 0 = 0 {
      simp;
    }
    def reflexive : 0 + 0 = 0 {
      simp;
    }
    def wrong(n : Nat, h : n = 1) : n + 0 = 0 {
      simp with [h];
    }
  `,"conditional_simp");
  assert.deepEqual(result.outputs.map(d=>d.verified),[true,true,false,true,false]);
  assert.deepEqual(result.outputs[1].axioms,[]);
  assert.match(result.outputs[2].reason,/unresolved equality/);
  assert.match(result.outputs[4].reason,/unresolved equality/);
  const reflexiveLink=result.links.find(link=>link.role==="simplification witness"&&link.description?.includes("1 rewrites"));
  assert.ok(reflexiveLink);
});

test("conditional premise simplification is bounded and keeps nested witnesses",async t=>{
  const program=new CubicalProgram(await createCubical(),readLibrary);
  t.after(()=>program.dispose());
  const result=await program.check(`import primes;
    def folded(n : Nat) = n + 0;
    def twice(n : Nat) = folded(n);
    def inner(n : Nat, h : n + 0 = n) : folded(n) = n { exact h; }
    def outer(n : Nat, h : folded(n) = n) : twice(n) = n { exact h; }
    def nested(n : Nat) : twice(n) = n {
      simp only [outer, inner, nat_add_zero];
    }
    def simpa_nested(n : Nat) : twice(n) = n {
      simpa only [outer, inner, nat_add_zero] using refl(n);
    }
    def no_base(n : Nat) : twice(n) = n {
      simp only [outer, inner];
    }
    def no_self(n : Nat) : twice(n) = n {
      simp only [outer];
    }
  `,"nested_premises");
  assert.deepEqual(result.outputs.map(d=>d.verified),[true,true,true,true,true,true,false,false]);
  assert.deepEqual(result.outputs[4].axioms,[]);
  assert.deepEqual(result.outputs[5].axioms,[]);
  assert.ok(result.outputs[4].rewriteWork.premiseAttempts>=2);
  assert.ok(result.outputs[4].rewriteWork.premiseProofs>=2);
  assert.ok(result.outputs[4].rewriteWork.premiseRewriteSteps>=2);
  for(const output of result.outputs.slice(6))
    assert.match(output.reason,/unproved premise/);
  assert.ok(result.outputs[6].rewriteWork.premiseAttempts>0);
  assert.equal(result.outputs[6].rewriteWork.premiseProofs,0);
  const step=result.links.find(link=>link.role==="simplification step"
    &&link.description.includes("using outer"));
  assert.match(step?.description??"",/Premise simplified using inner, nat_add_zero/);
  assert.equal(program.inspect(step.binding).type.tag,"Path");
});

test("rewrite errors identify the selected rule and explain an unproved premise",async t=>{
  const reverseSource="def reverse(n : Nat) : n = n { rw [<- refl(n)] at lhs; }";
  const reverseRule=parse(reverseSource).declarations[0].body[0].rules[0];
  assert.equal(reverseSource.slice(reverseRule.start,reverseRule.end),"<- refl(n)");
  const program=new CubicalProgram(await createCubical(),readLibrary);
  t.after(()=>program.dispose());
  const source=`import primes;
    def bad_rw(n : Nat) : n + 0 = n {
      rw [nat_add_zero(n)] at lhs occurrence 2;
    }
    def bad_simp(n : Nat) : n = n {
      simp only [0];
    }
    def zero_if(n : Nat, h : n = 0) : n + 0 = 0 {
      calc {
        n + 0 = n by nat_add_zero(n);
        _ = 0 by h;
      }
    }
    def missing_premise(n : Nat) : n + 0 = 0 {
      simp only [zero_if];
    }
  `;
  const result=await program.check(source,"rule_diagnostics");
  assert.deepEqual(result.outputs.map(d=>d.verified),[false,false,true,false]);
  for(const [name,token] of [["bad_rw","nat_add_zero(n)"],
    ["bad_simp","[0]"],["missing_premise","[zero_if]"]]) {
    const output=result.outputs.find(d=>d.name===name);
    const statementStart=source.indexOf(`def ${name}`);
    const expected=source.indexOf(token,statementStart)+(token.startsWith("[")?1:0);
    assert.equal(output.errorStart,expected,name);
    assert.equal(result.gaps.find(g=>g.name===name).start,expected,name);
  }
  assert.match(result.outputs.find(d=>d.name==="missing_premise").reason,
    /unproved premise at parameter 2.*simp with \[name\]/);
  assert.match(result.outputs.find(d=>d.name==="bad_rw").reason,/occurrence 2.* at \d+:\d+/);
  assert.match(result.outputs.find(d=>d.name==="bad_simp").reason,/homogeneous equality.* at \d+:\d+/);
});
