import test from "node:test";
import assert from "node:assert/strict";
import {parse} from "../web/cubist/parser.mjs";
import {expandedSyntax} from "../web/cubist/tuples.mjs";
import {formatCubist} from "../web/cubist/formatter.mjs";
import {requireTestMode,sourceTestCases} from "../web/cubist/test-pragmas.mjs";

test("test pragmas attach to the next declaration or supported directive with separate spans",()=>{
  const source=`import nat;
# test(generation.hom_universe)
# expect_error(E606)
def wrong : Void := tt;
# test(computation.zero)
evaluate zero expecting zero;`;
  const ast=parse(source),cases=sourceTestCases(ast);
  assert.deepEqual(cases.map(entry=>entry.id),["generation.hom_universe","computation.zero"]);
  assert.equal(cases[0].item.start,source.indexOf("def wrong"));
  assert.equal(cases[1].item.start,source.indexOf("evaluate"));
  assert.equal(source.slice(cases[0].item.testPragmas[1].start,cases[0].item.testPragmas[1].end),"# expect_error(E606)");
  assert.throws(()=>requireTestMode(ast,false),error=>error.offset===source.indexOf("#")&&/explicit test mode/.test(error.message));
  assert.doesNotThrow(()=>requireTestMode(ast,true));
  assert.equal(parse("def test : Unit := tt; def expect_error := test;").declarations.length,2);
});

test("test formatting preserves annotation attachment, comments and identities",()=>{
  const source=`#test(generation . hom) #expect_axioms([])\ndef x(A:U0,a:A):A:=a;
# test(failure) // the contract stays attached
# expect_error(E606)
def bad:Void:=tt;`;
  const formatted=formatCubist(source,{printWidth:40});
  assert.match(formatted,/# test\(generation\.hom\)\n# expect_axioms\(\[\]\)\ndef x/);
  assert.deepEqual(expandedSyntax(parse(formatted)),expandedSyntax(parse(source)));
  assert.equal(formatCubist(formatted,{printWidth:40}),formatted);
  assert.match(formatted,/\/\/ the contract stays attached/);
});

for(const [source,message] of [
  ["# unknown(x) def x := tt;",/Unknown test pragma/],
  ["# test() def x := tt;",/Expected a test pragma name/],
  ["# test(a.) def x := tt;",/Expected a test pragma name/],
  ["# test(a) # expect_error(W705) def x := tt;",/appropriate kind/],
  ["# test(a) # expect_warning(E606) def x := tt;",/appropriate kind/],
  ["# test(a) # expect_error(E606) # expect_error(E343) def x := tt;",/Repeated test pragma/],
  ["# test(a) def x := tt; # test(a) def y := tt;",/Duplicate test case/],
  ["# test(a) # expect_error(E606) # expect_axioms([]) def x := tt;",/refused test/],
  ["# test(a) # expect_axioms([Choice,Choice]) def x := tt;",/repeats a name/],
  ["# expect_error(E606) def x := tt;",/named # test/],
  ["# test(a)",/no following target/],
  ["# test(a) import nat;",/cannot target import/],
  ["# test(a) section (A : U0) { def x := A; }",/cannot target section/],
  ["section (A : U0) { # test(a) }",/cannot target/],
  ["# test(a) notation n { x + y := x; }",/cannot target notation/],
  ["# test(a) # expect_axioms([]) print(typeof(tt));",/need a declaration/],
])test(`test pragma refusal: ${source}`,()=>assert.throws(()=>parse(source),message));
