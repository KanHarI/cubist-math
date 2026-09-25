// A7 regressions for the HoTT automation roadmap. They pin what the kernel
// computes today, which probes it rejects, and why. A later milestone that
// changes one of these outcomes must update the fixture deliberately.
import test from "node:test";
import assert from "node:assert/strict";
import {readFile} from "node:fs/promises";
import createCubical from "../web/dist/cubical.mjs";
import {CubicalProgram} from "../web/cubical-program.mjs";
import {parse} from "../web/mathscript/parser.mjs";

const readLibrary = name => readFile(new URL(`../web/proofs/${name}.cubist`,import.meta.url),"utf8");
const example = name => readFile(new URL(`../docs/examples/hott-automation/${name}`,import.meta.url),"utf8");

async function checkExample(t,file,module) {
  const program=new CubicalProgram(await createCubical(),readLibrary,{collectReferences:false});
  t.after(()=>program.dispose());
  const source=await example(file);
  return {source,result:await program.check(source,module)};
}

function assertCheckedFixture(result,names) {
  assert.equal(result.complete,true,JSON.stringify(result.gaps));
  // Pin the declaration list so that no law silently leaves the fixture.
  assert.deepEqual(result.outputs.map(d=>d.name),names);
  for(const output of result.outputs)assert.deepEqual(output.axioms,[],output.name);
}

test("conversion laws the kernel computes stay checked declarations",async t=>{
  const {result}=await checkExample(t,"conversion-laws.cubist","hott_conversion_laws");
  assertCheckedFixture(result,["bridge_rec","bridge_rec_beta","bridge_ind","bridge_ind_beta",
    "bridge_code","bridge_code_meridian","bridge_code_upper","bridge_code_lower",
    "cong_constant_line","cong_identity_line","cong_compose_line","cong_refl_line",
    "cong_sym_line","sym_sym_line","transport_path_right","transport_arrow","happly_funext",
    "sigma_projection_eta","naturality_square","closed_constant_transport","PropLevel",
    "prop_level_zero","prop_level_one","reverse_dependent_path","dependent_congruence"]);
});

test("accepted cubical probes from the roadmap evidence keep checking",async t=>{
  const {result}=await checkExample(t,"cubical-probes.cubist","hott_cubical_probes");
  assertCheckedFixture(result,["sigma_line","filler_rewrite","multi_hole","square_rebuild",
    "trans_as_composition","sym_sym_refl","convertible_rule","right_unit_at_u1",
    "right_unit_at_u0","ordered_fillers"]);
});

test("closed assumption-free results compute to canonical values (invariant 10)",async t=>{
  const {source,result}=await checkExample(t,"canonicity.cubist","hott_canonicity");
  assertCheckedFixture(result,["closed_arithmetic","closed_path_induction","closed_transport",
    "closed_dependent_transport","winding_one","winding_two","winding_minus_one",
    "winding_integer_loop"]);
  // Each statement names its canonical value and is proved by computation
  // alone. Replacing rfl by a lemma would hide a result that stopped computing.
  for(const declaration of parse(source).declarations)
    assert.deepEqual(declaration.body.map(statement=>statement.kind),["rfl"],declaration.name.text);
});

// Expected outcome of each probe in rejected-probes.cubist.rejected. `until`
// names the milestone expected to make the probe check; a probe without one
// must stay rejected.
const rejectedProbes = {
  rejected_right_unit:{reason:/^Type mismatch\./},
  rejected_cong_trans:{reason:/^Type mismatch\./},
  rejected_transport_left:{reason:/^Type mismatch\./},
  rejected_constant_refl:{reason:/^Type mismatch\./},
  rejected_sequential_line:{reason:/^Type mismatch\./},
  rejected_convertible_rule_refl:{reason:/^Type mismatch\./},
  rejected_independent_fillers:{reason:/^Type mismatch\./},
  rejected_sym_pathp:{reason:/Unbound cubical dimension/,until:"E0 or A1a"},
  rejected_rule_constant:{reason:/not determined by the matched side/,until:"A1"},
  rejected_rule_ap:{reason:/not determined by the matched side/,until:"A1"},
  under_succ:{reason:/unresolved equality goal/,until:"A2"},
  use_ru:{reason:/unresolved equality goal/,until:"A1"},
  use_ru_at_u0:{reason:/unresolved equality goal/,until:"A1"},
};

test("rejected laws and pending simplifier probes keep their recorded outcomes",async t=>{
  const {result}=await checkExample(t,"rejected-probes.cubist.rejected","hott_rejected_probes");
  const outputs=new Map(result.outputs.map(d=>[d.name,d]));
  assert.deepEqual([...outputs.keys()].filter(name=>!rejectedProbes[name]),["convertible_rule","ru"]);
  for(const name of ["convertible_rule","ru"])assert.equal(outputs.get(name).verified,true,name);
  for(const [name,{reason,until}] of Object.entries(rejectedProbes)) {
    const output=outputs.get(name);
    assert.ok(output,name);
    const note=until?` If ${until} has landed, move ${name} to the checked fixtures.`:"";
    assert.equal(output.verified,false,`${name} unexpectedly checks.${note}`);
    assert.match(output.reason,reason,`${name}: ${output.reason}.${note}`);
  }
});
