import "./fresh-build.mjs";
import test from "node:test";
import assert from "node:assert/strict";
import { checkTestModule } from "./check-program.mjs";
import { elaboration } from "../web/cubical-elaboration.mjs";

// Partial elements whose variables' types mention their faces
// (cubist-tests/face_restriction.cubist): each checks, and its derivation
// types a part on its face with Restrict, as the workspace's Kernel graph
// shows.
test("partial elements on a face their variables' types mention check, through Restrict", async t => {
  const cases = ["glue_eta", "tube_on_its_face", "variable_inside_a_tube", "typed_inside_a_tube", "overlapping_tubes",
    "tubes_on_both_ends"];
  const { program, result, verdicts } = await checkTestModule(t, "face_restriction");
  assert.equal(result.complete, true, JSON.stringify(verdicts));
  const views = elaboration(program, "face_restriction");
  for (const name of cases) {
    const view = views.find(declaration => declaration.name === name);
    assert.ok(view?.derivation, name);
    assert.ok(view.derivation.steps.some(step => step.rule === "Restrict"), `${name} restricts a part to its face`);
  }
});
