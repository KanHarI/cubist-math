// A check of raw cubical syntax by the trusted kernel, for the library's
// tests: the instruction kernel derives the term at its type, through the
// elaborator's driver, in a kernel of its own. Definitions are admitted the
// same way, in order, and a term names one as {tag:"Ref", name}, in its
// input and its results. A refusal is a result, {ok:false, error}, not an
// exception. A result reports the term arena's size and the kernel's steps
// for the term's own check, so that a test can bound them.
import "../../../tests/fresh-build.mjs";
import createCubical from "../../../web/dist/cubical.mjs";
import { CubicalKernel } from "../../../web/cubical-kernel.mjs";
import { NativeCubicalElaborator } from "../../../web/cubical-elaborator.mjs";

const module = await createCubical();

// References to definitions renamed from one tag to another: Ref in the
// tests, DefRef in the elaborator's syntax. A shared subterm stays shared:
// syntax is a graph, and as a tree it can be exponential.
function retag(term, from, to, seen = new WeakMap()) {
  if (!term || typeof term !== "object") return term;
  if (seen.has(term)) return seen.get(term);
  const result = Array.isArray(term) ? term.map(item => retag(item, from, to, seen))
    : term.tag === from ? { ...term, tag: to }
    : Object.fromEntries(Object.entries(term).map(([key, value]) => [key, retag(value, from, to, seen)]));
  seen.set(term, result);
  return result;
}
const references = term => retag(term, "Ref", "DefRef"), shown = term => retag(term, "DefRef", "Ref");

export function checkKernel(term, expected = null, assumptions = [], { normalize = true, definitions = [] } = {}) {
  const kernel = new CubicalKernel(module);
  try {
    const elaborator = new NativeCubicalElaborator(kernel);
    for (const definition of definitions) {
      const value = references(definition.value);
      const type = definition.type ? references(definition.type) : elaborator.infer(value).type;
      elaborator.define(definition.name, value, type);
    }
    const context = new Map(assumptions.map(([name, type]) => [name, references(type)]));
    const steps = () => { const work = kernel.work(); return work.instructionSteps + work.querySteps; }, before = steps();
    const checked = elaborator.checkSyntax(references(term), expected && references(expected), context, elaborator.dimensions);
    const result = { ok: true, term: shown(checked.term), type: shown(checked.type), arenaNodes: checked.arenaNodes, steps: steps() - before };
    if (normalize) result.normal = shown(elaborator.syntax.decode(kernel.normalize(checked.expression), elaborator.dimensions));
    return result;
  } catch (error) {
    return { ok: false, error: error.message };
  } finally {
    kernel.dispose();
  }
}

// A checker for elaboration in tests, as source checking uses: the
// elaborator, over a kernel of its own.
export function kernelChecker() {
  return new NativeCubicalElaborator(new CubicalKernel(module));
}
