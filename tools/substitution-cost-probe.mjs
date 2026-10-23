// End-to-end regression controls for the substitution traversal refactor.
// Run the same script with cwd set to each checkout after `make wasm`.
// Each invocation uses fresh programs; timings include imports and checking.
import { pathToFileURL } from "node:url";
import { readFileSync } from "node:fs";
import { createHash } from "node:crypto";
const root = pathToFileURL(process.cwd() + "/");
const { default: createCubical } = await import(new URL("web/dist/cubical.mjs", root));
const { CubicalProgram } = await import(new URL("web/cubical-program.mjs", root));
const { sourceReader } = await import(new URL("tools/module-sources.mjs", root));
const { assertFreshBuild, sourceHash } = await import(new URL("tools/build-stamp.mjs", root));
assertFreshBuild();
const module = await createCubical();
const cases = [
  ["f4_check", "import f4_galois_correspondence;"],
  ["small_quotient", readFileSync(new URL("tests/fixtures/quotient-normalization.cubist", root), "utf8")],
  ["unary_quotient_unshared", `import quotients;
      def Related(a, b : Unit) : U0 := Unit;
      def Q : U0 := Quotient(U0, Unit, Related);
      computable def copy(x : Q) : Q := descend(
        U0, U0, Unit, Related, Q, quotient_is_set(U0, Unit, Related),
        fun (a : Unit) => typed(Q, class(a)),
        fun (a, b : Unit, r : Related(a, b)) => class_path(U0, Unit, Related, a, b, r), x
      );
      evaluate copy expecting !!_;`, { shareSyntax: false }],
  ["integer_multiplication", "import binary_integers; evaluate bint_mul expecting !!_;"],
  ["binary_fraction_one", `import fractions; import binary_integers;
      evaluate fraction_field(binary_integers, bint_decide, bint_mul_nonzero, bint_zero_ne_one).one expecting !!_;`],
];
for (const [name, source, optimizations = {}] of cases) {
  const program = new CubicalProgram(module, sourceReader(), { collectReferences: false, optimizations });
  program.kernel.maxQuerySteps = 40000000n;
  const started = performance.now();
  try {
    const result = await program.check(source, name);
    const ms = performance.now() - started;
    if (result.gaps.length) throw new Error(JSON.stringify(result.gaps));
    const expectedEvaluations = name === "f4_check" ? 0 : 1;
    if (result.evaluations.length !== expectedEvaluations)
      throw new Error(`${name}: expected ${expectedEvaluations} evaluations`);
    // An import/evaluation-only input has no declaration outputs, hence
    // complete=false is not a failed evaluation. Gaps and evaluations matter.
    const dependencies = Object.entries(program.sources).filter(([key]) => key !== name)
      .sort(([a], [b]) => a.localeCompare(b));
    console.log(JSON.stringify({ name, complete: result.complete, gaps: result.gaps,
      evaluations: result.evaluations.length, work: program.kernel.work(), arena: program.kernel.arena(), ms,
      sourceHash: createHash("sha256").update(source).digest("hex"),
      dependencyHash: createHash("sha256").update(JSON.stringify(dependencies)).digest("hex"),
      kernelHash: sourceHash("kernel"), node: process.version, platform: `${process.platform}/${process.arch}` }));
  } finally {
    program.dispose();
  }
}
