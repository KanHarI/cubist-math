import { readFile, writeFile, mkdir } from "node:fs/promises";
import { renderModule } from "./readable_backend.mjs";
import { parse } from "../../web/mathscript/parser.mjs";
import { leadingDocumentation } from "../../web/mathscript/documentation.mjs";
const scratch = new URL("../../.tools/mathscript-migration/", import.meta.url);
await mkdir(scratch, { recursive: true });
let arithmetic = await readFile(
  new URL("./arithmetic.mjs", import.meta.url),
  "utf8",
);
const first = arithmetic.indexOf("  const sym = def(");
const fields =
  "b,op,norm,app,N,Z,U,V,T,tt,S,one,two,lam,pi,arr,eq,refl,not,sum,L,R,absurd,cases,sigma,pair,split,and,both,ind,rec,J,transport,def";
arithmetic =
  `import {foundation} from '../../tools/proofs/readable_backend.mjs';\nexport function arithmetic(module){const {${fields}}=foundation();\n` +
  arithmetic.slice(first);
await writeFile(new URL("arithmetic.mjs", scratch), arithmetic);
for (const file of ["number_theory.mjs", "euclid.mjs"]) {
  let text = await readFile(new URL(file, import.meta.url), "utf8");
  if (file === "euclid.mjs")
    text = text.replace(
      /  if \(!b\.k\.verify\(statement, proof\)\)[\s\S]*?  return \{/,
      "  return {",
    );
  await writeFile(new URL(file, scratch), text);
}
const { euclid } = await import(new URL("euclid.mjs", scratch));
euclid(null);
let source = renderModule();
// Mathematical source is the authority for prose, even when proof bodies are
// regenerated. Retain its declaration comments instead of keeping a second
// documentation table in this generator.
const destination = new URL("../../web/proofs/primes.proof", import.meta.url);
let previous = "";
try { previous = await readFile(destination, "utf8"); }
catch (error) { if (error.code !== "ENOENT") throw error; }
const documentation = new Map(parse(previous).declarations.map(decl => [
  decl.name.text, leadingDocumentation(previous, decl.start)?.source ?? "",
]));
for (const decl of parse(source).declarations.reverse()) {
  const comment = documentation.get(decl.name.text);
  if (comment) source = source.slice(0, decl.start) + comment + source.slice(decl.start);
}
const { default: createKernel } = await import("../../web/dist/kernel.mjs");
const { compile } = await import("../../web/mathscript/compiler.mjs");
const checked = compile(await createKernel(), source);
console.log(
  `Independently checked ${checked.outputs.length} mathematical declarations; ${checked.axiomCount} axioms.`,
);
checked.kernel.dispose();
await writeFile(
  new URL("../../web/proofs/primes.proof", import.meta.url),
  source,
);
console.log("Generated mathematical source:", source.length, "characters");
