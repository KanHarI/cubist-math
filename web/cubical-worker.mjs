import { cubicalSourceFile } from "./cubical-sources.mjs";
import createCubical from "./dist/cubical.mjs";
import { sourceModules, cubicalSourceModules } from "./mathscript/modules.mjs";
import { CubicalProgram } from "./cubical-program.mjs";
const module = await createCubical();
let program = null;
const readSource = async name => {
  if (!/^[A-Za-z_][A-Za-z_0-9]*$/.test(name)) throw new Error("Invalid source module name.");
  if (![...sourceModules, ...cubicalSourceModules].includes(name))
    throw new Error(`Native source is not available for ${name}.`);
  const response = await fetch(new URL(`./proofs/${cubicalSourceFile(name)}`, import.meta.url), { cache: "no-store" });
  if (!response.ok) throw new Error(`Native source is not available for ${name}.`);
  return response.text();
};
self.postMessage({ ready: true, backend: "cubical" });
self.onmessage = async ({ data: { id, command, args } }) => {
  try {
    let result;
    if (command === "check") {
      const next = new CubicalProgram(module, readSource, { optimizations: args.optimizations });
      try { result = await next.check(args.source, args.module ?? "current", progress => self.postMessage({ id, progress })); }
      catch (error) { next.dispose(); throw error; }
      program?.dispose(); program = next;
    } else if (!program) throw new Error("Check a proof first.");
    else if (command === "inspect") result = program.inspect(args.binding, args);
    else if (command === "export-inspection") result = program.export(args.binding, args.side);
    else if (command === "export") result = program.export();
    else throw new Error("Unsupported cubical command.");
    self.postMessage({ id, result });
  } catch (error) { self.postMessage({ id, error: { message: error.message, offset: error.offset } }); }
};
