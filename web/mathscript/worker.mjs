import createKernel from "../dist/kernel.mjs";
import { compile } from "./compiler.mjs";
import { sourceModules } from "./modules.mjs";
import { MAX_STEPS } from "../language.mjs";
import { checkedFoldedView, exportInspection, inspectionContextNames, checkedContextView, inspectionAxiomNotation } from "./kernel-folding.mjs";
const module = await createKernel();
const library = Object.fromEntries(
  await Promise.all(
    sourceModules.map(async (name) => {
      const response = await fetch(
        new URL(`../proofs/${name}.proof`, import.meta.url),
        { cache: "no-store" },
      );
      if (!response.ok) throw new Error(`Unable to load ${name}.proof.`);
      return [name, await response.text()];
    }),
  ),
);
let checked = null;
self.postMessage({ ready: true, maxSteps: MAX_STEPS });
self.onmessage = ({ data: { id, command, args } }) => {
  try {
    let result;
    if (command === "check") {
      const next = compile(module, args.source, library, {
        optimizations: args.optimizations,
        onProgress: progress => self.postMessage({ id, progress }),
      });
      checked?.kernel.dispose();
      checked = next;
      const { kernel, ...metadata } = next;
      result = { ...metadata, stats: kernel.stats() };
    } else {
      if (!checked) throw new Error("Check a proof first.");
      if (command === "inspect") {
        result = checked.kernel.inspect(args.binding, {
          expand: args.expand ?? [],
        });
        Object.assign(result.contextNames, inspectionContextNames(checked));
        result.folded = checkedFoldedView(checked, args.binding, { expand: args.expand ?? [] });
        result.context = checkedContextView(checked, result);
        result.axiomNotation = inspectionAxiomNotation(checked);
      }
      else if (command === "export-folding")
        result = checkedFoldedView(checked, args.binding, { certificate: true })?.certificate;
      else if (command === "export-inspection")
        result = exportInspection(checked, args.binding, args.side, args.folded);
      else if (command === "export")
        result = {
          format: "thth-workbench",
          version: 1,
          policy: { allowAxioms: checked.allowAxioms },
          steps: checked.kernel.steps,
        };
      else throw new Error("Unknown command.");
    }
    self.postMessage({ id, result });
  } catch (e) {
    self.postMessage({
      id,
      error: {
        message: e.message,
        line: e.line,
        column: e.column,
        offset: e.offset,
      },
    });
  }
};
