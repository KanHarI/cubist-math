import createKernel from "./dist/kernel.mjs";
import { Session } from "./session.mjs";
const module = await createKernel();
let session = new Session(module);
session.loadDemo();
self.postMessage({
  ready: true,
  metadata: session.metadata,
  state: session.snapshot(),
});
self.onmessage = ({ data: { id, command, args } }) => {
  try {
    let result;
    if (command === "reset") {
      session.dispose();
      session = new Session(module);
      session.loadDemo();
      result = session.snapshot();
    } else if (command === "previewSource")
      result = session.previewSource(args.source);
    else if (command === "previewFocus") result = session.previewFocus(args);
    else if (command === "accept") result = session.accept(args.token);
    else if (command === "discard") {
      session.discard();
      result = session.snapshot();
    } else if (command === "inspect") result = session.inspect(args.name);
    else if (command === "undo") result = session.undo();
    else if (command === "checkout") result = session.checkout(args.revision);
    else if (command === "export") result = session.export();
    else if (command === "import") result = session.import(args.document);
    else if (command === "policy") result = session.setPolicy(args.allowAxioms);
    else if (command === "verify")
      result = session.verify(args.proposition, args.proof);
    else throw new Error("Unknown command.");
    self.postMessage({ id, result });
  } catch (e) {
    self.postMessage({ id, error: { message: e.message, details: e.details } });
  }
};
