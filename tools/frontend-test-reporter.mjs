// Machine-readable Node test events. Error's useful fields are not all
// enumerable; preserve causes explicitly instead of searching rendered TAP.
import { relative } from "node:path";
const errorRecord = error => !error ? null : {
  name: error.name, code: error.code, message: error.message?.split("\n")[0],
  failureType: error.failureType, cause: errorRecord(error.cause),
};
export default async function* report(source) {
  for await (const event of source) {
    if (["test:pass", "test:fail"].includes(event.type)) {
      const { name, file, nesting, todo, skip, details } = event.data;
      yield JSON.stringify({ type: event.type, name, file: file && relative(process.cwd(), file), nesting, todo, skip,
        error: errorRecord(details?.error) }) + "\n";
    } else if (event.type === "test:summary") {
      const { success, counts, file } = event.data;
      yield JSON.stringify({ type: event.type, success, counts,
        file: file && relative(process.cwd(), file) }) + "\n";
    }
  }
}
