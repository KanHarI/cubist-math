// Module sources on disk, resolved by the shared contract in
// web/module-resolution.mjs. The CLI, the test runner and the tests read
// imports through sourceReader, so each resolves them as the others do.
import { readFile } from "node:fs/promises";
import { basename, dirname, join, relative, resolve, sep } from "node:path";
import { fileURLToPath } from "node:url";
import { moduleReader, moduleRoots, placeOfPath } from "../web/module-resolution.mjs";

export const projectRoot = fileURLToPath(new URL("../", import.meta.url));

const text = async path => {
  try { return await readFile(path, "utf8"); }
  catch (error) { if (error.code === "ENOENT") return null; throw error; }
};

// The place of the file at `path`: archive, library or local.
export const placeOfFile = (path, root = projectRoot) =>
  placeOfPath(relative(root, resolve(path)).split(sep).join("/"));

// A readSource for CubicalProgram. With `path`, it checks that file: the file
// is placed where it lives, so an archive file is checked archive-isolated,
// and a file outside both roots imports from its own directory first. Without
// a path, the checked source is not a file (a REPL entry, a reference example)
// and imports library-first. Call it with a module name alone to read a main
// module library-first, as `check NAME` does.
export function sourceReader({ path = null, root = projectRoot } = {}) {
  const local = path === null ? null : dirname(resolve(path));
  const readSource = moduleReader((place, name) => place === "local"
    ? (local === null ? null : text(join(local, `${name}.cubist`)))
    : text(join(root, moduleRoots[place], `${name}.cubist`)));
  if (path !== null) readSource.place(basename(path, ".cubist"), placeOfFile(path, root));
  return readSource;
}
