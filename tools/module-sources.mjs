// Module sources on disk, resolved by the shared contract in
// web/module-resolution.mjs. The CLI, the test runner and the tests read
// imports through sourceReader, so each resolves them as the others do.
import { realpathSync } from "node:fs";
import { readFile } from "node:fs/promises";
import { basename, dirname, join, relative, resolve, sep } from "node:path";
import { fileURLToPath } from "node:url";
import { moduleReader, moduleRoots, placeOfPath } from "../web/module-resolution.mjs";

export const projectRoot = fileURLToPath(new URL("../", import.meta.url));

const text = async path => {
  try { return await readFile(path, "utf8"); }
  catch (error) { if (error.code === "ENOENT") return null; throw error; }
};

// A path with every symbolic link resolved, as reading the file resolves them.
// A path that does not exist stays as written; reading it reports the error.
const real = path => {
  try { return realpathSync(resolve(path)); }
  catch (error) { if (error.code === "ENOENT") return resolve(path); throw error; }
};

// The place of the file at `path`: archive, library or local. It is decided by
// where the file really is, so a link to an archive module elsewhere is still
// an archive module, and a link into the archive from elsewhere is too.
export const placeOfFile = (path, root = projectRoot) =>
  placeOfPath(relative(real(root), real(path)).split(sep).join("/"));

// A readSource for CubicalProgram. With `path`, it checks that file: the file
// is placed where it really lives, so an archive file is checked
// archive-first, and a file outside both roots imports from its own real
// directory first. It keeps the name it is checked under. Without a path, the
// checked source is not a file (a REPL entry, a reference example) and imports
// library-first. Call it with a module name alone to read a main module
// library-first, as `check NAME` does.
export function sourceReader({ path = null, root = projectRoot } = {}) {
  const local = path === null ? null : dirname(real(path));
  const readSource = moduleReader((place, name) => place === "local"
    ? (local === null ? null : text(join(local, `${name}.cubist`)))
    : text(join(root, moduleRoots[place], `${name}.cubist`)));
  if (path !== null) readSource.place(basename(path, ".cubist"), placeOfFile(path, root));
  return readSource;
}
