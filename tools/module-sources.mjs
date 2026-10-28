// Module sources on disk, resolved by the shared contract in
// web/module-resolution.mjs. The CLI, the test runner and the tests read
// imports through sourceReader, so each resolves them as the others do.
import { realpathSync } from "node:fs";
import { readFile } from "node:fs/promises";
import { basename, dirname, join, relative, resolve, sep } from "node:path";
import { fileURLToPath } from "node:url";
import { moduleListing } from "../web/module-listing.mjs";
import { moduleReader, moduleRoots, placeOfPath } from "../web/module-resolution.mjs";

export const projectRoot = fileURLToPath(new URL("../", import.meta.url));

// File-oriented tools keep alphabetical order; corpus tools keep their
// established import order separately. The module-resolution test checks
// inventories against the directory contents in both directions.
export const moduleFiles = place => [...moduleListing[place]].sort()
  .map(name => join(projectRoot, moduleRoots[place], `${name}.cubist`));

const text = async path => {
  try { return await readFile(path, "utf8"); }
  catch (error) { if (error.code === "ENOENT") return null; throw error; }
};

// A path with every symbolic link resolved, as reading the file resolves them,
// and each name spelled as its directory entry is: on a case-insensitive file
// system, archive/first-library/CLASSICAL.cubist and
// ARCHIVE/FIRST-LIBRARY/classical.cubist are the archive's classical.cubist,
// which provenance and a transfer's file name as the root lists it. The
// operating system's realpath gives that spelling; Node's own keeps the
// caller's. A path that does not exist stays as written; reading it reports
// the error.
const real = path => {
  try { return realpathSync.native(resolve(path)); }
  catch (error) { if (error.code === "ENOENT") return resolve(path); throw error; }
};

// The place of the file at `path`: archive, library or local. It is decided by
// where the file really is, so a link to an archive module elsewhere is still
// an archive module, and a link into the archive from elsewhere is too.
const realPath = (path, root) => relative(real(root), real(path)).split(sep).join("/");
export const placeOfFile = (path, root = projectRoot) => placeOfPath(realPath(path, root));

// The file a module is read from, as moduleReader's provenance takes it
// (web/module-resolution.mjs): its text, the root it really lives in and its
// path there, by its real path, whatever place or name it is read under.
const fileAt = (path, root, content) => {
  const place = placeOfFile(path, root);
  return { text: content, root: place, file: place === "local" ? null : realPath(path, root) };
};

// A readSource for CubicalProgram. With `path`, it checks that file: the file
// is placed where it really lives, so an archive file is checked
// archive-first, and a file outside both roots imports from its own real
// directory first. It keeps the name it is checked under. Without a path, the
// checked source is not a file (a REPL entry, a reference example) and imports
// library-first. Call it with a module name alone to read a main module
// library-first, as `check NAME` does. `files` maps explicit place/name aliases
// to files, for corpus examples checked under synthetic module names. They
// still obey that place's import policy; a missing explicit file is an error.
// The module a file is checked as: its name without .cubist, as an
// identifier, since module::name spells each of its declarations
// (web/reference/first-proof.html#qualified-names): any other character is
// _, and a leading digit follows one, so my-proof.cubist is my_proof.
export const moduleOfFile = path => basename(path, ".cubist").replace(/[^A-Za-z0-9_]/g, "_").replace(/^(?=[0-9])/, "_");

export function sourceReader({ path = null, root = projectRoot, files = new Map() } = {}) {
  const local = path === null ? null : dirname(real(path));
  // Each answer names the file it read, so that an alias or a link is
  // authenticated by the file it reaches, not by the place it stands in.
  const atFile = async file => { const content = await text(file); return content === null ? null : fileAt(file, root, content); };
  const readSource = moduleReader(async (place, name) => {
    const file = files.get(`${place}/${name}`);
    if (file !== undefined) return fileAt(file, root, await readFile(file, "utf8"));
    const at = place === "local" ? (local === null ? null : join(local, `${name}.cubist`)) : join(root, moduleRoots[place], `${name}.cubist`);
    return at === null ? null : atFile(at);
  });
  // The checked file comes from itself, whatever its name.
  if (path !== null) readSource.place(moduleOfFile(path), placeOfFile(path, root), () => atFile(path));
  return readSource;
}

// A readSource for a source that checks archive modules, such as a list of
// their imports, named `main`: it is placed in the archive, so its imports
// resolve as an archive module's do, in the archive, then in the library.
export function archiveReader(main, root = projectRoot) {
  const readSource = sourceReader({ root });
  readSource.place(main, "archive");
  return readSource;
}
