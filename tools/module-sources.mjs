// Module sources on disk, resolved by the shared contract in
// web/module-resolution.mjs. The CLI, the test runner and the tests read
// imports through sourceReader, so each resolves them as the others do.
import { realpathSync } from "node:fs";
import { readFile } from "node:fs/promises";
import { basename, dirname, isAbsolute, join, relative, resolve, sep } from "node:path";
import { fileURLToPath } from "node:url";
import { moduleListing } from "../web/module-listing.mjs";
import { moduleReader, moduleRoots, placeOfPath } from "../web/module-resolution.mjs";

export const projectRoot = fileURLToPath(new URL("../", import.meta.url));

// File-oriented tools keep alphabetical order; corpus tools keep their
// established import order separately. The module-resolution test checks
// inventories against the directory contents in both directions.
export const moduleFiles = place => [...moduleListing[place]].sort()
  .map(name => join(projectRoot, moduleRoots[place], `${name}.cubist`));

// A path made absolute as the operating system reads a relative one, from
// the working directory, and nothing more: path.resolve would also drop each
// `name/..` pair as text, so that `link/..` named the link's own directory
// where reading it leaves the link's target, another file.
const absolute = path => isAbsolute(path) ? path : `${process.cwd()}${sep}${path}`;
// A path below a directory, as the operating system reads it: join would
// drop a `link/..` in the directory as text too.
const below = (directory, path) => `${directory}${sep}${path}`;

// A path as the operating system reads it: every symbolic link resolved in
// order, a `..` after one leaving its target, and each name spelled as its
// directory entry is, so that on a case-insensitive file system
// archive/first-library/CLASSICAL.cubist and
// ARCHIVE/FIRST-LIBRARY/classical.cubist are the archive's classical.cubist,
// which provenance and a transfer's file name as the root lists it. The
// operating system's realpath gives that path; Node's own keeps the caller's
// spelling. A path that does not exist stays as written; reading it reports
// the error.
const real = path => {
  try { return realpathSync.native(absolute(path)); }
  catch (error) { if (error.code === "ENOENT") return resolve(path); throw error; }
};
// The path the file at `path` is read through, the one its provenance names.
export const canonicalFile = path => real(path);

// The place of the file at `path`: archive, library or local. It is decided by
// where the file really is, so a link to an archive module elsewhere is still
// an archive module, and a link into the archive from elsewhere is too.
const realPath = (path, root) => relative(real(root), real(path)).split(sep).join("/");
export const placeOfFile = (path, root = projectRoot) => placeOfPath(realPath(path, root));

// The file at `path` as moduleReader's provenance takes it
// (web/module-resolution.mjs): its text, the root it really lives in and its
// path there, whatever place or name it is read under. The text is read from
// the same real path the root and the path are taken from, so that what is
// read and the file it is vouched for are one file. A missing file is null,
// or, `required`, an error.
const fileAt = async (path, root, { required = false } = {}) => {
  let canonical;
  try { canonical = realpathSync.native(absolute(path)); }
  catch (error) { if (error.code === "ENOENT" && !required) return null; throw error; }
  const content = await readFile(canonical, "utf8");
  const place = placeOfFile(canonical, root);
  return { text: content, root: place, file: place === "local" ? null : realPath(canonical, root) };
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
  const readSource = moduleReader(async (place, name) => {
    const file = files.get(`${place}/${name}`);
    if (file !== undefined) return fileAt(file, root, { required: true });
    const at = place === "local" ? (local === null ? null : below(local, `${name}.cubist`)) : below(root, `${moduleRoots[place]}${name}.cubist`);
    return at === null ? null : fileAt(at, root);
  });
  // The checked file comes from itself, whatever its name.
  if (path !== null) readSource.place(moduleOfFile(path), placeOfFile(path, root), () => fileAt(path, root));
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
