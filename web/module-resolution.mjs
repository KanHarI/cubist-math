// Where imports come from. The CLI, the test runner, the library and reference
// tests and the browser worker all resolve imports through this contract, so a
// source checks against the same modules everywhere.
//
// Modules live in three roots: library/, the rebuilt library;
// archive/first-library/, the archived first library; and cubist-tests/, the
// Cubist sources the test suite checks, kept as modules so that the workspace
// opens them too. A checked file outside the roots adds one more place, its
// own directory ("local").
//
// Each module resolves its own imports by where it lives:
// - A library module resolves only in library/. The library is
//   self-contained: nothing in it depends on the archive.
// - An archive module resolves in the archive, then in library/. The archive
//   may build on the library, as many modules build on nat, which lives
//   there; a library module of the same name never replaces an
//   archive module's import, so the archive's checks keep their modules.
// - A test module resolves in cubist-tests/, then in library/, then in the
//   archive. Nothing else imports a test module.
// - A local module (the checked file or a module next to it) resolves in its
//   directory, then in library/, then in the archive.
// - A source that is not a file (a REPL entry, a reference example, the
//   browser's workspace) resolves in library/, then in the archive. It also
//   sees the checked source it is entered on top of, by that source's name.
// So checking a library module is library-only, checking an archive module is
// archive-first, and checking anything else is library-first: a library
// module shadows the archive module of that name.
//
// A root also vouches for its modules' text (fromLibrary, fromArchive): a
// module read unedited from library/'s file of its name names its axioms by
// their bare names, and only text read unedited from a file of the archive
// may use the archive's legacy builtins over Truncate. What vouches is the
// file a module was really read from, by its real path; a module's name, or
// a place given to it for its imports, vouches for nothing.
//
// A check holds one module per name. When two modules of one check would
// resolve the same name to different files, for example a library module and
// an archive module that both import a name the library shadows, the check
// fails on the later importer with a message naming both places. A check with
// any failed import, a clash included, is incomplete, even when no declaration
// uses that module.

export const moduleRoots = Object.freeze({ library: "library/", archive: "archive/first-library/", tests: "cubist-tests/" });
export const moduleNamePattern = /^[A-Za-z_][A-Za-z0-9_]*$/;

// Where a module is searched for, by where its importer lives.
const searchOrders = Object.freeze({
  archive: ["archive", "library"],
  library: ["library"],
  tests: ["tests", "library", "archive"],
  local: ["local", "library", "archive"],
  source: ["library", "archive"],
});
export function searchOrder(place = "source") {
  const order = searchOrders[place];
  if (!order) throw new Error(`Unknown module place: ${place}.`);
  return order;
}

// The place of a checked file, from its path relative to the repository root
// with "/" separators.
export const placeOfPath = path => path.startsWith(moduleRoots.archive) ? "archive"
  : path.startsWith(moduleRoots.library) ? "library" : path.startsWith(moduleRoots.tests) ? "tests" : "local";

const where = place => place === "local" ? "the checked file's directory" : moduleRoots[place];
const either = order => order.length === 1 ? where(order[0])
  : `${order.slice(0, -1).map(where).join(", ")} or ${where(order.at(-1))}`;

// A readSource for CubicalProgram. `read(place, name)` returns the text of the
// module `name` in that place, or null when there is none; each answer is read
// once per check. `place(name, where, origin)` records where a checked source
// lives before the check, for a source given as text rather than read here.
//
// Where a module's imports resolve (its place) is apart from which file it was
// read from (its origin). `read` may answer with the file it read,
// { text, root, file }: the root that file really lives in, by its real path,
// and its path there, or root "local" and file null outside every root. An
// answer of text alone vouches that it is that place's own file of that name,
// as a reader without aliases or links reads. A checked source's `origin`,
// when given, reads the file it came from in the same form.
//
// A reader can serve several checks, as a REPL session's entries do. Where each
// name was placed persists, since the modules a program holds keep their
// identity. What was read does not: `beginCheck()` forgets every answer, so a
// failed fetch is retried and a module created or fixed since is read again.
export function moduleReader(read) {
  // `given` holds the checked sources placed before their checks, and
  // `origins` how to read the file each came from, when its place's file of
  // its name is not that file.
  const probes = new Map(), placed = new Map(), given = new Set(), origins = new Map(), originProbes = new Map();
  const answer = (place, name, found) => found === null || found === undefined ? null : typeof found === "string"
    ? { text: found, root: place, file: Object.hasOwn(moduleRoots, place) ? `${moduleRoots[place]}${name}.cubist` : null } : found;
  const probe = (place, name) => {
    const key = `${place}/${name}`;
    if (!probes.has(key)) probes.set(key, Promise.resolve(read(place, name)).then(found => answer(place, name, found)));
    return probes.get(key);
  };
  // The first place in `order` that has the module.
  const locate = async (name, order) => {
    for (const place of order) if (await probe(place, name) !== null) return place;
    return null;
  };
  const readSource = async (name, importer = null) => {
    if (!moduleNamePattern.test(name)) throw new Error(`Invalid module name: ${name}.`);
    const order = searchOrder(placed.get(importer));
    const place = await locate(name, order);
    if (place === null) throw new Error(`No module named ${name} in ${either(order)}${
      placed.get(importer) === "library" ? ": a library module imports only from the library" : ""}.`);
    placed.set(name, place);
    origins.delete(name);
    return (await probe(place, name)).text;
  };
  readSource.place = (name, place, origin = null) => {
    searchOrder(place);
    placed.set(name, place);
    given.add(name);
    if (origin) origins.set(name, origin);
    else origins.delete(name);
  };
  readSource.placeOf = name => placed.get(name);
  // The file a module came from: a checked source's own, or the file its
  // place holds under its name, which is what this reader read for it.
  const originOf = name => {
    if (origins.has(name)) {
      if (!originProbes.has(name)) originProbes.set(name, Promise.resolve(origins.get(name)()).then(found => found ?? null));
      return originProbes.get(name);
    }
    return placed.has(name) ? probe(placed.get(name), name) : Promise.resolve(null);
  };
  // A root vouches only for text a file of its own holds: an edited source,
  // a file elsewhere aliased into a root's place, and a source placed in a
  // root for its imports alone, which no file of the root holds, are not
  // the root's. Its place and its name decide nothing here.
  //
  // Only a library module names its axioms by their bare names, as LEM and
  // Choice (web/cubical-assumptions.mjs). A bare label is a name, so the
  // module must also be the library's file of its own name: a library file
  // checked under another name, through a link, would give a second
  // assumption the same label.
  readSource.fromLibrary = async (name, text) => {
    const origin = await originOf(name);
    return origin?.root === "library" && origin.file === `${moduleRoots.library}${name}.cubist` && origin.text === text;
  };
  // Only an archive module may use the archive's legacy builtins, Truncate,
  // its three companions and the builtin LEM and Choice over it
  // (web/translator/builtins.mjs, legacyConfinement): text that a file of
  // the archive holds, under any name, as a link to it reads. The archive is
  // frozen until it retires, so an archive module edited, in the workspace or
  // elsewhere, is a module of the user's, and may not.
  readSource.fromArchive = async (name, text) => {
    const origin = await originOf(name);
    return origin?.root === "archive" && origin.text === text;
  };
  // The file `text` was read from, as a root's path, when it is that file's
  // text: what a transfer carries so that its receiver authenticates the
  // same file (rootProvenance), whatever name the module has.
  readSource.fileOf = async (name, text) => {
    const origin = await originOf(name);
    return origin?.text === text ? origin.file : null;
  };
  readSource.beginCheck = () => { probes.clear(); originProbes.clear(); };
  // Called after a module's imports are loaded: a refusal message when one of
  // them is not the module this importer would have loaded under that name.
  readSource.checkImports = async (importer, imports) => {
    const order = searchOrder(placed.get(importer));
    for (const name of imports) {
      const held = placed.get(name);
      // A module that failed to load, or an unplaced checked source such as an
      // earlier REPL entry, carries no place; its own failure or check reports it.
      if (held === undefined || !moduleNamePattern.test(name)) continue;
      // A REPL entry imports the checked source it runs on top of.
      if (!placed.has(importer) && given.has(name)) continue;
      const expected = await locate(name, order);
      if (expected === null) return `${importer} imports ${name}, but ${either(order)} has no ${name}; `
        + `this check loaded ${name} from ${where(held)}, which ${importer} does not see.`;
      if (expected !== held) return `${importer} imports ${name} from ${where(expected)}, but this check `
        + `already loaded ${name} from ${where(held)}; a check holds one module per name.`;
    }
    return null;
  };
  return readSource;
}

// Whether a source given as text, as a transfer gives one, is the text of a
// root's file, read through `fetchText` as listedReader reads it: the
// provenance of a module no reader placed. `file` is the file the transfer
// says the module was read from (CubicalProgram.export), a root's path, so
// that a module read under another name, through an alias or a link, is
// authenticated by its file, as its reader authenticated it; without one,
// the root's file of the module's name. Only a library module names its
// axioms by their bare names (fromLibrary), its file of its own name, and
// only an archive module may use the archive's legacy builtins
// (fromArchive). A file the root does not list, and a text that cannot be
// compared, as when the root is unreachable, are not the root's.
const rootProvenance = root => (listing, fetchText) => async (name, text, file = null) => {
  const path = file ?? `${moduleRoots[root]}${name}.cubist`;
  const own = path.startsWith(moduleRoots[root]) && path.endsWith(".cubist")
    ? path.slice(moduleRoots[root].length, -".cubist".length) : null;
  if (own === null || !listing[root]?.includes(own) || root === "library" && own !== name) return false;
  try { return await fetchText(path) === text; } catch { return false; }
};
export const libraryProvenance = rootProvenance("library");
export const archiveProvenance = rootProvenance("archive");

// Modules known by name, as the browser knows them: `listing` names the
// modules of each root, and fetchText(path) reads one by its path from the
// repository root. An unlisted name is never fetched. `main` is the checked
// module and `place` where its source came from, as the page that loaded it
// says. Without a place, a listed name is placed where it is listed, the
// library first, then the tests, then the archive; any other name is a source
// that is not a file.
export function listedReader(listing, fetchText, main = null, place = null) {
  const readSource = moduleReader((where, name) =>
    listing[where]?.includes(name) ? fetchText(`${moduleRoots[where]}${name}.cubist`) : null);
  const found = place ?? ["library", "tests", "archive"].find(root => listing[root]?.includes(main));
  if (main !== null && found) readSource.place(main, found);
  return readSource;
}
