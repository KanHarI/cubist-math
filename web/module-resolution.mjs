// Where imports come from. The CLI, the test runner, the library and reference
// tests and the browser worker all resolve imports through this contract, so a
// source checks against the same modules everywhere.
//
// Modules live in two roots: library/, the rebuilt library, and
// archive/first-library/, the archived first library. A checked file outside
// both roots adds a third place, its own directory ("local").
//
// Each module resolves its own imports by where it lives:
// - An archive module resolves only in the archive. The archive is a closed
//   world: its checks never change as the library grows, and a library module
//   of the same name never replaces an archive module's import.
// - A library module resolves in library/, then in the archive.
// - A local module (the checked file or a module next to it) resolves in its
//   directory, then in library/, then in the archive.
// - A source that is not a file (a REPL entry, a reference example, the
//   browser's workspace) resolves in library/, then in the archive. It also
//   sees the checked source it is entered on top of, by that source's name.
// So checking an archive module is archive-isolated, and checking anything else
// is library-first: a library module shadows the archive module of that name.
//
// A check holds one module per name. When two modules of one check would
// resolve the same name to different files, for example a library module and
// an archive module that both import a name the library shadows, the check
// fails on the later importer with a message naming both places. A check with
// any failed import, a clash included, is incomplete, even when no declaration
// uses that module.

export const moduleRoots = Object.freeze({ library: "library/", archive: "archive/first-library/" });
export const moduleNamePattern = /^[A-Za-z_][A-Za-z0-9_]*$/;

// Where a module is searched for, by where its importer lives.
const searchOrders = Object.freeze({
  archive: ["archive"],
  library: ["library", "archive"],
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
  : path.startsWith(moduleRoots.library) ? "library" : "local";

const where = place => place === "local" ? "the checked file's directory" : moduleRoots[place];
const either = order => order.length === 1 ? where(order[0])
  : `${order.slice(0, -1).map(where).join(", ")} or ${where(order.at(-1))}`;

// A readSource for CubicalProgram. `read(place, name)` returns the text of the
// module `name` in that place, or null when there is none; each answer is read
// once per check. `place(name, where)` records where a checked source lives
// before the check, for a source given as text rather than read here.
//
// A reader can serve several checks, as a REPL session's entries do. Where each
// name was placed persists, since the modules a program holds keep their
// identity. What was read does not: `beginCheck()` forgets every answer, so a
// failed fetch is retried and a module created or fixed since is read again.
export function moduleReader(read) {
  // `given` holds the checked sources placed before their checks.
  const probes = new Map(), placed = new Map(), given = new Set();
  const probe = (place, name) => {
    const key = `${place}/${name}`;
    if (!probes.has(key)) probes.set(key, Promise.resolve(read(place, name)).then(text => text ?? null));
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
      order.length === 1 ? ": an archive module imports only from the archive" : ""}.`);
    placed.set(name, place);
    return probe(place, name);
  };
  readSource.place = (name, place) => {
    searchOrder(place);
    placed.set(name, place);
    given.add(name);
  };
  readSource.placeOf = name => placed.get(name);
  readSource.beginCheck = () => probes.clear();
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

// Modules known by name, as the browser knows them: `listing` names the
// modules of the library and of the archive, and fetchText(path) reads one by
// its path from the repository root. An unlisted name is never fetched.
// `main` is the checked module and `place` where its source came from, as the
// page that loaded it says. Without a place, a listed name is placed where it
// is listed, the library first; any other name is a source that is not a file.
export function listedReader(listing, fetchText, main = null, place = null) {
  const readSource = moduleReader((where, name) =>
    listing[where]?.includes(name) ? fetchText(`${moduleRoots[where]}${name}.cubist`) : null);
  const found = place ?? ["library", "archive"].find(root => listing[root]?.includes(main));
  if (main !== null && found) readSource.place(main, found);
  return readSource;
}
