// Baselines obey the same importer-place contract as ordinary checks.
// Compared roots prefer their archived predecessor, then the rebuilt library;
// imports resolve by their importer's place, never by a global library-first
// fallback. `read` supplies pinned files and any explicitly shared foundations.
import { moduleReader, moduleNamePattern, placeOfPath, searchOrder } from "../web/module-resolution.mjs";

// The historical rewrite needs declarations from the same dependencies a
// check would load. Keep each dependency's own place when following imports.
export function importedDeclarationsReader({ available, readSyntax, modulePath }) {
  return path => {
    const seen = new Set();
    const visit = (path, includeOwn = true) => {
      if (!available.has(path) || seen.has(path)) return [];
      seen.add(path);
      const syntax = readSyntax(path), place = placeOfPath(path), declarations = [];
      for (const dependency of syntax.imports) {
        const paths = searchOrder(place).map(place => modulePath(place, dependency));
        const next = paths.find(path => available.has(path));
        if (next) declarations.push(...visit(next));
      }
      if (includeOwn) declarations.push(...syntax.declarations);
      return declarations;
    };
    return visit(path, false);
  };
}

export function migrationSourceReader(read, modules) {
  const compared = new Set(modules), reader = moduleReader(read);
  const original = async (name, importer = null) => {
    if (!moduleNamePattern.test(name)) throw Error(`Invalid module name: ${name}.`);
    if (compared.has(name) && reader.placeOf(importer) === undefined) {
      for (const place of ["archive", "library"]) {
        const source = await read(place, name);
        if (source !== null) { reader.place(name, place); return source; }
      }
      throw Error(`No baseline for compared module ${name}.`);
    }
    return reader(name, importer);
  };
  for (const name of ["place", "placeOf", "beginCheck", "checkImports"]) original[name] = reader[name];
  return original;
}
