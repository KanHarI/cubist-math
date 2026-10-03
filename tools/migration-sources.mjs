// Baselines obey the same importer-place contract as ordinary checks.
// Compared roots prefer their archived predecessor, then the rebuilt library;
// imports resolve by their importer's place, never by a global library-first
// fallback. `read` supplies pinned files and any explicitly shared foundations.
import { moduleReader, moduleNamePattern } from "../web/module-resolution.mjs";

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
