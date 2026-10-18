// Baselines obey the same importer-place contract as ordinary checks.
// Compared roots prefer their archived predecessor, then the rebuilt library;
// imports resolve by their importer's place, never by a global library-first
// fallback. `read` supplies pinned files and any explicitly shared foundations.
import { moduleReader, moduleNamePattern, moduleRoots, placeOfPath, searchOrder } from "../web/module-resolution.mjs";
import { currentSyntax, reservedBindingRenaming } from "../web/cubist/legacy-syntax.mjs";
import { parse, tokenize, languageKeywords } from "../web/cubist/parser.mjs";

// The relocation is valid only for the source unary epoch. A transitional
// UNat module may be bypassed only when it is the published identity alias;
// accepting an arbitrary module here could discard a changed carrier/view.
export function unaryNaturalBase({available,readSource}) {
  const words=text=>tokenize(text).map(token=>token.text).join(" ");
  const unary=["library/nat.cubist","archive/first-library/nat.cubist"]
    .some(path=>available.has(path)&&/\binductive Nat\b/.test(words(readSource(path))));
  if(!unary)return false;
  const alias=`import nat; def UNat : U0 := Nat;
    notation unat { x + y := add(x,y); x * y := mul(x,y);
      x <= y := le(x,y); x < y := isLt(x,y); numeral(n : Nat) := n; }`;
  for(const path of ["library/unat.cubist","archive/first-library/unat.cubist"])
    if(available.has(path)&&words(readSource(path))!==words(alias))
      throw Error(`Cannot relocate historical unary foundation: ${path} is not the identity alias.`);
  return true;
}

// Resolve renamed and relocated modules once for both baseline checks and
// historical declaration discovery. A relocated file has its current place
// even though its contents are read from the old archive path.
export function historicalModulePaths({ available, movedToLibrary = new Set(), unaryNat = false }) {
  const movedPaths = new Set();
  const modulePath = (place, name) => {
    const historicalName=unaryNat&&name==="unat"?"nat":name;
    const oldName = historicalName.endsWith("_") && languageKeywords.has(historicalName.slice(0, -1)) ? historicalName.slice(0, -1) : historicalName;
    const moved = movedToLibrary.has(name) || movedToLibrary.has(oldName);
    if (moved && place !== "library") return null;
    const root = moduleRoots[moved ? "archive" : place];
    const current = `${root}${historicalName}.cubist`, old = `${root}${oldName}.cubist`;
    const path = available.has(current) ? current : available.has(old) ? old : current;
    if (moved) movedPaths.add(path);
    return path;
  };
  return { modulePath, placeOf: path => movedPaths.has(path) ? "library" : placeOfPath(path) };
}

// The historical rewrite needs declarations from the same dependencies a
// check would load. Keep each dependency's own place when following imports.
export function importedDeclarationsReader({ available, readSyntax, modulePath, placeOf = placeOfPath }) {
  return path => {
    const seen = new Set();
    const visit = (path, includeOwn = true) => {
      if (!available.has(path) || seen.has(path)) return [];
      seen.add(path);
      let syntax;
      try { syntax = readSyntax(path); }
      catch (cause) { throw new Error(`Cannot read historical module ${path}: ${cause.message}`, { cause }); }
      const place = placeOf(path), declarations = [];
      for (const dependency of syntax.imports) {
        const paths = searchOrder(place).map(place => modulePath(place, dependency));
        const next = paths.find(path => available.has(path));
        if (next) {
          try { declarations.push(...visit(next)); }
          catch (cause) { throw new Error(`${path} imports ${dependency}: ${cause.message}`, { cause }); }
        }
      }
      if (includeOwn) declarations.push(...(syntax.items ?? syntax.declarations).filter(item => item.name));
      return declarations;
    };
    return visit(path, false);
  };
}

// Only the selected modules and their dependencies participate in the shared
// fresh-name plan. Syntax errors in that graph retain the importing path;
// unrelated historical files are never read or tokenized.
export function historicalMigrationSources({ available, readSource, modulePath, placeOf, implicitNat = false }) {
  const sources = new Map(), syntax = new Map();
  const source = path => {
    if (!sources.has(path)) sources.set(path, currentSyntax(readSource(path)));
    return sources.get(path);
  };
  const importsOf = importedDeclarationsReader({ available, modulePath, placeOf, readSyntax: path => {
    if (!syntax.has(path)) {
      const ast = parse(source(path), false, { bindable: languageKeywords });
      if (implicitNat && !path.endsWith("/nat.cubist") && !ast.imports.includes("nat")) ast.imports.unshift("nat");
      syntax.set(path, ast);
    }
    return syntax.get(path);
  } });
  const renamingFor = paths => {
    for (const path of paths) importsOf(path);
    return reservedBindingRenaming([...syntax.keys()].map(source));
  };
  return { source, importsOf, renamingFor };
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
