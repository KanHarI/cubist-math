// Package the same cubical syntax/elaboration sources used by native tests.
// Generated browser copies are build artifacts, never a second implementation.
// Under the build lock, the sources' hash is taken first, the stamp cleared
// before copying, and the hash stamped after (build-stamp.mjs).
import { mkdirSync, readFileSync, rmSync, writeFileSync } from "node:fs";
import { invalidate, runtimeModules, sourceHash, withLock, write } from "./build-stamp.mjs";
const output = new URL("../web/dist/cubical-runtime/", import.meta.url);
withLock(() => {
  const hash = sourceHash("runtime");
  invalidate("runtime");
  // A module dropped from the list must not stay behind in the copy.
  rmSync(output, { recursive: true, force: true });
  mkdirSync(output, { recursive: true });
  for (const name of runtimeModules) {
    const source = readFileSync(new URL(`../lib/cubical/${name}.mjs`, import.meta.url), "utf8");
    // The copy lives in web/dist/cubical-runtime/, so imports of web/ modules
    // move up two directories instead of naming web/.
    writeFileSync(new URL(`${name}.mjs`, output), source.replaceAll("../../web/", "../../"));
  }
  const naturalSource=readFileSync(new URL("../archive/first-library/nat.cubist",import.meta.url),"utf8");
  writeFileSync(new URL("nat-source.mjs",output),`export default ${JSON.stringify(naturalSource)};\n`);
  write("runtime", hash);
});
