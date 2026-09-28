// Package the same cubical syntax/elaboration sources used by native tests.
// Generated browser copies are build artifacts, never a second implementation.
// The sources' hash is taken before copying and stamped after (build-stamp.mjs).
import { mkdir, readFile, writeFile } from "node:fs/promises";
import { runtimeModules, sourceHash, writeStamp } from "./build-stamp.mjs";
const output = new URL("../web/dist/cubical-runtime/", import.meta.url);
const hash = sourceHash("runtime");
await mkdir(output, { recursive: true });
for (const name of runtimeModules) {
  const source = await readFile(new URL(`../lib/cubical/${name}.mjs`, import.meta.url), "utf8");
  // The copy lives in web/dist/cubical-runtime/, so imports of web/ modules
  // move up two directories instead of naming web/.
  await writeFile(new URL(`${name}.mjs`, output), source.replaceAll("../../web/", "../../"));
}
writeStamp("runtime", hash);
