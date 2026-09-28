// A stand-in for tools/build-stamp.mjs that always finds web/dist stale,
// loaded in its place through stale-build.mjs, so that a test can see each
// command refuse a stale build without making one.
export * from "../../tools/build-stamp.mjs?stand-in";
export function assertFreshBuild() {
  throw new Error("web/dist is stale: the test's stand-in says so. Run make wasm.");
}
