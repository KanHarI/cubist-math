// Module hooks for stale-build.mjs: tools/build-stamp.mjs resolves to the
// stand-in, which reaches the real module under another URL.
const real = new URL("../../tools/build-stamp.mjs", import.meta.url).href;
const standIn = new URL("./stale-build-stamp.mjs", import.meta.url).href;
export async function resolve(specifier, context, next) {
  const resolved = await next(specifier, context);
  return resolved.url === real ? { ...resolved, url: standIn } : resolved;
}
