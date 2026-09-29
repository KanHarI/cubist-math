// The build stamp (web/dist/build-stamp.json). web/dist is generated and not
// versioned: the WASM kernel, compiled from kernel/src, kernel/include and the
// bridge, and a copy of the translator's modules, which CubicalProgram loads.
// A build that no longer matches its sources, its compiler or its own outputs
// would make a run pass or fail for code it does not contain. So a build clears
// its stamp before it writes anything, hashes its sources, builds, and stamps
// the sources' hash, its compiler and flags, and its outputs' hashes; `make
// wasm` runs under a lock and rebuilds what no longer matches, whatever the
// file times say; and every runner refuses a stale build. The exported
// functions always check this repository; buildStamp(root) serves tests.
import { createHash } from "node:crypto";
import { execFileSync, spawnSync } from "node:child_process";
import { existsSync, mkdirSync, readFileSync, readdirSync, realpathSync, renameSync, rmSync, writeFileSync } from "node:fs";
import { fileURLToPath } from "node:url";

// The translator modules copied for the browser (tools/build-cubical-runtime.mjs).
export const runtimeModules = ["core", "lattice", "syntax-graph", "equivalence", "translate", "proof-rewrite",
  "simp-registry", "number-transport", "pushouts", "path-over", "path-algebra", "public-equivalence",
  "dimension-slots", "dependent-transport", "adjointification", "names", "elaboration", "proof-goals", "motives",
  "fuel", "inductive", "match", "hlevel"];

// A hash of files, by path and content, read through `read`.
export function hashOf(paths, read) {
  const hash = createHash("sha256");
  for (const path of paths) hash.update(path).update("\0").update(read(path)).update("\0");
  return hash.digest("hex");
}

// A compiler's identity and flags: its --version line, then its arguments.
export function compilerConfiguration(command) {
  let version = "unknown";
  try { version = execFileSync(command[0], ["--version"], { encoding: "utf8", stdio: ["ignore", "pipe", "ignore"] }).split("\n")[0]; }
  catch { /* A compiler that cannot say is still named by its path. */ }
  return `${version}\n${command.join(" ")}`;
}

const sleep = milliseconds => Atomics.wait(new Int32Array(new SharedArrayBuffer(4)), 0, 0, milliseconds);
const alive = pid => { try { process.kill(pid, 0); return true; } catch (error) { return error.code === "EPERM"; } };

// The stamp of the tree at `root`, a directory URL ending in a slash.
export function buildStamp(root, { lockTimeout = Number(process.env.CUBIST_BUILD_LOCK_TIMEOUT_MS ?? 20 * 60 * 1000) } = {}) {
  const at = path => new URL(path, root);
  const stampFile = at("web/dist/build-stamp.json");
  const lockDirectory = at("web/dist/.build-lock/"), ownerFile = at("web/dist/.build-lock/owner");
  const recoveryDirectory = at("web/dist/.build-lock-recovery/"), recoveryOwner = at("web/dist/.build-lock-recovery/owner");
  const listed = (directory, keep) => existsSync(at(directory))
    ? readdirSync(at(directory)).filter(keep).sort().map(name => `${directory}${name}`) : [];
  // Each build's inputs: the kernel's include the Makefile, which holds its
  // flags; the runtime's include the generator, and this file, which lists
  // the modules it copies.
  const sources = {
    kernel: () => [...listed("kernel/src/", name => /\.[ch]$/.test(name)), ...listed("kernel/include/", name => name.endsWith(".h")),
      "wasm/cubical_bridge.c", "Makefile"],
    runtime: () => [...runtimeModules.map(name => `lib/cubical/${name}.mjs`), "tools/build-cubical-runtime.mjs", "tools/build-stamp.mjs"],
  };
  const outputs = {
    kernel: () => ["web/dist/cubical.mjs", "web/dist/cubical.wasm"],
    runtime: () => runtimeModules.map(name => `web/dist/cubical-runtime/${name}.mjs`),
  };
  const kinds = Object.keys(sources);
  const hashFiles = paths => hashOf(paths, path => readFileSync(at(path)));
  const readStamp = () => { try { return JSON.parse(readFileSync(stampFile, "utf8")); } catch { return {}; } };
  // Written whole, then renamed into place: a reader never sees half a stamp.
  const saveStamp = stamp => {
    mkdirSync(at("web/dist/"), { recursive: true });
    const temporary = at(`web/dist/build-stamp.json.${process.pid}`);
    writeFileSync(temporary, `${JSON.stringify(stamp, null, 2)}\n`);
    renameSync(temporary, stampFile);
  };
  const known = kind => { if (!sources[kind]) throw new Error(`Unknown build ${kind}: expected ${kinds.join(" or ")}.`); return kind; };

  const sourceHash = kind => hashFiles(sources[known(kind)]());
  // Before a build writes any output: until it is stamped again, it is stale.
  const invalidate = kind => { const stamp = readStamp(); delete stamp[known(kind)]; saveStamp(stamp); };
  const write = (kind, sourcesHash, configuration = null) => {
    const stamp = readStamp();
    stamp[known(kind)] = { sources: sourcesHash, ...(configuration === null ? {} : { configuration }),
      outputs: hashFiles(outputs[kind]()) };
    saveStamp(stamp);
  };
  // Why a build is stale, or null. The configuration is compared only when
  // given, by `make wasm`, which knows the compiler and flags it would use.
  const staleness = (kind, configuration = null) => {
    const entry = readStamp()[known(kind)];
    if (!entry) return `no ${kind} build is recorded`;
    if (entry.sources !== sourceHash(kind)) return `the ${kind} sources changed since it was built`;
    if (configuration !== null && entry.configuration !== configuration)
      return `the ${kind} was built with another compiler or other flags`;
    const missing = outputs[kind]().find(path => !existsSync(at(path)));
    if (missing) return `${missing} is missing`;
    if (entry.outputs !== hashFiles(outputs[kind]())) return `the ${kind} outputs changed since they were built`;
    return null;
  };
  const staleBuilds = (names = kinds) => names.map(kind => staleness(kind)).filter(Boolean);
  const assertFreshBuild = names => {
    const stale = staleBuilds(names);
    if (stale.length) throw new Error(`web/dist is stale: ${stale.join("; ")}. Run make wasm.`);
  };

  // One build of web/dist at a time. The lock is a directory, made atomically,
  // holding its owner's process id. A process started under the lock
  // (CUBIST_BUILD_LOCK, by `locked`) runs in it.
  const ownerOf = file => { try { return Number(readFileSync(file, "utf8")); } catch { return 0; } };
  // A lock whose owner has exited is taken over, one recoverer at a time.
  // Under a second lock, the recoverer reads the owner again and removes the
  // lock only if it is still the exited owner's: a recoverer that saw the
  // exited owner leaves a lock another has taken since. The second lock is
  // held only for that moment and is never taken over; should its owner exit
  // holding it, the builds stop and say what to remove. False when another
  // recovery is under way.
  const recoverLock = exited => {
    try {
      mkdirSync(recoveryDirectory);
      writeFileSync(recoveryOwner, String(process.pid));
    } catch (error) {
      if (error.code !== "EEXIST") throw error;
      const recoverer = ownerOf(recoveryOwner);
      if (recoverer && !alive(recoverer) && ownerOf(recoveryOwner) === recoverer)
        throw new Error("A build of web/dist exited while taking over an abandoned lock. If no build is running, "
          + "remove web/dist/.build-lock and web/dist/.build-lock-recovery.");
      return false;
    }
    try {
      if (ownerOf(ownerFile) === exited) rmSync(lockDirectory, { recursive: true, force: true });
      return true;
    } finally {
      rmSync(recoveryDirectory, { recursive: true, force: true });
    }
  };
  const acquire = (timeout = lockTimeout) => {
    mkdirSync(at("web/dist/"), { recursive: true });
    const started = Date.now();
    for (let reported = false; ;) {
      try {
        mkdirSync(lockDirectory);
        writeFileSync(ownerFile, String(process.pid));
        return;
      } catch (error) {
        if (error.code !== "EEXIST") throw error;
      }
      const owner = ownerOf(ownerFile);
      if (owner && !alive(owner) && recoverLock(owner)) continue;
      if (Date.now() - started > timeout)
        throw new Error("Timed out waiting for another build of web/dist to finish. If none is running, remove web/dist/.build-lock.");
      if (!reported) { process.stderr.write("Waiting for another build of web/dist to finish.\n"); reported = true; }
      sleep(200);
    }
  };
  const release = () => rmSync(lockDirectory, { recursive: true, force: true });
  const withLock = operation => {
    const holder = Number(process.env.CUBIST_BUILD_LOCK);
    if (holder && ownerOf(ownerFile) === holder) return operation();
    acquire();
    try { return operation(); } finally { release(); }
  };

  return { sources, outputs, sourceHash, invalidate, write, staleness, staleBuilds, assertFreshBuild, withLock, recoverLock };
}

export const { sources, outputs, sourceHash, invalidate, write, staleness, staleBuilds, assertFreshBuild, withLock } =
  buildStamp(new URL("../", import.meta.url));

// node tools/build-stamp.mjs
//   hash KIND                        the sources' hash, for a build to stamp
//   invalidate KIND                  before a build writes its outputs
//   write KIND HASH [-- COMPILER...] after it succeeds
//   check [KIND...]                  refuse a stale build
//   check-kernel -- COMPILER...      also compare the compiler and flags
//   locked -- COMMAND...             run a build under the lock
// Run as a command, by any path to this file: a check that silently did
// nothing would pass.
const invoked = () => { try { return realpathSync(process.argv[1]) === fileURLToPath(import.meta.url); } catch { return false; } };
if (invoked()) {
  const argv = process.argv.slice(2), separator = argv.indexOf("--");
  const [command, ...rest] = separator < 0 ? argv : argv.slice(0, separator);
  const after = separator < 0 ? [] : argv.slice(separator + 1);
  try {
    if (command === "hash" && rest.length === 1) process.stdout.write(`${sourceHash(rest[0])}\n`);
    else if (command === "invalidate" && rest.length === 1) invalidate(rest[0]);
    else if (command === "write" && rest.length === 2) write(rest[0], rest[1], after.length ? compilerConfiguration(after) : null);
    else if (command === "check" && !after.length) assertFreshBuild(rest.length ? rest : undefined);
    else if (command === "check-kernel" && after.length) {
      const reason = staleness("kernel", compilerConfiguration(after));
      if (reason) throw new Error(`web/dist is stale: ${reason}.`);
    } else if (command === "locked" && after.length) {
      const result = withLock(() => spawnSync(after[0], after.slice(1), { stdio: "inherit",
        env: { ...process.env, CUBIST_BUILD_LOCK: String(process.pid) } }));
      if (result.error) throw result.error;
      process.exitCode = result.status ?? 1;
    } else throw new Error("Usage: node tools/build-stamp.mjs hash|invalidate|write|check|check-kernel|locked (see the source).");
  } catch (error) {
    process.stderr.write(`${error.message}\n`);
    process.exitCode = 1;
  }
}
