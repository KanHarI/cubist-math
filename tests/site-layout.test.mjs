import test from "node:test";
import assert from "node:assert/strict";
import { spawnSync } from "node:child_process";
import { copyFileSync, mkdirSync, mkdtempSync, readFileSync, realpathSync, renameSync, rmSync, writeFileSync } from "node:fs";
import { tmpdir } from "node:os";
import { dirname, join } from "node:path";

function fixture(t) {
  const root = realpathSync(mkdtempSync(join(tmpdir(), "cubist-site-")));
  t.after(() => rmSync(root, { recursive: true, force: true }));
  const put = (name, text) => {
    mkdirSync(dirname(join(root, name)), { recursive: true });
    writeFileSync(join(root, name), text);
  };
  for (const name of ["site-layout.json", "serve.py", "build-site.mjs"]) {
    mkdirSync(join(root, "tools"), { recursive: true });
    copyFileSync(new URL(`../tools/${name}`, import.meta.url), join(root, "tools", name));
  }
  put("tools/build-stamp.mjs", "export const assertFreshBuild = () => {};\n");
  for (const name of ["web/index.html", "archive/first-library/example.cubist", "library/example.cubist",
    "cubist-tests/example.cubist", "docs/example.cubist"]) put(name, name);
  const server = (...urls) => {
    const result = spawnSync("python3", ["-B", "-c", `
import json, runpy, sys
site = runpy.run_path(sys.argv[1])
handler = site["Handler"].__new__(site["Handler"])
handler.directory = str(site["ROOT"])
print(json.dumps({"version": site["site_version"](),
                  "paths": [handler.translate_path(url) for url in sys.argv[2:]]}))
`, join(root, "tools/serve.py"), ...urls], { encoding: "utf8" });
    assert.equal(result.status, 0, result.stderr);
    return JSON.parse(result.stdout);
  };
  const build = () => {
    const result = spawnSync(process.execPath, [join(root, "tools/build-site.mjs")], { encoding: "utf8" });
    assert.equal(result.status, 0, result.stderr);
  };
  return { root, put, server, build };
}

test("development and publication use the same public roots", t => {
  const { root, put, server, build } = fixture(t);
  const urls = ["/index.html", "/archive/first-library/example.cubist", "/library/example.cubist",
    "/cubist-tests/example.cubist", "/docs/example.cubist"];
  build();
  const { paths } = server(...urls);
  for (const [i, url] of urls.entries())
    assert.equal(readFileSync(join(root, "build/site", url), "utf8"), readFileSync(paths[i], "utf8"), url);
  assert.equal(server("/docs/../private.txt").paths[0], join(root, "docs/__outside__"));

  // Changing a mount in the shared layout affects both consumers.
  const layout = JSON.parse(readFileSync(join(root, "tools/site-layout.json")));
  delete layout.docs;
  layout.manual = "docs";
  const before = server().version;
  put("tools/site-layout.json", JSON.stringify(layout));
  build();
  assert.notEqual(server().version, before);
  assert.equal(server("/manual/example.cubist").paths[0], join(root, "docs/example.cubist"));
  assert.equal(readFileSync(join(root, "build/site/manual/example.cubist"), "utf8"), "docs/example.cubist");
});

test("development versions cover worker dependencies, source files, renames and removals", t => {
  const { root, put, server } = fixture(t);
  const inputs = ["diagnostics", "module-listing", "module-resolution", "repl-session", "generated-cubist",
    "contextual-session", "cubist/parser", "translator/arguments", "new/dependency"].map(name => `web/${name}.mjs`);
  inputs.push("web/cubist-files.json", "web/dist/cubical.wasm", "library/example.cubist",
    "archive/first-library/example.cubist", "cubist-tests/example.cubist", "docs/example.cubist");
  for (const input of inputs) put(input, "original");
  const original = server().version;
  assert.equal(server().version, original);
  for (const input of inputs) {
    put(input, "changed");
    assert.notEqual(server().version, original, input);
    put(input, "original");
  }
  put("private.txt", "not published");
  assert.equal(server().version, original, "unpublished files do not restart workers");
  renameSync(join(root, "web/new/dependency.mjs"), join(root, "web/new/renamed.mjs"));
  const renamed = server().version;
  assert.notEqual(renamed, original, "same bytes at a different path");
  rmSync(join(root, "web/new/renamed.mjs"));
  assert.notEqual(server().version, renamed, "a removed dependency");
});
