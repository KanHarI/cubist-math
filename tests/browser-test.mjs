// Own the server and browser once; individual scripts keep their scenarios,
// engines, viewports, timeouts and assertions.
import { spawn } from "node:child_process";
import { fileURLToPath } from "node:url";
import { chromium } from "playwright";
import { assertFreshBuild } from "../tools/build-stamp.mjs";

export async function browserTest(run, { base = null, site = false, engine = chromium } = {}) {
  let server, browser;
  try {
    if (!base) {
      if (!site) assertFreshBuild();
      const args = site
        ? ["-u", "-m", "http.server", "0", "--bind", "127.0.0.1", "--directory", "build/site"]
        : [fileURLToPath(new URL("../tools/serve.py", import.meta.url)), "--port", "0"];
      server = spawn("python3", args, { stdio: ["ignore", "pipe", "pipe"] });
      // Drain request logs so they cannot block the server during a long script.
      server.stderr.resume();
      base = await new Promise((resolve, reject) => {
        let output = "";
        const finish = (error, port) => {
          clearTimeout(timer);
          if (error) reject(error);
          else resolve(`http://127.0.0.1:${port}`);
        };
        const timer = setTimeout(() => finish(new Error("Test server did not start")), 10000);
        server.once("error", error => finish(error));
        server.once("exit", code => finish(new Error(`Test server exited: ${code}`)));
        server.stdout.on("data", data => {
          output += data;
          const match = output.match(site ? /port (\d+)/ : /127\.0\.0\.1:(\d+)\//);
          if (match) finish(null, match[1]);
        });
      });
    }
    browser = await engine.launch({ headless: true });
    await run({ browser, base });
  } finally {
    try { await browser?.close(); }
    finally { server?.kill(); }
  }
}
