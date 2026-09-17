#!/usr/bin/env python3
"""Local workbench server: never reuse stale compiler/source modules."""
import argparse
import hashlib
import json
import re
from urllib.parse import parse_qs, quote, urlsplit
from http.server import SimpleHTTPRequestHandler, ThreadingHTTPServer
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent / "web"


class Handler(SimpleHTTPRequestHandler):
    def __init__(self, *args, **kwargs):
        super().__init__(*args, directory=str(ROOT), **kwargs)

    def end_headers(self):
        self.send_header("Cache-Control", "no-store")
        super().end_headers()

    def do_GET(self):
        if self.path.split("?")[0] == "/mathscript-version":
            paths = sorted((ROOT / "mathscript").glob("*.mjs"))
            paths += sorted((ROOT / "proofs").glob("*.proof"))
            paths += [ROOT / "language.mjs", ROOT / "dist/kernel.mjs", ROOT / "dist/kernel.wasm", Path(__file__)]
            digest = hashlib.sha256()
            for path in paths:
                digest.update(path.read_bytes())
            body = json.dumps({"version": digest.hexdigest()}).encode()
            self.send_response(200)
            self.send_header("Content-Type", "application/json")
            self.send_header("Content-Length", str(len(body)))
            self.end_headers()
            self.wfile.write(body)
            return
        request = urlsplit(self.path)
        version = parse_qs(request.query).get("version", [None])[0]
        if version and request.path.endswith(".mjs"):
            path = Path(self.translate_path(request.path)).resolve()
            if ROOT not in path.parents or not path.is_file():
                self.send_error(404)
                return
            text = path.read_text()
            # A module worker has its own import graph. Versioning only its entry
            # leaves imports such as language.mjs eligible for old HTTP caches.
            # Carry the version through every local static/dynamic module import.
            pattern = r"(?P<prefix>\bfrom\s*|\bimport\s*(?:\(\s*)?)(?P<quote>['\"])(?P<path>\.\.?/[^'\"?]+\.mjs)(?P=quote)"
            def version_import(match):
                q = match["quote"]
                return match["prefix"] + q + match["path"] + "?version=" + quote(version, safe="") + q
            body = re.sub(pattern, version_import, text).encode()
            self.send_response(200)
            self.send_header("Content-Type", "text/javascript")
            self.send_header("Content-Length", str(len(body)))
            self.end_headers()
            self.wfile.write(body)
            return
        # Ignore old conditional cache validators, including requests from a tab
        # opened before this no-store policy was installed.
        for header in ("If-Modified-Since", "If-None-Match"):
            if header in self.headers:
                del self.headers[header]
        super().do_GET()


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--port", type=int, default=8088)
    args = parser.parse_args()
    server = ThreadingHTTPServer(("127.0.0.1", args.port), Handler)
    print(f"MathScript: http://127.0.0.1:{server.server_address[1]}/proof.html", flush=True)
    server.serve_forever()
