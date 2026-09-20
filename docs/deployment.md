# Website deployment

The public website is **https://thth.kanhar.art/** and its source is
**https://github.com/KanHarI/thth-c**.

The `Publish website` GitHub Action rebuilds and publishes GitHub Pages on
pushes to `main`. It also supports manual runs from the Actions tab. Pull
requests run the existing CI but do not publish the website.

The build installs Node.js 24 and Emscripten 6.0.9, compiles the C kernel to
WebAssembly, runs the mathematical test suite, and checks the actual static
artifact in Chromium before publication. Failed checks leave the prior website
in place. Publication uses GitHub's short-lived deployment identity, without
deployment secrets stored in this repository.

`npm run build:site` creates `build/site/` from `web/` and `docs/`. The build
versions module imports, worker URLs, CSS and the WASM loader using a content
hash. It supplies the static `mathscript-version` response used by the editor's
update check. No local server, credentials, build tools, or private workspace
files are included in the published artifact.

To check the same artifact locally:

```sh
npm run build:site
npm run test:site
python3 -m http.server 8089 --directory build/site
```

To check a deployed site, run `npm run test:site -- https://thth.kanhar.art/`.
The smoke test opens the landing page, Euclid, the F₄ Galois correspondence, and
the kernel workbench, checking the real worker and WASM checker.

## Domain

GitHub repository Settings → Pages uses **GitHub Actions** as the build source
and **thth.kanhar.art** as its custom domain. The DNS record at GoDaddy is:

| Type | Name | Value |
| --- | --- | --- |
| CNAME | `thth` | `kanhari.github.io` |

DNS points at GitHub Pages hosting, not at the Actions runner. GitHub provisions
the TLS certificate after DNS resolves correctly; HTTPS enforcement can then
be enabled. `web/CNAME` records the intended domain in the build artifact.

To restore an earlier version, revert the relevant source change on `main` and
push; the Action rebuilds and publishes that revision. Running the workflow
manually on `main` also republishes the current revision.
