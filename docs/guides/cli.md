# Cubist command-line guide

The CLI is a small source checker and inspection shell, not yet an editor or
language server. It uses the same C/WASM kernel as the website. Custom source
checking, local imports, inspection, native assembly, and single reductions
are supported. There is no completion, multiline source editor, or package manager.

## Setup

Install Node.js 24+, a C compiler, Make, and Emscripten, then run:

```sh
npm ci
make wasm
node cli/repl.mjs --help
```

## Check your own proof

Save this as `example.cubist`:

```text
// Every natural number equals itself.
theorem self_equal(n : Nat) : n =[Nat] n {
  exact refl(n);
}
```

Check it with:

```sh
node cli/repl.mjs check example.cubist
```

A successful check prints the declaration and kernel-step counts and exits with
status 0. Parse errors, missing imports, or unchecked declarations exit nonzero.
An explicitly declared axiom is a permitted assumption, not a proof of that axiom.
Universe templates are checked through their concrete instantiations.

To import another custom source, put `helpers.cubist` beside `example.cubist`
and write `import helpers;`. Imports resolve beside the root file first, then
in the bundled `web/proofs/` library. This same root directory is used for
transitive imports; nested module directories are not supported. No extension
appears in an import statement. A local module can intentionally shadow a
bundled module of the same name.

A bare module name selects the bundled library:

```sh
node cli/repl.mjs check euclid
npm test -- example.cubist
```

The selected test runner checks custom imports from the bundled library; use
the CLI for custom sources with sibling modules.

## Explore a checked proof

Start `node cli/repl.mjs`, then enter one command per line:

```text
check example.cubist
inspect self_equal
assembly self_equal
beta expression
export self_equal.json
quit
```

`inspect` shows context, expression, and type. `assembly` lists the actual native
opcodes and operands. Use a qualified binding such as `example__self_equal`
when a short name is ambiguous. `beta` or `delta` reduces the first applicable
occurrence in the expression (or `type`); the native checker validates the
result. The browser workbench supports choosing a particular occurrence.

`export` saves replayable source and inspection metadata for the selected
original declaration. It does not save an interactive reduction history.
The CLI does not yet provide an import command for this JSON format.

## Optimization controls

All three optimizations default on and affect performance, not proof authority:

```sh
node cli/repl.mjs --no-reuse-checks check example.cubist
node cli/repl.mjs --no-share-syntax --no-compact-paths check example.cubist
```

Use the corresponding flag without `no-` to re-enable it. Run focused checks
during development; reserve plain `npm test` for the final corpus regression.
