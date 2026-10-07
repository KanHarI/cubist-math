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
def self_equal(n : Nat) : n =[Nat] n {
  exact refl(n);
}
```

Check it with:

```sh
node cli/repl.mjs check example.cubist
```

A successful check prints the declaration and kernel-step counts and exits with
status 0. Parse errors, missing imports, or unchecked declarations exit nonzero,
each printed on a line of its own with its code, as
`error E606 at line 2:3 (wrong): Type mismatch: …`; a warning prints as
`warning W703 at line 1:37 (copy): …`. Every code has an entry in the
[error messages](../../web/reference/errors.html) chapter of the language
reference, and `node tools/diagnostic-codes.mjs` checks that every message
in the sources has one.
There is no `axiom` declaration: a source file cannot add assumptions. Each
`evaluate` directive's result is printed after the counts.
A declaration with a universe variable `U < UU0` is checked once, for every
universe.

To import another custom source, put `helpers.cubist` beside `example.cubist`
and write `import helpers;`. No extension appears in an import statement, and
nested module directories are not supported. Each module resolves its imports
by where it lives:

- A file outside the two libraries and `cubist-tests/`, and each module beside it, imports from
  its own directory first, then from the rebuilt `library/`, then from the
  archived `archive/first-library/`. A local module can intentionally shadow a
  bundled module of the same name.
- A module of `library/` imports only from `library/`: the library is
  self-contained.
- A module of the archive imports from the archive, then from `library/`, where
  `nat` lives. An archive module of a name always comes before a
  library module of that name, so the archive's checks keep their modules.
- A module of `cubist-tests/`, the Cubist sources the test suite checks,
  imports from `cubist-tests/`, then from `library/`, then from the archive.
  Nothing else imports a test module. Check one by its path:
  `node cli/repl.mjs check cubist-tests/glue.cubist`.

A check holds one module per name. When two modules of one check would load a
name from different places, for example an archive module and a library module
that both import a name the library shadows, the check fails and names both
places. A REPL entry imports from `library/`, then from the archive, and also
sees the module checked before it.

A bare module name is found in `library/` first, then in the archive:

```sh
node cli/repl.mjs check euclid
npm test -- euclid
npm test -- example.cubist
```

The test runner resolves imports exactly as the CLI does, sibling modules
included. The rules are specified in `web/module-resolution.mjs`.

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

`inspect` shows context, expression, type, and the assumptions the declaration
uses, or `none`. The language
reference's [checking chapter](../../web/reference/checking.html#cli) shows
checked sessions. `assembly` lists the actual native
opcodes and operands. Use a qualified binding such as `example__self_equal`
when a short name is ambiguous. `beta` or `delta` reduces the first applicable
occurrence in the expression (or `type`); the native checker validates the
result. The browser workbench supports selecting a particular occurrence.

`export` saves replayable source and inspection metadata for the selected
original declaration. It does not save an interactive reduction history.
The CLI does not yet provide an import command for this JSON format.

## Try terms in the REPL

A line that is not a command is a REPL entry. The kernel checks each entry as a
small module that imports the entries before it; after `check`, entries also
see the checked module's names.

```text
import nat;          Imported nat.
use nat;             Selected nat.
let x := 7;          x : Nat
typeof x;            Nat
evaluate x;          7
x + 3 * 4            19
```

`let` and `def` define names, and any declaration of a file works. `use`
selects a notation for the entries after it, as at a file's top level, so
that numerals and operators mean the naturals'; after `check`, entries read
in the selections the checked file ends with. `typeof`
prints a type. `evaluate`, or a term alone, prints the normal form of a closed
term that uses no assumption; a term that uses one is refused with the chain
through which it enters. An entry continues on the next line while a bracket
is open, so a proof block is one entry. A rejected entry changes nothing.
Entries also work noninteractively:

```sh
node cli/repl.mjs "import nat; use nat; evaluate 2 + 3;"
```

The same REPL runs in the browser, on `repl.html`, under each proof in the
workspace, and at the bottom of the language reference's pages.

## Optimization controls

All three optimizations default on and affect performance, not proof authority:

```sh
node cli/repl.mjs --no-reuse-checks check example.cubist
node cli/repl.mjs --no-share-syntax --no-compact-paths check example.cubist
```

Use the corresponding flag without `no-` to re-enable it. Run focused checks
during development; reserve plain `npm test` for the final corpus regression.
