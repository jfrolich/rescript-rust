# ReScript Tools

## Install

The `rescript` package provides the `rescript-tools` executable:

```sh
npm install --save-dev rescript
```

## CLI Usage

```sh
rescript-tools --help
```

### Generate documentation

Print JSON:

```sh
rescript-tools doc src/EntryPointLibFile.res
```

Write JSON:

```sh
rescript-tools doc src/EntryPointLibFile.res > doc.json
```

`doc <file>` runs `rescript doc <file>`: builds write no `.cmt` files to read
the module from, so it checks the file's project first, without writing
files, and fails when the project has an error. The check reads the last
build's record and type-checks only what changed since, so run it after a
build. Items another module declares (those of an `include`) take another
check that compiles the modules they come through with source locations.

To document many files, pass them all to one `rescript doc --batch`
instead of running `doc` once per file:

```sh
rescript doc --batch src/A.res src/B.resi src/C.res > docs.json
```

It prints one JSON object with a field for each file, named by its path as
given and in that order, holding the JSON `doc` prints for that file:

```json
{
  "src/A.res": { "name": "A", "docstrings": [], "source": {}, "items": [] },
  "src/B.resi": { "name": "B", "docstrings": [], "source": {}, "items": [] }
}
```

The files of a project share its checks and are documented in parallel, so
each file adds only its own type-check: on a 3,700-module application, 287
files take 0.7 s, against 14 s with one `doc` per file. The command fails
and prints no docs when any file cannot be documented (a missing file, a
project that does not build). A file given twice is documented once.

### Reanalyze

```sh
rescript-tools reanalyze --help
```

`reanalyze` type-checks the project it runs in, without writing files, and
reports dead code (`-dce`), exceptions that are thrown but not annotated
(`-exception`) and possible infinite loops (`-termination`); `-config` reads
which of them to run from the `reanalyze` section of `rescript.json`.

## Contributor documentation

- [Migration framework capabilities](src/migrate.md)
- [Reanalyze architecture](../analysis/reanalyze/README.md)

## Decode JSON

`RescriptTools.Docgen` in the standard library (`@rescript/runtime`)
decodes the JSON that `rescript-tools doc` prints:

```rescript
// Read JSON file and parse with `JSON.parseOrThrow`
json->RescriptTools.Docgen.decodeFromJson
```
