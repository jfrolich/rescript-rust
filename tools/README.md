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
the module from, so it type-checks the file's project first, without writing
files, and fails when the project has an error.

Several files are type-checked together, once per package, and printed as a
JSON list of their documentation, in the order given:

```sh
rescript-tools doc src/A.res src/B.res > docs.json
```

### Reanalyze

```sh
rescript-tools reanalyze --help
```

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
