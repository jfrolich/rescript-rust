#!/usr/bin/env node

// @ts-check

// Publishes a nightly of the workspace packages under another npm scope
// (.github/workflows/nightly.yml).
//
// Each package gets a scoped name: `rescript` becomes `<scope>/rescript`,
// `@rescript/runtime` becomes `<scope>/rescript-runtime`, and so on. The
// compiler package depends on the others through npm aliases
// (`"@rescript/runtime": "npm:<scope>/rescript-runtime@<version>"`), so they
// are installed under their usual names. The launchers find the platform
// binaries and the runtime by those names. Generated JavaScript imports the
// runtime as `@rescript/runtime`, so projects install it under an alias as
// well:
//
//   npm i rescript@npm:<scope>/rescript@nightly \
//     @rescript/runtime@npm:<scope>/rescript-runtime@nightly
//
// @rescript/belt is not published here: the build system identifies a package
// by its package.json name, so a scoped copy installed as @rescript/belt does
// not build. Belt ships only its sources, which the nightly compiles, so
// projects use the @rescript/belt release from npm, whose peer ranges
// (^13.0.0-alpha.7) admit the nightly versions:
//
//   npm i @rescript/belt@13.0.0-alpha.7
//
// The version appends `nightly.<commit time>.g<short sha>` to the package
// version, so nightlies sort in commit order and before the next release.
// The command rewrites the package.json files in place: run it on a throwaway
// checkout, after the platform binaries are in place. A platform package whose
// binaries are missing is left out of the compiler's optional dependencies.
// The runtime is published from its sources and the JavaScript checked in
// with them: the build system compiles it from source.
//
// The workflow publishes with npm trusted publishing (OIDC), without a token.
// npm can only trust a workflow for a package that exists, so each package is
// created once by hand, as a placeholder, with `--bootstrap` (see below).
//
// Usage: node scripts/nightlyPackages.js --scope @tellahq [--tag nightly]
//          [--repository owner/name] [--dry-run]
//
//        node scripts/nightlyPackages.js --scope @tellahq --bootstrap
//          --repository owner/name [--dry-run]
//
// `--bootstrap` runs on a maintainer's machine, logged in to npm (`npm login`)
// with two-factor authentication. For each package that does not exist yet it
// publishes `0.0.0-placeholder`; then it makes .github/workflows/nightly.yml in
// the repository the package's trusted publisher (`npm trust github`, npm
// 11.10 or later). npm asks for a second factor on the first request.

import * as child_process from "node:child_process";
import * as fs from "node:fs";
import * as os from "node:os";
import * as path from "node:path";
import { parseArgs } from "node:util";
import semver from "semver";

const root = path.resolve(import.meta.dirname, "..");
const platforms = ["darwin-arm64", "linux-arm64", "linux-x64", "win32-x64"];

const { values: args } = parseArgs({
  options: {
    scope: { type: "string" },
    tag: { type: "string", default: "nightly" },
    repository: { type: "string", default: process.env.GITHUB_REPOSITORY },
    "dry-run": { type: "boolean", default: false },
    bootstrap: { type: "boolean", default: false },
  },
});

if (!args.scope?.startsWith("@") || args.scope.includes("/")) {
  fail("--scope must be an npm scope such as @tellahq");
}
const scope = args.scope;
const tag = /** @type {string} */ (args.tag);
const dryRun = args["dry-run"] === true;

/** @param {string} dir */
const manifestPath = dir => path.join(root, dir, "package.json");

/** @param {string} dir @returns {Record<string, any>} */
const readManifest = dir =>
  JSON.parse(fs.readFileSync(manifestPath(dir), "utf8"));

/** @param {string} dir @param {Record<string, any>} manifest */
const writeManifest = (dir, manifest) =>
  fs.writeFileSync(manifestPath(dir), `${JSON.stringify(manifest, null, 2)}\n`);

/** @param {string} name */
const scopedName = name =>
  name === "rescript"
    ? `${scope}/rescript`
    : `${scope}/${name.replace(/^@rescript\//, "rescript-")}`;

// Every package the workflow may publish, under its scoped name.
const publishedNames = [
  "rescript",
  "@rescript/runtime",
  ...platforms.map(platform => `@rescript/${platform}`),
].map(scopedName);

if (args.bootstrap) {
  bootstrap();
  process.exit(0);
}

const version = nightlyVersion(readManifest(".").version);
/** @param {string} name */
const alias = name => `npm:${scopedName(name)}@${version}`;

const builtPlatforms = platforms.filter(platform => {
  const dir = `packages/@rescript/${platform}`;
  const executables = readManifest(dir).publishConfig.executableFiles;
  return executables.every((/** @type {string} */ file) =>
    fs.existsSync(path.join(root, dir, file)),
  );
});
const missingPlatforms = platforms.filter(p => !builtPlatforms.includes(p));

if (builtPlatforms.length === 0) {
  fail("No platform package has its binaries in bin/.");
}

// Dependencies first, so that the compiler package never refers to a version
// that is not on the registry yet.
const packages = [
  ...builtPlatforms.map(platform => ({
    dir: `packages/@rescript/${platform}`,
    /** @param {Record<string, any>} manifest */
    rewrite: manifest => manifest,
  })),
  {
    dir: "packages/@rescript/runtime",
    /** @param {Record<string, any>} manifest */
    rewrite: manifest => {
      delete manifest.devDependencies;
      delete manifest.scripts;
      return manifest;
    },
  },
  {
    dir: ".",
    /** @param {Record<string, any>} manifest */
    rewrite: manifest => {
      manifest.dependencies = {
        "@rescript/runtime": alias("@rescript/runtime"),
      };
      manifest.optionalDependencies = Object.fromEntries(
        builtPlatforms.map(platform => [
          `@rescript/${platform}`,
          alias(`@rescript/${platform}`),
        ]),
      );
      delete manifest.devDependencies;
      delete manifest.scripts;
      delete manifest.workspaces;
      delete manifest.packageManager;
      return manifest;
    },
  },
];

const current = registryVersion(`${scope}/rescript@${tag}`);
// Runs can finish out of order; an older commit must not take the tag back.
if (current !== undefined && semver.gte(current, version)) {
  console.log(
    `${scope}/rescript@${tag} is already ${current}, not older than ${version}.`,
  );
  if (!dryRun) {
    process.exit(0);
  }
}

// Trusted publishing needs npm 11.5.1 or later; an older npm would fall back to
// the (absent) token and fail with a less helpful error.
const publishWithOidc = process.env.GITHUB_ACTIONS === "true" && !dryRun;
if (publishWithOidc) {
  const npmVersion = output("npm", ["--version"]);
  if (!semver.gte(npmVersion, "11.5.1")) {
    fail(`npm ${npmVersion} cannot use trusted publishing; it needs 11.5.1.`);
  }
}

for (const { dir, rewrite } of packages) {
  const manifest = rewrite(readManifest(dir));
  manifest.name = scopedName(manifest.name);
  manifest.version = version;
  if (args.repository !== undefined) {
    // npm checks provenance against the repository the workflow ran in.
    manifest.repository = {
      type: "git",
      url: `git+https://github.com/${args.repository}.git`,
    };
    manifest.bugs = `https://github.com/${args.repository}/issues`;
  }
  writeManifest(dir, manifest);

  if (registryVersion(`${manifest.name}@${version}`) === version) {
    console.log(`${manifest.name}@${version} is already published.`);
    continue;
  }
  // The manifests ask for provenance, which npm can only attest in CI.
  const provenance = publishWithOidc;
  const publishArgs = [
    "publish",
    "--access",
    "public",
    "--tag",
    tag,
    `--provenance=${provenance}`,
  ];
  if (dryRun) {
    publishArgs.push("--dry-run");
  }
  console.log(`Publishing ${manifest.name}@${version}`);
  run(
    "npm",
    publishArgs,
    path.join(root, dir),
    publishWithOidc
      ? `Is ${manifest.name} set up for trusted publishing (--bootstrap)?`
      : undefined,
  );
}

writeSummary();

/**
 * Creates the packages that do not exist yet and makes the nightly workflow
 * their trusted publisher.
 */
function bootstrap() {
  const repository = args.repository;
  if (repository === undefined || !/^[^/]+\/[^/]+$/.test(repository)) {
    fail("--bootstrap needs --repository owner/name, where nightly.yml runs.");
  }
  const npmVersion = output("npm", ["--version"]);
  if (!semver.gte(npmVersion, "11.10.0")) {
    fail(`npm ${npmVersion} has no \`npm trust\`; it needs 11.10.0.`);
  }
  const placeholders = fs.mkdtempSync(
    path.join(os.tmpdir(), "nightly-bootstrap-"),
  );
  const dryRunArgs = dryRun ? ["--dry-run"] : [];
  /** @type {string[]} */
  const untrusted = [];
  for (const name of publishedNames) {
    if (registryVersion(name) !== undefined) {
      console.log(`${name} exists.`);
    } else {
      // npm also points `latest` at the first version of a package.
      const dir = path.join(placeholders, name.replace("/", "+"));
      fs.mkdirSync(dir);
      const manifest = {
        name,
        version: "0.0.0-placeholder",
        description: `Placeholder; install ${name}@nightly.`,
        license: readManifest(".").license,
        repository: {
          type: "git",
          url: `git+https://github.com/${repository}.git`,
        },
      };
      fs.writeFileSync(
        path.join(dir, "package.json"),
        `${JSON.stringify(manifest, null, 2)}\n`,
      );
      fs.writeFileSync(
        path.join(dir, "README.md"),
        `# ${name}\n\nThis version is empty. Nightly builds are published as \`${name}@nightly\`.\n`,
      );
      console.log(`Creating ${name}`);
      run(
        "npm",
        [
          "publish",
          "--access",
          "public",
          "--tag",
          "placeholder",
          "--provenance=false",
          ...dryRunArgs,
        ],
        dir,
      );
    }
    console.log(
      `Trusting ${repository} .github/workflows/nightly.yml for ${name}`,
    );
    const trust = child_process.spawnSync(
      "npm",
      [
        "trust",
        "github",
        name,
        "--file",
        "nightly.yml",
        "--repository",
        repository,
        "--allow-publish",
        "--yes",
        ...dryRunArgs,
      ],
      { stdio: "inherit", shell: process.platform === "win32" },
    );
    if (trust.status !== 0) {
      untrusted.push(name);
    }
    // npm asks for a pause between trust requests.
    Atomics.wait(new Int32Array(new SharedArrayBuffer(4)), 0, 0, 2000);
  }
  fs.rmSync(placeholders, { recursive: true, force: true });
  if (untrusted.length > 0) {
    fail(
      `npm trust failed for ${untrusted.join(", ")}. A package that already trusts a publisher must have it revoked first: npm trust list <package>, then npm trust revoke --id <id> <package>.`,
    );
  }
}

/**
 * @param {string} base
 * @returns {string}
 */
function nightlyVersion(base) {
  const parsed = semver.parse(base);
  if (parsed === null) {
    fail(`Invalid package version ${base}`);
  }
  // Committer time in UTC; numeric identifiers may not start with 0, and
  // this one starts with the year.
  const time = git(
    "show",
    "-s",
    "--date=format-local:%Y%m%d%H%M%S",
    "--format=%cd",
    "HEAD",
  );
  const sha = git("rev-parse", "--short=9", "HEAD");
  const suffix = `nightly.${time}.g${sha}`;
  return parsed.prerelease.length > 0
    ? `${base}.${suffix}`
    : `${base}-${suffix}`;
}

/**
 * The version a spec resolves to on the registry, if any.
 *
 * @param {string} spec
 * @returns {string | undefined}
 */
function registryVersion(spec) {
  const result = child_process.spawnSync(
    "npm",
    ["view", spec, "version", "--json"],
    { cwd: root, encoding: "utf8", shell: process.platform === "win32" },
  );
  if (result.status !== 0) {
    // E404: the package or the version does not exist yet.
    if (/E404|is not in this registry/.test(result.stderr + result.stdout)) {
      return undefined;
    }
    fail(`npm view ${spec} failed:\n${result.stderr}`);
  }
  const output = result.stdout.trim();
  if (output === "") {
    return undefined;
  }
  const parsed = JSON.parse(output);
  return Array.isArray(parsed) ? parsed.at(-1) : parsed;
}

function writeSummary() {
  const lines = [
    `${dryRun ? "Dry run of" : "Published"} \`${scope}/rescript@${version}\` as \`${tag}\`.`,
    "",
    "```sh",
    `npm i -D rescript@npm:${scope}/rescript@${version} @rescript/runtime@npm:${scope}/rescript-runtime@${version}`,
    "```",
    "",
    `Platforms: ${builtPlatforms.join(", ")}`,
  ];
  if (missingPlatforms.length > 0) {
    lines.push(`Not built, so not published: ${missingPlatforms.join(", ")}`);
  }
  const text = `${lines.join("\n")}\n`;
  console.log(text);
  if (process.env.GITHUB_STEP_SUMMARY) {
    fs.appendFileSync(process.env.GITHUB_STEP_SUMMARY, text);
  }
}

/** @param {string[]} gitArgs */
function git(...gitArgs) {
  return child_process
    .execFileSync("git", gitArgs, {
      cwd: root,
      encoding: "utf8",
      env: { ...process.env, TZ: "UTC" },
    })
    .trim();
}

/**
 * @param {string} command
 * @param {string[]} commandArgs
 * @param {string} cwd
 * @param {string} [hint] added to the error when the command fails
 */
function run(command, commandArgs, cwd, hint) {
  const result = child_process.spawnSync(command, commandArgs, {
    cwd,
    stdio: "inherit",
    shell: process.platform === "win32",
  });
  if (result.status !== 0) {
    const message = `${command} ${commandArgs.join(" ")} failed in ${cwd}`;
    fail(hint === undefined ? message : `${message}\n${hint}`);
  }
}

/**
 * @param {string} command
 * @param {string[]} commandArgs
 */
function output(command, commandArgs) {
  return child_process
    .execFileSync(command, commandArgs, {
      cwd: root,
      encoding: "utf8",
      shell: process.platform === "win32",
    })
    .trim();
}

/**
 * @param {string} message
 * @returns {never}
 */
function fail(message) {
  console.error(message);
  process.exit(1);
}
