#!/usr/bin/env node

// @ts-check

import * as fs from "node:fs/promises";
import * as path from "node:path";
import process from "node:process";

const packageDir = process.cwd();
const packageJsonPath = path.join(packageDir, "package.json");

/** @type {{name?: string, os?: string[], publishConfig?: {executableFiles?: string[]}}} */
const packageJson = JSON.parse(await fs.readFile(packageJsonPath, "utf8"));
const executableFiles = packageJson.publishConfig?.executableFiles;

if (!Array.isArray(executableFiles) || executableFiles.length === 0) {
  fail(`${packageJson.name ?? packageDir} does not declare publishConfig.executableFiles`);
}

const isWindowsPackage = packageJson.os?.includes("win32") === true;
const errors = [];

for (const executableFile of executableFiles) {
  const absolutePath = path.resolve(packageDir, executableFile);
  const relativePath = path.relative(packageDir, absolutePath);

  if (relativePath.startsWith("..") || path.isAbsolute(relativePath)) {
    errors.push(`${executableFile} escapes the package directory`);
    continue;
  }

  let stat;
  try {
    stat = await fs.stat(absolutePath);
  } catch {
    errors.push(`${executableFile} is missing`);
    continue;
  }

  if (!stat.isFile()) {
    errors.push(`${executableFile} is not a file`);
    continue;
  }

  if (stat.size === 0) {
    errors.push(`${executableFile} is empty`);
  }

  if (!isWindowsPackage && (stat.mode & 0o111) === 0) {
    errors.push(`${executableFile} is not executable`);
  }
}

if (errors.length > 0) {
  fail(`Invalid platform package ${packageJson.name ?? packageDir}:\n${errors.map(error => `- ${error}`).join("\n")}`);
}

function fail(message) {
  console.error(message);
  process.exit(1);
}
