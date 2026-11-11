/**
 * The examples of the page: the directories under `examples/`, listed in
 * `examples/index.json`. Each is a few TypeScript files and one ReScript
 * file that imports from them.
 */
import index from "../examples/index.json";

const sources = import.meta.glob("../examples/**/*", { query: "?raw", import: "default", eager: true });

export const examples = index.map((example) => ({
  ...example,
  files: example.files.map((name) => ({
    name,
    source: sources[`../examples/${example.id}/${name}`],
  })),
}));
