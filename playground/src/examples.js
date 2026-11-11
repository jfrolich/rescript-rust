/**
 * The examples of the playground: the projects under `examples/`, listed in
 * `examples/index.json`. Each is a few files that are compiled in dependency
 * order and run.
 */
import index from "../examples/index.json";

const sources = import.meta.glob("../examples/*/*", { query: "?raw", import: "default", eager: true });

export const examples = index.map((example) => ({
  ...example,
  files: example.files.map((name) => ({
    name,
    source: sources[`../examples/${example.id}/${name}`],
  })),
}));
