/**
 * The examples of the pages: the files under `examples/`, listed in
 * `examples/index.json`. Each is one ReScript file.
 */
import index from "../examples/index.json";

const sources = import.meta.glob("../examples/*.res", { query: "?raw", import: "default", eager: true });

export const examples = index.map((example) => ({
  ...example,
  name: "Demo.res",
  source: sources[`../examples/${example.id}.res`],
}));
