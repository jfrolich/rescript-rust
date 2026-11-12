/**
 * A session of the read-eval-print loop as text, the way a terminal shows
 * it: `> ` before an input, `. ` before its other lines, and what the loop
 * answered below. docs/comptime/README.md shows the opening session of the
 * page like this, and scripts/smoke.mjs checks that it is what the loop says.
 */

/** The modules a session starts with: every file of the examples but their programs. */
export function sessionLibraries(examples) {
  const seen = new Set();
  const libraries = [];
  for (const example of examples) {
    for (const file of example.files) {
      if (file.name === "Main.res" || seen.has(file.name)) continue;
      seen.add(file.name);
      libraries.push(file);
    }
  }
  return libraries;
}

export function transcriptOf(entries) {
  return entries
    .map((entry) => {
      const input = entry.input
        .split("\n")
        .map((line, index) => `${index === 0 ? ">" : "."} ${line}`.trimEnd())
        .join("\n");
      const output = entry.output.map((line) => line.text).join("\n");
      return output ? `${input}\n${output}` : input;
    })
    .join("\n\n");
}

/** Evaluate `inputs` in a new session of `engine`. */
export async function runSession(engine, libraries, inputs) {
  const started = engine.replStart(libraries);
  if (started.problems.length > 0) {
    throw new Error(started.problems.map((problem) => `${problem.file}:\n${problem.message}`).join("\n\n"));
  }
  const entries = [];
  for (const input of inputs) {
    const result = await engine.replEval(input);
    if (result.crashed) throw new Error(result.crashed);
    entries.push({
      input,
      output: result.output,
      expanded: result.expanded ?? null,
      javascript: result.javascript ?? null,
    });
  }
  return entries;
}
