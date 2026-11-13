/**
 * Completion for an editor of the page. The answers come from the compiler
 * (src/complete.js), through `request(source, offset, explicit)`, which
 * resolves with `{from, options, validFor}` or null.
 */
import { autocompletion } from "@codemirror/autocomplete";

// Where a completion starts by itself: in a name, after `.`, `->`, `%`, `@`.
const TRIGGER = /(?:[A-Za-z_][A-Za-z0-9_']*|\.|->\s*|[%@])$/;

/** `keys: false` leaves the keys of the list to the editor that has it. */
export function completion(request, { keys = true } = {}) {
  const source = async (context) => {
    const line = context.state.doc.lineAt(context.pos);
    if (!context.explicit && !TRIGGER.test(context.state.sliceDoc(line.from, context.pos))) return null;
    const result = await request(context.state.doc.toString(), context.pos, context.explicit);
    if (context.aborted || !result) return null;
    return { from: result.from, options: result.options, validFor: new RegExp(result.validFor) };
  };
  return autocompletion({ override: [source], activateOnTypingDelay: 40, maxRenderedOptions: 120, defaultKeymap: keys });
}
