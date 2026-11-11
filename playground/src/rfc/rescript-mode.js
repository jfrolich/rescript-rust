/** ReScript for CodeMirror: a tokenizer, used for editing and for static highlighting. */
import { StreamLanguage } from "@codemirror/language";

const keywords = new Set([
  "and", "as", "assert", "async", "await", "catch", "constraint", "downto", "else", "exception",
  "external", "for", "if", "in", "include", "lazy", "let", "module", "mutable", "of", "open",
  "private", "rec", "switch", "to", "try", "type", "when", "while", "with",
]);
const atoms = new Set(["true", "false"]);

function token(stream, state) {
  if (state.comment > 0) {
    while (!stream.eol()) {
      if (stream.match("*/")) {
        state.comment -= 1;
        if (state.comment === 0) break;
      } else if (stream.match("/*")) {
        state.comment += 1;
      } else {
        stream.next();
      }
    }
    return "comment";
  }
  if (state.template) {
    while (!stream.eol()) {
      const ch = stream.next();
      if (ch === "\\") stream.next();
      else if (ch === "`") {
        state.template = false;
        break;
      }
    }
    return "string";
  }
  if (stream.eatSpace()) return null;
  if (stream.match("//")) {
    stream.skipToEnd();
    return "comment";
  }
  if (stream.match("/*")) {
    state.comment = 1;
    return "comment";
  }
  if (stream.match(/^"(?:[^"\\]|\\.)*"?/)) return "string";
  if (stream.match(/^'(?:[^'\\]|\\.)'/)) return "string";
  if (stream.match("`")) {
    state.template = true;
    return "string";
  }
  if (stream.match(/^\d[\d_]*(?:\.[\d_]*)?(?:[eE][+-]?\d+)?n?/)) return "number";
  // A hole in a quote.
  if (stream.match("${")) return "atom";
  // Extensions and attributes: %code, %Json.encode, @macro, @@directive.
  if (stream.match(/^%%?[A-Za-z_][\w.]*/)) return "meta";
  if (stream.match(/^@@?[A-Za-z_][\w.]*/)) return "meta";
  if (stream.match(/^~[a-z_]\w*/)) return "propertyName";
  if (stream.match(/^#[A-Za-z_]\w*/)) return "atom";
  if (stream.match(/^'[a-z_]\w*/)) return "typeName";
  if (stream.match(/^[A-Z][\w$]*/)) return "typeName";
  if (stream.match(/^[a-z_][\w$']*/)) {
    const word = stream.current();
    if (keywords.has(word)) return "keyword";
    if (atoms.has(word)) return "atom";
    return "variableName";
  }
  if (stream.match(/^(?:=>|->|\.\.\.|===|!==|==|!=|<=|>=|&&|\|\||\+\+|\+\.|-\.|\*\.|\/\.|:=|[-+*/=<>|!?:])/)) {
    return "operator";
  }
  stream.next();
  return "punctuation";
}

export const rescript = StreamLanguage.define({
  name: "rescript",
  startState: () => ({ comment: 0, template: false }),
  token,
  languageData: {
    commentTokens: { line: "//", block: { open: "/*", close: "*/" } },
    closeBrackets: { brackets: ["(", "[", "{", '"', "`"] },
    indentOnInput: /^\s*[})\]]$/,
  },
});
