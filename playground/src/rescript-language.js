/**
 * Monaco Monarch tokenizer for ReScript.
 * Derived from the official rescript-vscode TextMate grammar.
 */

export const languageId = "rescript";

export const languageConfig = {
  comments: {
    lineComment: "//",
    blockComment: ["/*", "*/"],
  },
  brackets: [
    ["{", "}"],
    ["[", "]"],
    ["(", ")"],
  ],
  autoClosingPairs: [
    { open: "{", close: "}" },
    { open: "[", close: "]" },
    { open: "(", close: ")" },
    { open: '"', close: '"', notIn: ["string"] },
    { open: "`", close: "`", notIn: ["string"] },
    { open: "/*", close: " */", notIn: ["string"] },
  ],
  surroundingPairs: [
    { open: "{", close: "}" },
    { open: "[", close: "]" },
    { open: "(", close: ")" },
    { open: '"', close: '"' },
    { open: "'", close: "'" },
    { open: "`", close: "`" },
  ],
  folding: {
    markers: {
      start: /^\s*\/\*/,
      end: /^\s*\*\//,
    },
  },
  indentationRules: {
    increaseIndentPattern: /(\{[^}]*|\([^)]*|\[[^\]]*)$/,
    decreaseIndentPattern: /^\s*[}\])]|^\s*\|/,
  },
};

export const monarchTokens = {
  defaultToken: "",
  tokenPostfix: ".rescript",

  keywords: [
    "and", "as", "assert", "async", "await", "catch", "constraint",
    "downto", "else", "exception", "external", "for", "if", "in",
    "lazy", "mutable", "rec", "switch", "to", "try", "when",
    "while", "with", "private",
  ],

  typeKeywords: [
    "include", "let", "module", "of", "open", "type",
  ],

  constants: ["true", "false"],

  operators: [
    "->", "||", "&&", "++", "**",
    "+.", "+", "-.", "-", "*.", "*", "/.", "/",
    "...", "..", "===", "==", "^", ":=", "!",
    ">=", "<=", "=", "=>", "|>",
  ],

  symbols: /[=><!~?:&|+\-*\/\^%]+/,
  escapes: /\\(?:[abfnrtv\\"']|x[0-9A-Fa-f]{1,4}|u[0-9A-Fa-f]{4}|U[0-9A-Fa-f]{8})/,

  tokenizer: {
    root: [
      // FFI blocks: %raw(`...`) and %%raw(`...`)
      [/(%|%%)(raw|ffi)/, { token: "annotation", next: "@ffiStart" }],

      // Attributes: @foo, @@foo, %foo, %%foo
      [/(%%?|@@?)([A-Za-z_][A-Za-z0-9_.]*)/, ["annotation", "annotation"]],

      // Line comments
      [/\/\/.*$/, "comment"],

      // Block comments (nestable)
      [/\/\*/, "comment", "@comment"],

      // Strings
      [/"/, "string", "@string"],

      // Template strings
      [/([a-z_][0-9a-zA-Z_]*)?`/, "string.template", "@template"],

      // Characters
      [/'[^\\']'/, "string.character"],
      [/'\\.'/, "string.character"],

      // Type parameters
      [/'[A-Za-z][A-Za-z0-9_]*/, "type.identifier"],

      // Numbers
      [/0[xX][0-9a-fA-F_]+[Lln]?/, "number.hex"],
      [/0[oO][0-7_]+[Lln]?/, "number.octal"],
      [/0[bB][01_]+[Lln]?/, "number.binary"],
      [/[0-9][0-9_]*(\.[0-9_]+)?([eE][-+]?[0-9_]+)?[Lln]?/, "number"],

      // JSX tags
      [/<\/>|<>/, "delimiter.html"],
      [/<\/([A-Z_][0-9a-zA-Z_]*)/, ["delimiter.html", { token: "type.identifier", next: "@pop" }]],
      [/<\/([a-z_][0-9a-zA-Z_]*)/, ["delimiter.html", { token: "tag", next: "@pop" }]],
      [/<([A-Z_][0-9a-zA-Z_]*)/, ["delimiter.html", { token: "type.identifier" }]],
      [/\/>/, "delimiter.html"],

      // Module access: Module.something
      [/[A-Z_][0-9a-zA-Z_]*(?=\.)/, "type.identifier"],

      // Constructors
      [/#[a-zA-Z][0-9a-zA-Z_]*/, "variable.other.enummember"],
      [/#\.\.\./, "variable.other.enummember"],
      [/#/, "variable.other.enummember"],

      // Identifiers and keywords
      [/[a-z_][0-9a-zA-Z_]*/, {
        cases: {
          "@keywords": "keyword",
          "@typeKeywords": "keyword",
          "@constants": "constant.language",
          "list|dict": "keyword",
          "@default": "identifier",
        },
      }],

      // Capitalized identifiers (constructors, modules)
      [/[A-Z_][0-9a-zA-Z_]*/, "variable.other.enummember"],

      // Arrow function
      [/=>/, "keyword.operator.arrow"],

      // Operators
      [/->/, "keyword.operator"],
      [/\|>/, "invalid.deprecated"],
      [/\.\.\./, "keyword.operator"],
      [/\.\./, "keyword.operator"],
      [/===|==/, "keyword.operator"],
      [/\|\||&&/, "keyword.operator"],
      [/\+\+|\*\*/, "keyword.operator"],
      [/[+\-*\/]\./, "keyword.operator"],
      [/\^|:=|!/, "keyword.operator"],
      [/>=|<=|=/, "keyword.operator"],

      // Delimiters and punctuation
      [/[{}()\[\]]/, "@brackets"],
      [/[;,.:?|~]/, "delimiter"],

      // Whitespace
      [/\s+/, "white"],
    ],

    comment: [
      [/\/\*/, "comment", "@push"],
      [/\*\//, "comment", "@pop"],
      [/./, "comment"],
    ],

    string: [
      [/@escapes/, "string.escape"],
      [/[^\\"]+/, "string"],
      [/"/, "string", "@pop"],
    ],

    template: [
      [/\$\{/, { token: "delimiter.bracket", next: "@templateExpr" }],
      [/@escapes/, "string.escape"],
      [/[^`\\$]+/, "string.template"],
      [/`/, "string.template", "@pop"],
    ],

    templateExpr: [
      [/\}/, { token: "delimiter.bracket", next: "@pop" }],
      { include: "root" },
    ],

    ffiStart: [
      [/\(\s*`/, { token: "string.template", next: "@ffiBody" }],
      [/./, { token: "", next: "@pop" }],
    ],

    ffiBody: [
      [/`\s*\)/, { token: "string.template", next: "@popall" }],
      [/./, "string.template"],
    ],
  },
};

/**
 * Register ReScript language with Monaco.
 */
export function registerRescriptLanguage(monaco) {
  monaco.languages.register({
    id: languageId,
    extensions: [".res", ".resi"],
    aliases: ["ReScript", "rescript"],
  });

  monaco.languages.setMonarchTokensProvider(languageId, monarchTokens);
  monaco.languages.setLanguageConfiguration(languageId, languageConfig);
}
