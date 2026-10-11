// error-output-parity: malformed @module `from` field falls through to missing-from.
@module({from: 1, with: {type_: "json"}}) external x: int = "x"
