// error-output-parity: malformed @module `with` field falls through to missing-with.
@module({from: "pkg", with: 1}) external x: int = "x"
