import React from "react";

/** What the pages of docs/verify say about themselves. */
export const about = {
  doc: "docs/verify",
  branch: "rfc-proof",
  status: "Implemented on a branch",
  // The documents that have a page here; any other link goes to GitHub.
  pages: { "pure.md": "./pure", "law.md": "./law", "spec.md": "./spec", "proof.md": "./proof", "README.md": "./" },
  colophon: (
    <>
      The examples are compiled in your browser by that compiler, from its branch <code>rfc-proof</code>, built to
      WebAssembly.
    </>
  ),
};
