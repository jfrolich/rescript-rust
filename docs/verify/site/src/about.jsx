import React from "react";

/** What the pages of docs/verify say about themselves. */
export const about = {
  doc: "docs/verify",
  branch: "rfc-proof",
  status: "Implemented on a branch",
  // The documents that have a page here; any other link goes to GitHub.
  pages: { "pure.md": "./pure", "law.md": "./law", "spec.md": "./spec", "proof.md": "./proof", "README.md": "./" },
  // The RFCs of the series, in the order to read them. Each builds on the
  // ones before it; `page` is the key a page passes as `about.current`.
  series: [
    {
      page: "pure",
      href: "./pure",
      name: "Purity",
      adds: "@pure, @mutates",
      summary: "The compiler checks that a function only computes: it reads nothing that can change and changes nothing its caller sees.",
      checked: "in every build",
      pullRequest: 253,
    },
    {
      page: "law",
      href: "./law",
      name: "Laws",
      adds: "@law, rescript verify",
      summary: "A property of the program, written as a function that returns bool, run on values made from the types of its parameters.",
      checked: "on generated values",
      pullRequest: 254,
    },
    {
      page: "proof",
      href: "./proof",
      name: "Proofs",
      adds: "@law(proved)",
      summary: "rescript verify proves laws for every value, by cases, induction and the laws before them, with no proof to write.",
      checked: "for every value",
      pullRequest: 271,
    },
    {
      page: "spec",
      href: "./spec",
      name: "Specs",
      adds: "@spec, Spec.t",
      summary: "A reducer and what must be true of it. rescript verify goes through every state it can get into and prints the shortest run that breaks it.",
      checked: "over every state",
      pullRequest: 255,
    },
  ],
  colophon: (
    <>
      The examples are compiled in your browser by that compiler, from its branch <code>rfc-proof</code>, built to
      WebAssembly.
    </>
  ),
};
