import React from "react";
import { createRoot } from "react-dom/client";
import readme from "../../../docs/class-identity/README.md?raw";
import { Page } from "./Page.jsx";
import "./rfc.css";

createRoot(document.getElementById("root")).render(
  <Page
    markdown={readme}
    title={
      <>
        Class types that packages can <em>share</em>
      </>
    }
    lede="The DOM types are leaving the standard library, and a type belongs to the one module that declares it. This proposal makes the JavaScript class the identity of a class type: packages that each declare Element can pass elements to each other, and nobody has to own the DOM. The examples that show today's compiler are live."
    about={{
      doc: "docs/class-identity",
      branch: "class-identity-rfc",
      status: "Not implemented",
      source: {
        href: "https://github.com/rescript-lang/rescript/issues/9058",
        text: "Upstream RFC ↗",
      },
      jump: { href: "#the-proposal", text: "The proposal →" },
      colophon: (
        <>
          The examples are compiled in your browser by that compiler, from its branch{" "}
          <code>ts-import</code>, built to WebAssembly.
        </>
      ),
    }}
  />,
);
