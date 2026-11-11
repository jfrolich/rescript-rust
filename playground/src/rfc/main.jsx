import React from "react";
import { createRoot } from "react-dom/client";
import readme from "../../../docs/comptime/README.md?raw";
import { Page } from "./Page.jsx";
import "./rfc.css";

createRoot(document.getElementById("root")).render(
  <Page
    current="rfc"
    markdown={readme}
    title={
      <>
        Compile-time <em>macros</em> for ReScript
      </>
    }
    lede="One mechanism for what PPXs do today, written in ReScript, that can also ask the type checker about types. Every example on this page is live: edit it and see what the compiler makes of it."
    pages={{ "IMPLEMENTATION.md": "implementation.html", "README.md": "./" }}
  />,
);
