import React from "react";
import { createRoot } from "react-dom/client";
import markdown from "../../../docs/comptime/IMPLEMENTATION.md?raw";
import { Page } from "./Page.jsx";
import "./rfc.css";

createRoot(document.getElementById("root")).render(
  <Page
    current="implementation"
    markdown={markdown}
    title={
      <>
        Macros: the <em>compiler</em> side
      </>
    }
    lede="How the design of the RFC is implemented in the Rust compiler: parsing, the expansion passes, the type checker's hooks and the JavaScript engine."
    pages={{ "IMPLEMENTATION.md": "implementation.html", "README.md": "./" }}
  />,
);
