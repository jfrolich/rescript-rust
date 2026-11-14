import React from "react";
import { createRoot } from "react-dom/client";
import readme from "../../../docs/ts-import/README.md?raw";
import { Page } from "./Page.jsx";
import "./rfc.css";

createRoot(document.getElementById("root")).render(
  <Page
    markdown={readme}
    title={
      <>
        Import <em>TypeScript</em> into ReScript
      </>
    }
    lede="Name a TypeScript module and what you want from it. The compiler asks the TypeScript checker for the types and gives you ReScript ones: no bindings to write, none to keep in sync. Every example on this page is live: edit either side and see what the other makes of it."
  />,
);
