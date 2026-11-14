import React from "react";
import { createRoot } from "react-dom/client";
import document from "../../README.md?raw";
import { Page } from "./Page.jsx";
import { about } from "./about.jsx";
import "./rfc.css";

createRoot(window.document.getElementById("root")).render(
  <Page
    markdown={document}
    title={
      <>
        <em>Verification</em> for ReScript
      </>
    }
    lede="A program states what must hold, in ReScript, next to the code, and the tools check it. No proof language, no solver, no new kind of type."
    about={about}
  />,
);
