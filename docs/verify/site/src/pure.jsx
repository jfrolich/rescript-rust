import React from "react";
import { createRoot } from "react-dom/client";
import document from "../../pure.md?raw";
import { Page } from "./Page.jsx";
import { about } from "./about.jsx";
import "./rfc.css";

createRoot(window.document.getElementById("root")).render(
  <Page
    markdown={document}
    title={
      <>
        <em>Pure</em> functions the compiler checks
      </>
    }
    lede="A reducer that pushes onto the state it was given type checks, and so does a render function that reads the clock. @pure on a let is a promise the compiler checks: the binding reads nothing that can change and changes nothing its caller can see. Every example on this page is live: edit it and see what the compiler says."
    about={{ ...about, jump: { href: "#reference", text: "The rules →" } }}
  />,
);
