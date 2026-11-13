import React from "react";
import { createRoot } from "react-dom/client";
import document from "../../spec.md?raw";
import { Page } from "./Page.jsx";
import { about } from "./about.jsx";
import "./rfc.css";

createRoot(window.document.getElementById("root")).render(
  <Page
    markdown={document}
    title={
      <>
        <em>Specs</em>: every state of a reducer
      </>
    }
    lede="A reducer is a state machine, and its bugs are in the orders of actions nobody tried. Mark the machine and what must be true of it with @spec, and rescript verify goes through every state it can get into, then prints the shortest run that breaks a property. Every example on this page is live: the machines are explored in your browser."
    about={{ ...about, pullRequest: 255, jump: { href: "#reference", text: "The rules →" } }}
  />,
);
