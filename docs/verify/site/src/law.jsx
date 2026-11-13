import React from "react";
import { createRoot } from "react-dom/client";
import document from "../../law.md?raw";
import { Page } from "./Page.jsx";
import { about } from "./about.jsx";
import "./rfc.css";

createRoot(window.document.getElementById("root")).render(
  <Page
    markdown={document}
    title={
      <>
        <em>Laws</em>: properties the build runs
      </>
    }
    lede="A test checks the cases someone thought of. A law says what holds for every value: write it as a function that returns bool, mark it @law, and rescript verify runs it on values made from the types of its parameters, all of them when there are few. Every example on this page is live: the laws run in your browser."
    about={{ ...about, pullRequest: 254, jump: { href: "#reference", text: "The rules →" } }}
  />,
);
