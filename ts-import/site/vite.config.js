import { defineConfig } from "vite";
import react from "@vitejs/plugin-react";

export default defineConfig({
  // Relative URLs: the built site works from any path of any static host.
  base: "./",
  plugins: [react()],
  worker: { format: "es" },
  server: {
    // The pages are rendered from docs/, two directories up.
    fs: { allow: ["../.."] },
  },
  build: {
    target: "esnext",
    // One page per document: docs/ts-import and docs/class-identity.
    rollupOptions: { input: ["index.html", "classes.html"] },
  },
});
