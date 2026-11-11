import { defineConfig } from "vite";
import { resolve } from "path";
import react from "@vitejs/plugin-react";
import wasm from "vite-plugin-wasm";

export default defineConfig({
  // Relative URLs: the built site works from any path of any static host.
  base: "./",
  plugins: [react(), wasm()],
  worker: {
    format: "es",
    plugins: () => [wasm()],
  },
  server: {
    // The RFC pages are rendered from docs/comptime.
    fs: { allow: [".."] },
  },
  build: {
    target: "esnext",
    rollupOptions: {
      input: {
        // The RFC with live examples, the implementation notes, and the
        // full playground.
        index: resolve(import.meta.dirname, "index.html"),
        implementation: resolve(import.meta.dirname, "implementation.html"),
        playground: resolve(import.meta.dirname, "playground.html"),
      },
    },
  },
  optimizeDeps: {
    exclude: ["rescript-playground-wasm"],
  },
});
