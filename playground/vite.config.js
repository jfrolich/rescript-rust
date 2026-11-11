import { defineConfig } from "vite";
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
  build: {
    target: "esnext",
  },
  optimizeDeps: {
    exclude: ["rescript-playground-wasm"],
  },
});
