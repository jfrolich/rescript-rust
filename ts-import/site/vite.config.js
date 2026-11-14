import { defineConfig } from "vite";
import react from "@vitejs/plugin-react";

export default defineConfig({
  // Relative URLs: the built site works from any path of any static host.
  base: "./",
  plugins: [react()],
  worker: { format: "es" },
  server: {
    // The page is rendered from docs/ts-import, two directories up.
    fs: { allow: ["../.."] },
  },
  build: { target: "esnext" },
});
