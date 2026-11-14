import { defineConfig } from "vite";
import react from "@vitejs/plugin-react";

export default defineConfig({
  // Relative URLs: the built site works from any path of any static host.
  base: "./",
  plugins: [react()],
  worker: { format: "es" },
  server: {
    // The pages are rendered from the documents one directory up.
    fs: { allow: [".."] },
  },
  build: {
    target: "esnext",
    // One page per document of docs/verify.
    rollupOptions: { input: ["index.html", "pure.html"] },
  },
});
