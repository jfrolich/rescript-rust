/**
 * Loads ReScript stdlib files into the WASM compiler's virtual filesystem.
 */

/**
 * Derive a module name from a filename.
 * e.g., "Js.res" -> "Js", "Belt_Array.resi" -> "Belt_Array"
 */
function moduleNameFromPath(vfsPath) {
  const filename = vfsPath.split("/").pop();
  return filename.replace(/\.(res|resi)$/, "");
}

/**
 * Load all stdlib files into the WASM VFS and register modules.
 * @param {Object} compiler - The WASM compiler module
 * @returns {Promise<number>} Number of files loaded
 */
export async function loadStdlib(compiler) {
  const response = await fetch("/stdlib.json");
  if (!response.ok) {
    throw new Error(`Failed to fetch stdlib.json: ${response.status}`);
  }
  const files = await response.json();

  // Write all files to VFS
  for (const [path, content] of Object.entries(files)) {
    compiler.vfs_write_file(path, content);
  }

  // Register modules for on-demand type checking.
  // For each module, prefer .resi (interface) over .res (implementation).
  const modules = new Map();
  for (const path of Object.keys(files)) {
    const moduleName = moduleNameFromPath(path);
    const isInterface = path.endsWith(".resi");
    // .resi takes priority
    if (!modules.has(moduleName) || isInterface) {
      modules.set(moduleName, path);
    }
  }

  for (const [moduleName, path] of modules) {
    compiler.register_source_module(moduleName, path);
  }

  return Object.keys(files).length;
}
