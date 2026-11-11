/** A project in the URL: `#project=<base64url of the JSON of its files>`. */

const KEY = "#project=";

export function encodeProject(files) {
  const bytes = new TextEncoder().encode(JSON.stringify(files.map((file) => [file.name, file.source])));
  let binary = "";
  for (const byte of bytes) binary += String.fromCharCode(byte);
  return KEY + btoa(binary).replace(/\+/g, "-").replace(/\//g, "_").replace(/=+$/, "");
}

export function decodeProject(hash) {
  if (!hash.startsWith(KEY)) return null;
  try {
    const binary = atob(hash.slice(KEY.length).replace(/-/g, "+").replace(/_/g, "/"));
    const bytes = Uint8Array.from(binary, (char) => char.charCodeAt(0));
    const entries = JSON.parse(new TextDecoder().decode(bytes));
    if (!Array.isArray(entries) || entries.length === 0) return null;
    return entries.map(([name, source]) => ({ name: String(name), source: String(source) }));
  } catch {
    return null;
  }
}
