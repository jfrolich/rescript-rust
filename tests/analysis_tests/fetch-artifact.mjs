// Copy a typed artifact served by `rescript watch` to a file.
// In-process builds keep .cmi/.cmt/.cmti in the watcher (see
// rewatch/src/tooling_server.rs); tests use this to simulate files that
// editor tooling writes itself.
//
// Usage: node fetch-artifact.mjs <artifact path> <destination>
import fs from "node:fs";
import net from "node:net";
import path from "node:path";

const [artifact, destination] = process.argv.slice(2);
const absolute = path.resolve(artifact);

let dir = path.dirname(absolute);
let addressFile;
for (;;) {
  const candidate = path.join(dir, "lib", "rescript-watch.addr");
  if (fs.existsSync(candidate)) {
    addressFile = candidate;
    break;
  }
  const parent = path.dirname(dir);
  if (parent === dir) {
    console.error(`No rescript watch serves ${absolute}`);
    process.exit(1);
  }
  dir = parent;
}
const [address, token] = fs.readFileSync(addressFile, "utf8").trim().split(" ");
const separator = address.lastIndexOf(":");
const socket = net.connect(
  Number(address.slice(separator + 1)),
  address.slice(0, separator),
);

let buffer = Buffer.alloc(0);
const replies = [];
let pending = null;
const pump = () => {
  for (;;) {
    if (pending === null) {
      const newline = buffer.indexOf(10);
      if (newline < 0) return;
      const header = buffer.subarray(0, newline).toString();
      buffer = buffer.subarray(newline + 1);
      if (!header.startsWith("OK ")) {
        replies.push(null);
        continue;
      }
      pending = Number(header.slice(3));
    }
    if (buffer.length < pending) return;
    replies.push(buffer.subarray(0, pending));
    buffer = buffer.subarray(pending);
    pending = null;
  }
};
socket.on("data", chunk => {
  buffer = Buffer.concat([buffer, chunk]);
  pump();
  if (replies.length === 2) {
    socket.end();
    const bytes = replies[1];
    if (bytes === null) {
      console.error(`rescript watch does not serve ${absolute}`);
      process.exit(1);
    }
    fs.mkdirSync(path.dirname(destination), { recursive: true });
    fs.writeFileSync(destination, bytes);
  }
});
socket.write(`AUTH ${token}\nGET ${absolute}\n`);
