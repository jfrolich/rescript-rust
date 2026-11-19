#!/bin/sh
# Builds the compiler module (crate/) for wasm32-wasip1 and puts it where the
# pages load it from: public/compiler.wasm.
#
# The stack is 16 MB: the type checker recurses, and Rust's default for wasm
# is 1 MB. RUSTFLAGS replaces the repository's own flags, which is intended:
# those ask for the parallel frontend only.
set -eu
cd "$(dirname "$0")/../crate"
rustup target add wasm32-wasip1 >/dev/null 2>&1 || true
RUSTFLAGS="-C link-arg=-zstack-size=16777216" cargo build --release --target wasm32-wasip1
target_dir="${CARGO_TARGET_DIR:-target}"
mkdir -p ../public
cp "$target_dir/wasm32-wasip1/release/rescript_verify_wasm.wasm" ../public/compiler.wasm
ls -l ../public/compiler.wasm
