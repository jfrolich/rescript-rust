#!/usr/bin/env python3
"""Semantic comparator for typedtree sexp parity.

Treat two typedtree dumps as equivalent when their extracted inline type terms
match up to local ID reassignment. This intentionally ignores raw serializer
allocation identity noise.
"""

import argparse
import os
import sys

SCRIPT_DIR = os.path.dirname(os.path.abspath(__file__))
if SCRIPT_DIR not in sys.path:
    sys.path.insert(0, SCRIPT_DIR)

import parity_analyzer as pa


def load_sexpfile(path: str) -> pa.SexpFile:
    with open(path, encoding="utf-8", errors="replace") as handle:
        return pa.SexpFile.parse(handle.read())


def main() -> int:
    parser = argparse.ArgumentParser(
        description="Compare typedtree sexp files semantically by extracted type content."
    )
    parser.add_argument("ocaml")
    parser.add_argument("rust")
    parser.add_argument(
        "--explain",
        action="store_true",
        help="Print the first unmatched type mappings on failure.",
    )
    args = parser.parse_args()

    try:
        ocaml_sf = load_sexpfile(args.ocaml)
        rust_sf = load_sexpfile(args.rust)
    except Exception as exc:
        if args.explain:
            print(f"parse failure: {exc}", file=sys.stderr)
        return 1

    matches = pa.match_types(ocaml_sf.types, rust_sf.types)
    bad = [m for m in matches if m[2] not in ("MATCH", "SHIFTED")]
    if bad:
        if args.explain:
            print(
                f"type mismatch: {len(ocaml_sf.types)} ocaml types vs {len(rust_sf.types)} rust types",
                file=sys.stderr,
            )
            for ocaml_id, rust_id, status in bad[:10]:
                print(
                    f"  {status}: ocaml={ocaml_id!r} rust={rust_id!r}",
                    file=sys.stderr,
                )
        return 1

    return 0


if __name__ == "__main__":
    raise SystemExit(main())
