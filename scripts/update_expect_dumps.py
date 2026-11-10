#!/usr/bin/env python3
"""Update `expect_dump!` expectations in compiler-rust unit tests.

`expect_dump!(actual, "expected")` (compiler-rust/src/js_ir/dump.rs) prints
an `EXPECT_DUMP` line for every mismatch. With `EXPECT_DUMP_FILL` set it
does not panic, so one test run reports every stale expectation. This script
runs the tests that way and rewrites each reported string literal in place.

    scripts/update_expect_dumps.py [TEST_FILTER]

Review the resulting diff: it records whatever the compiler produces now.
"""
import json
import os
import subprocess
import sys

ROOT = os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "compiler-rust")


def find_close(s, i):
    """Index of the `)` closing the `(` at s[i - 1], skipping string literals."""
    depth = 1
    while depth:
        c = s[i]
        if c == '"':
            i += 1
            while s[i] != '"':
                i += 2 if s[i] == "\\" else 1
        elif c in "([{":
            depth += 1
        elif c in ")]}":
            depth -= 1
        i += 1
    return i - 1


def first_arg_end(s, i):
    """Index of the top-level `,` ending the first macro argument at s[i:]."""
    depth = 0
    while True:
        c = s[i]
        if c == '"':
            i += 1
            while s[i] != '"':
                i += 2 if s[i] == "\\" else 1
        elif c in "([{":
            depth += 1
        elif c in ")]}":
            depth -= 1
        elif c == "," and depth == 0:
            return i
        i += 1


def rust_string(value):
    out = []
    for ch in value:
        if ch == "\\":
            out.append("\\\\")
        elif ch == '"':
            out.append('\\"')
        elif ch == "\n":
            out.append("\\n")
        elif ch == "\t":
            out.append("\\t")
        elif ord(ch) < 32:
            out.append("\\u{%x}" % ord(ch))
        else:
            out.append(ch)
    return '"' + "".join(out) + '"'


def main():
    test_filter = sys.argv[1:] or [""]
    env = dict(os.environ, EXPECT_DUMP_FILL="1")
    run = subprocess.run(
        ["cargo", "test", "--lib", "-q", "--", *test_filter, "--nocapture", "--test-threads=1"],
        cwd=ROOT,
        env=env,
        capture_output=True,
        text=True,
    )
    reports = {}
    for line in (run.stdout + run.stderr).splitlines():
        k = line.find("EXPECT_DUMP\t")
        if k < 0:
            continue
        _, path, ln, col, actual = line[k:].split("\t", 4)
        reports.setdefault((path, int(ln), int(col)), json.loads(actual))
    if run.returncode != 0 and not reports:
        sys.stderr.write(run.stdout[-4000:] + run.stderr[-4000:])
        sys.exit(run.returncode)
    by_file = {}
    for (path, ln, col), actual in reports.items():
        by_file.setdefault(path, []).append((ln, col, actual))
    for path, items in by_file.items():
        full = os.path.join(ROOT, path)
        src = open(full).read()
        offsets = [0]
        for text in src.split("\n"):
            offsets.append(offsets[-1] + len(text) + 1)
        for ln, col, actual in sorted(items, reverse=True):
            start = src.index("expect_dump!(", offsets[ln - 1] + col - 1)
            open_paren = start + len("expect_dump!(")
            close = find_close(src, open_paren)
            comma = first_arg_end(src, open_paren)
            new = src[start:comma] + ", " + rust_string(actual) + ")"
            src = src[:start] + new + src[close + 1:]
        open(full, "w").write(src)
        print(f"{path}: updated {len(items)} expectation(s)")
    if not reports:
        print("all expectations match")


if __name__ == "__main__":
    main()
