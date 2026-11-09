#!/usr/bin/env python3
"""Summarize the allocation-site samples of a `rescript` built with alloc-stats.

Run a build with `RESCRIPT_ALLOC_SITES=<file>` (see scripts/perf/README.md);
the binary writes one backtrace per 8192 allocations of each thread. Then:

    scripts/perf/alloc_sites.py SAMPLES_FILE [--top N]

Each sample is attributed to the first frame in compiler-rust/src or
rewatch/src that is not a generic helper (clone, collect, fmt, ...), and to
the construct that allocated (String, format!, Vec growth/clone/with_capacity,
HashMap, Box, Arc, Rc, SmallVec spill, ...). The report groups samples by
construct, by module, by function and by file:line. Counts are scaled by the
sampling period to estimate allocations per build. File:line attribution
needs debug info; without it only function names are shown.
"""

import argparse
import collections
import re

SAMPLE_PERIOD = 8192

# Frames of the sampler itself, dropped before attribution.
SAMPLER = re.compile(r"backtrace|alloc_stats|CountingAlloc|__rust_alloc|__rdl_alloc")

# Generic helpers, matched against the function name without its crate
# prefix: the allocation belongs to whoever called them.
GENERIC = re.compile(
    r"^(alloc|core|std|hashbrown|smallvec|indexmap)::|^<(alloc|core|std|hashbrown|smallvec|indexmap)::"
    r"|::clone$|<.* as core::clone::Clone>|from_iter|::extend|::collect|to_vec|to_owned"
    r"|to_string|::fmt|serde|_platform"
    # The compiler's own container and decoding helpers.
    r"|^binser::|^fast_hash::"
)

# First match wins, so the more specific constructs come first.
CONSTRUCTS = [
    ("HashMap/HashSet", r"hashbrown|HashMap|HashSet|IndexMap|IndexSet"),
    ("SmallVec spill", r"smallvec"),
    ("Arc::new", r"Arc<.*>::new|Arc::new|sync::Arc.*new"),
    ("Rc::new", r"Rc<.*>::new|Rc::new"),
    ("Box::new", r"boxed::Box.*::new|Box<.*>::new"),
    ("format!/to_string", r"fmt::format|to_string|alloc::fmt"),
    ("String clone/from", r"string::String|str::.*to_owned|String as core::clone"),
    ("PathBuf/OsString", r"path::Path|PathBuf|OsStr"),
    ("Vec growth (push/extend)", r"grow_one|reserve|finish_grow|RawVec.*grow"),
    ("Vec clone/to_vec", r"to_vec|Vec<T,A> as core::clone|slice.*to_vec"),
    ("Vec::with_capacity", r"with_capacity"),
    ("BTreeMap", r"btree"),
]
CONSTRUCTS = [(name, re.compile(pattern)) for name, pattern in CONSTRUCTS]

OUR_SOURCE = re.compile(r"(compiler-rust|rewatch)/src/")
CRATE_PREFIX = re.compile(r"\brescript_compiler::|\brescript::")
GENERICS = re.compile(r"<[^<>]*>")
FRAME = re.compile(r"\s*\d+: (.*)")
LOCATION = re.compile(r"\s*at (.*)")
HASH_SUFFIX = re.compile(r"::h[0-9a-f]{16}$")


def parse(path):
    """Yield (size, [(function, location)]) per sample, leaf frame first."""
    with open(path) as f:
        blocks = f.read().split("@@SAMPLE ")[1:]
    for block in blocks:
        lines = block.split("\n")
        size = int(lines[0])
        frames = []
        for line in lines[1:]:
            m = FRAME.match(line)
            if m:
                frames.append([HASH_SUFFIX.sub("", m.group(1)), ""])
                continue
            m = LOCATION.match(line)
            if m and frames:
                frames[-1][1] = m.group(1)
        yield size, [(fn, loc) for fn, loc in frames if not SAMPLER.search(fn)]


def construct(frames):
    text = " ".join(fn for fn, _ in frames[:40])
    for name, pattern in CONSTRUCTS:
        if pattern.search(text):
            return name
    return "other"


def strip_generics(name):
    # Remove nested generic arguments innermost-first.
    while True:
        stripped = GENERICS.sub("", name)
        if stripped == name:
            return name
        name = stripped


def owner(frames):
    """The first compiler frame that is not a generic helper: (function, file:line)."""
    for fn, loc in frames:
        if not OUR_SOURCE.search(loc):
            continue
        plain = CRATE_PREFIX.sub("", fn.split("::{{")[0])
        if GENERIC.search(plain):
            continue
        name = CRATE_PREFIX.sub("", strip_generics(fn)).replace("::::", "::")
        line = OUR_SOURCE.split(loc, maxsplit=1)[-1]
        return name, line
    # Without debug info there are no locations: fall back to names only.
    for fn, _ in frames:
        if fn.startswith(("rescript_compiler::", "rescript::")):
            plain = CRATE_PREFIX.sub("", fn.split("::{{")[0])
            if not GENERIC.search(plain):
                return CRATE_PREFIX.sub("", strip_generics(fn)), "?"
    return "?", "?"


def module_of(function):
    return "::".join(function.split("::")[:2])


def main():
    parser = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    parser.add_argument("samples")
    parser.add_argument("--top", type=int, default=40, help="rows per table")
    args = parser.parse_args()

    by_construct = collections.Counter()
    by_module = collections.Counter()
    by_function = collections.Counter()
    by_site = collections.Counter()
    site_bytes = collections.Counter()
    small = collections.Counter()
    n = 0
    for size, frames in parse(args.samples):
        n += 1
        kind = construct(frames)
        function, line = owner(frames)
        by_construct[kind] += 1
        by_module[module_of(function)] += 1
        by_function[function] += 1
        site = (function, line, kind)
        by_site[site] += 1
        site_bytes[site] += size
        if size <= 32:
            small[(function, kind)] += 1

    if n == 0:
        print("no samples")
        return

    def row(count, label):
        print(f"{100 * count / n:5.1f}% {count * SAMPLE_PERIOD / 1e6:6.1f}M  {label}")

    print(f"samples {n} (x{SAMPLE_PERIOD} = about {n * SAMPLE_PERIOD / 1e6:.0f}M allocations)")
    print("\n== by construct")
    for kind, count in by_construct.most_common():
        row(count, kind)
    print("\n== by module (first compiler frame)")
    for module, count in by_module.most_common(args.top):
        row(count, module)
    print("\n== by function")
    for function, count in by_function.most_common(args.top):
        row(count, function[:110])
    print("\n== by file:line (with construct and mean size)")
    for (function, line, kind), count in by_site.most_common(args.top):
        mean = site_bytes[(function, line, kind)] / count
        row(count, f"{line}  {kind}  avg {mean:.0f}B  {function[:80]}")
    print("\n== small (<= 32 B) by function and construct")
    for (function, kind), count in small.most_common(args.top):
        row(count, f"{kind:24} {function[:100]}")


if __name__ == "__main__":
    main()
