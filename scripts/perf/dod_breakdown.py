#!/usr/bin/env python3
"""Break a samply profile of a `rescript build` down into data movement.

"Data movement" is CPU spent in allocation/free, memmove/memcmp, drops,
clones and hashing, attributed by the first three (leaf-most) frames of each
sample. The script reports:

  * the data-movement share of busy (non-waiting) compiler samples, per kind;
  * a root-cause breakdown (data movement and inclusive share per area);
  * the compiler functions that own the most data-movement samples.

Record profiles with scripts/perf/profile_build.sh (or any
`samply record --save-only --unstable-presymbolicate` run), then:

    scripts/perf/dod_breakdown.py PROFILE_DIR [PROFILE_DIR ...] [--cpu-seconds N]

Each PROFILE_DIR holds `prof.json.gz` and `prof.json.syms.json`. Pass several
runs of the same binary to average them. With --cpu-seconds (user + sys from
`/usr/bin/time -l` of an unprofiled build), shares are also shown in seconds.
Compare two binaries only with profiles recorded in the same batch.
"""

import argparse
import collections
import gzip
import json
import re

WAIT = re.compile(
    r"__psynch|semaphore_wait|swtch_pri|cthread_yield|Sleep::sleep|__ulock|kevent|mach_msg"
)

# Leaf categories. Match whole allocator symbols only: a substring `free`
# would also match graph walks such as `surely_occur_free`.
KINDS = [
    ("alloc/free", re.compile(
        r"^_?mi_|malloc|^_?free$|^_?free_|madvise|realloc|RawVecInner|grow_one|finish_grow")),
    ("memmove/memcmp", re.compile(r"_platform_mem")),
    ("drop", re.compile(r"drop_in_place|drop_slow")),
    ("clone", re.compile(r"::clone$|clone_subtree|::clone\.\d+$")),
    ("hash", re.compile(r"hashbrown|hash_one|ahash|Hasher")),
]

# Frames that are containers or allocator plumbing, never an "owner".
GENERIC = re.compile(
    r"^_?mi_|malloc|free$|_platform|drop_in_place|drop_slow|::clone$|hashbrown|hash_one|"
    r"ahash|Hasher|^alloc::|^core::|RawVec|::to_vec|from_iter|::extend|smallvec|^std::|"
    r"::fmt|^\?|::insert$|::get$|::entry$|::next$|::fold$|::spec_|::collect|OUTLINED"
)


def any_frame(pattern):
    rx = re.compile(pattern)
    return lambda kind, own, names: any(rx.search(n) for n in names[:40])


# Root causes, checked in order; the first match wins.
AREAS = [
    ("per-module teardown (context drops)",
     lambda kind, own, names: kind == "drop" and bool(own) and re.search(
         r"compile_preprocessed_structure|compile::compile::|::execute|bridge_producer|"
         r"compile_module_in_process", own[0]) is not None),
    ("rewatch metadata (item deps, records, state db)", any_frame(
        r"item_deps|unit_reads::|current_record|state_db|sqlite|write_in_process_record|"
        r"blake3|incremental::|clean::|UnitDigests|encode_core")),
    ("dependency env materialization", any_frame(
        r"persistent_env::|env_lazy::|shared_store::|replay_store_piece|touch_store_piece|"
        r"register_component_alias|_components|find_pers_struct|copy_lookup_.*with_paths|"
        r"persistent_env_clone|portable_types::|internalize|load_pervasives|open_module")),
    ("lambda / JS", any_frame(r"^lambda::|^raw_lambda::|^js_ir::")),
    ("parse / binary AST", any_frame(
        r"binary_ast::|parse_arena::|^parser::|binser::|run_implementation_frontend")),
    ("gentype", any_frame(r"gentype::")),
    ("type graph core (ctype, context, paths)",
     lambda kind, own, names: any(re.search(
         r"^types::ctype::|TypePayloadPool|^types::context::|^types::path::|subst::", n)
         for n in own[:2])),
    ("typecore / typemod / usage / parmatch", any_frame(r"^types::")),
]


def short(name):
    for _ in range(4):
        name = re.sub(r"<[^<>]*>", "", name)
    name = re.sub(r"::h[0-9a-f]{16}$", "", name)
    return name.replace("rescript_compiler::", "")


def load_samples(profile_dir):
    prof = json.load(gzip.open(f"{profile_dir}/prof.json.gz"))
    syms = json.load(open(f"{profile_dir}/prof.json.syms.json"))
    strings = syms["string_table"]
    libsym = {}
    for lib in syms["data"]:
        table = lib["symbol_table"]
        libsym[lib["debug_name"]] = {
            rva: strings[table[idx]["symbol"]]
            for rva, idx in lib["known_addresses"]
            if idx is not None and idx < len(table)
        }
    libs = prof["libs"]
    for thread in prof["threads"]:
        if not thread["name"].startswith("rewatch"):
            continue
        frames = thread["frameTable"]
        funcs = thread["funcTable"]
        resources = thread["resourceTable"]
        stacks = thread["stackTable"]
        memo = {}

        def frame_name(fi):
            if fi in memo:
                return memo[fi]
            func = frames["func"][fi]
            res = funcs["resource"][func]
            addr = frames["address"][fi]
            name = "?"
            if res is not None and res >= 0:
                table = libsym.get(libs[resources["lib"][res]]["debugName"], {})
                name = table.get(addr) or table.get(addr - 1) or "?"
            memo[fi] = short(name)
            return memo[fi]

        for stack in thread["samples"]["stack"]:
            if stack is None:
                continue
            names = []
            while stack is not None and len(names) < 80:
                names.append(frame_name(stacks["frame"][stack]))
                stack = stacks["prefix"][stack]
            yield names


def main():
    parser = argparse.ArgumentParser(description=__doc__,
                                     formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("profiles", nargs="+")
    parser.add_argument("--cpu-seconds", type=float)
    parser.add_argument("--owners", type=int, default=30)
    args = parser.parse_args()

    busy = 0
    by_kind = collections.Counter()
    area_dm = collections.Counter()
    area_incl = collections.Counter()
    area_kind = collections.defaultdict(collections.Counter)
    owners = collections.Counter()
    owner_kind = collections.defaultdict(collections.Counter)
    for profile in args.profiles:
        for names in load_samples(profile):
            if WAIT.search(names[0]):
                continue
            busy += 1
            kind = next((k for k, rx in KINDS if any(rx.search(n) for n in names[:3])), None)
            own = [n for n in names if not GENERIC.search(n)][:6]
            area = next((a for a, test in AREAS if test(kind, own, names)), "other")
            area_incl[area] += 1
            if kind is None:
                continue
            by_kind[kind] += 1
            area_dm[area] += 1
            area_kind[area][kind] += 1
            owner = own[0] if own else "?"
            owners[owner] += 1
            owner_kind[owner][kind] += 1

    if busy == 0:
        raise SystemExit("no compiler samples found")
    secs = (args.cpu_seconds / busy) if args.cpu_seconds else None

    def pct(n):
        text = f"{100 * n / busy:5.2f}%"
        return text + (f" {n * secs:5.2f}s" if secs else "")

    total = sum(by_kind.values())
    print(f"busy samples: {busy}")
    print(f"data movement: {pct(total)}")
    for kind, _ in KINDS:
        print(f"  {kind:16} {pct(by_kind[kind])}")
    print("\nroot cause: data movement | inclusive")
    for area, _ in AREAS + [("other", None)]:
        kinds = ", ".join(f"{k} {100 * v / busy:.2f}" for k, v in area_kind[area].most_common())
        print(f"  {pct(area_dm[area])} | {100 * area_incl[area] / busy:5.1f}%  {area}  ({kinds})")
    print(f"\ntop {args.owners} owners of data-movement samples")
    for owner, n in owners.most_common(args.owners):
        kinds = ", ".join(f"{k} {v}" for k, v in owner_kind[owner].most_common())
        print(f"  {pct(n)}  {owner[:100]}  ({kinds})")


if __name__ == "__main__":
    main()
