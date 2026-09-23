#!/usr/bin/env python3
"""Differential fuzzing loop: OCaml bsc (oracle) vs Rust bsc.

Subcommands:
  seeds              Build the seed corpus (and differential-check every seed).
  run                Mutate seeds, compare verdicts, record findings.
  reduce             Minimise unreduced findings (keeps kind + signature).
  report             Summarise buckets.
  check FILE...      Compare one or more .res files directly.
  regress            Re-run every reduced repro; mark fixed buckets.

State lives in .fuzz/ (git-ignored):
  .fuzz/seeds.json               seed list with OCaml verdicts
  .fuzz/findings/<kind>/<bucket>/<hash>.res
  .fuzz/findings/<kind>/<bucket>/meta.json
"""

from __future__ import annotations

import argparse
import hashlib
import json
import os
import random
import sys
import time
from concurrent.futures import ProcessPoolExecutor, as_completed
from pathlib import Path

sys.path.insert(0, str(Path(__file__).parent))

from difftest import ROOT, compare, case_hash  # noqa: E402
from mutate import Mutator  # noqa: E402
from reduce import reduce_source  # noqa: E402

STATE = ROOT / ".fuzz"
FINDINGS = STATE / "findings"
SEED_DIRS = [
    "tests/tests/src",
    "tests/build_tests/super_errors/fixtures",
    "tests/error_output_parity/compiler/fixtures",
    "tests/syntax_tests/data/printer",
    "tests/syntax_tests/data/parsing",
    "tests/syntax_tests/data/conversion",
    "tests/syntax_tests/data/ppx",
    "tests/gentype_tests",
    "tests/analysis_tests/tests/src",
    "tests/docstring_tests",
]
PRIORITY = ["rust_accepts", "crash", "rust_rejects", "msg_diff", "warn_diff", "ocaml_crash"]


def module_name(path: Path) -> str:
    stem = path.stem
    return stem[0].upper() + stem[1:] + ".res" if stem else "A.res"


def bucket_id(sig: str) -> str:
    return hashlib.sha1(sig.encode()).hexdigest()[:10]


def record(kind: str, sig: str, name: str, src: str, origin: dict) -> bool:
    b = FINDINGS / kind / bucket_id(sig)
    new_bucket = not b.exists()
    b.mkdir(parents=True, exist_ok=True)
    meta_p = b / "meta.json"
    meta = json.loads(meta_p.read_text()) if meta_p.exists() else {
        "kind": kind, "signature": sig, "status": "open", "count": 0,
        "first_seen": time.strftime("%Y-%m-%d %H:%M:%S"), "examples": [], "name": name,
    }
    meta["count"] += 1
    if len(meta["examples"]) < 5:
        h = hashlib.sha1(src.encode()).hexdigest()[:12]
        (b / f"{h}.res").write_text(src)
        meta["examples"].append({"file": f"{h}.res", **origin})
    if meta.get("status") == "fixed":
        meta["status"] = "reopened"
    meta_p.write_text(json.dumps(meta, indent=2))
    return new_bucket


# ---------------------------------------------------------------- seeds
def _check_seed(p: str):
    path = Path(p)
    try:
        src = path.read_text()
    except UnicodeDecodeError:
        return None
    name = module_name(path)
    r = compare({name: src})
    ov = "ok" if all(x.status == "ok" for x in r.ocaml) else r.ocaml[-1].status
    missing_dep = any(
        s in r.ocaml[-1].stderr for s in ("The module or file", "was not found", "Unbound module")
    ) if r.ocaml else False
    return {"path": p, "name": name, "ocaml": ov, "missing_dep": missing_dep,
            "kind": r.kind, "sig": r.signature, "size": len(src)}


def cmd_seeds(args):
    files = []
    for d in SEED_DIRS:
        base = ROOT / d
        if base.exists():
            files += [str(p) for p in base.rglob("*.res") if "/node_modules/" not in str(p)
                      and "/lib/" not in str(p) and p.stat().st_size < 60_000]
    print(f"checking {len(files)} candidate seeds", flush=True)
    seeds, n = [], 0
    with ProcessPoolExecutor(args.jobs) as ex:
        for fut in as_completed([ex.submit(_check_seed, f) for f in files]):
            s = fut.result()
            n += 1
            if s is None:
                continue
            if s["kind"] != "same" and not s["missing_dep"]:
                src = Path(s["path"]).read_text()
                if record(s["kind"], s["sig"], s["name"], src, {"seed": s["path"], "ops": []}):
                    print(f"  [{s['kind']}] seed {s['path']} :: {s['sig']}", flush=True)
            if not s["missing_dep"]:
                seeds.append(s)
    STATE.mkdir(exist_ok=True)
    (STATE / "seeds.json").write_text(json.dumps(seeds, indent=1))
    ok = sum(1 for s in seeds if s["ocaml"] == "ok")
    print(f"{len(seeds)} usable seeds ({ok} accepted by OCaml)")


# ---------------------------------------------------------------- run
_SEEDS: list[dict] = []
_DONORS: list[str] = []


def _init_worker(seeds, donors):
    global _SEEDS, _DONORS
    _SEEDS, _DONORS = seeds, donors


def _fuzz_one(seed_idx: int, rng_seed: int, check_text: bool):
    rng = random.Random(rng_seed)
    s = _SEEDS[seed_idx]
    src = Path(s["path"]).read_text()
    m = Mutator(rng, _DONORS)
    n = rng.choice([1, 1, 1, 2, 2, 3])
    mut, ops = m.mutate(src, n)
    if mut == src:
        return None
    r = compare({s["name"]: mut}, check_text=check_text)
    if not r.interesting:
        return None
    return r.kind, r.signature, s["name"], mut, {"seed": s["path"], "ops": ops, "rng": rng_seed}


def cmd_run(args):
    seeds = json.loads((STATE / "seeds.json").read_text())
    if args.only_valid:
        seeds = [s for s in seeds if s["ocaml"] == "ok"]
    if args.filter:
        seeds = [s for s in seeds if args.filter in s["path"]]
    donors = [Path(s["path"]).read_text() for s in seeds[:: max(1, len(seeds) // 200)]]
    kinds = set(args.kinds.split(",")) if args.kinds else None
    deadline = time.time() + args.minutes * 60
    base = args.seed if args.seed is not None else int(time.time())
    rng = random.Random(base)
    done = found = new = 0
    t0 = time.time()
    with ProcessPoolExecutor(args.jobs, initializer=_init_worker, initargs=(seeds, donors)) as ex:
        pending = set()
        while time.time() < deadline or pending:
            while time.time() < deadline and len(pending) < args.jobs * 4:
                pending.add(ex.submit(_fuzz_one, rng.randrange(len(seeds)), rng.getrandbits(48), args.text))
            fin = [f for f in list(pending) if f.done()]
            if not fin:
                time.sleep(0.01)
                continue
            for f in fin:
                pending.discard(f)
                done += 1
                res = f.result()
                if res is None:
                    continue
                kind, sig, name, mut, origin = res
                if kinds and kind not in kinds:
                    continue
                found += 1
                if record(kind, sig, name, mut, origin):
                    new += 1
                    print(f"  NEW [{kind}] {sig}  (seed {Path(origin['seed']).name}, ops {origin['ops']})", flush=True)
            if done and done % 2000 == 0:
                print(f"  .. {done} cases, {found} mismatches, {new} new buckets, {done / (time.time() - t0):.0f}/s", flush=True)
    print(f"done: {done} cases, {found} mismatches, {new} new buckets")


# ---------------------------------------------------------------- reduce
def _reduce_bucket(bdir: str):
    b = Path(bdir)
    meta = json.loads((b / "meta.json").read_text())
    if (b / "reduced.res").exists():
        return None
    ex = meta["examples"][0]
    src = (b / ex["file"]).read_text()
    name = meta.get("name", "A.res")
    kind, sig = meta["kind"], meta["signature"]

    def keep(s: str) -> bool:
        r = compare({name: s}, check_text=kind in ("msg_diff", "warn_diff"))
        if r.kind != kind:
            return False
        return kind in ("crash",) or r.signature == sig

    red = reduce_source(src, keep)
    (b / "reduced.res").write_text(red)
    meta["reduced_lines"] = red.count("\n") + 1
    (b / "meta.json").write_text(json.dumps(meta, indent=2))
    return str(b), meta["reduced_lines"]


def cmd_reduce(args):
    bdirs = []
    for kind in (args.kinds.split(",") if args.kinds else PRIORITY):
        d = FINDINGS / kind
        if d.exists():
            bdirs += [str(x) for x in sorted(d.iterdir()) if x.is_dir()]
    with ProcessPoolExecutor(args.jobs) as ex:
        for f in as_completed([ex.submit(_reduce_bucket, b) for b in bdirs]):
            r = f.result()
            if r:
                print(f"  reduced {r[0]} -> {r[1]} lines", flush=True)


# ---------------------------------------------------------------- regress
def _regress(bdir: str):
    b = Path(bdir)
    meta = json.loads((b / "meta.json").read_text())
    f = b / "reduced.res"
    if not f.exists():
        f = b / meta["examples"][0]["file"]
    r = compare({meta.get("name", "A.res"): f.read_text()},
                check_text=meta["kind"] in ("msg_diff", "warn_diff"))
    status = "open" if r.kind == meta["kind"] else "fixed"
    if meta.get("status") != status:
        meta["status"] = status
        (b / "meta.json").write_text(json.dumps(meta, indent=2))
    return str(b), status, r.kind


def cmd_regress(args):
    bdirs = [str(x) for k in PRIORITY if (FINDINGS / k).exists() for x in (FINDINGS / k).iterdir() if x.is_dir()]
    with ProcessPoolExecutor(args.jobs) as ex:
        res = [f.result() for f in as_completed([ex.submit(_regress, b) for b in bdirs])]
    fixed = [r for r in res if r[1] == "fixed"]
    print(f"{len(res)} buckets, {len(fixed)} fixed, {len(res) - len(fixed)} open")


# ---------------------------------------------------------------- report
def cmd_report(args):
    rows = []
    for kind in PRIORITY:
        d = FINDINGS / kind
        if not d.exists():
            continue
        for b in sorted(d.iterdir()):
            if not (b / "meta.json").exists():
                continue
            m = json.loads((b / "meta.json").read_text())
            if args.open and m.get("status") == "fixed":
                continue
            rows.append((PRIORITY.index(kind), -m["count"], kind, b.name, m))
    rows.sort()
    counts = {}
    for _, _, kind, _, m in rows:
        counts.setdefault(kind, [0, 0])
        counts[kind][0 if m.get("status") != "fixed" else 1] += 1
    for k, (o, f) in counts.items():
        print(f"{k:14s} open={o:4d} fixed={f:4d}")
    if args.json:
        print(json.dumps([{"kind": r[2], "bucket": r[3], **r[4]} for r in rows], indent=1))
        return
    for _, negc, kind, bid, m in rows[: args.limit]:
        red = " reduced" if (FINDINGS / kind / bid / "reduced.res").exists() else ""
        print(f"[{kind}] {bid} x{-negc} {m.get('status')}{red} :: {m['signature']}")


def cmd_check(args):
    case = {}
    for f in args.files:
        p = Path(f)
        case[p.name] = p.read_text()
    r = compare(case)
    print(f"kind={r.kind} sig={r.signature}")
    for tag, runs in (("ocaml", r.ocaml), ("rust", r.rust)):
        for x in runs:
            print(f"--- {tag}: {x.status} ({x.code})\n{x.stderr.rstrip()}")


def main():
    ap = argparse.ArgumentParser()
    sub = ap.add_subparsers(dest="cmd", required=True)
    jobs = max(2, (os.cpu_count() or 4) - 2)
    p = sub.add_parser("seeds"); p.add_argument("-j", "--jobs", type=int, default=jobs)
    p = sub.add_parser("run")
    p.add_argument("-m", "--minutes", type=float, default=5)
    p.add_argument("-j", "--jobs", type=int, default=jobs)
    p.add_argument("--seed", type=int)
    p.add_argument("--only-valid", action="store_true")
    p.add_argument("--filter")
    p.add_argument("--kinds", help="comma list of kinds to record")
    p.add_argument("--text", action="store_true", help="also compare diagnostic text")
    p = sub.add_parser("reduce"); p.add_argument("-j", "--jobs", type=int, default=jobs); p.add_argument("--kinds")
    p = sub.add_parser("regress"); p.add_argument("-j", "--jobs", type=int, default=jobs)
    p = sub.add_parser("report")
    p.add_argument("--open", action="store_true"); p.add_argument("--json", action="store_true")
    p.add_argument("--limit", type=int, default=60)
    p = sub.add_parser("check"); p.add_argument("files", nargs="+")
    args = ap.parse_args()
    {"seeds": cmd_seeds, "run": cmd_run, "reduce": cmd_reduce, "regress": cmd_regress,
     "report": cmd_report, "check": cmd_check}[args.cmd](args)


if __name__ == "__main__":
    main()
