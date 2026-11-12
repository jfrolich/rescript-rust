"""Compare stored interfaces byte-for-byte, or test clean 1/8/8-worker builds.

Pass two package/build directories (or rescript.sqlite files) to compare
existing builds. With no arguments, build tests/tests three times in place.
"""

import argparse
import os
from pathlib import Path
import sqlite3
import subprocess

ROOT = Path(__file__).resolve().parent.parent
TABLES = ("interfaces", "interface_extras", "runtime_interfaces")


def database_path(path):
    path = Path(path)
    candidates = ([path / "rescript.sqlite", path / "lib/rescript/rescript.sqlite",
                   path / "lib/bs/rescript.sqlite"] if path.is_dir() else [path])
    for candidate in candidates:
        if candidate.is_file():
            return candidate
    raise FileNotFoundError("No stored interface database found; tried: " +
                            ", ".join(str(candidate) for candidate in candidates))


def read_interfaces(path, *, allow_empty=False):
    path = database_path(path)
    with sqlite3.connect(path.resolve().as_uri() + "?mode=ro", uri=True) as db:
        result = {(table, module): bytes(data) for table in TABLES
                  for module, data in db.execute(f"SELECT module, data FROM {table}")}
    if not allow_empty and not any(table == "interfaces" for table, _ in result):
        raise ValueError(f"No stored module interfaces in {path}")
    return result


def compare(left, right):
    differences = [key for key in sorted(left.keys() | right.keys())
                   if left.get(key) != right.get(key)]
    for table, module in differences[:20]:
        a, b = left.get((table, module)), right.get((table, module))
        if a is None or b is None:
            detail = "missing from " + ("first" if a is None else "second")
        else:
            offset = next((i for i, (x, y) in enumerate(zip(a, b)) if x != y),
                          min(len(a), len(b)))
            detail = f"first difference at byte {offset}; lengths {len(a)}, {len(b)}"
        print(f"{table}/{module}: {detail}")
    print(f"{len(differences)} differing entries out of {len(left.keys() | right.keys())}")
    return not differences


def clean_builds(binary):
    package = ROOT / "tests/tests"
    env = dict(os.environ, RESCRIPT_RUNTIME=str(ROOT / "packages/@rescript/runtime"))
    snapshots = []
    # Reuse the source path: absolute filenames are meaningful interface data.
    for workers in (1, 8, 8):
        env["RAYON_NUM_THREADS"] = str(workers)
        for command in ("clean", "build"):
            subprocess.run([str(binary), command], cwd=package, env=env,
                           check=True, timeout=300)
        snapshots.append(read_interfaces(package / "lib/rescript/rescript.sqlite"))
    print("1 worker versus 8 workers:")
    different_workers = compare(snapshots[0], snapshots[1])
    print("Two consecutive 8-worker builds:")
    same_workers = compare(snapshots[1], snapshots[2])
    return different_workers and same_workers


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("directories", nargs="*")
    parser.add_argument("--rescript", type=Path,
                        default=Path(os.environ.get("RESCRIPT_EXECUTABLE",
                                                    ROOT / "rewatch/target/release/rescript")))
    args = parser.parse_args()
    if len(args.directories) == 2:
        success = compare(*(read_interfaces(path) for path in args.directories))
    elif not args.directories:
        success = clean_builds(args.rescript.resolve())
    else:
        parser.error("supply both build directories, or neither to run clean builds")
    raise SystemExit(0 if success else 1)


if __name__ == "__main__":
    main()
