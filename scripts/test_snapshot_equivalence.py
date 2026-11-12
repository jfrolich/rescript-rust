#!/usr/bin/env python3
"""Snapshot/source equivalence, at identical logical paths in separate result trees.

A package copied into two different absolute directories has different interface
hashes by design. Build at one stable path, move that completed tree aside, then
build the other there. This compares raw stored core bytes, not a lossy dump.
Belt's core equivalence for all modules is additionally asserted by the producer.
"""
import json
import os
from pathlib import Path
import re
import shutil
import sqlite3
import subprocess
import sys
import tempfile

ROOT = Path(__file__).resolve().parent.parent
BINARY = Path(os.environ.get("RESCRIPT_EXECUTABLE", ROOT / "rewatch/target/release/rescript")).resolve()


def resolve(package, name):
    for parent in (package, *package.parents, ROOT):
        candidate = parent / "node_modules" / name
        if (candidate / "rescript.json").is_file():
            return candidate.resolve()
    raise RuntimeError(f"cannot resolve {name} for {package.name}")


def stage(source, destination, seen=None, include_dev=True):
    seen = set() if seen is None else seen
    shutil.copytree(source, destination, ignore=shutil.ignore_patterns(
        "node_modules", "lib", ".git", "*.mjs", "*.cjs", "*.gen.ts", "*.gen.tsx"))
    config = json.loads((source / "rescript.json").read_text())
    for dependency in config.get("dependencies", []) + (config.get("dev-dependencies", []) if include_dev else []):
        name = dependency if isinstance(dependency, str) else dependency["name"]
        if name in seen:
            continue
        stage(resolve(source, name), destination / "node_modules" / name, seen | {name}, False)


def build(project, mode):
    env = dict(os.environ, RESCRIPT_RUNTIME=os.environ.get("RESCRIPT_RUNTIME", str(ROOT / "packages/@rescript/runtime")),
               RESCRIPT_SNAPSHOT=mode, RAYON_NUM_THREADS="1", NO_COLOR="1")
    env.pop("RESCRIPT_FULL_BUILD", None)
    env.pop("RESCRIPT_COMPILER_COUNTERS", None)
    result = subprocess.run([str(BINARY), "build", str(project)], env=env,
                            capture_output=True, timeout=10)
    if result.returncode:
        raise RuntimeError(result.stdout.decode(errors="replace") + result.stderr.decode(errors="replace"))
    return result.stdout.decode(), result.stderr


def javascript(project):
    return {str(p.relative_to(project)): p.read_bytes() for p in project.rglob("*")
            if p.is_file() and p.suffix in {".js", ".mjs", ".cjs", ".ts", ".tsx"}}


def records(project):
    result = {}
    for db in project.rglob("rescript.sqlite"):
        # Belt's unused cores deliberately stay embedded, not duplicated in its
        # database. All compiled dependents' entries must be exactly identical.
        if "node_modules/@rescript/belt/" in str(db.relative_to(project)):
            continue
        with sqlite3.connect(db) as connection:
            for table, columns in [
                ("interfaces", "module, data"), ("interface_extras", "module, data"),
                ("items", "module, data"), ("reads", "module, data"),
                ("modules", "module, implementation_warnings, interface_warnings, interface_digest, imports"),
            ]:
                result[(str(db.relative_to(project)), table)] = connection.execute(
                    f"SELECT {columns} FROM {table} ORDER BY module").fetchall()
    return result


def root_interfaces(project):
    with sqlite3.connect(project / "lib/rescript/rescript.sqlite") as connection:
        return connection.execute("SELECT module, hash, data FROM interfaces ORDER BY module").fetchall()


def check(source):
    with tempfile.TemporaryDirectory(prefix="snapshot-equivalence-") as temporary:
        base = Path(temporary)
        project = base / "project"
        stage(source, project)
        _, snapshot_diagnostics = build(project, "require")
        expected_js, expected_records = javascript(project), records(project)
        interfaces = root_interfaces(project)
        output, _ = build(project, "off")
        if root_interfaces(project) != interfaces:
            raise AssertionError(f"snapshot→source changed dependent interfaces: {source}")
        # No dependent may compile: only the 43 previously embedded Belt units.
        count = re.search(r"Compiled (\d+) modules?", output)
        if count and int(count[1]) not in (0, 43):
            raise AssertionError(f"snapshot→source recompiled dependents: {output}")
        project.rename(base / "snapshot")
        stage(source, project)
        _, source_diagnostics = build(project, "off")
        actual_js, actual_records = javascript(project), records(project)
        if expected_js != actual_js:
            changed = sorted(k for k in expected_js.keys() | actual_js.keys()
                             if expected_js.get(k) != actual_js.get(k))
            raise AssertionError(f"JavaScript differs: {changed[:20]}")
        if expected_records != actual_records:
            changed = [k for k in expected_records.keys() | actual_records.keys()
                       if expected_records.get(k) != actual_records.get(k)]
            raise AssertionError(f"stored entries differ: {changed}")
        if snapshot_diagnostics != source_diagnostics:
            raise AssertionError("diagnostics differ")
        interfaces = root_interfaces(project)
        output, _ = build(project, "require")
        if root_interfaces(project) != interfaces or re.search(r"Compiled [1-9]", output):
            raise AssertionError(f"source→snapshot recompiled dependents: {output}")
        project.rename(base / "source")
        print(f"PASS {source.relative_to(ROOT) if source.is_relative_to(ROOT) else source.name}: "
              f"{len(expected_js)} JavaScript/TypeScript files; all dependent interface entries; both incremental directions")


def check_runtime_laziness():
    """One List consumer reaches three runtime interfaces, not all 113."""
    with tempfile.TemporaryDirectory(prefix="snapshot-one-module-") as temporary:
        project = Path(temporary)
        (project / "src").mkdir()
        (project / "src/Main.res").write_text("let value = list{1, 2, 3}->List.length\n")
        (project / "rescript.json").write_text(json.dumps({
            "name": "snapshot-one-module", "sources": ["src"],
            "package-specs": {"module": "esmodule", "in-source": True}, "suffix": ".mjs",
        }))
        env = dict(os.environ, RESCRIPT_RUNTIME=os.environ.get("RESCRIPT_RUNTIME", str(ROOT / "packages/@rescript/runtime")),
                   RESCRIPT_SNAPSHOT="require", RESCRIPT_COMPILER_COUNTERS="1", RAYON_NUM_THREADS="1")
        result = subprocess.run([str(BINARY), "build", str(project)], env=env,
                                capture_output=True, text=True, timeout=10)
        if result.returncode:
            raise AssertionError(result.stdout + result.stderr)
        decoded = re.search(r"snapshot_modules_decoded=(\d+)", result.stderr)
        if decoded is None or int(decoded[1]) != 3:
            raise AssertionError(f"expected three reached runtime interfaces: {result.stderr}")
        print("PASS snapshot-one-module: exactly 3 runtime interfaces decoded")


def main():
    if not BINARY.is_file():
        raise RuntimeError("build rewatch in release mode, or set RESCRIPT_EXECUTABLE")
    projects = [Path(p).resolve() for p in sys.argv[1:]] or [ROOT / "tests/belt_tests", ROOT / "tests/tests", ROOT / "rewatch/testrepo"]
    for project in projects:
        check(project)
    check_runtime_laziness()
    with tempfile.TemporaryDirectory(prefix="snapshot-matrix-") as temporary:
        fixture = Path(temporary)
        (fixture / "src").mkdir()
        (fixture / "src/Main.res").write_text("let size = Belt_Array.length([1, 2, 3])\n")
        (fixture / "node_modules/@rescript").mkdir(parents=True)
        (fixture / "node_modules/@rescript/belt").symlink_to(ROOT / "packages/@rescript/belt", target_is_directory=True)
        for in_source in (False, True):
            for esm, cjs in ((".mjs", ".cjs"), (".res.mjs", ".res.cjs")):
                specs = [{"module": "esmodule", "suffix": esm, "in-source": in_source},
                         {"module": "commonjs", "suffix": cjs, "in-source": in_source}]
                for selected in ([specs[0]], [specs[1]], specs):
                    (fixture / "rescript.json").write_text(json.dumps({
                        "name": "snapshot-config-matrix", "sources": ["src"],
                        "dependencies": ["@rescript/belt"], "package-specs": selected,
                        "jsx": {"version": 4, "module": "react", "preserve": True},
                        "experimental-features": {"LetUnwrap": True},
                        "gentypeconfig": {"language": "typescript"},
                    }))
                    print(f"configuration: in-source={in_source} suffixes={[s['suffix'] for s in selected]}")
                    check(fixture)


if __name__ == "__main__":
    main()
