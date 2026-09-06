#!/usr/bin/env python3
"""Fixed 56-build Env ownership cohort. Timing modes require parent approval."""
import hashlib
import json
import os
from pathlib import Path
import runpy
import shutil
import subprocess
import sys

os.environ["MEASUREMENT_DIR"] = "/Users/jake/.opensession/artifacts/rescript-performance-20260905/env-ownership/candidate-timing"
import measurement_rebaseline as m
from env_ownership_runner import bounded, guarded, restore_backups

ROOT = Path("/Users/jake/checkouts/rescript-rust")
ARTIFACTS = Path("/Users/jake/.opensession/artifacts/rescript-performance-20260905")
ENV_ROOT = ARTIFACTS / "env-ownership"
CONTROL = ARTIFACTS / "architecture-round" / "bin"
CANDIDATE = ENV_ROOT / "candidate" / "bin"
APPROVAL = m.D / "parent-timing-approval.json"
EXPECTED_OUTPUT = "1cacd5cfb9604df30e204f3d8a419e4e433afa96e3f81d23ea54764af86f1d49"
EXPECTED_BINARIES = {
    "bsc-A": "7c39a09c163088ac7db372ff8139fa62e2a9b76960eafccfe4ed2385f9172ca0",
    "rescript-A": "0187abee145aebdcc1b43db8d60e28ed851840dd3c75397959f64223420c4332",
    "bsc-D": "a5ed9a622e3b787a8dae0cb5228a5eb5717849314d0af40c05f9689c6a6788af",
    "rescript-D": "5fe8158df5d3201d4cf07fd962cf61b22edf63874b03bfd5328e1fe16f47c3c4",
    "bsc-C": "88c8a9338abefba9681cc4f4d7d39228a28b47039ee7928ac2f81f9b26b0f4fe",
    "rescript-C": "5e149f9e75826404726fca8e4701f0525fca85c4f77cd17b6110d58df3dd3549",
}
SOURCES = {
    "A": "fb4497659fdf53b491fc5480d6588ec800e92e0a",
    "D": "5dc38ba2154e158d43436ada2142a13eef9f2c8c",
    "C-production": "b54d194c15b2e4c28ec81895db937a1b8c2c8536",
    "C-release-build": "57ff05309100737bd034b113668811844f10d8bb",
}
EXPECTED_PLAN = {
    "screen": 8,
    "paired": 32,
    "historical": 16,
    "total": 56,
}
assert Path.cwd() == ROOT and m.ROOT == ROOT


def command(*args):
    return subprocess.check_output(args).decode().strip()


def source_inventory():
    return {
        path: m.sha(ROOT / path)
        for path in command("git", "ls-files").splitlines()
        if (ROOT / path).is_file()
    }


def links():
    result = {}
    seen = set()
    for root in [m.T / "node_modules", m.WEB / "node_modules", ROOT / "packages/@rescript/runtime"]:
        for base, dirs, files in os.walk(root, followlinks=True):
            real = os.path.realpath(base)
            if real in seen:
                dirs[:] = []
                continue
            seen.add(real)
            dirs[:] = [name for name in dirs if name not in (".git", ".cache")]
            for name in dirs + files:
                path = Path(base) / name
                if path.is_symlink():
                    result[str(path)] = {"link": os.readlink(path), "resolved": str(path.resolve())}
    return result


def generated_metadata_paths():
    packages = [
        "@rescript/react", "@rescript/belt", "@jfrolich/ppx-spice",
        "rescript-debounce-react", "rescript-nodejs", "rescript-debounce",
        "bs-css", "bs-css-dom", "@tella-fusion/webapp",
        "@tella-fusion/webapp/packages/tella-std",
        "@tella-fusion/webapp/node_modules/rescript-webapi",
    ]
    paths = {str(m.T / "node_modules" / package / "lib/bs/compiler-info.json") for package in packages}
    paths.add(str(m.T / "node_modules/@tella-fusion/webapp/lib/bs/.sourcedirs.json"))
    return paths


def verify_binaries():
    hashes = json.loads((m.D / "binary-hashes.json").read_text())
    assert hashes == EXPECTED_BINARIES
    for name, digest in hashes.items():
        path = m.D / "bin" / name
        assert path.is_file() and m.sha(path) == digest
        assert not path.stat().st_mode & 0o222


def require_approval():
    approval = json.loads(APPROVAL.read_text())
    assert approval["approved_plan_sha256"] == m.sha(m.D / "plan.json")
    assert approval["approved_binary_sha256"] == m.sha(m.D / "binary-provenance.json")
    assert approval["approved_prep_head"] == command("git", "rev-parse", "HEAD")
    assert approval["allow_timed_full_builds"] is True
    assert os.environ.get("ENV_OWNERSHIP_HEAVY_LOCK") == "1"


def write_inventory(label):
    payload = {"inputs": m.inputs(), "source": source_inventory(), "symlinks": links()}
    path = m.D / f"inventory-{label}.json"
    assert not path.exists()
    path.write_text(json.dumps(payload, sort_keys=True))
    return payload


def verify_inventory(label):
    before = json.loads((m.D / "inventory-before.json").read_text())
    after = write_inventory(label)
    changed = sorted(
        path
        for path in before["inputs"].keys() | after["inputs"].keys()
        if before["inputs"].get(path) != after["inputs"].get(path)
    )
    allowed = generated_metadata_paths()
    report = {
        "before_count": len(before["inputs"]),
        "after_count": len(after["inputs"]),
        "changed": changed,
        "generated_metadata": [path for path in changed if path in allowed],
        "unexpected": [path for path in changed if path not in allowed],
        "source_equal": before["source"] == after["source"],
        "symlinks_equal": before["symlinks"] == after["symlinks"],
    }
    output = m.D / f"inventory-verification-{label}.json"
    output.write_text(json.dumps(report, indent=2))
    assert not report["unexpected"] and report["source_equal"] and report["symlinks_equal"]


def validate_screen(variant, workers):
    require_approval()
    verify_binaries()
    assert os.environ.get("ENV_OWNERSHIP_HEAVY_LOCK") == "1"
    rows_path = m.D / "screen-runs.jsonl"
    rows = [json.loads(line) for line in rows_path.read_text().splitlines()] if rows_path.exists() else []
    repetition = 1 + sum(row["variant"] == variant and row["workers"] == workers for row in rows)
    assert repetition <= 2
    current = m.D / f"logs/screen-{variant}-w{workers}-current.log"
    saved = m.D / f"logs/screen-{variant}-w{workers}-{repetition}.log"
    assert not saved.exists()
    saved.write_bytes(current.read_bytes())
    count, digest, manifest = m.outputs()
    manifest_path = m.D / f"screen-{variant}-w{workers}-{repetition}-js.json"
    manifest_path.write_text(json.dumps(manifest, sort_keys=True))
    text = current.read_text(errors="replace")
    metrics = {}
    for line in text.splitlines():
        import re
        match = re.match(r"\s*(user|sys|real)\s+([\d.]+)$", line)
        if match:
            metrics[match.group(1)] = float(match.group(2))
        for key in ["maximum resident set size", "instructions retired", "cycles elapsed", "peak memory footprint"]:
            if line.strip().endswith(key):
                metrics[key] = int(line.split()[0])
    row = {
        "stage": "screen", "variant": variant, "workers": workers,
        "repetition": repetition, "exit": 0, "load_after": os.getloadavg(),
        "js_count": count, "js_sha256": digest,
        "compiled_3248": "Compiled 3248 modules" in text, **metrics,
    }
    with rows_path.open("a") as output:
        output.write(json.dumps(row) + "\n")
    assert count == 5048 and digest == EXPECTED_OUTPUT and row["compiled_3248"]


def restore_tella():
    restore_backups(m.T, m.D / "backups", json.loads((m.D / "backups.json").read_text()), m.sha)


def timed_attempt(stage, pair, position, variant, workers):
    name = f"{stage}-{pair}-{position}-{variant}-w{workers}"
    clean, _ = bounded(
        [str(m.D / f"bin/rescript-{variant}"), "clean", str(m.WEB)],
        m.env(variant, workers), m.D / f"logs/{name}-clean", 120,
    )
    if clean["exit"] != 0 or clean["timeout"] or clean["error"]:
        raise RuntimeError(f"Clean failed; preserve {name}")
    load = os.getloadavg()
    process, log = bounded(
        ["/usr/bin/time", "-lp"] + m.command(variant),
        m.env(variant, workers), m.D / f"logs/{name}", 600,
    )
    text = log.decode(errors="replace")
    metrics = {}
    for line in text.splitlines():
        import re
        match = re.match(r"\s*(user|sys|real)\s+([\d.]+)$", line)
        if match:
            metrics[match.group(1)] = float(match.group(2))
        for key in ["maximum resident set size", "instructions retired", "cycles elapsed", "peak memory footprint"]:
            if line.strip().endswith(key):
                metrics[key] = int(line.split()[0])
    count, digest, manifest = m.outputs()
    (m.D / f"{name}-js.json").write_text(json.dumps(manifest, sort_keys=True))
    row = {
        "stage": stage, "pair": pair, "position": position, "variant": variant,
        "workers": workers, "load": load, "compiled_3248": "Compiled 3248 modules" in text,
        "js_count": count, "js_sha256": digest, **process, **metrics,
    }
    with (m.D / "runs.jsonl").open("a") as output:
        output.write(json.dumps(row) + "\n")
    print(json.dumps(row), flush=True)
    if process["exit"] != 0 or process["timeout"] or process["error"]:
        raise RuntimeError(f"Build failed; preserve {name}")
    if count != 5048 or digest != EXPECTED_OUTPUT or not row["compiled_3248"]:
        raise RuntimeError(f"Output mismatch; preserve {name}")


mode = sys.argv[1]
if mode == "prepare":
    assert not m.D.exists()
    (m.D / "bin").mkdir(parents=True)
    (m.D / "logs").mkdir()
    sources = {
        "bsc-A": CONTROL / "bsc-A", "rescript-A": CONTROL / "rescript-A",
        "bsc-D": CONTROL / "bsc-D", "rescript-D": CONTROL / "rescript-D",
        "bsc-C": CANDIDATE / "bsc", "rescript-C": CANDIDATE / "rescript",
    }
    for name, source in sources.items():
        assert m.sha(source) == EXPECTED_BINARIES[name]
        shutil.copy2(source, m.D / "bin" / name)
        (m.D / "bin" / name).chmod(0o555)
    (m.D / "binary-hashes.json").write_text(json.dumps(EXPECTED_BINARIES, indent=2))
    binary_provenance = {
        "sources": SOURCES,
        "pairs": {
            "A": ["bsc-A", "rescript-A"],
            "D": ["bsc-D", "rescript-D"],
            "C": ["bsc-C", "rescript-C"],
        },
        "candidate_release_build": {
            "head": SOURCES["C-release-build"],
            "commands": [
                ["cargo", "build", "--locked", "--manifest-path", "compiler-rust/Cargo.toml", "--release"],
                ["cargo", "build", "--locked", "--manifest-path", "rewatch/Cargo.toml", "--release"],
            ],
            "RUSTFLAGS": None,
            "features": "default",
        },
        "ordinary_release_bsc_excluded": {
            "sha256": "7f3e605c37473be2d1b172930a21eb95a9b7a2f007ae24cecaca7d52fbd6f1ce",
            "reason": "Rewritten by cargo test --release at test-only head 0e448cb49; not the coherent release-build artifact pair.",
        },
        "hashes": EXPECTED_BINARIES,
    }
    (m.D / "binary-provenance.json").write_text(json.dumps(binary_provenance, indent=2))
    plan = {
        "counts": EXPECTED_PLAN,
        "screen_order": [[variant, workers, repetition] for workers in [1, 12] for variant in ["D", "C"] for repetition in [1, 2]],
        "paired_order": [
            [pair, workers, position, variant]
            for pair in range(1, 9)
            for workers in ([1, 12] if pair % 2 else [12, 1])
            for position, variant in enumerate((["D", "C"] if pair % 2 else ["C", "D"]), 1)
        ],
        "historical_order": [
            [pair, position, variant, 12]
            for pair in range(1, 9)
            for position, variant in enumerate((["A", "C"] if pair % 2 else ["C", "A"]), 1)
        ],
        "output": {"modules": 3248, "js_files": 5048, "js_sha256": EXPECTED_OUTPUT},
        "bounds_seconds": {"clean": 120, "build": 600},
        "screens": "Four separate hyperfine invocations, two runs per D/C x w1/w12 cell.",
        "lock": "/tmp/rescript-tella-heavy.lock",
        "no_extensions_exclusions_pooling_or_retries": True,
    }
    assert len(plan["screen_order"]) == 8 and len(plan["paired_order"]) == 32 and len(plan["historical_order"]) == 16
    (m.D / "plan.json").write_text(json.dumps(plan, indent=2))
    runtime_setup = json.loads((ENV_ROOT / "runtime-mirror-setup.json").read_text())
    assert len(runtime_setup) == 156
    for row in runtime_setup:
        assert m.sha(Path(row["source"])) == row["sha256"]
        assert m.sha(Path(row["mirror"])) == row["sha256"]
    backups = json.loads((ARTIFACTS / "architecture-round/backups.json").read_text())
    assert len(backups) == 18
    assert set(command("git", "-C", str(m.T), "diff", "--name-only").splitlines()) == set(backups)
    for path, digest in backups.items():
        source = m.T / path
        assert m.sha(source) == digest
        destination = m.D / "backups" / path
        destination.parent.mkdir(parents=True, exist_ok=True)
        shutil.copy2(source, destination)
    (m.D / "backups.json").write_text(json.dumps(backups, sort_keys=True))
    provenance = {
        "prep_head": command("git", "rev-parse", "HEAD"),
        "branch": command("git", "branch", "--show-current"),
        "rustc": command("/Users/jake/.cargo/bin/rustc", "-Vv"),
        "cargo": command("/Users/jake/.cargo/bin/cargo", "-V"),
        "node": command("node", "-v"),
        "runtime": str(ROOT / "packages/@rescript/runtime"),
        "runtime_mirror_entries_verified": len(runtime_setup),
        "tella_head": command("git", "-C", str(m.T), "rev-parse", "HEAD"),
        "tella_status": command("git", "-C", str(m.T), "status", "--porcelain"),
        "RUSTFLAGS": None,
        "features": "default",
        "commands": {variant: m.command(variant) for variant in ["A", "D", "C"]},
        "environment": {
            f"{variant}-w{workers}": {
                key: m.env(variant, workers)[key]
                for key in ["RESCRIPT_BSC_EXE", "RESCRIPT_RUNTIME", "RAYON_NUM_THREADS"]
            }
            for variant in ["A", "D", "C"] for workers in [1, 12]
        },
    }
    (m.D / "provenance.json").write_text(json.dumps(provenance, indent=2))
    print(json.dumps({"plan_sha256": m.sha(m.D / "plan.json"), "binary_provenance_sha256": m.sha(m.D / "binary-provenance.json"), "prep_head": provenance["prep_head"]}))
elif mode == "freeze-inputs":
    require_approval()
    verify_binaries()
    assert not (m.D / "inventory-before.json").exists()
    clean, _ = bounded([str(m.D / "bin/rescript-D"), "clean", str(m.WEB)], m.env("D", 1), m.D / "logs/freeze-input-clean", 120)
    assert clean["exit"] == 0 and not clean["timeout"] and clean["error"] is None
    write_inventory("before")
elif mode == "screen-validate":
    validate_screen(sys.argv[2], int(sys.argv[3]))
elif mode == "screen":
    require_approval()
    verify_binaries()
    assert (m.D / "inventory-before.json").is_file()
    assert not (m.D / "screen-runs.jsonl").exists()
    def body():
        for workers in [1, 12]:
            for variant in ["D", "C"]:
                command_text = "/usr/bin/time -lp " + " ".join(m.command(variant)) + f" > {m.D}/logs/screen-{variant}-w{workers}-current.log 2>&1"
                hyperfine = [
                    "hyperfine", "--runs", "2",
                    "--prepare", f"{m.D}/bin/rescript-{variant} clean {m.WEB}",
                    "--conclude", f"python3 {Path(__file__).resolve()} screen-validate {variant} {workers}",
                    "--export-json", str(m.D / f"screen-{variant}-w{workers}.json"), command_text,
                ]
                result, _ = bounded(hyperfine, m.env(variant, workers), m.D / f"logs/screen-{variant}-w{workers}-driver", 600)
                assert result["exit"] == 0 and not result["timeout"] and result["error"] is None
    guarded(body, lambda: verify_inventory("after-screen"), restore_tella, m.D / "screen-failure.json")
elif mode == "paired":
    require_approval()
    verify_binaries()
    assert len((m.D / "screen-runs.jsonl").read_text().splitlines()) == 8
    assert not (m.D / "runs.jsonl").exists()
    def body():
        for pair in range(1, 9):
            for workers in ([1, 12] if pair % 2 else [12, 1]):
                for position, variant in enumerate((["D", "C"] if pair % 2 else ["C", "D"]), 1):
                    timed_attempt("paired", pair, position, variant, workers)
    guarded(body, lambda: verify_inventory("after-paired"), restore_tella, m.D / "paired-failure.json")
elif mode == "historical":
    require_approval()
    verify_binaries()
    rows = [json.loads(line) for line in (m.D / "runs.jsonl").read_text().splitlines()]
    assert len(rows) == 32 and all(row["stage"] == "paired" for row in rows)
    def body():
        for pair in range(1, 9):
            for position, variant in enumerate((["A", "C"] if pair % 2 else ["C", "A"]), 1):
                timed_attempt("historical", pair, position, variant, 12)
    guarded(body, lambda: verify_inventory("after-historical"), restore_tella, m.D / "historical-failure.json")
elif mode == "verify-final":
    require_approval()
    verify_binaries()
    screens = [json.loads(line) for line in (m.D / "screen-runs.jsonl").read_text().splitlines()]
    rows = [json.loads(line) for line in (m.D / "runs.jsonl").read_text().splitlines()]
    assert len(screens) == 8 and len(rows) == 48
    assert sum(row["stage"] == "paired" for row in rows) == 32
    assert sum(row["stage"] == "historical" for row in rows) == 16
    assert all(row["js_count"] == 5048 and row["js_sha256"] == EXPECTED_OUTPUT and row["compiled_3248"] for row in screens + rows)
    verify_inventory("final")
else:
    runpy.run_path(str(Path(__file__).with_name("measurement_rebaseline.py")), run_name="__main__")
