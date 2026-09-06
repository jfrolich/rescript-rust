#!/usr/bin/env python3
"""Fixed 56-build Env ownership cohort. Timing modes require parent approval."""
import hashlib
import json
import os
from pathlib import Path
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
    assert approval["approved_runner_head"] == command("git", "rev-parse", "HEAD")
    assert approval["approved_runner_sha256"] == m.sha(Path(__file__))
    assert approval["allow_timed_full_builds"] is True
    assert os.environ.get("ENV_OWNERSHIP_HEAVY_LOCK") == "1"


def capture_inventory():
    return {"inputs": m.inputs(), "source": source_inventory(), "symlinks": links()}


def compare_inventory(before, current, expect_metadata):
    metadata = generated_metadata_paths()
    baseline_metadata = metadata & before["inputs"].keys()
    current_metadata = metadata & current["inputs"].keys()
    changed = {path for path in before["inputs"].keys() | current["inputs"].keys() if before["inputs"].get(path) != current["inputs"].get(path)}
    report = {"before_count":len(before["inputs"]),"current_count":len(current["inputs"]),"baseline_metadata_present":sorted(baseline_metadata),"current_metadata_present":sorted(current_metadata),"expected_metadata_present":sorted(metadata if expect_metadata else set()),"unexpected":sorted(changed-metadata),"source_equal":before["source"]==current["source"],"symlinks_equal":before["symlinks"]==current["symlinks"]}
    report["valid"] = not baseline_metadata and current_metadata == (metadata if expect_metadata else set()) and not report["unexpected"] and report["source_equal"] and report["symlinks_equal"]
    return report


def verify_inventory_state(label, expect_metadata):
    before=json.loads((m.D/"inventory-before.json").read_text());current=capture_inventory()
    snapshot=m.D/f"inventory-{label}.json";report_path=m.D/f"inventory-verification-{label}.json"
    assert not snapshot.exists() and not report_path.exists()
    snapshot.write_text(json.dumps(current,sort_keys=True));report=compare_inventory(before,current,expect_metadata);report_path.write_text(json.dumps(report,indent=2))
    assert report["valid"],"Input/source/symlink drift; preserve evidence and stop"
    return report


def parse_required_metrics(text):
    import re
    metrics={}
    for line in text.splitlines():
        match=re.match(r"\s*(user|sys|real)\s+([\d.]+)$",line)
        if match: metrics[match.group(1)]=float(match.group(2))
        for key in ["maximum resident set size","instructions retired","cycles elapsed","peak memory footprint"]:
            if line.strip().endswith(key):metrics[key]=int(line.split()[0])
    missing=sorted({"real","user","sys","maximum resident set size","instructions retired","cycles elapsed"}-metrics.keys())
    if missing:raise RuntimeError(f"Missing required /usr/bin/time metrics: {missing}")
    return metrics


def verify_ordered_rows(plan,screens,rows):
    expected_screen=[tuple(row) for row in plan["screen_order"]]
    expected_runs=[("paired",row[0],row[2],row[3],row[1]) for row in plan["paired_order"]]+[("historical",row[0],row[1],row[2],row[3]) for row in plan["historical_order"]]
    actual_screen=[(row["variant"],row["workers"],row["repetition"]) for row in screens]
    actual_runs=[(row["stage"],row["pair"],row["position"],row["variant"],row["workers"]) for row in rows]
    if actual_screen!=expected_screen or actual_runs!=expected_runs:raise RuntimeError("Recorded cohort order differs from fixed plan")


def append_screen_row(row):
    with (m.D / "screen-runs.jsonl").open("a") as output:
        output.write(json.dumps(row) + "\n")
    print(json.dumps(row), flush=True)


def validate_screen_slot(variant, workers, repetition):
    if variant not in ("D", "C") or workers not in (1, 12) or repetition not in (1, 2):
        raise RuntimeError("Screen child is outside the fixed plan")
    if not (m.D / "inventory-before.json").is_file():
        raise RuntimeError("Frozen baseline is required before a screen child")
    return f"screen-{variant}-w{workers}-{repetition}"


def run_screen_process(process_command, env, prefix):
    import time
    prefix = Path(prefix)
    started_path = Path(str(prefix) + ".started.json")
    process_path = Path(str(prefix) + ".process.json")
    stdout_path = Path(str(prefix) + ".stdout")
    stderr_path = Path(str(prefix) + ".stderr")
    for path in (started_path, process_path, stdout_path, stderr_path):
        if path.exists():
            raise RuntimeError(f"Screen slot already started: {path}")
    started_path.write_text(json.dumps({
        "command": process_command,
        "load_before": os.getloadavg(),
        "perf_counter_ns_before": time.perf_counter_ns(),
    }, indent=2))
    start = time.perf_counter_ns()
    process = None
    error = None
    # Open durable streams before launch. This process remains in the outer
    # bounded Hyperfine group, so a driver timeout kills every descendant while
    # preserving output already written to these files.
    with stdout_path.open("wb") as stdout, stderr_path.open("wb") as stderr:
        try:
            process = subprocess.Popen(process_command, env=env, stdout=stdout, stderr=stderr)
            process.wait()
        except BaseException as exc:
            error = exc
    row = {
        "command": process_command,
        "wall_ns": time.perf_counter_ns() - start,
        "exit": process.returncode if process else None,
        "timeout": False,
        "error": repr(error) if error else None,
    }
    process_path.write_text(json.dumps(row, indent=2))
    if row["exit"] != 0 or row["error"]:
        raise RuntimeError("Screen child failed")
    return row


def screen_child(variant, workers, repetition):
    name = validate_screen_slot(variant, workers, repetition)
    run_screen_process(
        ["/usr/bin/time", "-lp"] + m.command(variant),
        m.env(variant, workers),
        m.D / f"logs/{name}-build",
    )


def finalize_screen(variant, workers, repetition, driver):
    name = validate_screen_slot(variant, workers, repetition)
    row = {
        "stage": "screen", "variant": variant, "workers": workers,
        "repetition": repetition, "driver": driver,
    }
    try:
        if driver.get("exit") != 0 or driver.get("timeout") or driver.get("error"):
            raise RuntimeError(f"Hyperfine driver failed; preserve {name}")
        process_path = m.D / f"logs/{name}-build.process.json"
        if not process_path.is_file():
            raise RuntimeError(f"Screen child record missing; preserve partial streams for {name}")
        row.update(json.loads(process_path.read_text()))
        stdout_path = m.D / f"logs/{name}-build.stdout"
        stderr_path = m.D / f"logs/{name}-build.stderr"
        text = stdout_path.read_text(errors="replace") + stderr_path.read_text(errors="replace")
        row.update(parse_required_metrics(text))
        if row.get("exit") != 0 or row.get("timeout") or row.get("error"):
            raise RuntimeError(f"Screen build failed; preserve {name}")
        count, digest, manifest = m.outputs()
        (m.D / f"{name}-js.json").write_text(json.dumps(manifest, sort_keys=True))
        row.update(
            js_count=count, js_sha256=digest,
            compiled_3248="Compiled 3248 modules" in text,
        )
        if count != 5048 or digest != EXPECTED_OUTPUT or not row["compiled_3248"]:
            raise RuntimeError(f"Screen output mismatch; preserve {name}")
    except BaseException as exc:
        row["attempt_error"] = repr(exc)
        raise
    finally:
        append_screen_row(row)


def record_screen_setup_failure(variant, workers, repetition, phase, details, exc):
    row = {
        "stage": "screen", "variant": variant, "workers": workers,
        "repetition": repetition, "phase": phase, phase: details,
        "attempt_error": repr(exc),
    }
    append_screen_row(row)


def restore_tella():
    restore_backups(m.T, m.D / "backups", json.loads((m.D / "backups.json").read_text()), m.sha)


def timed_attempt(stage,pair,position,variant,workers):
    name=f"{stage}-{pair}-{position}-{variant}-w{workers}";row={"stage":stage,"pair":pair,"position":position,"variant":variant,"workers":workers,"phase":"clean"}
    try:
        clean,_=bounded([str(m.D/f"bin/rescript-{variant}"),"clean",str(m.WEB)],m.env(variant,workers),m.D/f"logs/{name}-clean",120);row["clean"]=clean
        if clean["exit"]!=0 or clean["timeout"] or clean["error"]:raise RuntimeError(f"Clean failed; preserve {name}")
        row["phase"]="build";row["load_before"]=os.getloadavg();process,log=bounded(["/usr/bin/time","-lp"]+m.command(variant),m.env(variant,workers),m.D/f"logs/{name}",600);row.update(process)
        text=log.decode(errors="replace");row.update(parse_required_metrics(text))
        if process["exit"]!=0 or process["timeout"] or process["error"]:raise RuntimeError(f"Build failed; preserve {name}")
        row["phase"]="outputs";count,digest,manifest=m.outputs();(m.D/f"{name}-js.json").write_text(json.dumps(manifest,sort_keys=True));row.update(js_count=count,js_sha256=digest,compiled_3248="Compiled 3248 modules" in text)
        if count!=5048 or digest!=EXPECTED_OUTPUT or not row["compiled_3248"]:raise RuntimeError(f"Output mismatch; preserve {name}")
        row["phase"]="complete"
    except BaseException as exc:row["attempt_error"]=repr(exc);raise
    finally:
        with (m.D/"runs.jsonl").open("a") as output:output.write(json.dumps(row)+"\n")
        print(json.dumps(row),flush=True)



def main():
    if len(sys.argv)<2:raise SystemExit("Fixed runner mode required")
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
        before=capture_inventory();assert compare_inventory(before,before,False)["valid"]
        (m.D/"inventory-before.json").write_text(json.dumps(before,sort_keys=True))
    elif mode == "screen-child":
        require_approval()
        verify_binaries()
        screen_child(sys.argv[2], int(sys.argv[3]), int(sys.argv[4]))
    elif mode == "screen":
        require_approval()
        verify_binaries()
        assert (m.D/"inventory-before.json").is_file() and not (m.D/"screen-runs.jsonl").exists();verify_inventory_state("pre-screen",False)
        def body():
            for workers in [1, 12]:
                for variant in ["D", "C"]:
                    for repetition in [1, 2]:
                        name = validate_screen_slot(variant, workers, repetition)
                        clean = None
                        try:
                            clean, _ = bounded(
                                [str(m.D / f"bin/rescript-{variant}"), "clean", str(m.WEB)],
                                m.env(variant, workers), m.D / f"logs/{name}-clean", 120,
                            )
                            if clean["exit"] != 0 or clean["timeout"] or clean["error"]:
                                raise RuntimeError(f"Clean failed; preserve {name}")
                        except BaseException as exc:
                            record_screen_setup_failure(variant, workers, repetition, "clean", clean, exc)
                            raise
                        hyperfine = [
                            "hyperfine", "--runs", "1", "--warmup", "0",
                            "--export-json", str(m.D / f"{name}-hyperfine.json"),
                            f"python3 {Path(__file__).resolve()} screen-child {variant} {workers} {repetition}",
                        ]
                        driver = None
                        try:
                            driver, _ = bounded(
                                hyperfine, m.env(variant, workers),
                                m.D / f"logs/{name}-hyperfine", 600,
                            )
                        except BaseException as exc:
                            record_screen_setup_failure(variant, workers, repetition, "driver", driver, exc)
                            raise
                        finalize_screen(variant, workers, repetition, driver)
        guarded(body,lambda:verify_inventory_state("after-screen",True),restore_tella,m.D/"screen-failure.json")
    elif mode == "paired":
        require_approval()
        verify_binaries()
        assert len((m.D / "screen-runs.jsonl").read_text().splitlines()) == 8
        assert not (m.D/"runs.jsonl").exists();verify_inventory_state("pre-paired",True)
        def body():
            for pair in range(1, 9):
                for workers in ([1, 12] if pair % 2 else [12, 1]):
                    for position, variant in enumerate((["D", "C"] if pair % 2 else ["C", "D"]), 1):
                        timed_attempt("paired", pair, position, variant, workers)
        guarded(body, lambda: verify_inventory_state("after-paired",True), restore_tella, m.D / "paired-failure.json")
    elif mode == "historical":
        require_approval()
        verify_binaries()
        rows = [json.loads(line) for line in (m.D / "runs.jsonl").read_text().splitlines()]
        assert len(rows)==32 and all(row["stage"]=="paired" for row in rows);verify_inventory_state("pre-historical",True)
        def body():
            for pair in range(1, 9):
                for position, variant in enumerate((["A", "C"] if pair % 2 else ["C", "A"]), 1):
                    timed_attempt("historical", pair, position, variant, 12)
        guarded(body, lambda: verify_inventory_state("after-historical",True), restore_tella, m.D / "historical-failure.json")
    elif mode == "verify-final":
        require_approval()
        verify_binaries()
        screens = [json.loads(line) for line in (m.D / "screen-runs.jsonl").read_text().splitlines()]
        rows = [json.loads(line) for line in (m.D / "runs.jsonl").read_text().splitlines()]
        assert len(screens)==8 and len(rows)==48;verify_ordered_rows(json.loads((m.D/"plan.json").read_text()),screens,rows)
        assert all(row["js_count"]==5048 and row["js_sha256"]==EXPECTED_OUTPUT and row["compiled_3248"] for row in screens+rows)
        required = {"real", "user", "sys", "maximum resident set size", "instructions retired", "cycles elapsed"}
        assert all(required <= row.keys() for row in screens + rows)
        assert all(not row.get("attempt_error") and row.get("exit") == 0 and not row.get("timeout") and not row.get("error") for row in screens + rows)
        assert all(screen.get("driver", {}).get("exit") == 0 and not screen["driver"].get("timeout") and not screen["driver"].get("error") for screen in screens)
        verify_inventory_state("final",True)
    else:
        raise SystemExit("Unknown mode; refusing to run outside the fixed 56-build plan")

if __name__=="__main__":
    main()
