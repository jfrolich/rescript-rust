#!/usr/bin/env python3
"""Owned-process capture for the type-payload comparison, not a build launcher."""
import contextlib
import json
import os
from pathlib import Path
import signal
import subprocess
import time
import uuid


class SupervisorInterrupted(RuntimeError):
    pass


def interrupt(signum, frame):
    raise SupervisorInterrupted(f"supervisor received signal {signum}")


@contextlib.contextmanager
def handle_interrupts():
    previous = {sig: signal.signal(sig, interrupt)
                for sig in (signal.SIGINT, signal.SIGTERM)}
    try:
        yield
    finally:
        for sig, handler in previous.items():
            signal.signal(sig, handler)


@contextlib.contextmanager
def cleanup_without_reentrant_interrupts():
    previous = {sig: signal.signal(sig, signal.SIG_IGN)
                for sig in (signal.SIGINT, signal.SIGTERM)}
    try:
        yield
    finally:
        for sig, handler in previous.items():
            signal.signal(sig, handler)


def publish(path, value):
    path = Path(path)
    pending = path.with_name(path.name + ".publishing-" + uuid.uuid4().hex)
    with pending.open("x") as stream:
        json.dump(value, stream, indent=2)
        stream.write("\n")
        stream.flush()
        os.fsync(stream.fileno())
    os.link(pending, path)
    pending.unlink()


def group_exists(group):
    try:
        os.killpg(group, 0)
        return True
    except ProcessLookupError:
        return False
    except PermissionError:
        # EPERM does not prove absence. Keep polling/reaping rather than
        # abandoning cleanup when a group is transitioning to termination.
        return True


def valid_group(group):
    if (not isinstance(group, int) or isinstance(group, bool)
            or group <= 1 or group == os.getpgrp()):
        raise ValueError(f"invalid owned group: {group!r}")


def capture(argv, prefix, *, env, timeout, token=None, children=(),
            term_grace=15.0, kill_grace=5.0):
    """Capture one owned group and token-bound nested build groups.

    `children` lists (pid-record, completion-record) paths written by inner
    supervisors. Their pid records must contain pgid, owner_group and this
    token. Allow inner supervisors time to reap before escalation, even when
    the outer leader has exited. Surviving descendants invalidate success.

    Normal wall_ns surrounds Popen/communicate only. Validation and publication
    are outside that measurement. Failed commands are never benchmark samples.
    """
    prefix = Path(prefix)
    children = tuple(children)
    if len({str(pair[0]) for pair in children}) != len(children):
        raise ValueError("duplicate nested process record")
    if list(prefix.parent.glob(prefix.name + ".*")):
        raise RuntimeError(f"process replay or partial artifacts: {prefix}")
    token = token or uuid.uuid4().hex
    publish(str(prefix) + ".started.json", {
        "argv": argv, "token": token, "owner_group": os.getpgrp(),
        "environment": {key: env.get(key) for key in
                        ("RESCRIPT_BSC_EXE", "RESCRIPT_RUNTIME", "RAYON_NUM_THREADS")},
        "load": os.getloadavg(),
    })
    proc = None
    stdout = stderr = b""
    error = None
    timed_out = False
    actions = []
    cleanup_errors = []
    nested = {}
    reaped_children = {}
    invalid_records = set()

    def discover_children():
        for pid_path, completion_path in children:
            pid_path, completion_path = Path(pid_path), Path(completion_path)
            if not pid_path.exists() or str(pid_path) in invalid_records:
                continue
            try:
                row = json.loads(pid_path.read_text())
                if row.get("token") != token or row.get("owner_group") != proc.pid:
                    raise ValueError("untrusted nested process owner/token")
                group = row["pgid"]
                valid_group(group)
                if group == proc.pid:
                    raise ValueError("nested group must differ from outer group")
                old = nested.get(str(pid_path))
                if old is not None and old != row:
                    raise ValueError("nested process record changed")
                nested[str(pid_path)] = row
                if completion_path.exists():
                    completion = json.loads(completion_path.read_text())
                    if (completion.get("token") != token
                            or completion.get("pgid") != group):
                        raise ValueError("untrusted nested completion")
                    reaped_children[str(pid_path)] = bool(
                        completion.get("leader_reaped")
                        and completion.get("group_absent"))
            except SupervisorInterrupted:
                raise
            except Exception as exc:
                invalid_records.add(str(pid_path))
                cleanup_errors.append(f"{pid_path}: {exc!r}")

    def live_groups():
        # Poll reaps our leader; its zombie must not keep cleanup waiting.
        proc.poll()
        groups = {proc.pid} | {row["pgid"] for row in nested.values()}
        return {group for group in groups if group_exists(group)}

    def send(group, sig):
        valid_group(group)
        try:
            os.killpg(group, sig)
            actions.append({"pgid": group, "signal": signal.Signals(sig).name})
        except ProcessLookupError:
            pass
        except OSError as exc:
            # Do not let a failed signal skip attempts to reap and record the
            # remaining groups. The caller must not restore while they live.
            cleanup_errors.append(f"signal {sig} to {group}: {exc!r}")

    wall_start = time.time_ns()
    started = time.perf_counter_ns()
    elapsed = None
    try:
        proc = subprocess.Popen(argv, env=env, stdout=subprocess.PIPE,
                                stderr=subprocess.PIPE, start_new_session=True)
        valid_group(proc.pid)
        if os.getpgid(proc.pid) != proc.pid:
            raise RuntimeError("new process did not establish its own group")
        publish(str(prefix) + ".pid.json", {
            "pid": proc.pid, "pgid": proc.pid, "token": token,
            "owner_group": os.getpgrp(),
        })
        stdout, stderr = proc.communicate(timeout=timeout)
        elapsed = time.perf_counter_ns() - started
        discover_children()
        if proc.returncode != 0:
            error = f"command exited {proc.returncode}"
        elif live_groups():
            error = "leader exited with surviving descendants"
        elif (len(nested) != len(children)
              or len(reaped_children) != len(children)
              or not all(reaped_children.values()) or cleanup_errors):
            error = "nested supervision evidence incomplete"
    except BaseException as exc:
        error = repr(exc)
        timed_out = isinstance(exc, subprocess.TimeoutExpired)
    finally:
        if elapsed is None:
            elapsed = time.perf_counter_ns() - started
        if proc is not None and error is not None:
            with cleanup_without_reentrant_interrupts():
                # The outer Python child receives TERM and reaps its own build.
                send(proc.pid, signal.SIGTERM)
                deadline = time.monotonic() + term_grace
                while time.monotonic() < deadline:
                    discover_children()
                    if not live_groups():
                        break
                    time.sleep(0.01)
                discover_children()
                for group in live_groups():
                    send(group, signal.SIGKILL)
                deadline = time.monotonic() + kill_grace
                while live_groups() and time.monotonic() < deadline:
                    time.sleep(0.01)
                if live_groups():
                    cleanup_errors.append(f"groups remain: {sorted(live_groups())}")
                try:
                    stdout, stderr = proc.communicate(timeout=kill_grace)
                except BaseException as exc:
                    cleanup_errors.append(f"reap/capture failed: {exc!r}")
                discover_children()
    result = {
        "argv": argv, "token": token, "pid": proc.pid if proc else None,
        "pgid": proc.pid if proc else None,
        "exit": proc.returncode if proc else None,
        "wall_ns": elapsed, "build_start_wall_ns": wall_start,
        "timeout": timed_out, "error": error, "cleanup": actions,
        "cleanup_errors": cleanup_errors,
        "leader_reaped": proc is None or proc.poll() is not None,
        "group_absent": proc is None or not live_groups(),
        "nested_groups": nested, "nested_reaping": reaped_children,
    }
    for suffix, content in ((".stdout", stdout), (".stderr", stderr)):
        with Path(str(prefix) + suffix).open("xb") as stream:
            stream.write(content)
            stream.flush()
            os.fsync(stream.fileno())
    publish(str(prefix) + ".process.json", result)
    return result


def require_success(result):
    if (result["exit"] != 0 or result["timeout"] or result["error"]
            or result["cleanup_errors"] or not result["leader_reaped"]
            or not result["group_absent"]):
        raise RuntimeError(f"unsuccessful command: {result!r}")
