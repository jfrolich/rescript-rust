"""Differential verdict runner: OCaml bsc (oracle) vs Rust bsc.

A *case* is a dict of file name -> source text. Files are compiled in the
order given (put `.resi` before its `.res`, dependencies before dependents),
each compiler in its own scratch directory so artifacts never leak between
the two compilers.

The primary property is verdict agreement (exit status class). Diagnostic
text is compared as a secondary property.
"""

from __future__ import annotations

import hashlib
import os
import re
import shutil
import subprocess
import tempfile
from dataclasses import dataclass, field
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
OCAML_BSC = Path(os.environ.get("OCAML_BSC", ROOT / "_build/install/default/bin/bsc"))
RUST_BSC = Path(
    os.environ.get(
        "RUST_BSC",
        ROOT / "rewatch/target" / os.environ.get("RUST_TARGET", "release") / "bsc",
    )
)
# `bsc` is a wrapper script (scripts/rust_compiler_shims.sh) that runs the
# rescript executable's hidden `rescript bsc` command.
subprocess.run(
    [ROOT / "scripts/rust_compiler_shims.sh", os.environ.get("RUST_TARGET", "release")],
    check=False,
)
BELT_LIB = ROOT / "packages/@rescript/belt/lib/ocaml"
DEFAULT_FLAGS = ["-w", "+A", "-bs-jsx", "4", "-color", "never", "-I", str(BELT_LIB)]
TIMEOUT = float(os.environ.get("FUZZ_TIMEOUT", "10"))

ANSI = re.compile(r"\x1b\[[0-9;]*m")


@dataclass
class Run:
    status: str  # ok | error | crash | timeout
    code: int
    stderr: str


@dataclass
class Result:
    kind: str  # same | rust_accepts | rust_rejects | crash | msg_diff | warn_diff
    ocaml: list[Run] = field(default_factory=list)
    rust: list[Run] = field(default_factory=list)
    signature: str = ""

    @property
    def interesting(self) -> bool:
        return self.kind != "same"


def _classify(code: int, timed_out: bool) -> str:
    if timed_out:
        return "timeout"
    if code == 0:
        return "ok"
    if code in (1, 2):
        return "error"
    return "crash"


def _run(exe: Path, cwd: Path, name: str, flags: list[str]) -> Run:
    try:
        p = subprocess.run(
            [str(exe), *flags, name],
            cwd=cwd,
            stdout=subprocess.DEVNULL,
            stderr=subprocess.PIPE,
            timeout=TIMEOUT,
        )
        code, err, to = p.returncode, p.stderr, False
    except subprocess.TimeoutExpired as e:
        code, err, to = -1, e.stderr or b"", True
    # ANSI codes are kept: the two-step pipeline compares colored output.
    text = err.decode("utf-8", "replace")
    status = _classify(code, to)
    # Rust panics exit with 101; OCaml uncaught exceptions print "Fatal error".
    plain = ANSI.sub("", text)
    if "panicked at" in plain or "RUST_BACKTRACE" in plain or "Fatal error: exception" in plain:
        status = "crash"
    return Run(status, code, text)


# `direct` compiles each source file in one call. `two_step` is what the build
# system does: `bsc -bs-ast` writes the preprocessed tree (parser warnings,
# PPXs and their diagnostics happen here), then `bsc X.ast` type checks it.
PIPELINES = tuple(
    p for p in os.environ.get("FUZZ_PIPELINES", "direct,two_step").split(",") if p
)


def _compile_all(
    exe: Path, case: dict[str, str], flags: list[str], pipeline: str = "direct"
) -> list[Run]:
    d = Path(tempfile.mkdtemp(prefix="fz-"))
    try:
        for name, src in case.items():
            (d / name).write_text(src)
        runs = []
        if pipeline == "two_step":
            # The build system leaves bsc's default `-color always` in place.
            flags = [
                "always" if i and flags[i - 1] == "-color" else f for i, f in enumerate(flags)
            ]
        for name in case:
            if pipeline == "two_step":
                ast = name.rsplit(".", 1)[0] + (".iast" if name.endswith(".resi") else ".ast")
                r = _run(exe, d, name, [*flags, "-bs-ast", "-o", ast])
                runs.append(r)
                if r.status != "ok":
                    break
                r = _run(exe, d, ast, flags)
            else:
                r = _run(exe, d, name, flags)
            runs.append(r)
            if r.status != "ok":
                break
        return runs
    finally:
        shutil.rmtree(d, ignore_errors=True)


def overall(runs: list[Run]) -> str:
    for r in runs:
        if r.status != "ok":
            return r.status
    return "ok"


_HEADLINE_SKIP = re.compile(
    r"^\s*(We've found a bug for you!|Syntax error!|Warning number \d+|[\w./-]+\.resi?:\d+.*|\d+ [│┆].*|[│┆].*|\. [│┆].*|\s*)$"
)


def signature(stderr: str) -> str:
    """Coarse error identity: first message line, with names/numbers masked."""
    stderr = ANSI.sub("", stderr)
    for line in stderr.splitlines():
        if _HEADLINE_SKIP.match(line):
            continue
        s = line.strip()
        s = re.sub(r"\d+", "N", s)
        s = re.sub(r'"[^"]*"', '"_"', s)
        s = re.sub(r"`[^`']*[`']", "`_`", s)
        s = re.sub(r"(?<![A-Za-z])'[a-z_]\w*", "'a", s)
        # mask capitalised names except the leading word of the sentence
        s = re.sub(r"(?<=\S )[A-Z][\w.']*", "M", s)
        # mask identifiers that directly follow a noun keyword
        s = re.sub(r"\b(value|field|label|constructor|name|type|module|variable|tag|argument|signature)\s+[\w.'#]+",
                   r"\1 _", s)
        return s[:160]
    return "<no message>"


def compare(
    case: dict[str, str],
    flags: list[str] | None = None,
    check_text: bool = True,
    pipelines: tuple[str, ...] | None = None,
) -> Result:
    """Compare under each pipeline; return the first disagreement found."""
    result = None
    for pipeline in pipelines or PIPELINES:
        result = _compare_pipeline(case, flags or DEFAULT_FLAGS, check_text, pipeline)
        if result.interesting:
            if pipeline != "direct":
                result.signature = f"[{pipeline}] {result.signature}"
            if any(name.endswith(".resi") for name in case):
                result.signature = f"[resi] {result.signature}"
            return result
    assert result is not None
    return result


def _compare_pipeline(
    case: dict[str, str], flags: list[str], check_text: bool, pipeline: str
) -> Result:
    o = _compile_all(OCAML_BSC, case, flags, pipeline)
    r = _compile_all(RUST_BSC, case, flags, pipeline)
    ov, rv = overall(o), overall(r)
    sig = signature(o[-1].stderr) if ov != "ok" else ""
    if ov == "crash" and rv == "crash" and _norm(o[-1].stderr) == _norm(r[-1].stderr):
        # Both print the same uncaught-exception report: that is parity.
        kind = "same"
    elif ov == "timeout":
        # The oracle did not terminate (e.g. OCaml recursing until its much
        # larger stack overflows), so there is no verdict to compare against.
        kind = "ocaml_crash"
    elif "crash" in (rv,) or rv == "timeout":
        kind = "crash"
        sig = f"rust-{rv}: " + (signature(r[-1].stderr) if r else "")
    elif ov in ("crash", "timeout"):
        kind = "ocaml_crash"
    elif ov != "ok" and rv == "ok":
        kind = "rust_accepts"
    elif ov == "ok" and rv != "ok":
        kind = "rust_rejects"
        sig = "rust: " + signature(r[-1].stderr)
    elif not check_text:
        kind = "same"
    elif ov != "ok":
        kind = "same" if _norm(o[-1].stderr) == _norm(r[-1].stderr) else "msg_diff"
    else:
        ow = "".join(x.stderr for x in o)
        rw = "".join(x.stderr for x in r)
        kind = "same" if _norm(ow) == _norm(rw) else "warn_diff"
        if kind == "warn_diff":
            sig = "warn: " + signature(ow or rw)
    return Result(kind, o, r, sig)


def _norm(s: str) -> str:
    return _accepted(s).strip()


# Accepted differences (not compared):
# - `%raw` JavaScript parse errors: OCaml reports Flow's message as warning 103
#   (bs_flow_ast_utils.ml check_flow_errors), Rust uses a different JS parser.
# - The module listing under "Signature mismatch:".
_BLOCK_START = re.compile(r"^  (?:\x1b\[[0-9;]*m)*(?:Warning number \d+|We've found a bug for you!|Syntax error!)")
_FFI_OTHER = ("such externals are unsafe", "is redundant here")


def _accepted(s: str) -> str:
    blocks, cur = [], []
    for line in s.split("\n"):
        if _BLOCK_START.match(line) and cur:
            blocks.append(cur)
            cur = []
        cur.append(line)
    blocks.append(cur)
    out = []
    for b in blocks:
        plain = [ANSI.sub("", x) for x in b]
        ffi = [x for x in plain if "FFI warning: " in x]
        if ffi and not any(o in x for x in ffi for o in _FFI_OTHER):
            continue
        for i, x in enumerate(plain):
            if x.strip() == "Signature mismatch:":
                b = b[: i + 1]
                break
        out.append("\n".join(b))
    return "\n".join(out)


def case_hash(case: dict[str, str]) -> str:
    h = hashlib.sha1()
    for k, v in case.items():
        h.update(k.encode())
        h.update(b"\0")
        h.update(v.encode())
        h.update(b"\0")
    return h.hexdigest()[:12]
