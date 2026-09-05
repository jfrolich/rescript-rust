#!/usr/bin/env python3
"""Pin immutable executables and provenance before any E timing."""
import hashlib
import json
from pathlib import Path
import shutil
import subprocess

D = Path('/tmp/rescript-snapshot-projections-experiment')
ROOT = Path(__file__).resolve().parents[1]
assert not (D / 'provenance-before-timing.json').exists()

def sha(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()

def cmd(*args):
    return subprocess.check_output(args).decode().strip()

controls = {
    'D': (Path('/tmp/rescript-type-arg-experiment'), 'type-arg', {
        'bsc': 'a5ed9a622e3b787a8dae0cb5228a5eb5717849314d0af40c05f9689c6a6788af',
        'rescript': '5fe8158df5d3201d4cf07fd962cf61b22edf63874b03bfd5328e1fe16f47c3c4'}),
    'A': (Path('/tmp/rescript-measure-rebaseline-542'), 'measurement-542', {
        'bsc': '7c39a09c163088ac7db372ff8139fa62e2a9b76960eafccfe4ed2385f9172ca0',
        'rescript': '0187abee145aebdcc1b43db8d60e28ed851840dd3c75397959f64223420c4332'}),
}
provenance = {}
for v, (base, fallback, hashes) in controls.items():
    if not (base / 'bin').exists():
        base = Path('/Users/jake/.opensession/artifacts/rescript-performance-20260905') / fallback
    provenance[v] = json.loads((base / 'provenance.json').read_text())
    for tool, expected in hashes.items():
        source = base / f'bin/{tool}-{v}'
        assert sha(source) == expected and not source.stat().st_mode & 0o222
        dest = D / f'bin/{tool}-{v}'
        assert not dest.exists()
        shutil.copy2(source, dest)
assert provenance['A']['source_A'] == 'fb4497659fdf53b491fc5480d6588ec800e92e0a'
assert provenance['A']['RUSTFLAGS'] is None and provenance['A']['features'] == 'default'
assert provenance['D']['source_head'] == '5dc38ba2154e158d43436ada2142a13eef9f2c8c'
for tool, crate in [('bsc', 'compiler-rust'), ('rescript', 'rewatch')]:
    target = D / f'bin/{tool}-E'
    assert not target.exists()
    shutil.copy2(ROOT / crate / 'target/release' / tool, target)
    target.chmod(0o555)
hashes = {p.name:sha(p) for p in sorted((D / 'bin').iterdir())}
(D / 'binary-hashes.json').write_text(json.dumps(hashes, indent=2))
provenance.update(source_E=cmd('git','rev-parse','HEAD'),
    compiler_tree=cmd('git','rev-parse','HEAD:compiler-rust'),
    rewatch_tree=cmd('git','rev-parse','HEAD:rewatch'), binaries=hashes,
    features='default', RUSTFLAGS=None, profile='release; lto=true; codegen-units=1',
    rustc=cmd('/Users/jake/.cargo/bin/rustc','-Vv'), cargo=cmd('/Users/jake/.cargo/bin/cargo','-V'),
    node=cmd('node','-v'), hardware=cmd('sysctl','hw.model','hw.ncpu'),
    build_commands=['cargo build --locked --manifest-path compiler-rust/Cargo.toml --release',
                    'cargo build --locked --manifest-path rewatch/Cargo.toml --release'],
    timing_command='/usr/bin/time -lp bin/rescript-V build --in-process --no-timing true /Users/jake/dev/tella-fusion/packages/core/webapp',
    runtime=str(ROOT / 'packages/@rescript/runtime'),
    runtime_bootstrap='107 source modules per process, minimum two runtime workers',
    tella_head=cmd('git','-C','/Users/jake/dev/tella-fusion','rev-parse','HEAD'))
(D / 'provenance-before-timing.json').write_text(json.dumps(provenance, indent=2))
