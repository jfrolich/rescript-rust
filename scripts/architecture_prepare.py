#!/usr/bin/env python3
"""Verify immutable controls and preserve inputs, no builds."""
import os
os.environ['MEASUREMENT_DIR'] = '/Users/jake/.opensession/artifacts/rescript-performance-20260905/architecture-round'
import measurement_rebaseline as m
import json
import shutil
import subprocess

def cmd(*args):
    return subprocess.check_output(args).decode().strip()
assert not m.D.exists()
(m.D / 'bin').mkdir(parents=True)
(m.D / 'logs').mkdir()
controls = {
'A': ('measurement-542', '/tmp/rescript-measure-rebaseline-542', 'fb4497659fdf53b491fc5480d6588ec800e92e0a', ['7c39a09c163088ac7db372ff8139fa62e2a9b76960eafccfe4ed2385f9172ca0','0187abee145aebdcc1b43db8d60e28ed851840dd3c75397959f64223420c4332']),
'D': ('type-arg', '/tmp/rescript-type-arg-experiment', '5dc38ba2154e158d43436ada2142a13eef9f2c8c', ['a5ed9a622e3b787a8dae0cb5228a5eb5717849314d0af40c05f9689c6a6788af','5fe8158df5d3201d4cf07fd962cf61b22edf63874b03bfd5328e1fe16f47c3c4'])}
provenance = {}
hashes = {}
for v, (durable, original, source, expected) in controls.items():
    base = m.D.parent / durable
    provenance[v] = json.loads((base / 'provenance.json').read_text())
    for tool, digest in zip(['bsc','rescript'], expected):
        p = base / f'bin/{tool}-{v}'
        q = m.Path(original) / f'bin/{tool}-{v}'
        assert m.sha(p) == m.sha(q) == digest
        assert not p.stat().st_mode & 0o222 and not q.stat().st_mode & 0o222
        (m.D / f'bin/{tool}-{v}').symlink_to(p)
        hashes[f'{tool}-{v}'] = digest
    provenance[v]['verified_source'] = source
assert not cmd('git','diff',controls['D'][2],'--','compiler-rust','rewatch')
assert provenance['A']['source_A'] == controls['A'][2]
assert provenance['A']['features'] == 'default' and provenance['A']['RUSTFLAGS'] is None
assert provenance['D']['source_head'] == controls['D'][2]
assert provenance['D']['toolchain']['features'] == 'default' and provenance['D']['toolchain']['RUSTFLAGS'] == 'unset'
for tool, crate in [('bsc','compiler-rust'),('rescript','rewatch')]:
    assert m.sha(m.ROOT / crate / 'target/release' / tool) == hashes[f'{tool}-D']
assert cmd('git','-C',str(m.T),'rev-parse','HEAD') == '66a5edabdbfdbc5dd7496e59ee0573de2a2a1ffa'
backups = json.loads((m.D.parent / 'snapshot-projections/backups.json').read_text())
modified = cmd('git','-C',str(m.T),'diff','--name-only').splitlines()
assert len(backups) == 18 and set(modified) == set(backups)
for path, digest in backups.items():
    assert m.sha(m.T/path) == digest
    dest = m.D / 'backups' / path
    dest.parent.mkdir(parents=True, exist_ok=True)
    shutil.copy2(m.T/path, dest)
(m.D/'backups.json').write_text(json.dumps(backups, sort_keys=True))
(m.D/'binary-hashes.json').write_text(json.dumps(hashes, indent=2))
runtime = {str(p.relative_to(m.ROOT)):m.sha(p) for p in sorted((m.ROOT/'packages/@rescript/runtime').rglob('*')) if p.is_file() and p.suffix in ('.res','.resi','.json')}
provenance.update(head=cmd('git','rev-parse','HEAD'),rustc=cmd('/Users/jake/.cargo/bin/rustc','-Vv'),cargo=cmd('/Users/jake/.cargo/bin/cargo','-V'),node=cmd('node','-v'),hardware=cmd('sysctl','hw.model','hw.ncpu'),power=cmd('pmset','-g','batt'),thermal=cmd('pmset','-g','therm'),runtime_hashes=runtime,
environment_overrides={f'{v}-w{w}':{k:value for k,value in m.env(v,w).items() if k.startswith(('RESCRIPT_','RAYON','MIMALLOC_','OTEL_','RUST','CARGO'))} for v in controls for w in (1,12)},commands={v:m.command(v) for v in controls},tella_status=cmd('git','-C',str(m.T),'status','--porcelain'))
(m.D/'provenance-before-timing.json').write_text(json.dumps(provenance, indent=2))
print('Controls/source/toolchain/normal binaries/runtime/corpus/18 backups verified.')
