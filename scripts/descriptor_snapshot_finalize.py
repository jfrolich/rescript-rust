#!/usr/bin/env python3
"""Restore archived source, prove unchanged production and preserve local evidence."""
import hashlib
import io
import json
from pathlib import Path
import shutil
import subprocess
import tarfile
D = Path('/tmp/rescript-descriptor-snapshots')
OUT = Path('projects/in-process-performance/descriptor-snapshots-5dc38')
DURABLE = Path('/Users/jake/.opensession/artifacts/rescript-performance-20260905/descriptor-snapshots')
SOURCE = '5dc38ba2154e158d43436ada2142a13eef9f2c8c'
def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
def cmd(*args): return subprocess.check_output(args).decode().strip()
archive = subprocess.check_output(['git', 'archive', SOURCE, 'compiler-rust', 'rewatch'])
source_hashes = {}
with tarfile.open(fileobj=io.BytesIO(archive)) as tar:
    for member in tar:
        if not member.isfile(): continue
        data = tar.extractfile(member).read()
        name = member.name
        assert Path(name).read_bytes() == data, f'Normal source drift: {name}'
        p = D/'probe-source'/name
        p.write_bytes(data)
        assert p.read_bytes() == data
        source_hashes[name] = hashlib.sha256(data).hexdigest()
(D/'restored-source-hashes.json').write_text(json.dumps(source_hashes, sort_keys=True))
assert not cmd('git','diff', SOURCE, '--', 'compiler-rust', 'rewatch')
binaries = {p.name:sha(p) for p in sorted((D/'bin').iterdir())}
assert binaries == json.loads((D/'binary-hashes.json').read_text())
assert sha(Path('/tmp/rescript-type-arg-experiment/bin/bsc-D')) == binaries['bsc-D']
assert sha(Path('/tmp/rescript-type-arg-experiment/bin/rescript-D')) == binaries['rescript-D']
runtime = {str(p):sha(p) for p in sorted(Path('packages/@rescript/runtime').rglob('*')) if p.is_file() and p.suffix in ('.res','.resi','.json')}
(D/'runtime-source-hashes.json').write_text(json.dumps(runtime,sort_keys=True))
subprocess.run(['python3','scripts/descriptor_snapshot_measure.py','restore'],check=True)
provenance = dict(source=SOURCE, source_file_count=len(source_hashes),
    report_base_head=cmd('git','rev-parse','HEAD'), binaries=binaries,
    rustc=cmd('/Users/jake/.cargo/bin/rustc','-Vv'), cargo=cmd('/Users/jake/.cargo/bin/cargo','-V'),
    node=cmd('node','--version'), macos=cmd('sw_vers'), hardware=cmd('sysctl','-n','hw.model'),
    tella_head=cmd('git','-C','/Users/jake/dev/tella-fusion','rev-parse','HEAD'),
    restored_generated_count=len(json.loads((D/'backups.json').read_text())),
    archive_patch_sha256=sha(D/'probe.patch'),
    source_manifest_sha256=sha(D/'restored-source-hashes.json'),
    runtime_source_manifest_sha256=sha(D/'runtime-source-hashes.json'), runtime_source_count=len(runtime),
    frozen_inputs_sha256=sha(D/'frozen-inputs.json'),
    after_inputs_sha256=sha(D/'inputs-after.json'),
    profile_before_inputs_sha256=sha(D/'profile-inputs-before.json'),
    profile_after_inputs_sha256=sha(D/'profile-inputs-after.json'),
    flags='default release; lto=true; codegen-units=1; RUSTFLAGS unset during build',
    artifact_root=str(DURABLE))
for name in ['binary-hashes.json','input-verification.json','profile-runs.json','profile-input-differences.json']:
    shutil.copy2(D/name, OUT/name)
for name in ['probe.patch']:
    shutil.copy2(D/name, OUT/name)
provenance['logs']={str(p.relative_to(D)):sha(p) for p in sorted((D/'logs').iterdir()) if p.is_file()}
provenance['profiles']={p.name:sha(p) for p in sorted(D.glob('sample-D-*.txt'))}
(OUT/'provenance.json').write_text(json.dumps(provenance, indent=2)+'\n')
# Keep raw private inventories/backups/profiles local; never put corpus JS in Git.
def preserve_copy(src, dst):
    src, dst = Path(src), Path(dst)
    if dst.exists() and sha(src) == sha(dst):
        return str(dst)
    assert dst.parent.name != 'bin' or not dst.exists(), 'Never overwrite a saved binary'
    return shutil.copy2(src, dst)
shutil.copytree(D, DURABLE, dirs_exist_ok=True, ignore=shutil.ignore_patterns('target'), copy_function=preserve_copy)
shutil.copytree(OUT, DURABLE/'committed-summary', dirs_exist_ok=True)
shutil.copy2(OUT.parent/'DESCRIPTOR_SNAPSHOT_ATTRIBUTION.md', DURABLE/'DESCRIPTOR_SNAPSHOT_ATTRIBUTION.md')
(DURABLE/'scripts').mkdir(exist_ok=True)
for script in [*Path('scripts').glob('descriptor_snapshot_*.py'), Path('scripts/measurement_rebaseline.py')]:
    shutil.copy2(script, DURABLE/'scripts'/script.name)
manifest = {str(p.relative_to(DURABLE)):sha(p) for p in sorted(DURABLE.rglob('*')) if p.is_file() and p.name != 'artifact-hashes.json'}
(DURABLE/'artifact-hashes.json').write_text(json.dumps(manifest,sort_keys=True))
print(json.dumps(dict(preserved_files=len(manifest), restored_source_files=len(source_hashes), binaries=binaries)))
