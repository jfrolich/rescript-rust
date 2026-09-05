#!/usr/bin/env python3
"""Verify frozen source/restoration and preserve evidence locally, never upload."""
import hashlib
import io
import json
from pathlib import Path
import shutil
import subprocess
import sys
import tarfile
D = Path('/tmp/rescript-snapshot-projections-experiment')
OUT = Path('projects/in-process-performance/snapshot-projections-08c884')
DURABLE = Path('/Users/jake/.opensession/artifacts/rescript-performance-20260905/snapshot-projections')
SOURCE = '08c884be8412d44d4ca32ef76a8792febeae35e8'
def sha(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()
def cmd(*args):
    return subprocess.check_output(args).decode().strip()
restored = '--restored' in sys.argv
VERIFY_SOURCE = '5dc38ba2154e158d43436ada2142a13eef9f2c8c' if restored else SOURCE
source_hashes = {}
archive = subprocess.check_output(['git', 'archive', VERIFY_SOURCE, 'compiler-rust', 'rewatch'])
if not restored:
    (D / 'candidate-source.tar').write_bytes(archive)
    (D / 'candidate.patch').write_bytes(subprocess.check_output(['git', 'show', '--format=fuller', SOURCE]))
with tarfile.open(fileobj=io.BytesIO(archive)) as tar:
    for member in tar:
        if not member.isfile():
            continue
        data = tar.extractfile(member).read()
        assert Path(member.name).read_bytes() == data, member.name
        source_hashes[member.name] = hashlib.sha256(data).hexdigest()
(D / ('restored-source-hashes.json' if restored else 'source-hashes.json')).write_text(json.dumps(source_hashes, sort_keys=True))
binaries = json.loads((D / 'binary-hashes.json').read_text())
for name, expected in binaries.items():
    p = D / 'bin' / name
    assert sha(p) == expected and not p.stat().st_mode & 0o222
for v, base in [('A', '/tmp/rescript-measure-rebaseline-542'), ('D', '/tmp/rescript-type-arg-experiment')]:
    for tool in ['bsc', 'rescript']:
        p = Path(base) / f'bin/{tool}-{v}'
        assert sha(p) == binaries[p.name] and not p.stat().st_mode & 0o222
subprocess.run(['python3', 'scripts/snapshot_projections_measure.py', 'restore-generated'], check=True)
T = Path('/Users/jake/dev/tella-fusion')
backups = json.loads((D / 'backups.json').read_text())
assert len(backups) == 18 and all(sha(T / p) == h for p, h in backups.items())
status = subprocess.check_output(['git','-C',str(T),'status','--porcelain=v1'])
(D / 'tella-status-after.txt').write_bytes(status)
assert status == (D / 'tella-status-before.txt').read_bytes()
assert cmd('git','-C',str(T),'rev-parse','HEAD') == (D / 'tella-head.txt').read_text().strip()
provenance = json.loads((D / 'provenance-before-timing.json').read_text())
provenance.update(reviewed_source=SOURCE, report_head=cmd('git','rev-parse','HEAD'),
    source_file_count=len(source_hashes), source_manifest_sha256=sha(D/'source-hashes.json'),
    restored_generated_count=len(backups), artifact_root=str(DURABLE),
    production_source=VERIFY_SOURCE, candidate_rejected=restored,
    timing_head='706fa1f2f',
    restored_source_manifest_sha256=sha(D/'restored-source-hashes.json') if restored else None,
    tool_failures=['Initial setup tool returned after its 10s timeout; lockf/Python continued and completed. No setup or timing rerun.',
                   'Skill read tool rejected outside-workspace path; bash read succeeded.',
                   'Test-development failures preserved in focused logs; no production detour.',
                   'Post-cohort pre-gate classification initially missed two try-lock Cargo fingerprints; exact entries added, no inventory or cohort rerun.',
                   'A summary glob included JS manifest JSON; exact hyperfine paths used instead. No samples rerun.'],
    logs={str(p.relative_to(D)):sha(p) for p in sorted((D/'logs').iterdir()) if p.is_file()},
    power=cmd('pmset','-g','batt'), thermal=cmd('pmset','-g','therm'))
(D / 'provenance.json').write_text(json.dumps(provenance, indent=2))
OUT.mkdir(parents=True, exist_ok=True)
for name in ['runs.jsonl','screen-runs.jsonl','timing-summary.json','binary-hashes.json',
             'gates.jsonl','provenance.json','source-hashes.json',
             'timing-input-verification-after.json']:
    shutil.copy2(D/name, OUT/name)
shutil.copy2(D/'fixtures/results.json', OUT/'fixture-results.json')
shutil.copy2(D/'runtime-results.json', OUT/'runtime-results.json')
shutil.copy2(D/'candidate.patch', OUT/'candidate.patch')
if restored:
    shutil.copy2(D/'restored-source-hashes.json', OUT/'restored-source-hashes.json')
# Raw corpus JS, input paths/hashes, generated backups and all failures stay local.
def preserve_copy(src, dst):
    src, dst = Path(src), Path(dst)
    if dst.exists() and sha(src) == sha(dst):
        return str(dst)
    assert dst.parent.name != 'bin' or not dst.exists(), 'Never replace saved binaries'
    return shutil.copy2(src, dst)
shutil.copytree(D, DURABLE, dirs_exist_ok=True, copy_function=preserve_copy)
shutil.copytree(OUT, DURABLE/'committed-summary', dirs_exist_ok=True)
shutil.copy2(OUT.parent/'SNAPSHOT_PROJECTIONS_EXPERIMENT.md', DURABLE/'SNAPSHOT_PROJECTIONS_EXPERIMENT.md')
(DURABLE/'scripts').mkdir(exist_ok=True)
for script in [*Path('scripts').glob('snapshot_projections_*.py'), Path('scripts/measurement_rebaseline.py')]:
    shutil.copy2(script, DURABLE/'scripts'/script.name)
manifest = {str(p.relative_to(DURABLE)):sha(p) for p in sorted(DURABLE.rglob('*')) if p.is_file() and p.name != 'artifact-hashes.json'}
(DURABLE/'artifact-hashes.json').write_text(json.dumps(manifest,sort_keys=True))
print(json.dumps(dict(preserved_files=len(manifest), source_files=len(source_hashes), binaries=binaries)))
