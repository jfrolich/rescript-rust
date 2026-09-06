#!/usr/bin/env python3
"""Verify restoration and preserve compact evidence; no builds or uploads."""
import hashlib, json, shutil, subprocess
from pathlib import Path
D=Path('/Users/jake/.opensession/artifacts/rescript-performance-20260905/architecture-round')
ROOT=Path(__file__).resolve().parents[1]
OUT=ROOT/'projects/in-process-performance/architecture-e4370'
T=Path('/Users/jake/dev/tella-fusion')
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def cmd(*args):return subprocess.check_output(args).decode().strip()
assert not cmd('git','diff','5dc38ba2154e158d43436ada2142a13eef9f2c8c','--','compiler-rust','rewatch')
hashes=json.loads((D/'binary-hashes.json').read_text());binaries={}
for name,h in hashes.items():
    p=D/'bin'/name;assert sha(p)==h and not p.stat().st_mode & 0o222
    assert str(p.resolve()).startswith('/Users/jake/.opensession/artifacts/')
    binaries[name]=dict(sha256=h,resolved=str(p.resolve()),mode=oct(p.stat().st_mode & 0o777))
for tool,crate in [('bsc','compiler-rust'),('rescript','rewatch')]:assert sha(ROOT/crate/'target/release'/tool)==hashes[f'{tool}-D']
assert json.loads((D/'probe-source-before.json').read_text())==json.loads((D/'probe-source-restored.json').read_text())
backups=json.loads((D/'backups.json').read_text());assert len(backups)==18
assert set(cmd('git','-C',str(T),'diff','--name-only').splitlines())==set(backups)
for path,h in backups.items():assert sha(T/path)==sha(D/'backups'/path)==h
assert cmd('git','-C',str(T),'rev-parse','HEAD')=='66a5edabdbfdbc5dd7496e59ee0573de2a2a1ffa'
initial=json.loads((D/'provenance-before-timing.json').read_text())
assert cmd('git','-C',str(T),'status','--porcelain') == initial['tella_status']
for path,h in initial['runtime_hashes'].items():assert sha(ROOT/path)==h
validation=dict(head=cmd('git','rev-parse','HEAD'),source_D='5dc38ba2154e158d43436ada2142a13eef9f2c8c',binaries=binaries,archive_files=len(json.loads((D/'probe-source-restored.json').read_text())),restored_gen_files=len(backups),tella_status=cmd('git','-C',str(T),'status','--porcelain'),thermal=cmd('pmset','-g','therm'))
(D/'restoration.json').write_text(json.dumps(validation,indent=2)+'\n')
OUT.mkdir(exist_ok=True)
a=json.loads((D/'analysis.json').read_text())
# Full module-name tables and raw private logs/manifests stay in local durable storage.
for p in a['phases'].values():p.pop('modules')
(OUT/'analysis.json').write_text(json.dumps(a,indent=2)+'\n')
for name in ['runs.jsonl','screen-runs.jsonl','sample-runs.json','phases-runs.json','binary-hashes.json','timing-input-verification-after-paired.json','timing-input-verification-after-diagnostics.json']:
    shutil.copy2(D/name,OUT/name)
for name in ['summary.json','runs.jsonl','binary-hashes.json','input-verification.json']:
    shutil.copy2(D/'graph'/name,OUT/f'graph-{name}')
# Source trees and target cache are represented by the preserved tar, exact source
# inventories and patch; do not hash redundant build-cache artifacts.
files={str(p.relative_to(D)):sha(p) for p in sorted(D.rglob('*')) if p.is_file() and p.relative_to(D).parts[0]!='probe-source' and p.name!='artifact-hashes.json'}
(D/'artifact-hashes.json').write_text(json.dumps(files,sort_keys=True,indent=2)+'\n')
(OUT/'artifact-preservation.json').write_text(json.dumps(dict(root=str(D),files=len(files),inventory_sha256=sha(D/'artifact-hashes.json'),restoration_sha256=sha(D/'restoration.json'),excluded='probe-source extracted tree and Cargo target, represented by tar, patch, source hashes and separate saved rescript-P'),indent=2)+'\n')
print(json.dumps(validation,indent=2))
