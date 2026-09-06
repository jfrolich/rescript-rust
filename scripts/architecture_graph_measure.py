#!/usr/bin/env python3
"""Fixed D/P graph diagnostics, distinct from acceptance rows."""
import os
os.environ['MEASUREMENT_DIR']='/Users/jake/.opensession/artifacts/rescript-performance-20260905/architecture-round/graph'
import measurement_rebaseline as m
import json
import shutil

assert not m.D.exists()
(m.D/'bin').mkdir(parents=True);(m.D/'logs').mkdir()
for tool in ('bsc','rescript'):(m.D/f'bin/{tool}-D').symlink_to(m.D.parent/f'bin/{tool}-D')
(m.D/'bin/bsc-P').symlink_to(m.D.parent/'bin/bsc-D')
shutil.copy2(m.D.parent/'probe-source/rewatch/target/release/rescript',m.D/'bin/rescript-P')
(m.D/'binary-hashes.json').write_text(json.dumps({p.name:m.sha(p) for p in sorted((m.D/'bin').iterdir())},indent=2))
m.clean('D',1)
before=m.inputs();(m.D/'inputs-before.json').write_text(json.dumps(before,sort_keys=True))
try:
    for pos,(v,w) in enumerate([('D',1),('P',1),('D',12),('P',12)],1):
        row=m.run('graph',1,pos,v,w)
        assert row['js_sha256']=='1cacd5cfb9604df30e204f3d8a419e4e433afa96e3f81d23ea54764af86f1d49'
finally:
    after=m.inputs();(m.D/'inputs-after.json').write_text(json.dumps(after,sort_keys=True))
    changed=sorted(p for p in before.keys()|after.keys() if before.get(p)!=after.get(p))
    allowed=json.loads((m.D.parent/'timing-input-verification-after-diagnostics.json').read_text())['generated_metadata']
    unexpected=[p for p in changed if p not in allowed]
    (m.D/'input-verification.json').write_text(json.dumps(dict(before_count=len(before),after_count=len(after),changed=changed,unexpected=unexpected),indent=2))
    for path,digest in json.loads((m.D.parent/'backups.json').read_text()).items():
        backup=m.D.parent/'backups'/path;assert m.sha(backup)==digest
        if m.sha(m.T/path)!=digest:shutil.copy2(backup,m.T/path)
assert not unexpected
