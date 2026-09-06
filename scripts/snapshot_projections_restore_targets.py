#!/usr/bin/env python3
"""Restore ordinary release targets from immutable D. Run under the heavy lock."""
import hashlib
import json
import os
from pathlib import Path
import shutil
import subprocess

ROOT = Path(__file__).resolve().parents[1]
D = Path('/tmp/rescript-snapshot-projections-experiment')
subprocess.run(['git', 'diff', '--exit-code', '5dc38ba2154e158d43436ada2142a13eef9f2c8c',
                '--', 'compiler-rust', 'rewatch'], cwd=ROOT, check=True)
def sha(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()
rows = []
for crate, tool, expected in [
    ('compiler-rust', 'bsc', 'a5ed9a622e3b787a8dae0cb5228a5eb5717849314d0af40c05f9689c6a6788af'),
    ('rewatch', 'rescript', '5fe8158df5d3201d4cf07fd962cf61b22edf63874b03bfd5328e1fe16f47c3c4'),
]:
    source = Path('/tmp/rescript-type-arg-experiment/bin') / f'{tool}-D'
    target = ROOT / crate / 'target/release' / tool
    temporary = target.with_name(target.name + '.snapshot-D-restore')
    assert sha(source) == expected and not source.stat().st_mode & 0o222
    assert not temporary.exists()
    before = sha(target)
    # Replace rather than overwrite an inode Cargo may share with deps output.
    shutil.copy2(source, temporary)
    temporary.chmod(0o755)
    assert sha(temporary) == expected
    os.replace(temporary, target)
    assert sha(source) == expected and not source.stat().st_mode & 0o222
    assert sha(target) == expected
    rows.append(dict(target=str(target), previous_sha256=before, restored_sha256=expected,
                     control=str(source), control_unchanged_readonly=True))
(D / 'restored-release-targets.json').write_text(json.dumps(rows, indent=2))
print(json.dumps(rows, indent=2))
