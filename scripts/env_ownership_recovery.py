#!/usr/bin/env python3
"""One registered functional setup recovery; no parser benchmark reruns."""
import hashlib,json,os,re
from pathlib import Path
from env_ownership_runner import bounded
R=Path('/Users/jake/checkouts/rescript-rust');assert Path.cwd()==R
D=Path('/Users/jake/.opensession/artifacts/rescript-performance-20260905/env-ownership/candidate')
plan=json.loads((D/'recovery-48-registration.json').read_text());assert not (D/'recovery-results.jsonl').exists()
exe=Path(plan['test_binary']);assert hashlib.sha256(exe.read_bytes()).hexdigest()==plan['test_binary_sha256']
paths=[R/'tests/tests/lib/ocaml',R/'tests/dependencies/rescript-react/lib/ocaml',R/'node_modules/@rescript/runtime/lib/ocaml']
counts={str(p):len(list(p.glob('*.cmi'))) for p in paths};assert all(counts.values()),counts
(D/'recovery-prerequisites.json').write_text(json.dumps(counts,indent=2))
for index,(name,expected) in enumerate(plan['exact_name_multiplicities'].items(),1):
 assert not name.startswith('parser::')
 row,log=bounded([str(exe),name,'--exact','--show-output'],os.environ.copy(),D/f'recovery-{index:02}',10)
 match=re.search(rb'test result: ok\. (\d+) passed;',log)
 row.update(name=name,expected_instances=expected,passed=int(match[1]) if match else None)
 with (D/'recovery-results.jsonl').open('a') as f:f.write(json.dumps(row)+'\n')
 print(index,name,row['exit'],row['passed'],flush=True)
 assert row['exit']==0 and not row['timeout'] and row['passed']==expected,'Failed recovery retained; no retry'
