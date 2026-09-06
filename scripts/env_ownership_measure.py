#!/usr/bin/env python3
"""Fixed four D/P builds on new main; full runs require exact parent approval."""
import os
os.environ['MEASUREMENT_DIR']='/Users/jake/.opensession/artifacts/rescript-performance-20260905/env-ownership/runs'
import measurement_rebaseline as m
import json,shutil,subprocess,sys
from pathlib import Path
R=Path('/Users/jake/checkouts/rescript-rust');D=m.D.parent;assert Path.cwd()==R and m.ROOT==R
CONTROL=D.parent/'type-arg/bin'
EXPECTED={'bsc-D':'a5ed9a622e3b787a8dae0cb5228a5eb5717849314d0af40c05f9689c6a6788af','rescript-D':'5fe8158df5d3201d4cf07fd962cf61b22edf63874b03bfd5328e1fe16f47c3c4'}
def cmd(*a):return subprocess.check_output(a).decode().strip()
def source_inventory():return {p:m.sha(R/p) for p in cmd('git','ls-files').splitlines() if (R/p).is_file()}
def links():
 result={};seen=set()
 for root in [m.T/'node_modules',m.WEB/'node_modules',R/'packages/@rescript/runtime']:
  for base,dirs,files in os.walk(root,followlinks=True):
   real=os.path.realpath(base)
   if real in seen:dirs[:]=[];continue
   seen.add(real);dirs[:]=[x for x in dirs if x not in ('.git','.cache')]
   for name in dirs+files:
    p=Path(base)/name
    if p.is_symlink():result[str(p)]={'link':os.readlink(p),'resolved':str(p.resolve())}
 return result
base_env=m.env
def diagnostic_env(v,w):
 e=base_env(v,w);e['RESCRIPT_MODULE_TIMINGS']='1';return e
m.env=diagnostic_env
mode=sys.argv[1]
if mode=='prepare':
 assert not m.D.exists();(m.D/'bin').mkdir(parents=True);(m.D/'logs').mkdir()
 assert cmd('git','rev-parse','--abbrev-ref','HEAD')=='ocaml-to-rust-rewrite'
 assert not cmd('git','diff','5dc38ba2154e158d43436ada2142a13eef9f2c8c','--','compiler-rust','rewatch')
 assert cmd('git','-C',str(m.T),'rev-parse','HEAD')=='66a5edabdbfdbc5dd7496e59ee0573de2a2a1ffa'
 assert not os.environ.get('RUSTFLAGS')
 for name,digest in EXPECTED.items():
  p=CONTROL/name;assert m.sha(p)==digest and not p.stat().st_mode & 0o222
  (m.D/'bin'/name).symlink_to(p)
 (m.D/'bin/bsc-P').symlink_to(CONTROL/'bsc-D')
 shutil.copy2(D/'probe-source/rewatch/target/release/rescript',m.D/'bin/rescript-P')
 backups=json.loads((D.parent/'architecture-round/backups.json').read_text())
 assert len(backups)==18 and set(cmd('git','-C',str(m.T),'diff','--name-only').splitlines())==set(backups)
 for path,digest in backups.items():
  assert m.sha(m.T/path)==digest
  q=m.D/'backups'/path;q.parent.mkdir(parents=True,exist_ok=True);shutil.copy2(m.T/path,q)
 (m.D/'backups.json').write_text(json.dumps(backups,sort_keys=True))
 (m.D/'binary-hashes.json').write_text(json.dumps({p.name:m.sha(p) for p in (m.D/'bin').iterdir()},indent=2))
 (m.D/'provenance.json').write_text(json.dumps({'root':str(R),'head':cmd('git','rev-parse','HEAD'),'rustc':cmd('/Users/jake/.cargo/bin/rustc','-Vv'),'cargo':cmd('/Users/jake/.cargo/bin/cargo','-V'),'node':cmd('node','-v'),'runtime':str(R/'packages/@rescript/runtime'),'features':'default','RUSTFLAGS':'unset','tella_status':cmd('git','-C',str(m.T),'status','--porcelain'),'commands':{v:m.command(v) for v in ['D','P']},'environment':{f'{v}{w}':{k:x for k,x in m.env(v,w).items() if k.startswith(('RESCRIPT_','RAYON','RUST','CARGO'))} for v in ['D','P'] for w in [1,12]}},indent=2))
 print('Prepared controls, probe, new-root provenance and 18 backups. No full build.')
elif mode=='run':
 assert (D/'parent-probe-approval.txt').exists(),'Exact probe approval required'
 assert not (m.D/'runs.jsonl').exists() and not (m.D/'inputs-before.json').exists(),'Never replace full attempts'
 for name,h in json.loads((m.D/'binary-hashes.json').read_text()).items():assert m.sha(m.D/'bin'/name)==h
 m.clean('D',1)
 before=m.inputs();sources=source_inventory();symlinks=links()
 for name,data in [('inputs-before',before),('source-before',sources),('symlinks-before',symlinks)]:
  (m.D/f'{name}.json').write_text(json.dumps(data,sort_keys=True))
 try:
  for pos,(v,w) in enumerate([('D',1),('P',1),('D',12),('P',12)],1):
   row=m.run('env',1,pos,v,w)
   assert row['js_sha256']=='1cacd5cfb9604df30e204f3d8a419e4e433afa96e3f81d23ea54764af86f1d49'
 finally:
  after=m.inputs();after_sources=source_inventory();after_links=links()
  for name,data in [('inputs-after',after),('source-after',after_sources),('symlinks-after',after_links)]:
   (m.D/f'{name}.json').write_text(json.dumps(data,sort_keys=True))
  changed=sorted(p for p in before.keys()|after.keys() if before.get(p)!=after.get(p))
  allowed=json.loads((D.parent/'architecture-round/timing-input-verification-after-diagnostics.json').read_text())['generated_metadata']
  unexpected=[p for p in changed if p not in allowed]
  report={'before_count':len(before),'after_count':len(after),'changed':changed,'unexpected':unexpected,'source_equal':sources==after_sources,'symlinks_equal':symlinks==after_links}
  (m.D/'verification.json').write_text(json.dumps(report,indent=2));print(report)
  for path,digest in json.loads((m.D/'backups.json').read_text()).items():
   backup=m.D/'backups'/path;assert m.sha(backup)==digest
   if m.sha(m.T/path)!=digest:shutil.copy2(backup,m.T/path)
 assert not unexpected and sources==after_sources and symlinks==after_links
else:raise SystemExit('prepare|run')
