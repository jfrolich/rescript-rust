#!/usr/bin/env python3
"""One final gate attempt per phase; keep failures and finish halted test targets."""
import json,os,sys,subprocess,hashlib
from pathlib import Path
from env_ownership_runner import bounded, guarded, restore_backups
R=Path('/Users/jake/checkouts/rescript-rust');assert Path.cwd()==R
D=Path('/Users/jake/.opensession/artifacts/rescript-performance-20260905/env-ownership/candidate')
E=os.environ.copy();E['PATH']='/Users/jake/.cargo/bin:'+E['PATH']
assert not E.get('RUSTFLAGS')
E['CARGO_TARGET_DIR']=str(D.parent/'probe-source/rewatch/target')
E['OCAML_BSC']=str(R/'_build/install/default/bin/bsc')
E['OCAML_PARSER']=str(R/'_build/install/default/bin/res_parser')
E['RESCRIPT_RUNTIME']=str(R/'packages/@rescript/runtime')
E['RESCRIPT_CLI']=str(R/'rewatch/target/release/rescript')
phase=sys.argv[1];marker=D/f'gate-{phase}-started.json';assert not marker.exists(),'No replacement final gate'
marker.write_text(json.dumps({'phase':phase,'head':subprocess.check_output(['git','rev-parse','HEAD']).decode().strip(),'CARGO_TARGET_DIR':E['CARGO_TARGET_DIR'],'RUSTFLAGS':E.get('RUSTFLAGS'),'show_output':True,'runtime':E['RESCRIPT_RUNTIME'],'binaries':{str(p):hashlib.sha256(p.read_bytes()).hexdigest() for p in [R/'compiler-rust/target/release/bsc',R/'rewatch/target/release/rescript',R/'_build/install/default/bin/bsc'] if p.is_file()}},indent=2))
def run(name,args,timeout=600):
 result,_=bounded(args,E,D/name,timeout)
 with (D/'gates.jsonl').open('a') as out:out.write(json.dumps(dict(name=name,**result))+'\n')
 print(name,result['exit'],result['timeout'],flush=True)
 return result['exit'] if not result['timeout'] else 124
if phase.endswith('build'):
 release=phase.startswith('release')
 for crate in ['compiler-rust','rewatch']:
  code=run(f'gate-{phase}-{crate}',['cargo','build','--locked','--manifest-path',f'{crate}/Cargo.toml']+(['--release'] if release else []))
  if code:raise SystemExit('Build failed; preserved')
elif phase.endswith('tests'):
 release=phase.startswith('release');args=['cargo','test','--locked','--manifest-path','compiler-rust/Cargo.toml']+(['--release'] if release else [])
 for target in [['--lib'],['--bins'],['--test','comptime_tests'],['--doc']]:
  run(f'gate-{phase}-compiler-{target[-1].lstrip("-")}',args+target+['--','--show-output'])
 run(f'gate-{phase}-rewatch',['cargo','test','--locked','--manifest-path','rewatch/Cargo.toml']+(['--release'] if release else [])+['--','--show-output'])
elif phase=='parity':
 def parity():
  for directory in ['diffs','ocaml','rust']:
   for p in (R/'.parity-cache/tests'/directory).rglob('*'):
    if p.is_file():p.unlink()
  for name,args in [('typed',['./scripts/test_typedtree_parity.sh','--release']),('raw',['./scripts/test_lambda_parity.sh','--release','--raw']),('optimized',['./scripts/test_lambda_parity.sh','--release']),('js',['./scripts/test_js_output_parity.sh','--release']),('diagnostics',['./scripts/test_error_output_parity.sh','--release']),('external',['./scripts/test_js_output_parity.sh','--release','--with-external'])]:run('gate-parity-'+name,args)
 def restore():
  base=D.parent/'runs'
  restore_backups(Path('/Users/jake/dev/tella-fusion'),base/'backups',json.loads((base/'backups.json').read_text()),lambda p:hashlib.sha256(p.read_bytes()).hexdigest())
 def verify():
  old='/Users/jake/.opensession/worktrees/rescript-compiler-can-you-do-a-torough-look'
  after=subprocess.check_output(['git','-C',old,'status','--porcelain'])
  (D/'old-worktree-status-after-parity.txt').write_bytes(after)
  assert after==(D/'old-worktree-status-before-gates.txt').read_bytes(),'Old worktree changed; preserve and investigate'
 guarded(parity,verify,restore,D/'gate-parity-failure.json')

else:raise SystemExit('release-build|default-build|release-tests|default-tests|parity')
