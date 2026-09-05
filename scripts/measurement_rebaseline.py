#!/usr/bin/env python3
"""Local fixed-corpus measurement. Run under the campaign heavy lock; no uploads.
Usage: measurement_rebaseline.py init|screen|paired|scaling A|confirm A N
Artifacts default to /tmp/rescript-measure-rebaseline-542. No source edits.
"""
import hashlib, json, os, re, shutil, subprocess, sys, time
from pathlib import Path
D = Path(os.environ.get('MEASUREMENT_DIR', '/tmp/rescript-measure-rebaseline-542'))
ROOT = Path(__file__).resolve().parents[1]
T = Path('/Users/jake/dev/tella-fusion')
WEB = T / 'packages/core/webapp'

def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
def tracked():
    return subprocess.check_output(['git','-C',str(T),'ls-files','-z']).decode().split('\0')[:-1]
def inputs():
    paths = {T/p for p in tracked() if not p.endswith(('.gen.ts','.js','.map')) and (T/p).is_file()}
    # Include actual resolved dependency sources/config/PPX binaries, following symlinks.
    seen = set()
    for root in [T/'node_modules', WEB/'node_modules', ROOT/'packages/@rescript/runtime']:
        for base, dirs, files in os.walk(root, followlinks=True):
            real = os.path.realpath(base)
            if real in seen: dirs[:] = []; continue
            seen.add(real)
            dirs[:] = [x for x in dirs if x not in ('.git', '.cache')]
            for name in files:
                p = Path(base)/name
                if p.is_file() and (p.suffix in ('.res','.resi','.ml','.mli','.json','.exe','.wasm') or name.endswith(('lock','.lockb')) or 'ppx' in name.lower()): paths.add(p)
    return {str(p):sha(p) for p in sorted(paths)}
def outputs():
    files=[]
    for base,dirs,names in os.walk(WEB):
        dirs[:] = [x for x in dirs if x != 'node_modules']
        files += [Path(base)/x for x in names if x.endswith('.js')]
    h=hashlib.sha256(); manifest={}
    for p in sorted(files):
        rel=p.relative_to(WEB).as_posix().encode(); data=p.read_bytes()
        h.update(len(rel).to_bytes(4,'big')); h.update(rel); h.update(len(data).to_bytes(8,'big')); h.update(data)
        manifest[rel.decode()]=hashlib.sha256(data).hexdigest()
    return len(files),h.hexdigest(),manifest

def env(v,w):
    e=os.environ.copy()
    for k in list(e):
        if k.startswith(('RESCRIPT_', 'MIMALLOC_', 'OTEL_')): del e[k]
    e.update(RESCRIPT_BSC_EXE=str(D/f'bin/bsc-{v}'),RESCRIPT_RUNTIME=str(ROOT/'packages/@rescript/runtime'),RAYON_NUM_THREADS=str(w))
    return e

def command(v): return [str(D/f'bin/rescript-{v}'),'build','--in-process','--no-timing','true',str(WEB)]
def clean(v,w):
    subprocess.run([str(D/f'bin/rescript-{v}'),'clean',str(WEB)],env=env(v,w),stdout=subprocess.DEVNULL,stderr=subprocess.PIPE,check=True,timeout=120)
def run(stage,pair,pos,v,w):
    clean(v,w); name=f'{stage}-{pair}-{pos}-{v}-w{w}'
    load=os.getloadavg(); start=time.perf_counter_ns()
    p=subprocess.run(['/usr/bin/time','-lp']+command(v),env=env(v,w),capture_output=True,timeout=180)
    ns=time.perf_counter_ns()-start
    log=p.stdout+p.stderr; (D/f'logs/{name}.log').write_bytes(log)
    text=log.decode(errors='replace'); metrics={}
    for line in text.splitlines():
        m=re.match(r'\s*(user|sys|real)\s+([\d.]+)$',line)
        if m: metrics[m[1]]=float(m[2])
        for key in ['maximum resident set size','instructions retired','cycles elapsed','peak memory footprint']:
            if line.strip().endswith(key): metrics[key]=int(line.split()[0])
    count,digest,manifest=outputs()
    (D/f'{name}-js.json').write_text(json.dumps(manifest,sort_keys=True))
    row=dict(stage=stage,pair=pair,position=pos,variant=v,workers=w,wall_ns=ns,exit=p.returncode,compiled_3248='Compiled 3248 modules' in text,js_count=count,js_sha256=digest,load=load,**metrics)
    with (D/'runs.jsonl').open('a') as f: f.write(json.dumps(row)+'\n')
    print(json.dumps(row),flush=True)
    if p.returncode or count!=5048 or not row['compiled_3248']: raise RuntimeError('invalid attempt retained; stopping')
    return row

if __name__=='__main__':
    mode=sys.argv[1]
    if mode=='init':
        (D/'inputs-before.json').write_text(json.dumps(inputs(),sort_keys=True))
        modified=subprocess.check_output(['git','-C',str(T),'diff','--name-only','-z']).decode().split('\0')[:-1]
        if len(modified)!=18 or any(not p.endswith('.gen.ts') for p in modified): raise RuntimeError('unexpected modifications')
        backups={}
        for p in modified:
            dest=D/'backups'/p; dest.parent.mkdir(parents=True,exist_ok=True); shutil.copy2(T/p,dest); backups[p]=sha(T/p)
        (D/'backups.json').write_text(json.dumps(backups,sort_keys=True))
        (D/'binary-hashes.json').write_text(json.dumps({p.name:sha(p) for p in sorted((D/'bin').iterdir())}))
    elif mode=='screen':
        for w in [1,12]:
            for v in ['A','B']:
                prep=f'{D}/bin/rescript-{v} clean {WEB}'
                subprocess.run(['hyperfine','--runs','2','--prepare',prep,'--export-json',str(D/f'screen-{v}-w{w}.json'),' '.join(command(v))],env=env(v,w),check=True)
    elif mode=='paired':
        for pair in range(1,9):
            for w in ([1,12] if pair%2 else [12,1]):
                for pos,v in enumerate(['A','B'] if pair%2 else ['B','A'],1): run(mode,pair,pos,v,w)
    elif mode=='scaling':
        for rep in range(1,4):
            ws=[1,2,4,6,8,10,12,16]
            for pos,w in enumerate(ws if rep%2 else ws[::-1],1): run(mode,rep,pos,sys.argv[2],w)
    elif mode=='confirm':
        n=int(sys.argv[3]); other=12 if n!=12 else 10
        for pair in range(1,5):
            for pos,w in enumerate([n,other] if pair%2 else [other,n],1): run(mode,pair,pos,sys.argv[2],w)
    elif mode=='verify':
        current=inputs(); (D/'inputs-after.json').write_text(json.dumps(current,sort_keys=True))
        before=json.loads((D/'inputs-before.json').read_text())
        changed=[p for p in before.keys()|current.keys() if before.get(p)!=current.get(p)]
        generated=[p for p in changed if p.endswith('/lib/bs/compiler-info.json')]
        print('Generated compiler-info changes (output metadata, not input):',generated)
        changed=[p for p in changed if p not in generated]
        print('Changed input paths:',changed)
        if changed: raise RuntimeError('input drift')
    elif mode=='restore-generated':
        for p,h in json.loads((D/'backups.json').read_text()).items():
            backup=D/'backups'/p
            if sha(backup)!=h: raise RuntimeError('backup changed')
            if sha(T/p)!=h: shutil.copy2(backup,T/p)
    else: raise SystemExit('unknown mode')
