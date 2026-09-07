#!/usr/bin/env python3
"""Fixed current-main versus rollback Tella timing. Local artifacts only."""
import hashlib,json,os,re,shutil,signal,statistics,subprocess,sys,time,traceback
from pathlib import Path
os.environ['MEASUREMENT_DIR']='/Users/jake/.opensession/artifacts/rescript-performance-20260905/rollback-comparison'
import measurement_rebaseline as m
from env_ownership_runner import bounded
W=Path('/Users/jake/.opensession/worktrees/rescript-rust-revert-unaccepted-performance'); MAIN=Path('/Users/jake/checkouts/rescript-rust')
A=Path('/Users/jake/.opensession/artifacts/rescript-performance-20260905'); D=m.D
ORIG={'bsc-M':A/'env-ownership/postfix-validation/preserved-release/bsc','rescript-M':A/'env-ownership/postfix-validation/preserved-release/rescript','bsc-R':A/'rollback-unaccepted/bin/bsc','rescript-R':A/'rollback-unaccepted/bin/rescript'}
HASH={'bsc-M':'c69f746756255b192b322f1379b66d77d4b256c628aa08e3cd7de54c65d26347','rescript-M':'e8c1a61ce7d98ee44dad54ec60a4c540dd62d613bfc04c0640673f1a0be7758d','bsc-R':'1757849cfea709fe8880b06cff866f4cc863a372b65d87a3cbd976a74b183682','rescript-R':'65267807023955d39745503f2e1cd7d1a9e13e03971f010b4f8f9fa3d121ee01'}
OUT='1cacd5cfb9604df30e204f3d8a419e4e433afa96e3f81d23ea54764af86f1d49'; PY='/usr/bin/python3'; HF='/opt/homebrew/bin/hyperfine'; OLD=A/'env-ownership/candidate-timing'
m.ROOT=MAIN
assert Path.cwd()==W

def cmd(*a): return subprocess.check_output(a).decode().strip()
def append(p,x):
 with p.open('a') as f:f.write(json.dumps(x)+'\n')
def src(root):
 names=subprocess.check_output(['git','-C',str(root),'ls-files','-z']).decode().split('\0')[:-1]
 return {n:m.sha(root/n) for n in names if (root/n).is_file()}
def metadata():
 ps=['@rescript/react','@rescript/belt','@jfrolich/ppx-spice','rescript-debounce-react','rescript-nodejs','rescript-debounce','bs-css','bs-css-dom','@tella-fusion/webapp','@tella-fusion/webapp/packages/tella-std','@tella-fusion/webapp/node_modules/rescript-webapi']
 r={str(m.T/'node_modules'/p/'lib/bs/compiler-info.json') for p in ps};r.add(str(m.T/'node_modules/@tella-fusion/webapp/lib/bs/.sourcedirs.json'));assert len(r)==12;return r
def links():
 out={};seen=set()
 for root in [m.T/'node_modules',m.WEB/'node_modules',MAIN/'packages/@rescript/runtime']:
  for base,dirs,files in os.walk(root,followlinks=True):
   real=os.path.realpath(base)
   if real in seen:dirs[:]=[];continue
   seen.add(real);dirs[:]=[x for x in dirs if x not in('.git','.cache')]
   for n in dirs+files:
    p=Path(base)/n
    if p.is_symlink():out[str(p)]={'link':os.readlink(p),'resolved':str(p.resolve())}
 return out
def inventory():return {'inputs':m.inputs(),'main':src(MAIN),'rollback':src(W),'links':links(),'copies':{n:m.sha(D/'bin'/n) for n in HASH},'originals':{n:m.sha(p) for n,p in ORIG.items()}}
def compare(before,now,expect_meta):
 md=metadata();changed={p for p in before['inputs'].keys()|now['inputs'].keys() if before['inputs'].get(p)!=now['inputs'].get(p)}
 report={'metadata_present':sorted(md&now['inputs'].keys()),'unexpected':sorted(changed-md),'main_equal':before['main']==now['main'],'rollback_equal':before['rollback']==now['rollback'],'links_equal':before['links']==now['links'],'copies_equal':before['copies']==now['copies']==HASH,'originals_equal':before['originals']==now['originals']==HASH}
 report['valid']=not(md&before['inputs'].keys()) and md&now['inputs'].keys()==(md if expect_meta else set()) and not report['unexpected'] and all(report[k] for k in ['main_equal','rollback_equal','links_equal','copies_equal','originals_equal']);return report
def verify(label,expect):
 before=json.loads((D/'inventory-before.json').read_text());now=inventory();(D/f'inventory-{label}.json').write_text(json.dumps(now,sort_keys=True));r=compare(before,now,expect);(D/f'inventory-verification-{label}.json').write_text(json.dumps(r,indent=2));
 if not r['valid']:raise RuntimeError('inventory drift at '+label)
def env(v,w):
 e=os.environ.copy()
 for k in list(e):
  if k.startswith(('RESCRIPT_','MIMALLOC_','OTEL_')):del e[k]
 e.update(RESCRIPT_BSC_EXE=str(D/'bin'/f'bsc-{v}'),RESCRIPT_RUNTIME=str(MAIN/'packages/@rescript/runtime'),RAYON_NUM_THREADS=str(w));return e
def build(v):return [str(D/'bin'/f'rescript-{v}'),'build','--in-process','--no-timing','true',str(m.WEB)]
def metrics(text):
 x={}
 for line in text.splitlines():
  q=re.match(r'\s*(user|sys|real)\s+([\d.]+)$',line)
  if q:x[q.group(1)]=float(q.group(2))
  for k in ['maximum resident set size','instructions retired','cycles elapsed','peak memory footprint']:
   if line.strip().endswith(k):x[k]=int(line.split()[0])
 missing={'real','user','sys','maximum resident set size','instructions retired','cycles elapsed'}-x.keys()
 if missing:raise RuntimeError('missing metrics '+repr(sorted(missing)))
 return x
def clean(v,w,name):
 r,_=bounded([str(D/'bin'/f'rescript-{v}'),'clean',str(m.WEB)],env(v,w),D/'logs'/f'{name}-clean',120)
 if r['exit']!=0 or r['timeout'] or r['error']:raise RuntimeError('clean failed '+name)
 return r
def restore():
 failures=[]
 for rel,digest in json.loads((D/'backups.json').read_text()).items():
  try:
   b=D/'backups'/rel;p=m.T/rel
   if m.sha(b)!=digest:raise RuntimeError('backup changed '+rel)
   if not p.is_file() or m.sha(p)!=digest:p.parent.mkdir(parents=True,exist_ok=True);shutil.copy2(b,p)
   if m.sha(p)!=digest:raise RuntimeError('restore mismatch '+rel)
  except BaseException as e:failures.append({'path':rel,'error':repr(e),'traceback':traceback.format_exc()})
 if failures:(D/'restoration-errors.json').write_text(json.dumps(failures,indent=2));raise RuntimeError('restoration failures; see restoration-errors.json')
def guarded(body,check,error):
 failures=[]
 try:body()
 except BaseException as e:failures.append(('body',e,traceback.format_exc()))
 try:check()
 except BaseException as e:failures.append(('verification',e,traceback.format_exc()))
 try:restore()
 except BaseException as e:failures.append(('restoration',e,traceback.format_exc()))
 if failures:(D/error).write_text(json.dumps([{'phase':p,'error':repr(e),'traceback':t} for p,e,t in failures],indent=2));raise failures[0][1]
def inner(command,e,prefix):
 prefix=Path(prefix);paths=[Path(str(prefix)+s) for s in ['.started.json','.process.json','.stdout','.stderr']]
 if any(p.exists() for p in paths):raise RuntimeError('slot exists')
 paths[0].write_text(json.dumps({'command':command,'load_before':os.getloadavg(),'perf_counter_ns_before':time.perf_counter_ns()},indent=2));start=time.perf_counter_ns();p=None;err=None
 with paths[2].open('wb') as out,paths[3].open('wb') as stderr:
  try:p=subprocess.Popen(command,env=e,stdout=out,stderr=stderr);p.wait()
  except BaseException as ex:err=ex
 r={'command':command,'wall_ns':time.perf_counter_ns()-start,'exit':p.returncode if p else None,'timeout':False,'error':repr(err) if err else None};paths[1].write_text(json.dumps(r,indent=2))
 if r['exit']!=0 or r['error']:raise RuntimeError('inner failed')
 return r
def rows():
 out=[]
 for pair in range(1,9):
  ws=[12,1] if pair%2 else [1,12];vs=['M','R'] if pair%2 else ['R','M']
  for mi,w in enumerate(ws,1):
   for pos,v in enumerate(vs,1):out.append([pair,mi,pos,v,w])
 return out
def slot(pair,mi,v,w):
 found=[x for x in rows() if x[0]==pair and x[1]==mi and x[3]==v and x[4]==w]
 if len(found)!=1:raise RuntimeError('outside plan')
 x=found[0];return x[2],f'pair-{pair}-mode-{mi}-pos-{x[2]}-{v}-w{w}'
def archive(label):
 count,digest,manifest=m.outputs();(D/f'{label}-js.json').write_text(json.dumps(manifest,sort_keys=True));root=D/'qualification-outputs'/label
 for rel in manifest:
  dest=root/rel;dest.parent.mkdir(parents=True,exist_ok=True);shutil.copy2(m.WEB/rel,dest)
 return count,digest,manifest
def qualification(v):
 name=f'qualification-{v}-w12';r={'variant':v,'workers':12,'phase':'clean'}
 try:
  r['clean']=clean(v,12,name);r['phase']='build';p,log=bounded(['/usr/bin/time','-lp']+build(v),env(v,12),D/'logs'/name,180);r.update(p);r.update(metrics(log.decode(errors='replace')));r['phase']='outputs';count,digest,manifest=archive(name);r.update(js_count=count,js_sha256=digest,compiled_3248='Compiled 3248 modules' in log.decode(errors='replace'))
  if p['exit']!=0 or count!=5048 or not r['compiled_3248']:raise RuntimeError('qualification failed')
  r['phase']='complete';return r,manifest
 except BaseException as e:r['attempt_error']=repr(e);raise
 finally:append(D/'qualification.jsonl',r)
def child(pair,mi,v,w):slot(pair,mi,v,w);inner(['/usr/bin/time','-lp']+build(v),env(v,w),D/'logs'/slot(pair,mi,v,w)[1])
def finalize(pair,mi,v,w,driver):
 pos,name=slot(pair,mi,v,w);r={'pair':pair,'mode_index':mi,'position':pos,'variant':v,'workers':w,'driver':driver}
 try:
  pp=D/'logs'/f'{name}.process.json'
  if driver['exit']!=0 or driver['timeout'] or driver['error'] or not pp.is_file():raise RuntimeError('outer/child failed')
  r.update(json.loads(pp.read_text()));text=(D/'logs'/f'{name}.stdout').read_text(errors='replace')+(D/'logs'/f'{name}.stderr').read_text(errors='replace');r.update(metrics(text));count,digest,manifest=m.outputs();(D/f'{name}-js.json').write_text(json.dumps(manifest,sort_keys=True));r.update(js_count=count,js_sha256=digest,compiled_3248='Compiled 3248 modules' in text)
  if r['exit']!=0 or count!=5048 or digest!=OUT or not r['compiled_3248']:raise RuntimeError('timed contract failed')
 except BaseException as e:r['attempt_error']=repr(e);raise
 finally:append(D/'runs.jsonl',r)
def prepare():
 if D.exists():raise RuntimeError('artifact directory exists')
 (D/'bin').mkdir(parents=True);(D/'logs').mkdir()
 for n,p in ORIG.items():
  if m.sha(p)!=HASH[n]:raise RuntimeError('original hash '+n)
  shutil.copy2(p,D/'bin'/n);(D/'bin'/n).chmod(0o555)
 (D/'binary-hashes.json').write_text(json.dumps({n:{'original':m.sha(ORIG[n]),'copy':m.sha(D/'bin'/n)} for n in HASH},indent=2))
 heads={'main_checkout':cmd('git','-C',str(MAIN),'rev-parse','HEAD'),'rollback_worktree':cmd('git','-C',str(W),'rev-parse','HEAD'),'tella':cmd('git','-C',str(m.T),'rev-parse','HEAD'),'main_binary_source':'a59f271c7437b9b6f3568cab44b56851f079a07a','rollback_binary_source':'24875256e'}
 if heads['main_checkout']!='d98b8b9430045d40d08ed89dd75174b5669fa829' or heads['rollback_worktree']!='65a3f342f385580134aeb0e1a539e4db5032f2c5' or heads['tella']!='66a5edabdbfdbc5dd7496e59ee0573de2a2a1ffa':raise RuntimeError('head mismatch')
 old=json.loads((OLD/'backups.json').read_text());modified=cmd('git','-C',str(m.T),'diff','--name-only').splitlines()
 if len(old)!=18 or set(old)!=set(modified):raise RuntimeError('protected generated set mismatch')
 for rel,digest in old.items():
  if m.sha(m.T/rel)!=digest or m.sha(OLD/'backups'/rel)!=digest:raise RuntimeError('protected original mismatch')
  dest=D/'backups'/rel;dest.parent.mkdir(parents=True,exist_ok=True);shutil.copy2(m.T/rel,dest)
 (D/'backups.json').write_text(json.dumps(old,sort_keys=True));plan={'qualification_order':[['M',12],['R',12]],'timed_rows':rows(),'timed_build_count':32,'pair_rule':'odd w12,w1 MR; even w1,w12 RM','hyperfine':{'path':HF,'runs':1,'warmup':0},'authoritative':'inner perf_counter_ns around /usr/bin/time -lp plus build','bounds':{'clean':120,'build':180,'outer':210},'command':['build','--in-process','--no-timing','true'],'output':{'modules':3248,'js':5048,'digest':OUT},'no_extensions_exclusions_replacements_seed_search_retries':True};(D/'plan.json').write_text(json.dumps(plan,indent=2));(D/'provenance.json').write_text(json.dumps({'heads':heads,'runtime':str(MAIN/'packages/@rescript/runtime'),'python':cmd(PY,'--version'),'hyperfine':cmd(HF,'--version'),'lock':'/tmp/rescript-tella-heavy.lock','env':{f'{v}-w{w}':{k:env(v,w)[k] for k in ['RESCRIPT_BSC_EXE','RESCRIPT_RUNTIME','RAYON_NUM_THREADS']} for v in ['M','R'] for w in [1,12]}},indent=2));print(m.sha(D/'plan.json'))
def freeze():
 clean('M',1,'freeze-inputs');before=inventory()
 if not compare(before,before,False)['valid']:raise RuntimeError('bad clean baseline')
 (D/'inventory-before.json').write_text(json.dumps(before,sort_keys=True))
def qualify():
 verify('pre-qualification',False);got={}
 def body():
  for v in ['M','R']:got[v]=qualification(v)
  diffs=sorted(p for p in got['M'][1].keys()|got['R'][1].keys() if got['M'][1].get(p)!=got['R'][1].get(p));r={'M_digest':got['M'][0]['js_sha256'],'R_digest':got['R'][0]['js_sha256'],'required_digest':OUT,'per_file_difference_count':len(diffs),'per_file_differences':diffs};r['valid']=not diffs and r['M_digest']==r['R_digest']==OUT;(D/'qualification-report.json').write_text(json.dumps(r,indent=2));
  if not r['valid']:raise RuntimeError('qualification contract failed; timed plan prohibited')
 guarded(body,lambda:verify('after-qualification',True),'qualification-failure.json')
def timed():
 if not json.loads((D/'qualification-report.json').read_text())['valid'] or (D/'runs.jsonl').exists():raise RuntimeError('timed prerequisites failed')
 verify('pre-timed',True)
 def body():
  for pair in range(1,9):
   ws=[12,1] if pair%2 else [1,12];vs=['M','R'] if pair%2 else ['R','M']
   for mi,w in enumerate(ws,1):
    for v in vs:
     name=slot(pair,mi,v,w)[1];append(D/'attempts.jsonl',{'name':name,'attempted_before_clean_ns':time.perf_counter_ns()});clean(v,w,name);driver,_=bounded([HF,'--runs','1','--warmup','0','--export-json',str(D/f'{name}-hyperfine.json'),f'{PY} {Path(__file__).resolve()} child {pair} {mi} {v} {w}'],env(v,w),D/'logs'/f'{name}-hyperfine',210);finalize(pair,mi,v,w,driver)
   verify(f'after-pair-{pair}',True)
 guarded(body,lambda:verify('after-timed',True),'timed-failure.json')
def analyze():
 rs=[json.loads(x) for x in (D/'runs.jsonl').read_text().splitlines()];actual=[[r[k] for k in ['pair','mode_index','position','variant','workers']] for r in rs]
 if len(rs)!=32 or actual!=rows() or len((D/'attempts.jsonl').read_text().splitlines())!=32:raise RuntimeError('order/count')
 req={'wall_ns','real','user','sys','maximum resident set size','instructions retired','cycles elapsed'}
 if any(not req<=r.keys() or r.get('attempt_error') or r['exit']!=0 for r in rs):raise RuntimeError('bad sample')
 s={'sample_count':32,'failed_slots':0,'cells':{},'paired_R_minus_M':{}}
 for w in [1,12]:
  for v in ['M','R']:
   xs=[r['wall_ns']/1e9 for r in rs if r['workers']==w and r['variant']==v];s['cells'][f'{v}-w{w}']={'n':len(xs),'mean_s':statistics.mean(xs),'sd_s':statistics.stdev(xs),'min_s':min(xs),'max_s':max(xs)}
  ds=[]
  for p in range(1,9):
   q={r['variant']:r['wall_ns']/1e9 for r in rs if r['workers']==w and r['pair']==p};ds.append(q['R']-q['M'])
  mean=statistics.mean(ds);sd=statistics.stdev(ds);half=2.364624251*sd/(8**.5);s['paired_R_minus_M'][f'w{w}']={'n':8,'differences_s':ds,'mean_s':mean,'sd_s':sd,'ci95_t_s':[mean-half,mean+half]}
 (D/'summary.json').write_text(json.dumps(s,indent=2));print(json.dumps(s,indent=2))
def main():
 mode=sys.argv[1]
 if mode=='prepare':prepare()
 elif mode=='freeze':freeze()
 elif mode=='qualify':qualify()
 elif mode=='timed':timed()
 elif mode=='child':child(int(sys.argv[2]),int(sys.argv[3]),sys.argv[4],int(sys.argv[5]))
 elif mode=='analyze':analyze()
 else:raise SystemExit('unknown mode')
if __name__=='__main__':main()
