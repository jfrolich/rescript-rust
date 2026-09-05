#!/usr/bin/env python3
"""Separate profiling runs; timing acceptance uses measurement_rebaseline.py.
Run under lockf. Optional args select kinds (default phases/counters/allocator/
sample-full/phases-B/sample-B). Census kinds require instrumented archive builds.
"""
import subprocess,sys
from measurement_rebaseline import D, env, clean, command, outputs
kinds=sys.argv[1:] or ['phases','counters','allocator','sample-full','phases-B','sample-B']
for w in [1,12]:
    for kind in kinds:
        if kind=='sample-B' and w!=1: continue
        v='B' if kind.endswith('-B') else 'A'
        clean(v,w); e=env(v,w);cmd=command(v)
        if kind.startswith('phases'): e.update(RESCRIPT_PHASE_TIMINGS='1',RESCRIPT_MODULE_TIMINGS='1',RESCRIPT_SCHEDULER_COUNTERS='1')
        if kind=='counters': e.update(RESCRIPT_COMPILER_COUNTERS='1')
        if kind=='allocator': e.update(MIMALLOC_SHOW_STATS='1')
        if kind in ('census','census-trace'): cmd[0]=str(D/f'bin/rescript-{kind}')
        name=f'profile-{kind}-w{w}'
        with (D/f'logs/{name}.log').open('w') as f:
            if kind.startswith('sample'):
                p=subprocess.Popen(cmd,env=e,stdout=f,stderr=f)
                subprocess.run(['/usr/bin/sample',str(p.pid),'25' if w==1 else '8','1','-file',str(D/f'{name}.txt')],stdout=f,stderr=f,timeout=40)
                code=p.wait(timeout=180)
            else:
                code=subprocess.run(['/usr/bin/time','-lp']+cmd,env=e,stdout=f,stderr=f,timeout=180).returncode
        n,h,_=outputs()
        print(name,code,n,h,flush=True)
        if code or n!=5048: raise RuntimeError('invalid profile')
