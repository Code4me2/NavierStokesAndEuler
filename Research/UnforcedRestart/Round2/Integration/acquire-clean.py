#!/usr/bin/env python3
"""Single source-only acquisition campaign; no Lake/hooks/build/cache invocation.
Stops on any failure; do not rerun a failed campaign without review.
"""
import hashlib, json, os, pathlib, shutil, subprocess, time
R = pathlib.Path('/home/velvet/worktrees/unforced-restart-20260909T202951Z')
C = pathlib.Path('/home/velvet/research-builds/unforced-round2-clean-20260909T221339Z')
E = C.with_name(C.name + '-evidence')
S = pathlib.Path('/home/velvet/research-snapshots/unforced-round1-20260909T221339Z')
BASE = '597692fa5d55e07d810b2d96ead1a67972585425'

def run(cmd, cwd=None):
    print(json.dumps({'time':time.time(), 'cwd':str(cwd), 'command':cmd}), flush=True)
    subprocess.run(cmd, cwd=cwd, env=env, check=True, timeout=180)

if __name__ == '__main__':
    E.mkdir(parents=True, exist_ok=True)
    status = {'status':'FAIL', 'scope':'source acquisition only; not a clean build'}
    try:
        cg = pathlib.Path('/sys/fs/cgroup' + pathlib.Path('/proc/self/cgroup').read_text().split('0::')[1].strip())
        controls = {f:(cg/f).read_text().strip() for f in ['cpu.max','memory.max','memory.swap.max','pids.max']}
        assert controls == {'cpu.max':'200000 100000','memory.max':'17179869184','memory.swap.max':'0','pids.max':'128'}, controls
        (E/'controls.json').write_text(json.dumps(controls, indent=2))
        assert shutil.disk_usage(C.parent).free > 80*1024**3
        assert hashlib.sha256((S/'SHA256SUMS').read_bytes()).hexdigest() == '192e15dc0ff1cb79cae02a19941e0f816dc194e91123c205153ccf808322a488'
        home=E/'home'; home.mkdir(exist_ok=True)
        env={'PATH':'/usr/bin:/bin', 'HOME':str(home), 'XDG_CACHE_HOME':str(home/'cache'),
             'GIT_CONFIG_NOSYSTEM':'1','GIT_CONFIG_GLOBAL':'/dev/null','GIT_TERMINAL_PROMPT':'0',
             'MATHLIB_NO_CACHE_ON_UPDATE':'1', 'LEAN_NUM_THREADS':'2', 'OMP_NUM_THREADS':'1',
             'OPENBLAS_NUM_THREADS':'1', 'CC_THREADS':'1'}
        (E/'environment.json').write_text(json.dumps(env,indent=2))
        run(['sha256sum','-c','SHA256SUMS'], S)
        assert not C.exists(), 'Campaign path already exists; review required'
        run(['git','-c','core.hooksPath=/dev/null','clone','--no-local','--no-hardlinks','--no-checkout',str(R),str(C)])
        run(['git','-c','core.hooksPath=/dev/null','checkout','--detach',BASE], C)
        assert not (C/'.git/objects/info/alternates').exists()
        pins=json.loads((C/'lake-manifest.json').read_text())['packages']
        for pin in pins:
            assert shutil.disk_usage(C).free > 80*1024**3
            p=C/'.lake/packages'/pin['name']; p.mkdir(parents=True)
            run(['git','-c','core.hooksPath=/dev/null','init',str(p)])
            run(['git','-C',str(p),'remote','add','origin',pin['url']])
            run(['git','-c','core.hooksPath=/dev/null','-C',str(p),'fetch','--depth=1','origin',pin['rev']])
            run(['git','-c','core.hooksPath=/dev/null','-C',str(p),'checkout','--detach',pin['rev']])
        # A subsequent reviewed source-build driver is required; never certify mere acquisition.
        status['status']='SOURCES_ACQUIRED_BUILD_NOT_RUN'
    except Exception as exc:
        status['error']=repr(exc)
        raise
    finally:
        (E/'acquisition-status.json').write_text(json.dumps(status,indent=2)+'\n')
