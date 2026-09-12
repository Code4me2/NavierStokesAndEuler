#!/usr/bin/env python3
"""One no-cache source build; stop at first root error, OOM, timeout or disk floor.
Run only inside PLAN's 2 CPU /16 GiB/no-swap cgroup after acquire-clean.py.
No retry or artifact substitution. This driver cannot issue clean acceptance.
"""
import hashlib, json, os, pathlib, shutil, signal, subprocess, time
C=pathlib.Path('/home/velvet/research-builds/unforced-round2-clean-20260909T221339Z')
E=C.with_name(C.name+'-evidence')
P=pathlib.Path('/home/velvet/.elan/toolchains/leanprover--lean4---v4.34.0-rc2').resolve()
def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
def cap(args,cwd=C): return subprocess.check_output(args,cwd=cwd,text=True).strip()
def main():
    assert not (E/'build-driver.exit').exists(), 'Prior campaign attempt requires review'
    assert not (E/'build-status.json').exists(), 'No silent campaign retry'
    cg=pathlib.Path('/sys/fs/cgroup'+pathlib.Path('/proc/self/cgroup').read_text().split('0::')[1].strip())
    controls={f:(cg/f).read_text().strip() for f in ['cpu.max','memory.max','memory.swap.max','pids.max']}
    assert controls=={'cpu.max':'200000 100000','memory.max':'17179869184','memory.swap.max':'0','pids.max':'128'}
    (E/'build-controls.json').write_text(json.dumps(controls,indent=2))
    pins=json.loads((C/'lake-manifest.json').read_text())['packages']
    roots=[C]+[C/'.lake/packages'/p['name'] for p in pins]
    configs=[]; sources=[]; artifacts=[]; nested=[]
    for root in roots:
        if root!=C:
            pin=next(p for p in pins if p['name']==root.name)
            assert cap(['git','rev-parse','HEAD'],root)==pin['rev']
        assert not cap(['git','diff','HEAD','--'],root)
        assert not cap(['git','diff','--cached','--'],root)
        for name in cap(['git','ls-files'],root).splitlines():
            f=root/name
            assert f.resolve().is_relative_to(C)
            sources.append({'path':str(f.relative_to(C)),'sha256':sha(f)})
        for name in ['lakefile.lean','lakefile.toml','lake-manifest.json','lean-toolchain']:
            f=root/name
            if f.exists(): configs.append({'path':str(f.relative_to(C)),'sha256':sha(f),'text':f.read_text()})
        m=root/'lake-manifest.json'
        if root!=C and m.exists():
            for p in json.loads(m.read_text()).get('packages',[]):
                q=next((q for q in pins if p['name']==q['name']),None)
                nested.append({'package':root.name,'dependency':p['name'],'nested_rev':p.get('rev'),'resolved_rev':q and q['rev']})
    for f in C.rglob('*'):
        if f.is_symlink(): assert f.resolve().is_relative_to(C)
        if f.is_file() and '.git' not in f.parts and (any(x in f.name for x in ['.olean','.ilean']) or f.suffix in ['.o','.a','.so','.dll','.dylib','.trace','.bc']): artifacts.append(str(f.relative_to(C)))
    (E/'initial-inventory.json').write_text(json.dumps({'sources':sources,'configs':configs,'nested':nested,'preexisting_artifacts':artifacts},indent=2)+'\n')
    assert not artifacts, artifacts
    assert cap(['git','rev-parse','HEAD'])=='597692fa5d55e07d810b2d96ead1a67972585425'
    env=json.loads((E/'environment.json').read_text())
    env.update(PATH=str(P/'bin')+':/usr/bin:/bin', LEAN_SYSROOT=str(P), LAKE_HOME=str(P), LAKE_CACHE_DIR=str(E/'home/lake-cache'))
    (E/'build-environment.json').write_text(json.dumps(env,indent=2))
    trust={'version':cap([str(P/'bin/lean'),'--version']), 'prefix':str(P),
           'executables':{str((P/'bin'/n).resolve()):sha((P/'bin'/n).resolve()) for n in ['lean','lake','leanc','clang'] if (P/'bin'/n).exists()},
           'host':cap(['uname','-a']), 'core_trust':'Installed official release asserted by installation; not bootstrapped or independently authenticated here.'}
    (E/'toolchain.json').write_text(json.dumps(trust,indent=2)+'\n')
    cmd=[str(P/'bin/lake'),'--no-cache','--verbose','build','Common','NavierStokes','Euler']
    (E/'build-command.json').write_text(json.dumps(cmd))
    start=time.time(); reason=None
    with (E/'build.log').open('w') as log:
        proc=subprocess.Popen(cmd,cwd=C,env=env,stdout=log,stderr=subprocess.STDOUT,start_new_session=True)
        while proc.poll() is None:
            time.sleep(1)
            text=(E/'build.log').read_text(errors='replace')
            if '\nerror:' in '\n'+text or '\n✖' in text: reason='first build error; no retry'
            if shutil.disk_usage(C).free<80*1024**3: reason='80 GiB disk floor'
            if time.time()-start>28800: reason='8-hour wall budget'
            if reason:
                os.killpg(proc.pid,signal.SIGTERM)
                try: proc.wait(timeout=10)
                except subprocess.TimeoutExpired: os.killpg(proc.pid,signal.SIGKILL)
                break
        rc=proc.wait()
    (E/'build-status.json').write_text(json.dumps({'exit':rc,'stop_reason':reason,'seconds':time.time()-start,
        'status':'LIBRARIES_BUILT_NOT_ACCEPTED' if rc==0 and reason is None else 'CLEAN_BUILD_FAILED',
        'resource_final':{f:(cg/f).read_text() for f in ['memory.events','memory.peak','cpu.stat','pids.events']}},indent=2)+'\n')
    raise SystemExit(0 if rc==0 and reason is None else 1)
if __name__=='__main__': main()
