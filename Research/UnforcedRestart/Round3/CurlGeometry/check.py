#!/usr/bin/env python3
"""Unique-output focused check; frozen wrapper replay, no dependency build."""
import hashlib,json,os,subprocess,tempfile
from pathlib import Path
root=Path('/home/velvet/worktrees/unforced-restart-20260909T202951Z')
role=root/'Research/UnforcedRestart/Round3/CurlGeometry'
run=Path(tempfile.mkdtemp(prefix='strict-',dir=role/'out'))
lib=run/'lib'; lib.mkdir(); home=run/'home';home.mkdir()
r=json.loads((root/'docs/unforced-restart/round3/snapshot/external-evidence.json').read_text())['resolver']
lean=Path(r['implicit_core']).parents[1]/'bin/lean'
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
assert sha(lean)=='79fb1d26fa5a39385d59fdc48a711a14b0710ca6480271acce99b4d177cea085'
wrapper=root/'Research/UnforcedRestart/Round3/WitnessFeasibility/Main.lean'
assert sha(wrapper)=='7d77092a3da73faedebac0a052c6fd2ce6fc46d340f48f796dd5e45f926be8da'
env={'PATH':str(lean.parent)+':/usr/bin:/bin','HOME':str(home),'LEAN_NUM_THREADS':'1','OMP_NUM_THREADS':'1','OPENBLAS_NUM_THREADS':'1','LEAN_PATH':':'.join([str(lib)]+r['explicit'])}
records=[]
for src in [wrapper,role/'Main.lean']:
    text=src.read_text()
    import re
    assert not re.search(r'\b(sorry|admit|axiom|unsafe|native_decide|set_option)\b',text)
    dst=lib/src.relative_to(root).with_suffix('.olean');dst.parent.mkdir(parents=True,exist_ok=True)
    cmd=['systemd-run','--user','--scope','--quiet','-p','CPUQuota=100%','-p','MemoryMax=6G','-p','MemorySwapMax=0','-p','TasksMax=32','timeout','600','env','-i',*[f'{k}={v}' for k,v in env.items()],str(lean),'-j1','-DautoImplicit=false','-DwarningAsError=true','-o',str(dst),'-i',str(dst.with_suffix('.ilean')),str(src)]
    log=run/(src.parent.name+'.log')
    rec={'source':str(src),'source_sha256':sha(src),'command':cmd,'cwd':str(root),'lean_sha256':sha(lean)}
    records.append(rec)
    (run/'manifest.json').write_text(json.dumps(records,indent=2)+'\n')
    with log.open('w') as f:p=subprocess.run(cmd,cwd=root,stdout=f,stderr=subprocess.STDOUT)
    rec.update(exit=p.returncode,log=str(log),log_sha256=sha(log),outputs={str(q):sha(q) for q in [dst,dst.with_suffix('.ilean')] if q.exists()})
    assert sha(src)==rec['source_sha256']
    (run/'manifest.json').write_text(json.dumps(records,indent=2)+'\n')
    print(run,src,p.returncode,flush=True);print(log.read_text(),flush=True)
    if p.returncode:raise SystemExit(p.returncode)
