#!/usr/bin/env python3
"""Focused, source-built-dependency check; not aggregate Round3 acceptance."""
import hashlib, json, os, subprocess, sys, tempfile
from pathlib import Path
ROOT=Path('/home/velvet/worktrees/unforced-restart-20260909T202951Z')
E=Path('/home/velvet/research-builds/unforced-round2-clean-20260909T221339Z-evidence-attempt2')
assert Path.cwd()==ROOT
role=sys.argv[1]
assert role in {'WitnessFeasibility','CurlGeometry','MeanTopology','LocalizedForce'}
src=ROOT/f'Research/UnforcedRestart/Round3/{role}/Main.lean'
base=src.parent/'out'; base.mkdir(exist_ok=True)
out=Path(tempfile.mkdtemp(prefix='strict-',dir=base))
lib=out/'lib';lib.mkdir()
home=out/'home';home.mkdir()
resolver=json.loads((E/'research-replay/resolver.json').read_text())
lean=Path('/home/velvet/.elan/toolchains/leanprover--lean4---v4.34.0-rc2/bin/lean')
def sha(p):
 with Path(p).open('rb') as f:return hashlib.file_digest(f,'sha256').hexdigest()
assert sha(lean)=='79fb1d26fa5a39385d59fdc48a711a14b0710ca6480271acce99b4d177cea085'
env={'PATH':str(lean.parent)+':/usr/bin:/bin','HOME':str(home),'LEAN_NUM_THREADS':'1','OMP_NUM_THREADS':'1','OPENBLAS_NUM_THREADS':'1','LEAN_PATH':':'.join([str(lib)]+resolver['explicit'])}
cmd=['systemd-run','--user','--scope','--quiet','-p','CPUQuota=100%','-p','MemoryMax=6G','-p','MemorySwapMax=0','-p','TasksMax=32','timeout','600','env','-i',*[f'{k}={v}' for k,v in env.items()],str(lean),'-j1','-DautoImplicit=false','-DwarningAsError=true','-o',str(lib/'Main.olean'),'-i',str(lib/'Main.ilean'),str(src)]
record={'command':cmd,'cwd':str(ROOT),'source':str(src),'source_sha256':sha(src),'lean_sha256':sha(lean),'scope':'focused exports only; not aggregate semantic audit','resolver_evidence_sha256':sha(E/'research-replay/resolver.json')}
(out/'command.json').write_text(json.dumps(record,indent=2)+'\n')
with (out/'compile.log').open('w') as log:
 result=subprocess.run(cmd,cwd=ROOT,stdout=log,stderr=subprocess.STDOUT)
assert sha(src)==record['source_sha256'] and sha(lean)==record['lean_sha256']
record.update(exit=result.returncode,log_sha256=sha(out/'compile.log'),outputs={p.name:sha(p) for p in lib.iterdir() if p.is_file()})
(out/'result.json').write_text(json.dumps(record,indent=2)+'\n')
print(out);print((out/'compile.log').read_text());sys.exit(result.returncode)
