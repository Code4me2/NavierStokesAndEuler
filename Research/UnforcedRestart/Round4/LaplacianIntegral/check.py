#!/usr/bin/env python3
"""Focused new-source compilation; unique outputs, read-only historical inputs."""
import hashlib,json,os,re,shutil,subprocess,sys,tempfile
from pathlib import Path
ROOT=Path(__file__).resolve().parents[4]
HERE=Path(__file__).resolve().parent
PRIOR=ROOT/'Research/UnforcedRestart/Round3/ValidationRepair/replay-1oafv980/receipt.json'
def sha(p):
    with Path(p).open('rb') as f:return hashlib.file_digest(f,'sha256').hexdigest()
r=json.loads(PRIOR.read_text())
for p,h in (r['pins']|r['artifacts']).items():
    assert sha(p)==h,p
source=Path(sys.argv[1]); assert source.parts[:3]==('Research','UnforcedRestart','Round4')
text=(ROOT/source).read_text()
assert not re.search(r'\b(sorry|admit|axiom|unsafe)\b',re.sub(r'/\-.*?\-/|--[^\n]*','',text,flags=re.S))
out=Path(tempfile.mkdtemp(prefix='strict-',dir=HERE)); lib=out/'lib'
oldlib=Path(r['environment']['LEAN_PATH'].split(':')[0]); shutil.copytree(oldlib,lib)
inputs={str(p):sha(p) for p in oldlib.rglob('*') if p.is_file()}
for arg in sys.argv[2:]:
    f=json.loads(Path(arg).read_text()); assert f['exit']==0
    assert sha(ROOT/f['source'])==f['source_sha256']
    for p,h in f['outputs'].items():
        assert sha(p)==h
        q=lib/Path(p).relative_to(Path(f['lib']));q.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(p,q)
        inputs[p]=h
    inputs[str(ROOT/f['source'])]=f['source_sha256']
env=dict(r['environment']);env['LEAN_PATH']=':'.join([str(lib)]+env['LEAN_PATH'].split(':')[1:]);env['HOME']=str(out/'home');Path(env['HOME']).mkdir()
lean=r['runs'][0]['command'];lean=lean[lean.index('-j1')-1]
target=lib/source.with_suffix('.olean'); target.parent.mkdir(parents=True,exist_ok=True)
cmd=['systemd-run','--user','--scope','--quiet','-p','CPUQuota=100%','-p','MemoryMax=6G','-p','MemorySwapMax=0','-p','TasksMax=32','timeout','600','env','-i',*[f'{k}={v}' for k,v in env.items()],lean,'-j1','-DautoImplicit=false','-DwarningAsError=true','-o',str(target),'-i',str(target.with_suffix('.ilean')),str(source)]
row={'source':str(source),'source_sha256':sha(ROOT/source),'compiler_sha256':sha(lean),'prior_receipt_sha256':sha(PRIOR),'inputs':inputs,'command':cmd,'environment':env,'cwd':str(ROOT),'lib':str(lib)}
(out/'source.lean').write_text(text);(out/'command.json').write_text(json.dumps(row,indent=2)+'\n')
with (out/'compile.log').open('x') as log:result=subprocess.run(cmd,cwd=ROOT,stdout=log,stderr=subprocess.STDOUT)
log=(out/'compile.log').read_text();row.update(exit=result.returncode,log_sha256=sha(out/'compile.log'),outputs={str(p):sha(p) for p in target.parent.glob(target.stem+'.*')})
if result.returncode==0:
    assert not re.search(r'error:|warning:|sorryAx',log)
    closures=re.findall(r"'([^']+)' depends on axioms:\s*\[([^]]*)\]",log)
    for name,ax in closures:assert set(a.strip() for a in ax.split(','))<={'propext','Classical.choice','Quot.sound'},name
    row['closures']=closures
(out/'receipt.json').write_text(json.dumps(row,indent=2)+'\n')
print(out);print(log);sys.exit(result.returncode)
