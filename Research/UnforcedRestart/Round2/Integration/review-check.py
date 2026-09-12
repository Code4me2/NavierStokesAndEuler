#!/usr/bin/env python3
"""Record review repair checks; never launches/retries the blocked clean build."""
import hashlib
import json
from pathlib import Path
import subprocess
import time

ROOT=Path(__file__).resolve().parents[4]
TOOLS=Path(__file__).resolve().parent
E=TOOLS/'evidence'/('review-'+time.strftime('%Y%m%dT%H%M%SZ',time.gmtime()))
E.mkdir(exist_ok=False)
def sha(p):
    with p.open('rb') as f: return hashlib.file_digest(f,'sha256').hexdigest()
def run(label,args):
    log=E/(label+'.log')
    with log.open('w') as f:
        p=subprocess.run(args,cwd=ROOT,stdout=f,stderr=subprocess.STDOUT)
    record={'command':args,'cwd':str(ROOT),'exit':p.returncode,'log':str(log),'sha256':sha(log)}
    (E/(label+'.json')).write_text(json.dumps(record,indent=2)+'\n')
    print(label,p.returncode,flush=True)
    return p.returncode

external=Path('/home/velvet/research-builds/unforced-round2-clean-20260909T221339Z')
old=external.with_name(external.name+'-evidence')
verdict=json.loads((old/'CLEAN-VERDICT.json').read_text())
assert verdict['lake_invocations']==0 and verdict['project_or_dependency_compilations']==0
for trace in verdict['traces']:
    assert sha(Path(trace['path']))==trace['sha256']
for name in ['build.log','build-status.json','build-command.json']:
    assert not (old/name).exists(), 'External campaign state changed; review required'
initial=json.loads((old/'initial-inventory.json').read_text())
for source in initial['sources']:
    assert sha(external/source['path'])==source['sha256'], source['path']
pins=json.loads((ROOT/'lake-manifest.json').read_text())['packages']
for pin in pins:
    actual=subprocess.check_output(['git','rev-parse','HEAD'],cwd=external/'.lake/packages'/pin['name'],text=True).strip()
    assert actual==pin['rev']
(E/'clean-provenance-recheck.json').write_text(json.dumps({
    'status':'BLOCKED_NOT_RETRIED','external':str(external),'pins':pins,
    'tracked_source_hashes_verified':len(initial['sources']),
    'evidence':[{'path':str(p),'sha256':sha(p)} for p in sorted(old.iterdir()) if p.is_file()],
    'traces':[{k:t[k] for k in ['path','tracked','sha256']} for t in verdict['traces']],
    'lake_invocations_this_pass':0,'source_build_compilations_this_pass':0,
    'policy':'No exemption or deletion authorized; successful pinned-source build chain absent.'},indent=2)+'\n')
inputs=[TOOLS/'review-check.py',TOOLS/'validate.py',TOOLS/'selftest.py',TOOLS.parent/'MANIFEST.json']
m=json.loads((TOOLS.parent/'MANIFEST.json').read_text())
inputs += [ROOT/e['path'] for e in m['inherited_accepted']+m['accepted_round2']+[m['audit']]]
(E/'sources.json').write_text(json.dumps([{'path':str(p.relative_to(ROOT)),'sha256':sha(p)} for p in inputs],indent=2)+'\n')
assert run('selftest',['python3',str(TOOLS/'selftest.py')])==0
assert run('clean-negative',['python3',str(TOOLS/'validate.py'),'--clean'])==1
# Separate cached campaign, explicitly not a fallback clean resolver.
assert run('cached-validation',['python3',str(TOOLS/'validate.py')])==0
print(E,flush=True)
