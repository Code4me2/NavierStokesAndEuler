#!/usr/bin/env python3
"""Read-only final verification. Receipt generation belongs to record_final.py."""
import hashlib, json, os, re, subprocess
from pathlib import Path
HERE=Path(__file__).resolve().parent
ROOT=HERE.parents[3]
SNAP=Path('/home/velvet/research-builds/unforced-round4-preserved-sf3yoys5')
PIN='d1087cfeda45b6cf8d62e5ad8e89e2230cbcd84038c6fabfcf831a27cdee026a'
ALLOWED={'propext','Classical.choice','Quot.sound'}
def sha(p):
    with Path(p).open('rb') as f: return hashlib.file_digest(f,'sha256').hexdigest()
def load(p): return json.loads(Path(p).read_text())
def require(b,msg):
    if not b: raise RuntimeError(msg)
def git(*args): return subprocess.check_output(['git',*args],cwd=ROOT,text=True)
def verify():
    freeze=load(HERE/'FINAL-MANIFEST.json')
    for p,h in freeze['files'].items(): require(sha(ROOT/p)==h,'frozen file '+p)
    require(sha(SNAP/'manifest.json')==PIN,'historical manifest')
    b=load(SNAP/'manifest.json')
    for p,h in b['files'].items():
        q=ROOT/p
        require(('symlink:'+os.readlink(q) if q.is_symlink() else sha(q))==h,'preservation '+p)
    for p,h in b['snapshot_sources'].items():
        q=SNAP/'source'/p
        require(sha(q)==h and q.stat().st_mode & 0o222 == 0,'snapshot '+p)
    require(git('rev-parse','HEAD')==b['head'],'HEAD')
    require(sha(b['index'])==b['index_sha256'],'index')
    require(not git('diff','--no-ext-diff') and not git('diff','--cached','--no-ext-diff'),'tracked changes')
    for p in ROOT.rglob('*'):
        q=p.relative_to(ROOT)
        if q.parts[0] in ('.git','.lake') or not (p.is_file() or p.is_symlink()): continue
        if str(q) not in b['files']:
            require(str(q).startswith(('Research/UnforcedRestart/Round4/','docs/unforced-restart/round4/')),'unauthorized addition '+str(q))
    refs=git('show-ref')
    chain=load(ROOT/freeze['chain'])
    require(chain['status']=='PASS','chain incomplete')
    newmods={};exports=0; rows=[]
    for p in chain['receipts']:
        r=load(p);source=ROOT/r['source'];log=Path(p).parent/'compile.log'
        require(r['exit']==0 and sha(source)==r['source_sha256'],'strict source '+str(source))
        require(sha(log)==r['log_sha256'],'strict log')
        require(not re.search(r'error:|warning:|sorryAx',log.read_text()),'diagnostic')
        cmd=r['command']
        require('-DautoImplicit=false' in cmd and '-DwarningAsError=true' in cmd and '-j1' in cmd,'strict flags')
        lean=Path(cmd[cmd.index('-j1')-1]);require(sha(lean)==r['compiler_sha256'],'compiler')
        require(sha(ROOT/'Research/UnforcedRestart/Round3/ValidationRepair/replay-1oafv980/receipt.json')==r['prior_receipt_sha256'],'clean replay pin')
        for q,h in (r['inputs']|r['outputs']).items(): require(sha(q)==h,'input/object '+q)
        expected=re.findall(r'^#print axioms ([\w.]+)$',source.read_text(),re.M)
        actual=[n.rsplit('.',1)[-1] for n,_ in r['closures']]
        require(actual==[n.rsplit('.',1)[-1] for n in expected],'export coverage')
        for n,ax in r['closures']: require(set(filter(None,(a.strip() for a in ax.split(','))))<=ALLOWED,n)
        exports+=len(actual)
        newmods[r['source'][:-5].replace('/','.')]=r
        rows.append({'receipt':p,'sha256':sha(p),'exports':actual})
    a=load(chain['receipts'][-1]);text=(Path(chain['receipts'][-1]).parent/'compile.log').read_text()
    mods=re.findall(r'^MODULE\t(.+)$',text,re.M)
    coverage=re.findall(r'^COVERAGE\t([^\t]+)\t([^\t]+)\t\[([^]]*)\]$',text,re.M)
    count=int(re.search(r'^COVERAGE_COUNT\t(\d+)$',text,re.M)[1])
    require(count==len(coverage)==len(set(n for _,n,_ in coverage)) and count>0,'aggregate coverage')
    for m,n,ax in coverage: require(set(filter(None,ax.split(',')))<=ALLOWED,n)
    prior=ROOT/'Research/UnforcedRestart/Round3/ValidationRepair/aggregate-btau1ozq/receipt.json'
    history={x['module']:x for x in load(prior)['correspondence']}
    lean=Path(a['command'][a['command'].index('-j1')-1]);core=lean.parent.parent/'lib/lean'
    roots=[Path(s) for s in a['environment']['LEAN_PATH'].split(':')]+[core]
    correspondence=[]
    for m in mods:
        rel=Path(m.replace('.','/')).with_suffix('.olean')
        prefix=next((p for p in roots if (p/rel.parts[0]).exists()),None)
        require(prefix is not None and (prefix/rel).is_file(),'unresolved '+m)
        obj=prefix/rel
        if m in newmods:
            r=newmods[m];original=Path(r['lib'])/rel
            require(sha(obj)==r['outputs'][str(original)],'new provenance '+m)
            source=ROOT/r['source'];h=r['source_sha256'];provenance='fresh strict Round4 source build'
        else:
            require(m in history,'uncovered historical module '+m)
            old=history[m];require(sha(obj)==old['object_sha256'],'historical object '+m)
            source=Path(old['source']);h=old['source_sha256'];provenance='pinned historical source-build correspondence'
        require(sha(source)==h,'module source '+m)
        correspondence.append({'module':m,'object':str(obj),'object_sha256':sha(obj),'source':str(source),'source_sha256':h,'provenance':provenance})
    acceptance=load(chain['receipts'][-2])
    require(acceptance['source'].endswith('/Acceptance.lean') and acceptance['exit']==0,'acceptance')
    return {'mathematical_status':'PASS_SELECTED_FORCE_COMPONENT_CELL_MEAN_ZERO_ON_ICC',
        'preservation_status':'PASS' if refs==b['refs'] else 'FAIL_SHARED_REFS_CHANGED',
        'preserved_files':len(b['files']),'head_index':'unchanged','refs_before':b['refs'],'refs_after':refs,
        'manifest_sha256':sha(HERE/'FINAL-MANIFEST.json'),'accepted_sources':rows,'printed_exports':exports,
        'project_constants':count,'modules':len(mods),'correspondence':correspondence,
        'prior_aggregate_sha256':sha(prior),'acceptance_exit':acceptance['exit'],
        'scope':'Fresh strict Round4 chain; historical source-built dependencies reused read-only. Compiler/core/runtime/host trusted; no independent kernel check.',
        'nonconclusion':'Zero mean does not decide curl or imply gradient forcing.'}
if __name__=='__main__':
    result=verify()
    print(json.dumps({k:v for k,v in result.items() if k!='correspondence'},indent=2))
    raise SystemExit(0 if result['preservation_status']=='PASS' else 1)
