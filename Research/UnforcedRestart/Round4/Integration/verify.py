#!/usr/bin/env python3
"""Read-only verification by default; --record creates a unique Round4 receipt."""
import hashlib,json,os,re,subprocess,sys,tempfile
from pathlib import Path
ROOT=Path(__file__).resolve().parents[4]
HERE=Path(__file__).resolve().parent
SNAP=Path('/home/velvet/research-builds/unforced-round4-preserved-sf3yoys5')
PIN='d1087cfeda45b6cf8d62e5ad8e89e2230cbcd84038c6fabfcf831a27cdee026a'
def sha(p):
    with Path(p).open('rb') as f:return hashlib.file_digest(f,'sha256').hexdigest()
def load(p):return json.loads(Path(p).read_text())
def require(b,msg):
    if not b:raise RuntimeError(msg)
def git(*args):return subprocess.check_output(['git',*args],cwd=ROOT,text=True)
require(sha(SNAP/'manifest.json')==PIN,'external manifest pin')
b=load(SNAP/'manifest.json')
for p,h in b['files'].items():
    q=ROOT/p
    require(('symlink:'+os.readlink(q) if q.is_symlink() else sha(q))==h,'preservation '+p)
for p,h in b['snapshot_sources'].items():
    q=SNAP/'source'/p
    require(sha(q)==h and q.stat().st_mode & 0o222 == 0,'snapshot '+p)
require(git('rev-parse','HEAD')==b['head'],'HEAD')
refs_now=git('show-ref')
refs_unchanged=refs_now==b['refs']
require(sha(b['index'])==b['index_sha256'],'index')
require(not git('diff','--no-ext-diff') and not git('diff','--cached','--no-ext-diff'),'tracked/index diff')
for p in ROOT.rglob('*'):
    q=p.relative_to(ROOT)
    if q.parts[0] in ('.git','.lake') or not (p.is_file() or p.is_symlink()):continue
    if str(q) not in b['files']:
        require(str(q).startswith(('Research/UnforcedRestart/Round4/','docs/unforced-restart/round4/')),'unauthorized addition '+str(q))
f=load(HERE/'FREEZE-2.json'); receipts=[]; newmods={}
for row in f['rows']:
    p=ROOT/row['receipt']; require(sha(p)==row['receipt_sha256'],'freeze receipt')
    r=load(p); require(r['exit']==0 and sha(ROOT/r['source'])==row['source_sha256']==r['source_sha256'],'source')
    require(row['outputs']==r['outputs'],'frozen objects')
    log=p.parent/'compile.log';require(sha(log)==r['log_sha256'],'log')
    require(not re.search(r'error:|warning:|sorryAx',log.read_text()),'accepted diagnostic')
    for q,h in (r['inputs']|r['outputs']).items():require(sha(q)==h,'object/input '+q)
    expected=re.findall(r'^#print axioms (\w+)$',(ROOT/r['source']).read_text(),re.M)
    actual=[name.rsplit('.',1)[-1] for name,ax in r['closures']]
    require(actual==expected,'exact printed export coverage')
    for name,ax in r['closures']:
        require(set(a.strip() for a in ax.split(','))<={'propext','Classical.choice','Quot.sound'},name)
    mod=r['source'][:-5].replace('/','.')
    newmods[mod]=r
    receipts.append({'path':str(p),'sha256':sha(p),'exports':len(actual)})
audit=HERE/'strict-s8judypi/receipt.json';a=load(audit)
require(a['exit']==0 and sha(ROOT/a['source'])==a['source_sha256'],'aggregate source')
log=audit.parent/'compile.log';require(sha(log)==a['log_sha256'],'aggregate log')
text=log.read_text();require(not re.search(r'error:|warning:|sorryAx',text),'aggregate diagnostics')
for q,h in (a['inputs']|a['outputs']).items():require(sha(q)==h,'aggregate object/input '+q)
mods=re.findall(r'^MODULE\t(.+)$',text,re.M)
coverage=re.findall(r'^COVERAGE\t([^\t]+)\t([^\t]+)\t\[([^]]*)\]$',text,re.M)
count=int(re.search(r'^COVERAGE_COUNT\t(\d+)$',text,re.M)[1]);require(count==len(coverage),'coverage count')
require(len(set(n for _,n,_ in coverage))==count,'duplicate constant')
for m,n,ax in coverage:require(set(filter(None,ax.split(',')))<={'propext','Classical.choice','Quot.sound'},n)
prior=ROOT/'Research/UnforcedRestart/Round3/ValidationRepair/aggregate-btau1ozq/receipt.json'
history={x['module']:x for x in load(prior)['correspondence']}
lean=Path(a['command'][a['command'].index('-j1')-1]);core=lean.parent.parent/'lib/lean'
roots=[Path(s) for s in a['environment']['LEAN_PATH'].split(':')]+[core]
correspondence=[]
for m in mods:
    rel=Path(m.replace('.','/')).with_suffix('.olean')
    # Lean resolves a package prefix from its first matching root.
    prefix=next((p for p in roots if (p/rel.parts[0]).exists()),None)
    require(prefix is not None and (prefix/rel).is_file(),'unresolved module '+m)
    obj=prefix/rel
    if m in newmods:
        r=newmods[m]; original=Path(r['lib'])/rel
        require(sha(obj)==r['outputs'][str(original)],'new object provenance '+m)
        source=ROOT/r['source'];h=r['source_sha256']; provenance='new focused strict source build'
    else:
        require(m in history,'uncovered historical module '+m)
        old=history[m];require(sha(obj)==old['object_sha256'],'historical object '+m)
        source=Path(old['source']);h=old['source_sha256'];provenance='frozen prior aggregate/source-build provenance'
    require(sha(source)==h,'module source '+m)
    correspondence.append({'module':m,'object':str(obj),'object_sha256':sha(obj),'source':str(source),'source_sha256':h,'provenance':provenance})
negative=HERE/'strict-7b4qdio7/receipt.json';n=load(negative)
require(n['exit']!=0 and sha(ROOT/n['source'])==n['source_sha256'],'acceptance must fail closed')
require(sha(negative.parent/'compile.log')==n['log_sha256'],'acceptance log')
require('Unknown identifier `UnforcedRestart.Round4.Integration.selected_force_cell_mean_zero`' in (negative.parent/'compile.log').read_text(),'wrong acceptance failure')
result={'status':'PARTIAL_FAILURE_END_TO_END_TARGET_NOT_PROVED','preserved_files':len(b['files']),
    'external_snapshot':str(SNAP),'external_manifest_sha256':PIN,'head_index':'unchanged','tracked_index_diff':'empty',
    'preservation_status':'PASS' if refs_unchanged else 'FAIL_SHARED_REFS_CHANGED',
    'refs_before':b['refs'],'refs_after':refs_now,
    'accepted_sources':receipts,'printed_exports':sum(r['exports'] for r in receipts),
    'aggregate_receipt':str(audit),'aggregate_receipt_sha256':sha(audit),'project_constants':count,'modules':len(mods),
    'correspondence':correspondence,'prior_aggregate_sha256':sha(prior),'acceptance_receipt':str(negative),
    'acceptance_receipt_sha256':sha(negative),'acceptance_exit':n['exit'],
    'scope':'New focused strict compilation and imported project/helper axiom audit; source-built dependencies reused read-only. Installed compiler/core/runtime/host trusted. No independent Comparator/Nanoda or full rebuild.'}
if '--record' in sys.argv:
    out=Path(tempfile.mkdtemp(prefix='verification-',dir=HERE));result['new_tree_hashes']={str(p.relative_to(ROOT)):sha(p) for base in [ROOT/'Research/UnforcedRestart/Round4',ROOT/'docs/unforced-restart/round4'] for p in base.rglob('*') if p.is_file()}
    (out/'receipt.json').write_text(json.dumps(result,indent=2)+'\n');print(out/'receipt.json')
print(json.dumps({k:v for k,v in result.items() if k not in ('correspondence','new_tree_hashes')},indent=2))
sys.exit(0 if refs_unchanged else 1)
