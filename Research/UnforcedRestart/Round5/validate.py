#!/usr/bin/env python3
"""Additive focused validation. Historical validators/receipts are read-only.
Usage: validate.py init | validate.py compile SOURCE | validate.py audit
One unique external workspace; every attempt has a separate immutable log/receipt.
"""
import sys
sys.dont_write_bytecode = True
import json, os, re, shutil, subprocess, tempfile
from pathlib import Path
ROOT = Path(__file__).resolve().parents[3]
HERE = Path(__file__).resolve().parent
OLD = ROOT / 'Research/UnforcedRestart/Round3/ValidationRepair'
sys.path.insert(0, str(OLD))
import audit as established
import aggregate
sha, load, require = established.sha, established.load, established.require
STATE = HERE / 'workspace.json'
SNAP = Path('/home/velvet/research-snapshots/research-and-companion-20260912T192848Z/research-manifest.json')
def save(p, r): p.write_text(json.dumps(r, indent=2) + '\n')
def files():
    return {str(p.relative_to(ROOT)): ('symlink:'+os.readlink(p) if p.is_symlink() else sha(p))
            for p in ROOT.rglob('*') if (p.is_file() or p.is_symlink())
            and p.relative_to(ROOT).parts[0] not in ('.git','.lake')}
def git(*args): return subprocess.check_output(['git',*args],cwd=ROOT,text=True)
def preserved(w):
    now=files()
    for p,h in w['baseline'].items():
        # The validator itself is new Round5 work, not a frozen inherited input.
        if p == str(Path(__file__).relative_to(ROOT)): continue
        require(now.get(p)==h, 'preserved '+p)
    for p in now.keys()-w['baseline'].keys():
        require(p.startswith(('Research/UnforcedRestart/Round5/','docs/unforced-restart/round5/')), 'addition '+p)
    require(git('rev-parse','HEAD')==w['head'] and git('show-ref')==w['refs'], 'HEAD/refs')
    require(sha(w['index'])==w['index_sha256'], 'index')
    require(git('diff','--no-ext-diff')==w['diff'] and git('diff','--cached','--no-ext-diff')==w['cached'], 'diffs')
    require(sha(SNAP)==w['snapshot_sha256'], 'snapshot manifest')
    for p,r in load(SNAP)['files'].items():
        if 'symlink' in r:
            require((ROOT/p).is_symlink() and os.readlink(ROOT/p)==r['symlink'], 'snapshot symlink '+p)
        else:
            require(sha(ROOT/p)==r['sha256'], 'snapshot source '+p)
def history():
    r=load(OLD/'aggregate-btau1ozq/receipt.json')
    for p,h in r['artifacts'].items(): require(sha(p)==h, 'aggregate artifact '+p)
    require(sha(OLD/'aggregate.py')==r['checker_sha256'], 'aggregate tool')
    mods,cov=aggregate.parsed(Path(r['log']).read_text())
    require(mods==[x['module'] for x in r['correspondence']], 'old correspondence')
    require(len(mods)==r['modules'] and len(cov)==r['project_constants'], 'old counts')
    for x in r['correspondence']:
        require(sha(x['source'])==x['source_sha256'] and sha(x['object'])==x['object_sha256'], 'old source/object '+x['module'])
    replay=load(OLD/'replay-1oafv980/receipt.json')
    require(sha(r['replay_receipt'])==r['replay_sha256'], 'replay pin')
    for p,h in (replay['pins']|replay['artifacts']).items(): require(sha(p)==h,'replay artifact '+p)
    return {x['module']:x for x in r['correspondence']}, replay

def init():
    require(not STATE.exists(), 'workspace already exists')
    hist,r=history()
    out=Path(tempfile.mkdtemp(prefix='unforced-round5-',dir='/home/velvet/research-builds'))
    lib=out/'lib'; oldlib=Path(r['environment']['LEAN_PATH'].split(':')[0]);shutil.copytree(oldlib,lib)
    env=dict(r['environment']); env['LEAN_PATH']=':'.join([str(lib)]+env['LEAN_PATH'].split(':')[1:]);env['HOME']=str(out/'home');Path(env['HOME']).mkdir()
    cmd=r['runs'][0]['command'];lean=cmd[cmd.index('-j1')-1]
    index=git('rev-parse','--git-path','index').strip();index=str((ROOT/index).resolve())
    w={'out':str(out),'lib':str(lib),'environment':env,'lean':lean,'compiler_sha256':sha(lean),
       'baseline':files(),'head':git('rev-parse','HEAD'),'refs':git('show-ref'),'index':index,'index_sha256':sha(index),
       'diff':git('diff','--no-ext-diff'),'cached':git('diff','--cached','--no-ext-diff'),
       'snapshot_sha256':sha(SNAP),'history':hist,'accepted':{},'attempts':[]}
    save(STATE,w);preserved(w);print(out)
def compile(source):
    w=load(STATE);preserved(w);require(sha(w['lean'])==w['compiler_sha256'],'compiler')
    source=Path(source);require(source.parts[:3]==('Research','UnforcedRestart','Round5'),'source scope')
    text=(ROOT/source).read_text();stripped=re.sub(r'/\-.*?\-/|--[^\n]*','',text,flags=re.S)
    require(not re.search(r'\b(sorry|admit|axiom|unsafe)\b',stripped),'forbidden source token')
    run=Path(tempfile.mkdtemp(prefix='attempt-',dir=w['out']))
    deps=subprocess.run([w['lean'],'--deps',str(source)],cwd=ROOT,env=w['environment'],capture_output=True,text=True)
    save(run/'deps.json',{'exit':deps.returncode,'stdout':deps.stdout,'stderr':deps.stderr})
    require(deps.returncode==0,'deps failed')
    roots=[Path(p) for p in w['environment']['LEAN_PATH'].split(':')]+[Path(w['lean']).parent.parent/'lib/lean']
    correspondence=[]
    for p in deps.stdout.splitlines():
        obj=Path(p);root=next(x for x in roots if obj.is_relative_to(x));mod=str(obj.relative_to(root).with_suffix('')).replace('/','.')
        row=w['accepted'].get(mod,w['history'].get(mod));require(row is not None,'uncovered import '+mod)
        require(sha(obj)==row['object_sha256'] and sha(row['source'])==row['source_sha256'],'import provenance '+mod)
        correspondence.append({'module':mod,'resolved':p,**row})
    target=Path(w['lib'])/source.with_suffix('.olean');target.parent.mkdir(parents=True,exist_ok=True)
    cmd=['systemd-run','--user','--scope','--quiet','-p','CPUQuota=100%','-p','MemoryMax=6G','-p','MemorySwapMax=0','-p','TasksMax=32','timeout','600','env','-i',*[f'{k}={v}' for k,v in w['environment'].items()],w['lean'],'-j1','-DautoImplicit=false','-DwarningAsError=true','-o',str(run/'output.olean'),'-i',str(run/'output.ilean'),str(source)]
    row={'source':str(ROOT/source),'source_sha256':sha(ROOT/source),'command':cmd,'cwd':str(ROOT),'environment':w['environment'],'compiler_sha256':w['compiler_sha256'],'imports':correspondence}
    save(run/'command.json',row);(run/'source.lean').write_text(text)
    with (run/'compile.log').open('x') as log: result=subprocess.run(cmd,cwd=ROOT,stdout=log,stderr=subprocess.STDOUT)
    log=(run/'compile.log').read_text();row.update(exit=result.returncode,log_sha256=sha(run/'compile.log'))
    save(run/'receipt.json',row);w['attempts'].append(str(run/'receipt.json'));save(STATE,w)
    print(run,flush=True)
    if result.returncode: print(log);return result.returncode
    closures=established.exports(log)
    expected=re.findall(r'^#print axioms ([\w.]+)$',text,re.M)
    require(sorted(x['name'].rsplit('.',1)[-1] for x in closures)==sorted(x.rsplit('.',1)[-1] for x in expected),'export coverage')
    row.update(exports=closures,object=str(run/'output.olean'),object_sha256=sha(run/'output.olean'))
    shutil.copyfile(run/'output.olean',target);shutil.copyfile(run/'output.ilean',target.with_suffix('.ilean'))
    save(run/'receipt.json',row);w['accepted'][str(source.with_suffix('')).replace('/','.')]=row;save(STATE,w)
    preserved(w);print('PASS');return 0

def final_audit():
    w=load(STATE);preserved(w);history()
    auditrow=w['accepted']['Research.UnforcedRestart.Round5.Audit']
    run=Path(auditrow['object']).parent;mods,cov=aggregate.parsed((run/'compile.log').read_text())
    roots=[Path(p) for p in w['environment']['LEAN_PATH'].split(':')]+[Path(w['lean']).parent.parent/'lib/lean']
    corr=[]
    for mod in mods:
        rel=Path(mod.replace('.','/')+'.olean');prefix=rel.parts[0]
        root=next(p for p in roots if (p/prefix).exists() or (p/(prefix+'.olean')).exists())
        row=w['accepted'].get(mod,w['history'].get(mod));require(row is not None,'closure uncovered '+mod)
        require(sha(root/rel)==row['object_sha256'] and sha(row['source'])==row['source_sha256'],'closure provenance '+mod)
        corr.append({'module':mod,'source':row['source'],'source_sha256':row['source_sha256'],'object':str(root/rel),'object_sha256':row['object_sha256']})
    for row in w['accepted'].values():
        require(sha(row['source'])==row['source_sha256'] and sha(row['object'])==row['object_sha256'],'accepted bytes')
        require(sha(Path(row['object']).parent/'compile.log')==row['log_sha256'],'accepted log')
    result={'status':'PASS_PARTIAL_ONLY','modules':len(mods),'project_constants':len(cov),'correspondence':corr,'preservation':'baseline, HEAD, refs, index, diffs, supervisor manifest source hashes unchanged','accepted':w['accepted'],'attempts':w['attempts'],'tool_sha256':sha(__file__),'established_tools':{str(p):sha(p) for p in [OLD/'audit.py',OLD/'aggregate.py']},'scope':'Pinned source-built imported objects and compiler/core trust roots; no independent kernel checker. No N, W or Z acceptance.'}
    dest=Path(tempfile.mkdtemp(prefix='audit-',dir=w['out']))/'receipt.json';save(dest,result);print(dest)
if __name__=='__main__':
    if sys.argv[1]=='init':init()
    elif sys.argv[1]=='compile':sys.exit(compile(sys.argv[2]))
    elif sys.argv[1]=='audit':final_audit()
    else:raise RuntimeError('unknown command')
