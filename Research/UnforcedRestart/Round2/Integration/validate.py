#!/usr/bin/env python3
"""Independent Round2 validator, not a rerun/patch of the frozen validator.
Cached acceptance only. --clean fails closed until a complete source-build
provenance verifier is supplied; source acquisition is never clean acceptance.
All output is unique and new. No Lake build/config elaboration or cache fetch.
"""
import argparse
import fcntl
import hashlib
import io
import json
import os
from pathlib import Path
import re
import subprocess
import sys
import tarfile
import time

ROOT = Path('/home/velvet/worktrees/unforced-restart-20260909T202951Z')
BASE = ROOT/'Research/UnforcedRestart'
R2 = BASE/'Round2'
SNAP = Path('/home/velvet/research-snapshots/unforced-round1-20260909T221339Z')
ALLOWED = {'propext','Classical.choice','Quot.sound'}
SEAL = '192e15dc0ff1cb79cae02a19941e0f816dc194e91123c205153ccf808322a488'

def require(ok, msg):
    if not ok: raise RuntimeError(msg)

def digest(p):
    with p.open('rb') as stream:
        return hashlib.file_digest(stream, 'sha256').hexdigest()

# Lean Environment imports may consume split objects and IR beside the base
# object. Inventory a conservative superset, not just the named .olean.
MODULE_SUFFIXES = ('.olean', '.olean.server', '.olean.private', '.ir', '.ir.sig')

def compiler_artifact(p):
    return any(p.name.endswith(s) for s in MODULE_SUFFIXES) or p.suffix in {
        '.ilean', '.so', '.a', '.o', '.bc', '.dll', '.dylib'}

def artifact_inventory(roots):
    return {str(p): {'realpath': str(p.resolve()), 'sha256': digest(p)}
            for root in roots for p in sorted(root.rglob('*'))
            if p.is_file() and compiler_artifact(p)}

def require_stable(before, after):
    require(before == after, 'Compiler input inventory changed (content, path, addition or deletion)')

def module_artifacts(obj):
    stem = str(obj).removesuffix('.olean')
    return [{'path': str(p), 'realpath': str(p.resolve()), 'sha256': digest(p)}
            for ext in MODULE_SUFFIXES if (p := Path(stem + ext)).is_file()]

def command(args, cwd=ROOT):
    return subprocess.check_output(args,cwd=cwd,text=True,stderr=subprocess.STDOUT).strip()

def code_only(s):
    out=[]; i=0; depth=0
    while i<len(s):
        if depth:
            if s.startswith('/-',i): depth+=1; i+=2
            elif s.startswith('-/',i): depth-=1; i+=2
            else: out.append('\n' if s[i]=='\n' else ' '); i+=1
        elif s.startswith('/-',i): depth=1; i+=2
        elif s.startswith('--',i):
            j=s.find('\n',i); i=len(s) if j<0 else j
        elif s[i]=='"':
            i+=1
            while i<len(s) and s[i]!='"': i+=2 if s[i]=='\\' else 1
            i+=1; out.append(' ')
        else: out.append(s[i]); i+=1
    require(depth==0,'Unclosed comment')
    return ''.join(out)

def imports(s):
    return re.findall(r'^\s*(?:public |meta )?import\s+([^\n]+)',code_only(s),re.M)

def module(path): return path.removesuffix('.lean').replace('/','.')

def forbidden(s, options=False):
    c=code_only(s)
    require(not re.search(r'\b(sorry|admit|axiom|unsafe|native_decide|implemented_by)\b',c),'Forbidden source construct')
    if options: require(not re.search(r'\bset_option\b',c),'Research option override')
    return c

def preservation(m):
    require(command(['git','rev-parse','HEAD'])==m['baseline'],'HEAD mismatch')
    require(not command(['git','diff',m['baseline'],'--']),'Tracked diff')
    require(not command(['git','diff','--cached','--']),'Index diff')
    # Byte-check every tracked baseline file, not just a clean git status.
    data=subprocess.check_output(['git','archive',m['baseline']],cwd=ROOT)
    n=0
    with tarfile.open(fileobj=io.BytesIO(data)) as archive:
        for member in archive:
            if member.isfile():
                require((ROOT/member.name).read_bytes()==archive.extractfile(member).read(),'Baseline bytes: '+member.name)
                n+=1
    require(digest(SNAP/'SHA256SUMS')==SEAL,'External snapshot digest')
    command(['sha256sum','-c','SHA256SUMS'],SNAP)
    frozen=[]
    with tarfile.open(SNAP/'source-docs.tar.gz') as archive:
        for member in archive:
            if member.isfile():
                p=ROOT/member.name
                require(p.resolve().is_relative_to(ROOT),'Archive escaping path')
                expected=hashlib.sha256(archive.extractfile(member).read()).hexdigest()
                require(digest(p)==expected,'Frozen archive mismatch: '+member.name)
                frozen.append({'path':member.name,'sha256':expected})
    require(len(frozen)==114,'Incomplete frozen archive coverage')
    sealed_inventory={e['path']:e for e in json.loads((SNAP/'inventory.json').read_text())}
    for p in command(['git','ls-files','--others','--exclude-standard']).splitlines():
        require(p.startswith(('Research/UnforcedRestart/','docs/unforced-restart/')),'Unauthorized untracked file '+p)
        if not p.startswith(('Research/UnforcedRestart/Round2/','docs/unforced-restart/round2/')):
            require(p in sealed_inventory,'New file outside Round2 '+p)
            require(digest(ROOT/p)==sealed_inventory[p]['sha256'],'Changed pre-Round2 artifact '+p)
    pins=json.loads((ROOT/'lake-manifest.json').read_text())['packages']
    for pin in pins:
        p=ROOT/'.lake/packages'/pin['name']
        require(p.resolve().is_relative_to(ROOT),'Escaping package')
        require(command(['git','rev-parse','HEAD'],p)==pin['rev'],'Package pin '+pin['name'])
        require(not command(['git','diff','HEAD','--'],p),'Package tracked diff')
        require(not command(['git','diff','--cached','--'],p),'Package staged diff')
    for top in [ROOT/'.lake/build',ROOT/'.lake/packages',BASE]:
        for p in top.rglob('*'):
            if p.is_symlink(): require(p.resolve().is_relative_to(ROOT),'Escaping symlink '+str(p))
    return {'baseline_files':n,'snapshot_files':frozen,'pins':pins}

def trust_root(out):
    prefix=Path(command(['lean','--print-prefix'])).resolve()
    version=command([str(prefix/'bin/lean'),'--version'])
    require('4.34.0-rc2' in version and '6a10ac8c22beadecabdbb0919c2b50214762f91d' in version,'Wrong toolchain')
    info={'version':version,'prefix':str(prefix),'shim':command(['which','lean']),
          'host':command(['uname','-a']),'executables':[],
          'trust':'Installed release Lean/core/Lake/compiler/runtime and host OS/hardware trusted, not bootstrapped; hashes are not an independent release-signature verification.'}
    for name in ['lean','lake','leanc','clang','ld.lld','llvm-ar']:
        p=prefix/'bin'/name
        if p.exists(): info['executables'].append({'name':name,'realpath':str(p.resolve()),'sha256':digest(p)})
    for tool in ['cc','ld','git','python3']:
        p=Path(command(['which',tool])).resolve()
        info['executables'].append({'name':tool,'realpath':str(p),'sha256':digest(p)})
    info['core_artifacts']=[{'path':str(p),'sha256':digest(p)} for p in sorted((prefix/'lib/lean').rglob('*')) if p.is_file() and compiler_artifact(p)]
    (out/'toolchain.json').write_text(json.dumps(info,indent=2)+'\n')
    return prefix

def compile_entry(e,out,prefix,paths):
    src=ROOT/e['path']; forbidden(src.read_text(),True)
    require(digest(src)==e['sha256'],'Accepted source changed')
    require(imports(src.read_text())==e['imports'],'Exact imports mismatch: '+e['path'])
    target=out/'lib'/Path(e['path']).with_suffix(''); target.parent.mkdir(parents=True,exist_ok=True)
    log=out/(e['path'].replace('/','_')+'.log')
    lp=':'.join(map(str,paths))
    lean=[str(prefix/'bin/lean'),'-j1','-DautoImplicit=false','-DwarningAsError=true',
          '-o',str(target)+'.olean','-i',str(target)+'.ilean',e['path']]
    # A fresh scope verifies the enforced values before executing Lean.
    gate='''set -eu
cg=$(awk -F: '$1==0 {print $3}' /proc/self/cgroup)
d=/sys/fs/cgroup$cg
for f in cpu.max memory.max memory.swap.max pids.max; do printf '%s=' "$f"; head -c 100 "$d/$f"; done
test "$(<"$d/cpu.max")" = '100000 100000'
test "$(<"$d/memory.max")" = 6442450944
test "$(<"$d/memory.swap.max")" = 0
test "$(<"$d/pids.max")" = 32
exec timeout 600 env -u LEAN_SRC_PATH LEAN_NUM_THREADS=1 LEAN_PATH="$1" "${@:2}"
'''
    cmd=['systemd-run','--user','--wait','--pipe','-p','WorkingDirectory='+str(ROOT),
         '-p','CPUQuota=100%','-p','MemoryMax=6G','-p','MemorySwapMax=0','-p','TasksMax=32',
         '/bin/bash','-c',gate,'--',lp]+lean
    start=time.time()
    with log.open('w') as stream:
        proc=subprocess.run(cmd,cwd=ROOT,stdout=stream,stderr=subprocess.STDOUT)
    record={'path':e['path'],'module':module(e['path']),'source_sha256':digest(src),'command':cmd,
            'start':start,'finish':time.time(),'exit':proc.returncode,'log':str(log),'log_sha256':digest(log)}
    (log.with_suffix('.json')).write_text(json.dumps(record,indent=2)+'\n')
    require(proc.returncode==0,'Strict compile failed: '+str(log))
    text=log.read_text()
    closures=dict(re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]",text))
    closures.update({n:'' for n in re.findall(r"'([^']+)' does not depend on any axioms",text)})
    for name in e.get('declarations',[]):
        require(name in closures,'Missing inline audit '+name)
        require(set(filter(None,map(str.strip,closures[name].split(','))))<=ALLOWED,'Forbidden closure '+name)
    record['artifacts']=module_artifacts(Path(str(target)+'.olean')) + [
        {'path':str(target)+'.ilean','sha256':digest(Path(str(target)+'.ilean'))}]
    print('PASS',e['path'],flush=True)
    return record,text

def main():
    parser=argparse.ArgumentParser(); parser.add_argument('--clean',action='store_true'); args=parser.parse_args()
    require(Path(__file__).resolve()==R2/'Integration/validate.py','Unauthorized runner root')
    out=R2/'Integration/runs'/time.strftime('%Y%m%dT%H%M%SZ',time.gmtime())
    out.mkdir(parents=True,exist_ok=False)
    try:
        m=json.loads((R2/'MANIFEST.json').read_text()); old=json.loads((BASE/'MANIFEST.json').read_text())
        require(m['inherited_accepted']==old['accepted'],'Frozen accepted set changed')
        require(m['allowed_axioms']==sorted(ALLOWED),'Axiom whitelist changed')
        require(m['accepted_round2'],'Empty new acceptance cannot pass')
        for e in m['frozen_tools']+[old['validation_script'],old['audit']]:
            require(digest(ROOT/e['path'])==e['sha256'],'Frozen source/tool mismatch '+e['path'])
        (out/'preservation-before.json').write_text(json.dumps(preservation(m),indent=2)+'\n')
        prefix=trust_root(out)
        if args.clean:
            raise RuntimeError('CLEAN BLOCKER: zero-artifact preflight failed; no complete source-built closure. This runner cannot upgrade cached evidence to clean acceptance.')
        accepted=m['inherited_accepted']+m['accepted_round2']
        audit=m['audit']; oldaudit=dict(old['audit'],imports=imports((ROOT/old['audit']['path']).read_text()))
        expected={e['path'] for e in accepted+[audit,oldaudit]}|set(m['excluded_lean'])
        present={str(p.relative_to(ROOT)) for p in BASE.rglob('*.lean')}
        require(present==expected,'Unclassified Lean sources: '+str(present^expected))
        # Topological check; all research imports must be in the preceding closure.
        seen=set()
        for e in accepted+[oldaudit,audit]:
            for imp in e['imports']:
                imp=imp.replace('«','').replace('»','')
                if imp.startswith('Research.'):
                    require(imp in seen,'Research dependency out of order: '+imp)
                require(not imp.startswith('ComparatorChallenges'),'Challenge import')
            seen.add(module(e['path']))
        paths=[out/'lib',ROOT/'.lake/build/lib/lean']+sorted((ROOT/'.lake/packages').glob('*/.lake/build/lib/lean'))
        # Do not allow historical research objects in the resolver.
        (out/'resolver.json').write_text(json.dumps({'LEAN_PATH':list(map(str,paths)),'LEAN_SRC_PATH':None,'LEAN_NUM_THREADS':1},indent=2))
        input_roots=paths[1:]+[prefix/'lib/lean']
        inputs_before=artifact_inventory(input_roots)
        (out/'compiler-inputs-before.json').write_text(json.dumps(inputs_before,indent=2)+'\n')
        results=[]
        with (R2/'Integration/focused.lock').open('w') as lock:
            fcntl.flock(lock,fcntl.LOCK_EX)
            for e in accepted+[oldaudit,audit]:
                result,text=compile_entry(e,out,prefix,paths); results.append(result)
        rows=[line.split('\t')[1:] for line in text.splitlines() if line.startswith('COVERAGE\t')]
        mods=[line.split('\t')[1] for line in text.splitlines() if line.startswith('MODULE\t')]
        counts=re.findall(r'^COVERAGE_COUNT\t(\d+)$',text,re.M)
        require(len(counts)==1 and int(counts[0])==len(rows) and rows,'Incomplete semantic enumeration')
        require(len({r[1] for r in rows})==len(rows),'Duplicate constant coverage')
        for row in rows:
            require(len(row)==3,'Malformed semantic row')
            require(row[2].startswith('[') and row[2].endswith(']'),'Truncated closure')
            require(set(filter(None,map(str.strip,row[2][1:-1].split(','))))<=ALLOWED,'Forbidden semantic closure')
        names={r[1] for r in rows}
        require(all(n in names for e in accepted for n in e['declarations']),'Missing named export')
        require(mods and len(set(mods))==len(mods),'Missing/duplicate module inventory')
        for e in accepted:
            require(module(e['path']) in {mod.replace('«','').replace('»','') for mod in mods},'Accepted module not audited')
        (out/'declarations.tsv').write_text('module\tdeclaration\taxioms\n'+'\n'.join('\t'.join(r) for r in rows)+'\n')
        roots=[ROOT]+sorted((ROOT/'.lake/packages').iterdir())+[prefix/'src/lean',prefix/'src/lean/lake']
        inventory=[]
        for mod in mods:
            require(not mod.startswith('ComparatorChallenges'),'Challenge closure')
            rel=Path(mod.replace('«','').replace('»','').replace('.','/'))
            src=next((r/rel.with_suffix('.lean') for r in roots if (r/rel.with_suffix('.lean')).is_file()),None)
            obj=next((r/rel.with_suffix('.olean') for r in paths+[prefix/'lib/lean'] if (r/rel.with_suffix('.olean')).is_file()),None)
            require(src is not None and obj is not None,'Unresolved module '+mod)
            project=src.is_relative_to(ROOT) and not src.is_relative_to(ROOT/'.lake')
            c=forbidden(src.read_text()) if project else code_only(src.read_text())
            inventory.append({'module':mod,'source':str(src),'source_sha256':digest(src),'olean':str(obj),
                'olean_sha256':digest(obj),'compiler_artifacts':module_artifacts(obj),
                'imports':imports(src.read_text()),
                'inherited_options':re.findall(r'\bset_option\s+[^\n]+',c) if project else [],
                'coverage':'all constants, unsafe checks, transitive standard axioms' if project else 'cached external/core; used axioms checked transitively'})
        (out/'dependencies.json').write_text(json.dumps(inventory,indent=2)+'\n')
        inputs_after=artifact_inventory(input_roots)
        (out/'compiler-inputs-after.json').write_text(json.dumps(inputs_after,indent=2)+'\n')
        require_stable(inputs_before, inputs_after)
        for result in results:
            for artifact in result['artifacts']:
                require(digest(Path(artifact['path']))==artifact['sha256'],
                        'Fresh research artifact changed: '+artifact['path'])
        trust=json.loads((out/'toolchain.json').read_text())
        for executable in trust['executables']:
            require(digest(Path(executable['realpath']))==executable['sha256'], 'Executable changed')
        (out/'preservation-after.json').write_text(json.dumps(preservation(m),indent=2)+'\n')
        # Recheck frozen additions/tools against changes during the run.
        for e in accepted+[audit]+m['frozen_tools']:
            require(digest(ROOT/e['path'])==e['sha256'],'Source changed during validation')
        evidence={'status':'CACHED_CHECKS_PASS_CLEAN_BLOCKED','results':results,'exports':sum(len(e['declarations']) for e in accepted),
            'constants':len(rows),'modules':len(mods),'manifest_sha256':digest(R2/'MANIFEST.json'),
            'clean':'NOT ACCEPTED; source-built dependency closure unavailable',
            'scope':'Fresh strict research elaboration including frozen audit; new aggregate audit. Not a literal frozen-validator rerun, independent kernel/Comparator certification, or A/B claim.'}
        (out/'CACHED_SUCCESS.json').write_text(json.dumps(evidence,indent=2)+'\n')
        print(str(out),flush=True)
    except Exception as exc:
        (out/'FAILURE.json').write_text(json.dumps({'error':repr(exc),'time':time.time()},indent=2)+'\n')
        raise

if __name__=='__main__':
    try: main()
    except Exception as exc:
        print('FAIL:',exc,file=sys.stderr); sys.exit(1)
