#!/usr/bin/env python3
"""Focused MeanTopology check; immutable cross-role source freeze, unique outputs."""
import hashlib, json, os, re, subprocess, tempfile
from pathlib import Path
ROOT = Path('/home/velvet/worktrees/unforced-restart-20260909T202951Z')
ROLE = ROOT/'Research/UnforcedRestart/Round3/MeanTopology'
def sha(p):
    return hashlib.sha256(Path(p).read_bytes()).hexdigest()
assert Path.cwd() == ROOT
freeze = ROOT/'Research/UnforcedRestart/Round3/WitnessFeasibility/Main.lean'
assert sha(freeze) == '7d77092a3da73faedebac0a052c6fd2ce6fc46d340f48f796dd5e45f926be8da'
lean = Path('/home/velvet/.elan/toolchains/leanprover--lean4---v4.34.0-rc2/bin/lean')
assert sha(lean) == '79fb1d26fa5a39385d59fdc48a711a14b0710ca6480271acce99b4d177cea085'
resolver = ROOT/'docs/unforced-restart/round3/snapshot/external-evidence.json'
roots = json.loads(resolver.read_text())['resolver']['explicit']
(ROLE/'out').mkdir(exist_ok=True)
out = Path(tempfile.mkdtemp(prefix='strict-', dir=ROLE/'out'))
lib = out/'lib'; lib.mkdir()
home = out/'home'; home.mkdir()
env = dict(PATH=str(lean.parent)+':/usr/bin:/bin', HOME=str(home),
           LEAN_NUM_THREADS='1', OMP_NUM_THREADS='1', OPENBLAS_NUM_THREADS='1',
           LEAN_PATH=':'.join([str(lib)]+roots))
print(out, flush=True)
for src in [freeze, ROLE/'Main.lean']:
    text = src.read_text()
    clean = re.sub(r'/\-.*?\-/', '', text, flags=re.S)
    clean = re.sub(r'--[^\n]*', '', clean)
    assert not re.search(r'\b(sorry|admit|axiom|unsafe|native_decide|implemented_by|set_option)\b', clean)
    assert 'Challenge' not in clean
    target = lib/src.relative_to(ROOT).with_suffix('.olean')
    target.parent.mkdir(parents=True, exist_ok=True)
    tag = src.parent.name
    (out/(tag+'.source.lean')).write_bytes(src.read_bytes())
    cmd = ['systemd-run','--user','--scope','--quiet','-p','CPUQuota=100%',
           '-p','MemoryMax=6G','-p','MemorySwapMax=0','-p','TasksMax=32',
           'timeout','600','env','-i',*[f'{k}={v}' for k,v in env.items()], str(lean),
           '-j1','-DautoImplicit=false','-DwarningAsError=true',
           '-o',str(target),'-i',str(target.with_suffix('.ilean')),str(src)]
    rec = dict(command=cmd, cwd=str(ROOT), source=str(src), source_sha256=sha(src),
               lean_sha256=sha(lean), resolver_sha256=sha(resolver),
               scope='focused named exports, not aggregate generated/helper/import audit')
    (out/(tag+'.command.json')).write_text(json.dumps(rec,indent=2)+'\n')
    log = out/(tag+'.log')
    with log.open('w') as stream:
        result = subprocess.run(cmd,cwd=ROOT,stdout=stream,stderr=subprocess.STDOUT)
    assert sha(src) == rec['source_sha256']
    rec.update(exit=result.returncode, log_sha256=sha(log),
               outputs={str(p.relative_to(lib)):sha(p) for p in target.parent.glob('Main.*')})
    (out/(tag+'.result.json')).write_text(json.dumps(rec,indent=2)+'\n')
    print(log.read_text(), flush=True)
    if result.returncode:
        raise SystemExit(result.returncode)
    for axioms in re.findall(r'depends on axioms:\s*\[([^]]*)\]', log.read_text()):
        assert {a.strip() for a in axioms.split(',') if a.strip()} <= {'propext','Classical.choice','Quot.sound'}
print('FOCUSED_PASS')
