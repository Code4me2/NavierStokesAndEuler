#!/usr/bin/env python3
"""Strict new-module check; frozen accepted role imports, read-only clean dependencies."""
import hashlib, json, re, shutil, subprocess, tempfile
from pathlib import Path
ROOT = Path('/home/velvet/worktrees/unforced-restart-20260909T202951Z')
ROLE = ROOT/'Research/UnforcedRestart/Round3/SelectedBridge'
def sha(p):
    with Path(p).open('rb') as f:
        return hashlib.file_digest(f, 'sha256').hexdigest()
assert Path.cwd() == ROOT
lean = Path('/home/velvet/.elan/toolchains/leanprover--lean4---v4.34.0-rc2/bin/lean')
assert sha(lean) == '79fb1d26fa5a39385d59fdc48a711a14b0710ca6480271acce99b4d177cea085'
manifest = ROOT/'docs/unforced-restart/round3/VALIDATION-MANIFEST.json'
accepted = json.loads(manifest.read_text())
resolver = ROOT/'docs/unforced-restart/round3/snapshot/external-evidence.json'
roots = json.loads(resolver.read_text())['resolver']['explicit']
(ROLE/'out').mkdir(exist_ok=True)
out = Path(tempfile.mkdtemp(prefix='strict-', dir=ROLE/'out'))
lib = out/'lib'; lib.mkdir()
frozen = lib  # Lean resolves a module's top-level prefix in the first matching root.
home = out/'home'; home.mkdir()
inputs = {}
for module in ['WitnessFeasibility', 'MeanTopology']:
    source = f'Research/UnforcedRestart/Round3/{module}/Main.lean'
    row = next(c for c in accepted['checks'] if c['source'] == source
               and 'MeanTopology/out/' in c['record'])
    assert sha(ROOT/source) == row['source_sha256']
    inputs[source] = sha(ROOT/source)
    for p, h in row['outputs'].items():
        assert sha(ROOT/p) == h
        suffix = Path(p).suffix
        dest = frozen/Path(source).with_suffix(suffix)
        dest.parent.mkdir(parents=True, exist_ok=True)
        shutil.copyfile(ROOT/p, dest)
        inputs[str(dest.relative_to(ROOT))] = sha(dest)
# Pin the actual directly used baseline source and output, in the existing clean build.
clean = Path('/home/velvet/research-builds/unforced-round2-clean-20260909T221339Z')
for source in ['NavierStokes/R3/CompactTimeIntegral.lean', 'NavierStokes/ProblemStatement.lean',
               'NavierStokes/SpatialLocalization.lean', 'NavierStokes/MixedPeriodicAssembly.lean',
               'NavierStokes/TimeLocalization.lean']:
    assert sha(ROOT/source) == sha(clean/source)
    inputs[source] = sha(ROOT/source)
    obj = clean/'.lake/build/lib/lean'/Path(source).with_suffix('.olean')
    inputs[str(obj)] = sha(obj)
src = ROLE/'Main.lean'
text = src.read_text()
code = re.sub(r'/\-.*?\-/', '', text, flags=re.S)
code = re.sub(r'--[^\n]*', '', code)
assert not re.search(r'\b(sorry|admit|axiom|unsafe|native_decide|implemented_by|set_option)\b', code)
names = re.findall(r'^theorem\s+(\w+)', code, re.M)
assert set(names) == set(re.findall(r'^#print axioms (\w+)', code, re.M))
snapshot = out/'SOURCE.md'
snapshot.write_text('# Source snapshot (acceptance requires result.json exit 0)\n\n```lean\n'+text+'```\n')
target = lib/src.relative_to(ROOT).with_suffix('.olean')
target.parent.mkdir(parents=True)
env = dict(PATH=str(lean.parent)+':/usr/bin:/bin', HOME=str(home), LEAN_NUM_THREADS='1',
           OMP_NUM_THREADS='1', OPENBLAS_NUM_THREADS='1',
           LEAN_PATH=':'.join([str(lib)]+roots))
cmd = ['systemd-run','--user','--scope','--quiet','-p','CPUQuota=100%',
       '-p','MemoryMax=6G','-p','MemorySwapMax=0','-p','TasksMax=32',
       'timeout','600','env','-i',*[f'{k}={v}' for k,v in env.items()],str(lean),
       '-j1','-DautoImplicit=false','-DwarningAsError=true',
       '-o',str(target),'-i',str(target.with_suffix('.ilean')),str(src)]
rec = dict(command=cmd, cwd=str(ROOT), source=str(src.relative_to(ROOT)), source_sha256=sha(src),
           compiler_sha256=sha(lean), inputs=inputs, manifest_sha256=sha(manifest),
           resolver_sha256=sha(resolver), source_snapshot_sha256=sha(snapshot), checker_sha256=sha(ROLE/'check.py'), scope='All new named theorems: transitive axiom closures; not an aggregate imported helper audit')
(out/'command.json').write_text(json.dumps(rec,indent=2)+'\n')
print(out, flush=True)
log = out/'compile.log'
with log.open('w') as f:
    result = subprocess.run(cmd,cwd=ROOT,stdout=f,stderr=subprocess.STDOUT)
rec.update(exit=result.returncode, log=str(log.relative_to(ROOT)), log_sha256=sha(log),
           outputs={str(p.relative_to(ROOT)):sha(p) for p in target.parent.glob('Main.*')})
printed = re.findall(r"'([^']+)' depends on axioms:\s*\[([^]]*)\]",log.read_text())
rec['exports'] = [{'name':n, 'axioms':sorted(a.strip() for a in ax.split(',') if a.strip())} for n,ax in printed]
assert sha(src) == rec['source_sha256']
for p,h in inputs.items(): assert sha(ROOT/p) == h, p
(out/'result.json').write_text(json.dumps(rec,indent=2)+'\n')
print(log.read_text(),flush=True)
if result.returncode: raise SystemExit(result.returncode)
assert {n for n,_ in printed} == {'UnforcedRestart.Round3.SelectedBridge.'+n for n in names}
assert all(set(e['axioms']) <= {'propext','Classical.choice','Quot.sound'} for e in rec['exports'])
print('STRICT_PASS',flush=True)
