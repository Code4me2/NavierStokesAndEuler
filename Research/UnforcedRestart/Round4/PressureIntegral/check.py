#!/usr/bin/env python3
"""Focused strict compile; dependencies and historical receipts are read-only."""
import hashlib, json, pathlib, subprocess, tempfile
root = pathlib.Path.cwd()
owner = root / 'Research/UnforcedRestart/Round4/PressureIntegral'
prior = root / 'Research/UnforcedRestart/Round4/Integration/strict-pu_v_ph4/receipt.json'
r = json.loads(prior.read_text())
def sha(p): return hashlib.sha256(pathlib.Path(p).read_bytes()).hexdigest()
for p, h in (r['inputs'] | r['outputs']).items():
    assert sha(p) == h, p
assert sha(root / r['source']) == r['source_sha256']
out = pathlib.Path(tempfile.mkdtemp(prefix='strict-', dir=owner))
(out / 'home').mkdir()
(out / 'lib/Research/UnforcedRestart/Round4/PressureIntegral').mkdir(parents=True)
source = 'Research/UnforcedRestart/Round4/PressureIntegral/Components.lean'
env = dict(r['environment'])
env['HOME'] = str(out / 'home')
# Lean resolves the Research package from its first search root; keep frozen imports first.
env['LEAN_PATH'] = env['LEAN_PATH'] + ':' + str(out / 'lib')
compiler = r['command'][r['command'].index('-j1')-1]
assert sha(compiler) == r['compiler_sha256']
obj = out / 'lib' / source.replace('.lean', '.olean')
idx = obj.with_suffix('.ilean')
cmd = ['systemd-run','--user','--scope','--quiet','-p','CPUQuota=100%', '-p','MemoryMax=6G','-p','MemorySwapMax=0','-p','TasksMax=32','timeout','600','env','-i']
cmd += [f'{k}={v}' for k,v in env.items()]
cmd += [compiler,'-j1','-DautoImplicit=false','-DwarningAsError=true','-o',str(obj),'-i',str(idx),source]
p = subprocess.run(cmd, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
(out / 'compile.log').write_bytes(p.stdout)
receipt = dict(source=source, source_sha256=sha(source), prior_receipt=str(prior), prior_receipt_sha256=sha(prior), compiler_sha256=sha(compiler), command=cmd, exit=p.returncode, log_sha256=sha(out/'compile.log'), outputs={str(x):sha(x) for x in (obj,idx) if x.exists()})
(out / 'receipt.json').write_text(json.dumps(receipt,indent=2)+'\n')
print(out)
print(p.stdout.decode())
raise SystemExit(p.returncode)
