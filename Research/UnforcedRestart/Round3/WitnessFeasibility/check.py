#!/usr/bin/env python3
"""Unique, serial focused checks; no Lake or shared output writes."""
import hashlib, json, os, re, subprocess, tempfile
from pathlib import Path
ROOT = Path('/home/velvet/worktrees/unforced-restart-20260909T202951Z')
ROLE = Path('Research/UnforcedRestart/Round3/WitnessFeasibility')
assert Path.cwd() == ROOT

def sha(p):
    with Path(p).open('rb') as f:
        return hashlib.file_digest(f, 'sha256').hexdigest()

snapshot = ROOT / 'docs/unforced-restart/round3/snapshot/external-evidence.json'
resolver = json.loads(snapshot.read_text())['resolver']['explicit']
lean = Path('/home/velvet/.elan/toolchains/leanprover--lean4---v4.34.0-rc2/bin/lean')
assert sha(lean) == '79fb1d26fa5a39385d59fdc48a711a14b0710ca6480271acce99b4d177cea085'
assert sha(ROOT / ROLE / 'Main.lean') == '7d77092a3da73faedebac0a052c6fd2ce6fc46d340f48f796dd5e45f926be8da'
out = Path(tempfile.mkdtemp(prefix='certificates-', dir=ROOT / ROLE / 'out'))
lib = out / 'lib'
(lib / ROLE).mkdir(parents=True)
(out / 'home').mkdir()
env = {'PATH': str(lean.parent) + ':/usr/bin:/bin', 'HOME': str(out / 'home'),
       'LEAN_NUM_THREADS': '1', 'OMP_NUM_THREADS': '1', 'OPENBLAS_NUM_THREADS': '1',
       'LEAN_PATH': ':'.join([str(lib)] + resolver)}
manifest = {'scope': 'focused named exports only; not aggregate imported/helper audit',
            'tool_sha256': sha(__file__), 'resolver_sha256': sha(snapshot),
            'lean_sha256': sha(lean), 'checks': []}
for name in ['Main', 'Certificates']:
    src = ROOT / ROLE / (name + '.lean')
    text = src.read_text()
    # Lexical triage, in addition to strict compilation and printed axiom closures.
    assert not re.search(r'\b(sorry|admit|axiom|unsafe|native_decide|set_option)\b', text)
    assert not re.search(r'^import .*Challenge', text, re.M | re.I)
    stem = lib / ROLE / name
    cmd = ['systemd-run', '--user', '--scope', '--quiet', '-p', 'CPUQuota=100%',
           '-p', 'MemoryMax=6G', '-p', 'MemorySwapMax=0', '-p', 'TasksMax=32',
           'timeout', '600', 'env', '-i', *[f'{k}={v}' for k, v in env.items()],
           str(lean), '-j1', '-DautoImplicit=false', '-DwarningAsError=true',
           '-o', str(stem.with_suffix('.olean')), '-i', str(stem.with_suffix('.ilean')), str(src)]
    record = {'source': str(src.relative_to(ROOT)), 'source_sha256': sha(src),
              'command': cmd, 'cwd': str(ROOT), 'triage': 'PASS'}
    (out / (name + '-command.json')).write_text(json.dumps(record, indent=2) + '\n')
    log = out / (name + '.log')
    with log.open('w') as f:
        result = subprocess.run(cmd, cwd=ROOT, stdout=f, stderr=subprocess.STDOUT)
    assert sha(src) == record['source_sha256']
    record.update(exit=result.returncode, log_sha256=sha(log),
                  outputs={str(p.relative_to(out)): sha(p) for p in stem.parent.glob(name + '.*')})
    manifest['checks'].append(record)
    (out / 'result.json').write_text(json.dumps(manifest, indent=2) + '\n')
    print(out, name, result.returncode, flush=True)
    print(log.read_text(), flush=True)
    if result.returncode:
        raise SystemExit(result.returncode)
