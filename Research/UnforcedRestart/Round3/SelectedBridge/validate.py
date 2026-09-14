#!/usr/bin/env python3
"""Reconcile the single accepted new run and check preservation, without rebuilding."""
import hashlib, json, re, subprocess
from pathlib import Path
ROOT = Path('/home/velvet/worktrees/unforced-restart-20260909T202951Z')
ROLE = ROOT/'Research/UnforcedRestart/Round3/SelectedBridge'
assert Path.cwd() == ROOT

def sha(p):
    with Path(p).open('rb') as f:
        return hashlib.file_digest(f, 'sha256').hexdigest()

def git(*args):
    return subprocess.check_output(['git', *args], cwd=ROOT, text=True)

before = json.loads((ROLE/'preserved-before.json').read_text())
for p,h in before['files'].items():
    assert sha(ROOT/p) == h, p
assert git('rev-parse','HEAD') == before['head']
assert git('show-ref') == before['refs']
assert sha(ROOT/before['index']) == before['index_sha256']
assert not git('diff','--no-ext-diff')
assert not git('diff','--cached','--no-ext-diff')
command = ['python3','Research/UnforcedRestart/Round3/Integration/verify.py']
old = subprocess.run(command,cwd=ROOT,text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
(ROLE/'PRESERVATION.log').write_text(old.stdout)
assert old.returncode == 0, old.stdout
out = ROLE/'out/strict-bx6aiy6v'
rec = json.loads((out/'result.json').read_text())
assert rec['exit'] == 0
assert sha(ROOT/rec['source']) == rec['source_sha256']
assert sha(ROOT/rec['log']) == rec['log_sha256']
assert sha(out/'SOURCE.md') == rec['source_snapshot_sha256']
assert sha(ROLE/'check.py') == rec['checker_sha256']
assert sha(rec['command'][rec['command'].index('-j1')-1]) == rec['compiler_sha256']
for p,h in (rec['inputs'] | rec['outputs']).items():
    assert sha(ROOT/p) == h, p
log = (ROOT/rec['log']).read_text()
assert 'sorryAx' not in log and 'error:' not in log and 'warning:' not in log
exports = re.findall(r'^theorem\s+(\w+)', (ROOT/rec['source']).read_text(),re.M)
assert {e['name'] for e in rec['exports']} == {
    'UnforcedRestart.Round3.SelectedBridge.'+n for n in exports}
assert len(rec['exports']) == len(exports) == 5
for e in rec['exports']:
    assert set(e['axioms']) <= {'Classical.choice','Quot.sound','propext'}
# Reconcile all frozen earlier accepted exports as evidence, without executing
# their integration writer or recompiling any earlier module.
prior = ROOT/'docs/unforced-restart/round3/VALIDATION-MANIFEST.json'
prior_rec = json.loads(prior.read_text())
prior_exports = set()
for c in prior_rec['checks']:
    assert sha(ROOT/c['source']) == c['source_sha256']
    assert sha(ROOT/c['log']) == c['log_sha256']
    for p,h in c['outputs'].items(): assert sha(ROOT/p) == h
    prior_exports.update(e['name'] for e in c['exports'])
assert len(prior_exports) == 36
files = {}
for p in ROLE.rglob('*'):
    if p.is_file() and p.name != 'VALIDATION-MANIFEST.json':
        files[str(p.relative_to(ROOT))] = sha(p)
receipt = {
    'status':'PASS', 'decision':'3: neither absorption nor obstruction decided',
    'substantive_result':'For every 0<t<1 and i:Fin 3, integral over R3 of (temporalDerivative MeanTopology.compactVelocity t x) i equals zero.',
    'accepted_run': str(out.relative_to(ROOT)), 'accepted_check':rec,
    'validation_command':['python3','Research/UnforcedRestart/Round3/SelectedBridge/validate.py'],
    'prior_manifest':str(prior.relative_to(ROOT)), 'prior_manifest_sha256':sha(prior),
    'prior_printed_exports_reconciled':36, 'new_printed_exports':5,
    'axiom_audit_scope':'Transitive closure of every new named theorem; not aggregate imported/helper re-audit',
    'preservation':{'preexisting_files':len(before['files']), 'all_hashes_equal':True,
        'head_refs_index':'unchanged', 'tracked_index_diffs':'empty',
        'prior_verifier_command':command, 'prior_verifier_exit':old.returncode,
        'prior_verifier_result':json.loads(old.stdout)},
    'attempt_history':[
        {'run':'strict-2giy3tju','status':'REJECTED: first-root module resolution; source in QUARANTINED.md'},
        {'run':'strict-rmmpxk96','status':'REJECTED: elaboration; diagnostic sorryAx not accepted; source in QUARANTINED.md; failed target objects removed'},
        {'run':'strict-gohyv7l2','status':'PASS: superseded by final provenance-recording replay'},
        {'run':'strict-bx6aiy6v','status':'ACCEPTED: strict exit 0, five allowed axiom closures'}],
    'trust_roots':['pinned installed Lean/core/compiler/runtime', 'host OS/hardware',
        'frozen existing external clean source-built dependencies and their earlier evidence',
        'hash-checked earlier Round3 accepted objects copied to phase-owned resolver'],
    'operations_not_performed':['dependency rebuild','earlier-module compilation','Lake invocation',
        'numerical experiment','baseline/earlier research/docs/config edit','commit','push','ref/index write'],
    'open':['pressure and Laplacian integral adapters','cell/whole-space measure and periodization transport',
        'force mean zero and endpoint composition','slab curl producer or actual nonzero jet',
        'periodic potential sufficiency','absorption/obstruction','comparator lifespan and growth transfer'],
    'artifact_sha256':files}
(ROLE/'VALIDATION-MANIFEST.json').write_text(json.dumps(receipt,indent=2)+'\n')
print(json.dumps({'status':'PASS','accepted_run':receipt['accepted_run'],
    'new_printed_exports':5,'prior_exports_preserved':36,
    'preexisting_files_unchanged':len(before['files']), 'head_refs_index':'unchanged'},indent=2))
