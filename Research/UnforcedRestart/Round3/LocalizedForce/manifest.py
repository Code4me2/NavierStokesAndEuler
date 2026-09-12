#!/usr/bin/env python3
"""Owned, read-only input hashing and focused evidence inventory; no Lean build."""
import hashlib, json, re
from pathlib import Path
root = Path.cwd()
role = root / 'Research/UnforcedRestart/Round3/LocalizedForce'
def sha(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()
inputs = [
 'docs/unforced-restart/round3/PLAN.md',
 'docs/unforced-restart/round3/REPORT.md',
 'Research/UnforcedRestart/Round3/WitnessFeasibility/Main.lean',
 'Research/UnforcedRestart/Round3/Integration/focused.py',
 *['NavierStokes/' + n + '.lean' for n in [
 'ActualCandidateAssembly', 'ActualCandidateConstruction', 'AxisymmetricFields',
 'TailGaugePotential', 'MixedPeriodicAssembly', 'SpatialLocalization',
 'JointResidualLimits', 'TimeLocalization', 'ResidualRegularity']]]
src = role / 'Main.lean'
forbidden = r'\b(sorry|admit|axiom|unsafe|native_decide|set_option)\b'
assert not re.search(forbidden, src.read_text())
assert sha(root / inputs[2]) == '7d77092a3da73faedebac0a052c6fd2ce6fc46d340f48f796dd5e45f926be8da'
runs = []
for name in ['strict-jjgf8wtb', 'strict-tiajf2yo', 'strict-_w9_cwc3']:
    d = role / 'out' / name
    r = json.loads((d / 'result.json').read_text())
    runs.append({'directory': str(d.relative_to(root)), 'exit': r['exit'],
                 'evidence': {p.name: sha(p) for p in d.iterdir() if p.is_file()}})
assert [r['exit'] for r in runs] == [1, 1, 0]
assert json.loads((role / 'out/strict-_w9_cwc3/result.json').read_text())['source_sha256'] == sha(src)
record = {'scope': 'focused named exports, not aggregate acceptance',
          'command': 'python3 Research/UnforcedRestart/Round3/LocalizedForce/manifest.py',
          'source_sha256': sha(src), 'input_hashes': {p: sha(root / p) for p in inputs},
          'declarations': ['cutResidual_zero_outside', 'cutResidual_eventually_zero_outside',
                           'terminal_boundary_jets_zero_outside'],
          'namespace': 'UnforcedRestart.Round3.LocalizedForce',
          'axiom_whitelist': ['propext', 'Classical.choice', 'Quot.sound'],
          'source_triage': 'PASS', 'runs': runs}
(role / 'evidence.json').write_text(json.dumps(record, indent=2) + '\n')
print('PASS', record['source_sha256'])
