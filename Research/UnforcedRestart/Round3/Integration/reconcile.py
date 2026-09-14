#!/usr/bin/env python3
"""Read-only evidence reconciliation, not Lean replay or aggregate proof auditing.
Writes only the new Round3 integration manifest and preservation log.
"""
import hashlib
import json
import re
import subprocess
from pathlib import Path

ROOT = Path('/home/velvet/worktrees/unforced-restart-20260909T202951Z')
assert Path.cwd() == ROOT
R = Path('Research/UnforcedRestart/Round3')
D = Path('docs/unforced-restart/round3')
ALLOWED = {'propext', 'Classical.choice', 'Quot.sound'}


def sha(path):
    with Path(path).open('rb') as f:
        return hashlib.file_digest(f, 'sha256').hexdigest()


def load(path):
    return json.loads(Path(path).read_text())


def git(*args):
    return subprocess.check_output(['git', *args], text=True).strip()


def git_state():
    index = Path(git('rev-parse', '--git-path', 'index'))
    return {'head': git('rev-parse', 'HEAD'), 'index_sha256': sha(index),
            'refs': git('for-each-ref', '--format=%(refname) %(objectname)')}


before = git_state()
# Sources, reports, evidence records and outputs are read, never rewritten.
checks = []
exports_by_source = {}
evidence_hashes = {}


def accept(record, record_path, log, output_root):
    src = Path(record['source'])
    if not src.is_absolute():
        src = ROOT / src
    relative = str(src.relative_to(ROOT))
    assert record['exit'] == 0, record_path
    assert sha(src) == record['source_sha256'], src
    assert sha(log) == record['log_sha256'], log
    text = src.read_text()
    assert not re.search(r'\b(sorry|admit|axiom|unsafe|native_decide|set_option)\b', text), src
    assert not re.search(r'^import .*Challenge', text, re.M | re.I), src
    namespace = re.search(r'^namespace (\S+)', text, re.M).group(1)
    printed = re.findall(r'^#print axioms (\S+)', text, re.M)
    declared = re.findall(r'^(?:noncomputable )?(?:def|theorem) (\w+)', text, re.M)
    assert set(printed) == set(declared), (src, printed, declared)
    logtext = Path(log).read_text()
    assert not re.search(r'\b(error|warning):|sorryAx', logtext), log
    pairs = re.findall(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]", logtext, re.S)
    pairs += [(name, '') for name in re.findall(r"'([^']+)' does not depend on any axioms", logtext)]
    assert len(pairs) == len(printed), (log, pairs)
    names = {name: sorted(filter(None, (x.strip() for x in axioms.split(','))))
             for name, axioms in pairs}
    assert set(names) == {namespace + '.' + p for p in printed}, log
    entries = []
    for name in printed:
        full = namespace + '.' + name
        assert set(names[full]) <= ALLOWED, (full, names[full])
        pattern = re.compile(r'^(?:noncomputable )?(def|theorem) ' + re.escape(name) + r'\b')
        line, kind = next((i, pattern.match(s).group(1)) for i, s in enumerate(text.splitlines(), 1)
                          if pattern.match(s))
        entries.append({'name': full, 'line': line, 'kind': kind, 'axioms': names[full]})
    previous = exports_by_source.setdefault(relative, entries)
    assert previous == entries
    outputs = {}
    for p, h in record['outputs'].items():
        path = Path(p)
        if not path.is_absolute():
            path = Path(output_root) / path
        assert sha(path) == h, path
        outputs[str(path.relative_to(ROOT) if path.is_absolute() else path)] = h
    cmd = record['command']
    for flag in ['-j1', '-DautoImplicit=false', '-DwarningAsError=true', 'env', '-i',
                 'LEAN_NUM_THREADS=1', 'CPUQuota=100%', 'MemoryMax=6G',
                 'MemorySwapMax=0', 'TasksMax=32', 'timeout', '600']:
        assert flag in cmd, (record_path, flag)
    assert not any(x.startswith('LEAN_SRC_PATH=') for x in cmd)
    lp = next(x.removeprefix('LEAN_PATH=') for x in cmd if x.startswith('LEAN_PATH='))
    resolver = load(D / 'snapshot/external-evidence.json')['resolver']['explicit']
    assert lp.split(':')[1:] == resolver
    assert lp.split(':')[0].startswith(str(ROOT / R))
    compiler = next(x for x in cmd if x.endswith('/bin/lean'))
    assert sha(compiler) == '79fb1d26fa5a39385d59fdc48a711a14b0710ca6480271acce99b4d177cea085'
    for p in [record_path, log]:
        evidence_hashes[str(p)] = sha(p)
    checks.append({'source': relative, 'source_sha256': sha(src), 'exports': entries,
                   'record': str(record_path), 'record_sha256': sha(record_path),
                   'accepted_exit': record['exit'], 'command': cmd, 'cwd': record['cwd'],
                   'log': str(log), 'log_sha256': sha(log), 'outputs': outputs,
                   'compiler_sha256': sha(compiler), 'reconciliation': 'PASS'})


w = R / 'WitnessFeasibility/out/certificates-v6ayi6z_'
for record in load(w / 'result.json')['checks']:
    name = Path(record['source']).stem
    accept(record, w / 'result.json', w / (name + '.log'), w)
c = R / 'CurlGeometry/out/strict-0m49nclb'
for record in load(c / 'manifest.json'):
    accept(record, c / 'manifest.json', Path(record['log']), c)
m = R / 'MeanTopology/out/strict-mb_z5gut'
for name in ['WitnessFeasibility', 'MeanTopology']:
    record = load(m / (name + '.result.json'))
    accept(record, m / (name + '.result.json'), m / (name + '.log'), m / 'lib')
l = R / 'LocalizedForce/out/strict-_w9_cwc3'
accept(load(l / 'result.json'), l / 'result.json', l / 'compile.log', l / 'lib')
assert len(exports_by_source) == 5
assert sum(map(len, exports_by_source.values())) == 36

# Recheck the specific baseline sources used in the integration against the
# already source-built external checkout, without compiling or changing it.
clean = Path('/home/velvet/research-builds/unforced-round2-clean-20260909T221339Z')
baseline = {}
for name in ['ProblemStatement', 'ActualCandidateAssembly', 'ActualCandidateConstruction',
             'ActualCarrierGeometry', 'MixedCandidateWitness', 'SolenoidalDiagonal',
             'JointResidualLimits', 'MixedPeriodicAssembly', 'SpatialLocalization',
             'TimeLocalization', 'TailGaugePotential', 'CandidateFromLimits',
             'PeriodicIntegration', 'SpatialCurl', 'R3/CompactTimeIntegral', 'SmoothParameterIntegral']:
    path = Path('NavierStokes') / (name + '.lean')
    assert sha(path) == sha(clean / path), path
    baseline[str(path)] = {'sha256': sha(path), 'clean_source_equal': True}

# This existing verifier is read-only. It is not a frozen historical validator,
# snapshot creator, dependency build, or Lean check.
command = ['python3', str(R / 'Integration/verify.py')]
preservation = subprocess.run(command, text=True, capture_output=True)
assert preservation.returncode == 0, preservation.stdout + preservation.stderr
preservation_result = json.loads(preservation.stdout)
for command_git in [['git', 'diff', '--exit-code', before['head'], '--'],
                    ['git', 'diff', '--cached', '--exit-code']]:
    result = subprocess.run(command_git, text=True, capture_output=True)
    assert result.returncode == 0 and not result.stdout and not result.stderr
assert git_state() == before

artifacts = {}
for path in [D / 'DECISION.md', D / 'ACCEPTED-SOURCE-MAP.md',
             *(D / (role + '.md') for role in
               ['WitnessFeasibility', 'CurlGeometry', 'MeanTopology', 'LocalizedForce']),
             R / 'WitnessFeasibility/check.py', R / 'CurlGeometry/check.py',
             R / 'MeanTopology/check.py', R / 'LocalizedForce/manifest.py',
             R / 'Integration/focused.py', R / 'Integration/verify.py', Path(__file__),
             R / 'Integration/reconcile-attempt1.txt',
             R / 'WitnessFeasibility/source-manifest.json',
             c / 'source-manifest.json', R / 'MeanTopology/MANIFEST.json',
             R / 'LocalizedForce/evidence.json', D / 'snapshot/external-evidence.json',
             Path('Research/UnforcedRestart/strong-norm-growth-transfer/Main.lean')]:
    artifacts[str(path.relative_to(ROOT) if path.is_absolute() else path)] = sha(path)
log = D / 'INTEGRATION-VALIDATION.log'
log.write_text('$ ' + ' '.join(command) + '\n' + preservation.stdout + preservation.stderr)
manifest = {
    'status': 'PASS',
    'scope': 'Existing focused Lean evidence reconciled against current sources, logs, outputs and printed exports; no fresh Lean compilation or aggregate helper/imported-closure audit.',
    'decision': '3: neither exact absorption nor obstruction decided; analytical certificates only',
    'integration_command': 'python3 Research/UnforcedRestart/Round3/Integration/reconcile.py',
    'integration_exit_on_success': 0,
    'permitted_axioms': sorted(ALLOWED),
    'unique_modules': 5, 'unique_printed_exports': 36,
    'completed_role_exports_excluding_frozen_wrapper': 28,
    'checks': checks, 'baseline_source_cross_checks': baseline,
    'artifact_sha256': artifacts, 'evidence_record_sha256': evidence_hashes,
    'preservation': {'command': command, 'exit': preservation.returncode,
                     'result': preservation_result, 'log': str(log), 'log_sha256': sha(log),
                     'git_before_and_after_equal': True, 'git_state': before,
                     'tracked_and_index_diffs': 'empty'},
    'rejected_attempts': 'All other role out/ attempts excluded from this acceptance set; retained without modification. Failed diagnostic sorryAx is not accepted.',
    'integration_attempt_history': ['Initial Python reconciliation exit 1: MeanTopology output root needed lib/; no Lean invocation or evidence writes. See hashed reconcile-attempt1.txt.', 'Corrected reconciliation passed; no acceptance criteria weakened.'],
    'not_accepted_as_mathematics': ['Python tools', 'analytical report formulas',
                                  'force-mean-zero composition', 'torus potential sufficiency',
                                  'nonzero annular curl', 'whole-terminal-slab identity',
                                  'projected-response existence or growth-relative estimates'],
    'trust_roots': ['installed pinned Lean/core/compiler/runtime', 'host OS/hardware',
                   'frozen external source-built dependency evidence (read-only)'],
    'operations_not_performed': ['Lean recompilation', 'dependency rebuild', 'Lake invocation',
                                 'numerical experiment', 'commit', 'push', 'ref/index write',
                                 'baseline or earlier research/docs edits']
}
(D / 'VALIDATION-MANIFEST.json').write_text(json.dumps(manifest, indent=2) + '\n')
print(json.dumps({'status': 'PASS', 'modules': 5, 'exports': 36,
                  'baseline_sources_equal': len(baseline),
                  'preservation': preservation_result,
                  'manifest': str(D / 'VALIDATION-MANIFEST.json')}, indent=2))
