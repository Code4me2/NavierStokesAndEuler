#!/usr/bin/env python3
"""Additive audit. Default is read-only; --replay creates a unique receipt directory.
Never execute historical receipt writers. No Lake/cache/dependency build invocation.
"""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parents[4]
ROLE = Path(__file__).resolve().parent
PRIOR = ROOT / 'docs/unforced-restart/round3/VALIDATION-MANIFEST.json'
RESOLVER = ROOT / 'docs/unforced-restart/round3/snapshot/external-evidence.json'
BRIDGE = ROOT / 'Research/UnforcedRestart/Round3/SelectedBridge'
ALLOWED = {'propext', 'Classical.choice', 'Quot.sound'}


def sha(path):
    with Path(path).open('rb') as f:
        return hashlib.file_digest(f, 'sha256').hexdigest()


def load(path):
    return json.loads(Path(path).read_text())


def git(*args):
    return subprocess.check_output(['git', *args], cwd=ROOT, text=True)


def require(ok, message):
    if not ok:
        raise RuntimeError(message)


def exports(text):
    pairs = re.findall(r"'([^']+)' depends on axioms:\s*\[([^]]*)\]", text)
    pairs += [(n, '') for n in re.findall(r"'([^']+)' does not depend on any axioms", text)]
    result = []
    for name, axioms in pairs:
        ax = sorted(a.strip() for a in axioms.split(',') if a.strip())
        require(set(ax) <= ALLOWED, f'Forbidden axioms: {name}: {ax}')
        result.append({'name': name, 'axioms': ax})
    require(len({r['name'] for r in result}) == len(result), 'Duplicate printed export')
    require(not re.search(r'sorryAx|error:|warning:', text), 'Diagnostic in accepted log')
    return sorted(result, key=lambda r: r['name'])


def normalized(rows):
    return sorted([{'name': r['name'], 'axioms': sorted(r['axioms'])} for r in rows],
                  key=lambda r: r['name'])


def preservation():
    b = load(ROLE / 'baseline.json')
    for p, h in b['files'].items():
        p = ROOT / p
        actual = 'symlink:' + os.readlink(p) if p.is_symlink() else sha(p)
        require(actual == h, f'Preservation: {p}')
    require(git('rev-parse', 'HEAD') == b['head'], 'HEAD changed')
    require(git('show-ref') == b['refs'], 'Refs changed')
    require(sha(b['index']) == b['index_sha256'], 'Index changed')
    require(not git('diff', '--no-ext-diff') and not git('diff', '--cached', '--no-ext-diff'),
            'Tracked/index diff')
    return {'files': len(b['files']), 'head': b['head'].strip(), 'refs_index_diffs': 'unchanged/empty'}


def accepted():
    rows = load(PRIOR)['checks']
    bridge = load(BRIDGE / 'out/strict-bx6aiy6v/result.json')
    require(sha(PRIOR) == bridge['manifest_sha256'], 'Prior manifest hash')
    require(sha(RESOLVER) == bridge['resolver_sha256'], 'Resolver hash')
    require(sha(BRIDGE / 'check.py') == bridge['checker_sha256'], 'Frozen checker hash')
    require(sha(BRIDGE / 'out/strict-bx6aiy6v/SOURCE.md') == bridge['source_snapshot_sha256'],
            'Bridge source snapshot')
    for p, h in bridge['inputs'].items():
        require(sha(ROOT / p) == h, f'Bridge input: {p}')
    # Some historical logs contain several modules; equate the union for each log.
    by_log = {}
    unique = {}
    for row in rows + [bridge]:
        require(sha(ROOT / row['source']) == row['source_sha256'], row['source'])
        require(sha(ROOT / row['log']) == row['log_sha256'], row['log'])
        for p, h in row['outputs'].items():
            require(sha(ROOT / p) == h, p)
        by_log.setdefault(row['log'], []).extend(row['exports'])
        unique[row['source']] = row
    for log, recorded in by_log.items():
        require(exports((ROOT / log).read_text()) == normalized(recorded), f'Log exports: {log}')
    require(len(unique) == 6, 'Accepted source coverage')
    return unique, bridge


def preflight():
    preserved = preservation()
    modules, bridge = accepted()
    resolver = load(RESOLVER)
    evidence = Path(resolver['root'])
    manifest = evidence / 'research-evidence-sha256.json'
    require(sha(manifest) == resolver['evidence_manifest_sha256'], 'Historical evidence manifest')
    for p, h in load(manifest).items():
        require(sha(evidence / p) == h, f'Historical evidence: {p}')
    historical = load(evidence / 'research-replay/compiler-inputs-before.json')
    objects = {p: r['sha256'] for p, r in historical.items() if p.endswith('.olean')}
    for r in load(evidence / 'research-replay/results.json'):
        require(r['exit'] == 0, 'Historical build failed')
        for a in r['artifacts']:
            objects[a['path']] = a['sha256']
    for p, h in objects.items():
        require(sha(p) == h, f'Historical object mismatch: {p}')
    clean = Path(resolver['resolver']['cwd'])
    initial = {r['path']: r['sha256'] for r in load(evidence / 'initial-inventory.json')['sources']}
    incremental = []
    buildlog = (evidence / 'build.log').read_text().splitlines()
    for name in ['CompactEnergy', 'CompactTimeIntegral']:
        source = f'NavierStokes/R3/{name}.lean'
        require(sha(ROOT / source) == sha(clean / source) == initial[source], source)
        obj = clean / '.lake/build/lib/lean' / Path(source).with_suffix('.olean')
        require(str(obj) in objects, f'Missing historical object: {obj}')
        lines = [{'line': i + 1, 'text': line} for i, line in enumerate(buildlog)
                 if f'NavierStokes.R3.{name}' in line or source in line]
        require(bool(lines), f'Missing build command evidence: {name}')
        incremental.append({'source': source, 'source_sha256': initial[source],
                            'object': str(obj), 'historical_sha256': objects[str(obj)],
                            'build_log': str(evidence / 'build.log'), 'build_lines': lines})
    lean = Path(bridge['command'][bridge['command'].index('-j1') - 1])
    require(sha(lean) == bridge['compiler_sha256'], 'Compiler hash')
    return modules, resolver, objects, lean, {
        'preservation': preserved, 'historical_objects_checked': len(objects),
        'incremental_source_build_correspondence': incremental,
        'pins': {str(p): sha(p) for p in [PRIOR, RESOLVER, manifest, lean, Path(__file__), ROLE / 'baseline.json']},
        'scope': 'Historical source-built dependencies reused and hash compared; no fresh dependency rebuild; named export axiom closures, not aggregate semantic helper audit; Comparator/Nanoda not run'}


def replay():
    modules, resolver, objects, lean, receipt = preflight()
    out = Path(tempfile.mkdtemp(prefix='replay-', dir=ROLE))
    print(out, flush=True)
    lib = out / 'lib'
    lib.mkdir()
    roots = [Path(p) for p in resolver['resolver']['explicit']]
    # First-root prefix resolution requires all inherited Research objects in this root.
    for p in roots[0].rglob('*'):
        if p.is_file():
            require(str(p) in objects and sha(p) == objects[str(p)], f'Uncovered copied input: {p}')
            dest = lib / p.relative_to(roots[0])
            dest.parent.mkdir(parents=True, exist_ok=True)
            shutil.copyfile(p, dest)
            objects[str(dest)] = sha(dest)
    home = out / 'home'
    home.mkdir()
    env = {'PATH': str(lean.parent) + ':/usr/bin:/bin', 'HOME': str(home),
           'LEAN_PATH': ':'.join(map(str, [lib] + roots[1:])), 'LEAN_NUM_THREADS': '1',
           'OMP_NUM_THREADS': '1', 'OPENBLAS_NUM_THREADS': '1'}
    receipt.update(environment=env, cwd=str(ROOT), runs=[], resolved_imports=[])
    # Compiler-resolved direct imports, not a regex approximation of Lean's header.
    def dependencies(source):
        cmd = [str(lean), '--deps', str(source)]
        result = subprocess.run(cmd, cwd=ROOT, env=env, text=True, capture_output=True, check=True)
        paths = result.stdout.splitlines()
        require(bool(paths), f'Empty resolution: {source}')
        for p in paths:
            require(p in objects and sha(p) == objects[p], f'Uncovered resolved import: {p}')
        receipt['resolved_imports'].append({'source': str(source), 'command': cmd,
            'exit': result.returncode, 'stderr': result.stderr,
            'objects': {p: objects[p] for p in paths}})
    for extra in receipt['incremental_source_build_correspondence']:
        dependencies(ROOT / extra['source'])
    pending = dict(modules)
    while pending:
        progress = False
        for source, old in list(pending.items()):
            text = (ROOT / source).read_text()
            imports = re.findall(r'^import\s+(\S+)', text, re.M)
            if any(i.replace('.', '/') + '.lean' in pending for i in imports):
                continue
            dependencies(ROOT / source)
            target = lib / Path(source).with_suffix('.olean')
            target.parent.mkdir(parents=True, exist_ok=True)
            cmd = ['systemd-run', '--user', '--scope', '--quiet', '-p', 'CPUQuota=100%',
                   '-p', 'MemoryMax=6G', '-p', 'MemorySwapMax=0', '-p', 'TasksMax=32',
                   'timeout', '600', 'env', '-i', *[f'{k}={v}' for k, v in env.items()],
                   str(lean), '-j1', '-DautoImplicit=false', '-DwarningAsError=true',
                   '-o', str(target), '-i', str(target.with_suffix('.ilean')), source]
            log = out / (str(len(receipt['runs'])) + '.log')
            row = {'source': source, 'source_sha256': sha(ROOT / source), 'command': cmd,
                   'log': str(log), 'expected_exports': normalized(old['exports'])}
            (out / (str(len(receipt['runs'])) + '.command.json')).write_text(json.dumps(row, indent=2) + '\n')
            with log.open('x') as f:
                result = subprocess.run(cmd, cwd=ROOT, stdout=f, stderr=subprocess.STDOUT)
            row.update(exit=result.returncode, log_sha256=sha(log))
            require(result.returncode == 0, f'Compile failed: {log}')
            row['exports'] = exports(log.read_text())
            require(row['exports'] == row['expected_exports'], f'Replay exports: {source}')
            row['outputs'] = {str(p): sha(p) for p in target.parent.glob(target.stem + '.*')}
            objects.update(row['outputs'])
            receipt['runs'].append(row)
            del pending[source]
            progress = True
            print('PASS ' + source, flush=True)
        require(progress, 'Import cycle/unresolved accepted module')
    receipt['preservation_after'] = preservation()
    receipt['status'] = 'PASS_BOUNDED_REPLAY'
    receipt['artifacts'] = {str(p): sha(p) for p in out.rglob('*') if p.is_file()}
    (out / 'receipt.json').write_text(json.dumps(receipt, indent=2) + '\n')
    print('Receipt: ' + str(out / 'receipt.json'), flush=True)


def verify(path):
    _, _, _, _, summary = preflight()
    if path:
        r = load(path)
        require(r['status'] == 'PASS_BOUNDED_REPLAY' and len(r['runs']) == 6, 'Replay receipt status')
        for p, h in (r['pins'] | r['artifacts']).items():
            require(sha(p) == h, f'Receipt hash: {p}')
        for run in r['runs']:
            require(run['exit'] == 0 and sha(ROOT / run['source']) == run['source_sha256'], 'Replay source/exit')
            require(exports(Path(run['log']).read_text()) == run['exports'] == run['expected_exports'], 'Replay axiom lists')
        for resolution in r['resolved_imports']:
            for p, h in resolution['objects'].items():
                require(sha(p) == h, f'Resolved import changed: {p}')
        summary['replay_modules'] = len(r['runs'])
        summary['replay_exports'] = sum(len(x['exports']) for x in r['runs'])
    print(json.dumps(summary, indent=2))


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--replay', action='store_true')
    parser.add_argument('--receipt', type=Path)
    args = parser.parse_args()
    require(not (args.replay and args.receipt), 'Choose replay or read-only receipt verification')
    replay() if args.replay else verify(args.receipt)
