#!/usr/bin/env python3
"""Aggregate project/helper axiom audit and resolved transitive module provenance.
--run REPLAY_RECEIPT creates unique outputs; --verify RECEIPT is read-only.
"""
import sys
sys.dont_write_bytecode = True
import argparse
import json
from pathlib import Path
import re
import subprocess
import tempfile
import audit as a


def parsed(text):
    a.require(not re.search(r'error:|warning:|sorryAx', text), 'Aggregate diagnostic')
    modules = re.findall(r'^MODULE\t(.+)$', text, re.M)
    coverage = re.findall(r'^COVERAGE\t([^\t]+)\t([^\t]+)\t\[([^]]*)\]$', text, re.M)
    counts = re.findall(r'^COVERAGE_COUNT\t(\d+)$', text, re.M)
    a.require(len(counts) == 1 and int(counts[0]) == len(coverage) > 0, 'Coverage count')
    a.require(len(modules) == len(set(modules)) > 0, 'Module coverage')
    a.require(len({n for _, n, _ in coverage}) == len(coverage), 'Duplicate constant')
    for mod, name, ax in coverage:
        a.require(mod in modules and set(filter(None, ax.split(','))) <= a.ALLOWED, name)
    return modules, coverage


def run(replay_path):
    a.verify(replay_path)
    _, resolver, objects, lean, preflight = a.preflight()
    replay = a.load(replay_path)
    out = Path(tempfile.mkdtemp(prefix='aggregate-', dir=a.ROLE))
    env = replay['environment']
    src = a.ROLE / 'Audit.lean'
    cmd = ['systemd-run', '--user', '--scope', '--quiet', '-p', 'CPUQuota=100%',
           '-p', 'MemoryMax=6G', '-p', 'MemorySwapMax=0', '-p', 'TasksMax=32',
           'timeout', '1200', 'env', '-i', *[f'{k}={v}' for k, v in env.items()], str(lean),
           '-j1', '-DautoImplicit=false', '-DwarningAsError=true',
           '-o', str(out / 'Audit.olean'), '-i', str(out / 'Audit.ilean'), str(src)]
    receipt = {'command': cmd, 'cwd': str(a.ROOT), 'environment': env,
               'replay_receipt': str(replay_path.resolve()), 'replay_sha256': a.sha(replay_path),
               'source': str(src), 'source_sha256': a.sha(src), 'preflight': preflight,
               'checker_sha256': a.sha(__file__)}
    (out / 'command.json').write_text(json.dumps(receipt, indent=2) + '\n')
    print(out, flush=True)
    log = out / 'audit.log'
    with log.open('x') as f:
        result = subprocess.run(cmd, cwd=a.ROOT, stdout=f, stderr=subprocess.STDOUT)
    a.require(result.returncode == 0, f'Aggregate failed: {log}')
    modules, coverage = parsed(log.read_text())
    evidence = Path(resolver['root'])
    old = {r['module']: r for r in a.load(evidence / 'research-replay/dependencies.json')}
    clean = Path(resolver['resolver']['cwd'])
    initial = {r['path']: r['sha256'] for r in a.load(evidence / 'initial-inventory.json')['sources']}
    roots = [Path(p) for p in env['LEAN_PATH'].split(':')] + [Path(resolver['resolver']['implicit_core'])]
    new = {}
    for row in replay['runs']:
        module = row['source'][:-5].replace('/', '.')
        new[module] = row
        objects.update(row['outputs'])
    # Include inherited Research copies, whose hashes were checked before replay.
    for p, h in replay['artifacts'].items():
        if p.endswith('.olean'):
            objects[p] = h
    loglines = (evidence / 'build.log').read_text().splitlines()
    correspondence = []
    for module in modules:
        rel = Path(module.replace('.', '/') + '.olean')
        prefix = module.split('.')[0]
        root = next((r for r in roots if (r / prefix).is_dir() or (r / (prefix + '.olean')).exists()), None)
        a.require(root is not None, f'Unresolved prefix: {module}')
        obj = root / rel
        a.require(str(obj) in objects and a.sha(obj) == objects[str(obj)], f'Uncovered object: {obj}')
        row = {'module': module, 'object': str(obj), 'object_sha256': objects[str(obj)]}
        if module in new:
            source = a.ROOT / new[module]['source']
            row.update(source=str(source), source_sha256=new[module]['source_sha256'], provenance='fresh strict Round3 replay')
        elif module in old:
            inherited = old[module]
            row.update(source=inherited['source'], source_sha256=inherited['source_sha256'],
                       provenance=inherited['provenance'], historical_dependency_record=inherited)
        else:
            source = clean / rel.with_suffix('.lean')
            key = str(source.relative_to(clean))
            a.require(key in initial, f'No historical source inventory: {module}')
            lines = [{'line': i + 1, 'text': line} for i, line in enumerate(loglines)
                     if module in line or key in line]
            a.require(bool(lines), f'No source build command: {module}')
            row.update(source=str(source), source_sha256=initial[key],
                       provenance='incremental addition to prior dependency union; initial source inventory + historical object + source build log',
                       build_log=str(evidence / 'build.log'), build_lines=lines)
        a.require(a.sha(row['source']) == row['source_sha256'], f'Source mismatch: {module}')
        correspondence.append(row)
    receipt.update(exit=0, log=str(log), log_sha256=a.sha(log), modules=len(modules),
                   project_constants=len(coverage), correspondence=correspondence,
                   incremental_modules=[r['module'] for r in correspondence if r['module'] not in old and r['module'] not in new],
                   coverage_sha256=a.sha(log), preservation_after=a.preservation(),
                   scope='All imported project constants and generated helpers checked for unsafe/forbidden transitive axioms; all imported modules resolved and source/object provenance checked. Libraries/core are pinned trust roots, not independently kernel-checked. No fresh dependency rebuild or Comparator/Nanoda check.',
                   status='PASS_AGGREGATE_PROJECT_AUDIT')
    receipt['artifacts'] = {str(p): a.sha(p) for p in out.rglob('*') if p.is_file()}
    (out / 'receipt.json').write_text(json.dumps(receipt, indent=2) + '\n')
    print(json.dumps({'receipt': str(out / 'receipt.json'), 'modules': len(modules),
                      'project_constants': len(coverage), 'incremental_modules': receipt['incremental_modules']}), flush=True)


def verify(path):
    r = a.load(path)
    a.verify(Path(r['replay_receipt']))
    a.require(a.sha(r['replay_receipt']) == r['replay_sha256'], 'Replay receipt changed')
    a.require(a.sha(__file__) == r['checker_sha256'], 'Aggregate checker changed')
    a.require(a.sha(r['source']) == r['source_sha256'], 'Aggregate source changed')
    a.require(r['exit'] == 0 and r['status'] == 'PASS_AGGREGATE_PROJECT_AUDIT', 'Aggregate exit/status')
    for p, h in r['artifacts'].items():
        a.require(a.sha(p) == h, f'Aggregate artifact: {p}')
    modules, coverage = parsed(Path(r['log']).read_text())
    a.require(modules == [x['module'] for x in r['correspondence']], 'Module correspondence')
    a.require(len(modules) == r['modules'] and len(coverage) == r['project_constants'], 'Recorded counts')
    for row in r['correspondence']:
        a.require(a.sha(row['object']) == row['object_sha256'], row['object'])
        a.require(a.sha(row['source']) == row['source_sha256'], row['source'])
    print(json.dumps({'status': r['status'], 'modules': len(modules), 'project_constants': len(coverage),
                      'preservation': a.preservation()}, indent=2))


if __name__ == '__main__':
    p = argparse.ArgumentParser(description=__doc__)
    g = p.add_mutually_exclusive_group(required=True)
    g.add_argument('--run', type=Path)
    g.add_argument('--verify', type=Path)
    args = p.parse_args()
    run(args.run) if args.run else verify(args.verify)
