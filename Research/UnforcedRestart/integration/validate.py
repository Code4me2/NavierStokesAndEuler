#!/usr/bin/env python3
"""Serial, fail-closed validation. No builds, installs, or original-checkout writes."""
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[3]
BASE = ROOT / 'Research/UnforcedRestart'
MANIFEST = BASE / 'MANIFEST.json'
OUT = BASE / 'integration/validation'
ALLOWED = {'propext', 'Classical.choice', 'Quot.sound'}


def run(args, **kw):
    return subprocess.run(args, cwd=ROOT, check=True, text=True, **kw)


def capture(args):
    return run(args, stdout=subprocess.PIPE).stdout.strip()


def digest(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()


def require(ok, message):
    if not ok:
        raise RuntimeError(message)


def code_only(s):
    # Nested Lean comments and strings removed; this is triage, not the semantic audit.
    out, i, depth = [], 0, 0
    while i < len(s):
        if depth:
            if s.startswith('/-', i): depth += 1; i += 2
            elif s.startswith('-/', i): depth -= 1; i += 2
            else: out.append('\n' if s[i] == '\n' else ' '); i += 1
        elif s.startswith('/-', i): depth = 1; i += 2
        elif s.startswith('--', i):
            j = s.find('\n', i); i = len(s) if j < 0 else j
        elif s[i] == '"':
            i += 1
            while i < len(s) and s[i] != '"':
                i += 2 if s[i] == '\\' else 1
            i += 1
            out.append(' ')
        else: out.append(s[i]); i += 1
    require(depth == 0, 'Unclosed comment')
    return ''.join(out)


def baseline(m):
    require(ROOT == Path('/home/velvet/worktrees/unforced-restart-20260909T202951Z'),
            'Not the authorized worktree')
    require(capture(['git', 'rev-parse', 'HEAD']) == m['baseline'], 'Baseline HEAD mismatch')
    run(['git', 'diff', '--exit-code', m['baseline'], '--'])
    run(['git', 'diff', '--cached', '--exit-code'])
    for p in capture(['git', 'ls-files', '--others', '--exclude-standard']).splitlines():
        require(p.startswith(('Research/UnforcedRestart/', 'docs/unforced-restart/')),
                'Unauthorized new file: ' + p)
    pins = json.loads((ROOT / 'lake-manifest.json').read_text())['packages']
    for pin in pins:
        p = ROOT / '.lake/packages' / pin['name']
        require(p.resolve().is_relative_to(ROOT), 'Escaping package')
        require(capture(['git', '-C', str(p), 'rev-parse', 'HEAD']) == pin['rev'],
                'Package revision mismatch: ' + pin['name'])
        run(['git', '-C', str(p), 'diff', '--exit-code', 'HEAD', '--'])
    for top in [ROOT / '.lake/build', ROOT / '.lake/packages', BASE]:
        for p in top.rglob('*'):
            if p.is_symlink():
                require(p.resolve().is_relative_to(ROOT), 'Escaping symlink: ' + str(p))


def compile_file(entry, env):
    src = ROOT / entry['path']
    require(digest(src) == entry['sha256'], 'Frozen source mismatch: ' + entry['path'])
    code = code_only(src.read_text())
    require(not re.search(r'\b(sorry|admit|axiom|unsafe|native_decide|implemented_by)\b', code),
            'Forbidden source construct: ' + entry['path'])
    require(not re.search(r'\bset_option\b', code), 'Research option override')
    target = OUT / 'lib' / Path(entry['path']).with_suffix('')
    target.parent.mkdir(parents=True, exist_ok=True)
    log = OUT / (src.parent.name + '-' + src.stem + '.log')
    cmd = ['lake', 'env', 'lean', '-j1', '-DautoImplicit=false', '-DwarningAsError=true',
           '-o', str(target) + '.olean', '-i', str(target) + '.ilean', entry['path']]
    with log.open('w') as stream:
        result = subprocess.run(cmd, cwd=ROOT, env=env, text=True, stdout=stream,
                                stderr=subprocess.STDOUT)
    log.with_suffix('.exit').write_text(str(result.returncode) + '\n')
    require(result.returncode == 0, f'Compiler failure ({result.returncode}): {log}')
    text = log.read_text()
    closures = dict(re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]", text))
    closures.update({n: '' for n in re.findall(r"'([^']+)' does not depend on any axioms", text)})
    for name in entry.get('declarations', []):
        require(name in closures, 'Missing inline axiom print: ' + name)
        require(set(filter(None, map(str.strip, closures[name].split(',')))) <= ALLOWED,
                'Forbidden axiom closure: ' + name)
    print('PASS', entry['path'], flush=True)
    return {'path': entry['path'], 'command': cmd, 'exit': result.returncode,
            'log': str(log.relative_to(ROOT)), 'axioms': closures}


def main():
    os.chdir(ROOT)
    require(ROOT == Path('/home/velvet/worktrees/unforced-restart-20260909T202951Z'),
            'Not the authorized worktree; refusing output writes')
    OUT.mkdir(parents=True, exist_ok=True)
    # Never leave a stale success marker following a failed rerun.
    (OUT / 'SUCCESS.json').unlink(missing_ok=True)
    m = json.loads(MANIFEST.read_text())
    require(digest(Path(__file__).resolve()) == m['validation_script']['sha256'],
            'Frozen validator mismatch')
    baseline(m)
    expected = {e['path'] for e in m['accepted']} | {m['audit']['path'],
                'Research/UnforcedRestart/setup/ImportProbe.lean'}
    present = {str(p.relative_to(ROOT)) for p in BASE.rglob('*.lean')}
    require(present == expected, 'Unclassified Lean files: ' + str(present ^ expected))
    env = dict(os.environ, LEAN_NUM_THREADS='1')
    # lake env prepends baseline paths, but research modules exist ONLY under this root.
    env['LEAN_PATH'] = str(OUT / 'lib')
    results = [compile_file(e, env) for e in m['accepted']]
    results.append(compile_file(m['audit'], env))
    text = (OUT / 'integration-Audit.log').read_text()
    coverage = [line.split('\t')[1:] for line in text.splitlines() if line.startswith('COVERAGE\t')]
    modules = [line.split('\t')[1] for line in text.splitlines() if line.startswith('MODULE\t')]
    counts = re.findall(r'^COVERAGE_COUNT\t(\d+)$', text, re.M)
    require(len(counts) == 1 and int(counts[0]) == len(coverage) and coverage,
            'Incomplete semantic coverage output')
    names = {row[1] for row in coverage}
    require(all(n in names for e in m['accepted'] for n in e['declarations']),
            'Missing research declaration in aggregate environment')
    require(all(len(row) == 3 for row in coverage), 'Malformed coverage row')
    for _, name, axs in coverage:
        require(axs.startswith('[') and axs.endswith(']'), 'Truncated axiom row: ' + name)
        require(set(filter(None, map(str.strip, axs.strip('[]').split(',')))) <= ALLOWED,
                'Forbidden dependency axiom: ' + name)
    (OUT / 'declarations.tsv').write_text('module\tdeclaration\taxioms\n' +
        '\n'.join('\t'.join(row) for row in coverage) + '\n')
    # Record EVERY actual imported module, not only the direct imports or chosen probes.
    roots = [ROOT] + sorted((ROOT / '.lake/packages').iterdir())
    prefix = Path(capture(['lean', '--print-prefix']))
    roots += [prefix / 'src/lean', prefix / 'src/lean/lake']
    paths = capture(['lake', 'env', 'printenv', 'LEAN_PATH']).split(':')
    paths.insert(0, str(OUT / 'lib'))
    inventory = []
    for mod in modules:
        rel = Path(mod.replace('«', '').replace('»', '').replace('.', '/'))
        src = next((r / rel.with_suffix('.lean') for r in roots if (r / rel.with_suffix('.lean')).is_file()), None)
        obj = next((Path(r) / rel.with_suffix('.olean') for r in paths if (Path(r) / rel.with_suffix('.olean')).is_file()), None)
        require(src is not None and obj is not None, 'Unresolved dependency: ' + mod)
        code = code_only(src.read_text())
        project = src.is_relative_to(ROOT) and not src.is_relative_to(ROOT / '.lake')
        if project:
            require(not re.search(r'\b(sorry|admit|axiom|unsafe|native_decide|implemented_by)\b', code),
                    'Forbidden construct in dependency: ' + str(src))
        inventory.append({'module': mod, 'source': str(src), 'source_sha256': digest(src),
                          'olean': str(obj), 'olean_sha256': digest(obj),
                          'imports': re.findall(r'^\s*(?:public |meta )?import\s+([^\n]+)', code, re.M),
                          'inherited_options': re.findall(r'\bset_option\s+[^\n]+', code) if project else [],
                          'coverage': 'all constants and axiom closures' if mod.startswith(('NavierStokes.', 'Euler.', 'Common.', 'Research.')) else 'cached external library; used axioms covered transitively'})
    (OUT / 'dependencies.json').write_text(json.dumps(inventory, indent=2) + '\n')
    baseline(m)
    evidence = {'baseline': m['baseline'], 'toolchain': capture(['lean', '--version']),
                'research_declarations': sum(len(e['declarations']) for e in m['accepted']),
                'dependency_and_research_constants': len(coverage), 'imported_modules': len(modules),
                'results': results, 'baseline_checks': 'PASS',
                'provenance': 'Fresh research and aggregate elaboration; cached dependency artifacts, not a clean dependency rebuild.'}
    (OUT / 'SUCCESS.json').write_text(json.dumps(evidence, indent=2) + '\n')
    print(json.dumps({k: v for k, v in evidence.items() if k != 'results'}, indent=2))


if __name__ == '__main__':
    try:
        main()
    except Exception as exc:
        print('FAIL:', exc, file=sys.stderr)
        sys.exit(1)
