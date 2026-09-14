#!/usr/bin/env python3
"""Versioned repair verification; retain the original strict-ref result.

Reuses every original verification check, selecting a separately pinned v2
manifest rather than editing the historical freeze. The concurrent-ref policy
is an additional result, never a rewrite of strict equality.
"""
import json
import re
import subprocess
import sys
sys.dont_write_bytecode = True
import verify_final as original

HERE = original.HERE
ROOT = original.ROOT
OLD_PIN = '51970afbbfd4a1f67c068305a05b219dff4f084cd5cb634a325020c7878cc190'
AUTHORIZED = {'refs/heads/docs/native-weighted-control-20260912T185404Z':
              '26e896edbdbe1215c0d50ddba24b2b6453646f5f'}
DOC_CHANGES = {'docs/unforced-restart/round4/PLAN.md',
               'docs/unforced-restart/round4/FINAL-REPORT.md'}

def refs(text):
    rows = [line.split() for line in text.splitlines()]
    result = {name: value for value, name in rows}
    original.require(len(result) == len(rows), 'duplicate ref')
    return result

def verify():
    old_path = HERE / 'FINAL-MANIFEST.json'
    new_path = HERE / 'REPAIR-MANIFEST.json'
    original.require(original.sha(old_path) == OLD_PIN, 'historical freeze changed')
    old = original.load(old_path)
    new = original.load(new_path)
    original.require(new['previous_manifest_sha256'] == OLD_PIN, 'freeze lineage')
    original.require(set(old['files']) <= set(new['files']), 'removed frozen entry')
    changed = {p for p, h in old['files'].items() if new['files'][p] != h}
    original.require(changed == DOC_CHANGES, 'unapproved freeze change')
    original.require(new['documentation_changes'] == {
        p: {'before': old['files'][p], 'after': new['files'][p]} for p in changed},
        'documentation change accounting')
    # Only manifest selection changes; all source/axiom/import/provenance,
    # snapshot, HEAD, index, tracked-diff and addition checks remain original.
    load = original.load
    def selected_load(path):
        return load(new_path if original.Path(path) == old_path else path)
    original.load = selected_load
    try:
        result = original.verify()
    finally:
        original.load = load
    chain = original.load(ROOT / new['chain'])
    fresh = [original.load(p) for p in chain['receipts']]
    supplemental = original.load(ROOT / new['endpoint_receipt'])
    for r, frozen in zip(fresh, old['rows'], strict=True):
        original.require(r['source'] == frozen['source'] and
                         r['source_sha256'] == frozen['source_sha256'] and
                         set(r['outputs'].values()) == set(frozen['outputs'].values()),
                         'fresh source/object differs from accepted freeze')
    # Audit direct imports of every compilation, not just the final environment.
    objects = {row['module']: row['object_sha256'] for row in result['correspondence']}
    for r in fresh + [supplemental]:
        for p, h in r['outputs'].items():
            if p.endswith('.olean'):
                objects[r['source'][:-5].replace('/', '.')] = h
    for r in fresh + [supplemental]:
        original.require(r['exit'] == 0 and original.sha(ROOT / r['source']) ==
                         r['source_sha256'], 'replay source')
        text = (ROOT / r['source']).read_text()
        stripped = re.sub(r'/\-.*?\-/|--[^\n]*', '', text, flags=re.S)
        original.require(not re.search(r'\b(sorry|admit|axiom|unsafe)\b', stripped),
                         'forbidden source token')
        for p, h in (r['inputs'] | r['outputs']).items():
            original.require(original.sha(p) == h, 'replay input/output ' + p)
        cmd = r['command']
        original.require(all(f in cmd for f in
                         ['-j1', '-DautoImplicit=false', '-DwarningAsError=true']), 'flags')
        lean = original.Path(cmd[cmd.index('-j1') - 1])
        original.require(original.sha(lean) == r['compiler_sha256'], 'compiler')
        log = original.Path(r['lib']).parent / 'compile.log'
        original.require(original.sha(log) == r['log_sha256'] and
                         not re.search(r'error:|warning:|sorryAx', log.read_text()), 'log')
        closures = re.findall(r"'([^']+)' depends on axioms:\s*\[([^]]*)\]", log.read_text())
        expected = re.findall(r'^#print axioms ([\w.]+)$', text, re.M)
        original.require([n.rsplit('.', 1)[-1] for n, _ in closures] ==
                         [n.rsplit('.', 1)[-1] for n in expected], 'export coverage')
        for n, ax in closures:
            original.require(set(filter(None, map(str.strip, ax.split(',')))) <=
                             original.ALLOWED, n)
        roots = [original.Path(p) for p in r['environment']['LEAN_PATH'].split(':')]
        roots.append(lean.parent.parent / 'lib/lean')
        deps = subprocess.check_output([str(lean), '--deps', r['source']],
                                       cwd=ROOT, env=r['environment'], text=True)
        for p in deps.splitlines():
            obj = original.Path(p)
            prefix = next(root for root in roots if obj.is_relative_to(root))
            mod = str(obj.relative_to(prefix).with_suffix('')).replace('/', '.')
            original.require(not mod.startswith('ComparatorChallenges') and
                             mod in objects and original.sha(obj) == objects[mod],
                             'direct import provenance ' + mod)
    result.update(fresh_objects_byte_identical=True, strict_compilations=len(fresh) + 1,
                  endpoint_exports=[n for n, _ in supplemental['closures']],
                  direct_import_provenance='PASS', source_scan='PASS')
    before, after = refs(result['refs_before']), refs(result['refs_after'])
    added = {n: h for n, h in after.items() if n not in before}
    removed = {n: h for n, h in before.items() if n not in after}
    moved = {n: {'before': h, 'after': after[n]} for n, h in before.items()
             if n in after and after[n] != h}
    accepted = not removed and not moved and added == AUTHORIZED
    result.update(
        historical_manifest_sha256=OLD_PIN,
        manifest_sha256=original.sha(new_path),
        documentation_changes=new['documentation_changes'],
        ref_delta={'added': added, 'removed': removed, 'moved': moved},
        concurrent_ref_preservation_status='PASS_EXACT_DOCUMENTED_ADDITION' if accepted else 'FAIL',
        ref_policy_evidence='docs/unforced-restart/round4/SUPERVISOR-REF-ADDENDUM.md')
    return result

if __name__ == '__main__':
    result = verify()
    print(json.dumps(result, indent=2))
    raise SystemExit(0 if result['concurrent_ref_preservation_status'] ==
                     'PASS_EXACT_DOCUMENTED_ADDITION' else 1)
