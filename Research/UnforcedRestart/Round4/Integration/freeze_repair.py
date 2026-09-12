#!/usr/bin/env python3
"""Explicit one-shot versioned freeze generation; never overwrites a freeze."""
import json
import sys
sys.dont_write_bytecode = True
import verify_repair as repair
v = repair.original
old = v.load(v.HERE / 'FINAL-MANIFEST.json')
v.require(v.sha(v.HERE / 'FINAL-MANIFEST.json') == repair.OLD_PIN, 'old freeze')
files = dict(old['files'])
for p, h in files.items():
    v.require(p in repair.DOC_CHANGES or v.sha(v.ROOT / p) == h, 'unapproved drift ' + p)
changes = {p: {'before': files[p], 'after': v.sha(v.ROOT / p)} for p in repair.DOC_CHANGES}
for p in repair.DOC_CHANGES:
    files[p] = changes[p]['after']
chain_path = v.HERE / 'chain-7hszmr9h/receipt.json'
endpoint = v.HERE / 'strict-txfa5ys7/receipt.json'
chain = v.load(chain_path)
v.require(chain['status'] == 'PASS', 'chain')
paths = [chain_path, endpoint, v.HERE / 'verify_repair.py', v.HERE / 'freeze_repair.py',
         v.HERE / 'repair-replay.log', v.HERE / 'repair-endpoints.log',
         v.ROOT / 'docs/unforced-restart/round4/SUPERVISOR-REF-ADDENDUM.md']
for receipt in [*map(v.Path, chain['receipts']), endpoint]:
    r = v.load(receipt)
    paths.extend([receipt, receipt.parent / 'compile.log', v.ROOT / r['source']])
    paths.extend(map(v.Path, r['outputs']))
for p in paths:
    files[str(p.relative_to(v.ROOT))] = v.sha(p)
new = dict(old, status='VERSIONED_DOCUMENTATION_REPAIR', files=files,
           chain=str(chain_path.relative_to(v.ROOT)),
           endpoint_receipt=str(endpoint.relative_to(v.ROOT)),
           previous_manifest_sha256=repair.OLD_PIN, documentation_changes=changes)
# rows retain the historical accepted source/object baseline; chain is fresh.
with (v.HERE / 'REPAIR-MANIFEST.json').open('x') as f:
    f.write(json.dumps(new, indent=2) + '\n')
print(v.HERE / 'REPAIR-MANIFEST.json')
