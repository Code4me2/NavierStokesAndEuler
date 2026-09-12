#!/usr/bin/env python3
"""Source-only negative tests. Not Lean acceptance or a proof oracle."""
import importlib.util
import json
from pathlib import Path
import sys
import tempfile
sys.dont_write_bytecode = True
p=Path(__file__).with_name('validate.py')
spec=importlib.util.spec_from_file_location('round2_validator',p)
v=importlib.util.module_from_spec(spec); spec.loader.exec_module(v)
tests=[]
for token in ['sorry','admit','axiom','unsafe','native_decide','implemented_by']:
    try: v.forbidden('theorem x : True := '+token)
    except RuntimeError: tests.append('reject '+token)
    else: raise AssertionError(token)
try: v.forbidden('set_option autoImplicit true',True)
except RuntimeError: tests.append('reject option override')
else: raise AssertionError('override accepted')
try: v.code_only('/- outer /- inner -/')
except RuntimeError: tests.append('reject unclosed nested comment')
else: raise AssertionError('unclosed accepted')
v.forbidden('/- sorry /- admit -/ unsafe -/\n-- axiom\n theorem x : True := True.intro')
tests.append('nested comments do not cause false construct rejection')
assert v.imports('import A\n/- import Fake -/\nimport B\n')==['A','B']
tests.append('exact imports ignore comments')
m=json.loads(p.parents[1].joinpath('MANIFEST.json').read_text())
assert len(m['accepted_round2'])==2 and sum(len(e['declarations']) for e in m['accepted_round2'])==8
assert v.ALLOWED=={'propext','Classical.choice','Quot.sound'}
tests.append('nonempty accepted set and exact standard axioms')
with tempfile.TemporaryDirectory(prefix='round2-input-test-') as scratch:
    root=Path(scratch)
    for ext in v.MODULE_SUFFIXES:
        (root/('Test'+ext)).write_text(ext)
    before=v.artifact_inventory([root])
    assert len(before)==5 and len(v.module_artifacts(root/'Test.olean'))==5
    v.require_stable(before,v.artifact_inventory([root]))
    for ext in v.MODULE_SUFFIXES:
        f=root/('Test'+ext)
        f.write_text('changed')
        try: v.require_stable(before,v.artifact_inventory([root]))
        except RuntimeError: pass
        else: raise AssertionError('undetected mutation '+ext)
        f.write_text(ext)
    (root/'Added.ir').write_text('new')
    try: v.require_stable(before,v.artifact_inventory([root]))
    except RuntimeError: pass
    else: raise AssertionError('undetected addition')
    (root/'Added.ir').unlink()
    (root/'Test.ir.sig').unlink()
    try: v.require_stable(before,v.artifact_inventory([root]))
    except RuntimeError: pass
    else: raise AssertionError('undetected deletion')
    tests.append('all five module inputs inventoried; mutations/additions/deletions rejected')
print(json.dumps({'status':'SOURCE_TOOL_TESTS_ONLY','tests':tests},indent=2))
