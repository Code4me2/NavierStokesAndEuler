#!/usr/bin/env python3
"""Local source preservation only; never run historical validators or move HEAD/index."""
import hashlib, json, os, re, subprocess, tempfile
from pathlib import Path
from datetime import datetime, timezone

ROOT = Path('/home/velvet/worktrees/unforced-restart-20260909T202951Z')
EVIDENCE = Path('/home/velvet/research-builds/unforced-round2-clean-20260909T221339Z-evidence-attempt2')
OUT = ROOT / 'docs/unforced-restart/round3/snapshot'
BASE = '597692fa5d55e07d810b2d96ead1a67972585425'
def git(*args, env=None):
    return subprocess.check_output(['git', *args], cwd=ROOT, env=env).decode().strip()
def sha(p):
    with p.open('rb') as f:
        return hashlib.file_digest(f, 'sha256').hexdigest()
def save(name, value):
    p = OUT / name
    assert not p.exists(), p
    p.write_text(json.dumps(value, indent=2) + '\n')
assert Path.cwd() == ROOT
assert git('rev-parse', 'HEAD') == BASE
assert not git('diff', '--name-only') and not git('diff', '--cached', '--name-only')
assert not OUT.exists(), 'One-shot script: preserve receipt, never overwrite it'
index = Path(git('rev-parse', '--git-path', 'index'))
if not index.is_absolute(): index = ROOT / index
index_hash = sha(index)
refs = git('for-each-ref', '--format=%(refname) %(objectname)')
old = set(git('ls-files').splitlines())
for prefix in ['Research/UnforcedRestart', 'docs/unforced-restart']:
    old.update(str(p.relative_to(ROOT)) for p in (ROOT/prefix).rglob('*') if p.is_file() and 'Round3' not in p.parts and 'round3' not in p.parts)
preserved = {p: (('symlink:' + os.readlink(ROOT/p)) if (ROOT/p).is_symlink() else sha(ROOT/p)) for p in sorted(old)}
manifest1 = json.loads((ROOT/'Research/UnforcedRestart/MANIFEST.json').read_text())
manifest2 = json.loads((ROOT/'Research/UnforcedRestart/Round2/MANIFEST.json').read_text())
rows = manifest1['accepted'] + manifest2['accepted_round2'] + [manifest1['audit'], manifest2['audit']]
for r in rows + [manifest1['validation_script']] + manifest2['frozen_tools']:
    assert sha(ROOT/r['path']) == r['sha256'], r['path']
copies = json.loads((EVIDENCE/'research-replay/source-copies.json').read_text())
assert len(copies) == 16
for r in copies:
    assert sha(Path(r['source'])) == sha(Path(r['destination'])) == r['sha256']
for p, h in json.loads((EVIDENCE/'research-evidence-sha256.json').read_text()).items():
    assert sha(EVIDENCE/p) == h, p
assert json.loads((EVIDENCE/'research-replay/SUCCESS.json').read_text())['targets'] == 16
for i in range(1,17): assert (EVIDENCE/f'research-replay/{i:02}.exit').read_text().strip() == '0'
paths = {r['path'] for r in rows}
paths.update(['Research/UnforcedRestart/MANIFEST.json', 'Research/UnforcedRestart/MANIFEST.md', 'Research/UnforcedRestart/PLAN.md', 'Research/UnforcedRestart/Round2/MANIFEST.json', 'Research/UnforcedRestart/setup/ImportProbe.lean'])
# Deliberate source/docs selection; no out/, runs/, evidence/, drafts or caches.
paths.update(str(p.relative_to(ROOT)) for p in (ROOT/'docs/unforced-restart').rglob('*.md') if 'round3' not in p.parts)
paths.update(str(p.relative_to(ROOT)) for p in (ROOT/'Research/UnforcedRestart').rglob('*') if p.suffix in {'.py','.sh'} and not set(p.parts)&{'out','runs','evidence','__pycache__','Round3'})
paths.add('Research/UnforcedRestart/Round3/Integration/snapshot.py')
for p in paths:
    assert not (ROOT/p).is_symlink() and (ROOT/p).stat().st_size < 1024*1024, p
OUT.mkdir(parents=True)
save('preserved-before.json', {'head':BASE, 'index_sha256':index_hash, 'refs':refs.splitlines(), 'files':preserved})
save('accepted-clean-hashes.json', rows)
save('external-evidence.json', {'root':str(EVIDENCE), 'evidence_manifest_sha256':sha(EVIDENCE/'research-evidence-sha256.json'), 'verified_all_manifest_entries':True, 'source_copies':copies, 'success':json.loads((EVIDENCE/'research-replay/SUCCESS.json').read_text()), 'resolver':json.loads((EVIDENCE/'research-replay/resolver.json').read_text())})
excluded = sorted(p for p in old if p.startswith(('Research/', 'docs/unforced-restart/')) and p not in paths)
save('excluded-paths.json', excluded)
# Audit actual Markdown links against the future source tree, retaining historical text.
links=[]
tracked=set(git('ls-files').splitlines())
for p in sorted(paths):
    if not p.endswith('.md'): continue
    for target in re.findall(r'\]\(([^)]+)\)', (ROOT/p).read_text()):
        if '://' in target or target.startswith('#'): continue
        target=target.split('#')[0]
        resolved=os.path.normpath(str(Path(p).parent/target))
        if resolved not in paths|tracked:
            links.append({'document':p, 'link':target, 'resolved':resolved, 'disposition':'Historical/external evidence reference, not supplied by source snapshot; consult original worktree at identical relative path or external recovery evidence. Missing historical links are not acceptance evidence.', 'exists_in_preserved_worktree':(ROOT/resolved).exists()})
save('documentation-links.json', links)
(OUT/'PROVENANCE.md').write_text('''# Validated research source snapshot (local preservation)

Parent is the isolated baseline 597692fa5d55e07d810b2d96ead1a67972585425. This snapshot preserves 14 accepted mathematical sources, two audits, frozen manifests/tools, research documentation and reproducible scripts. The setup ImportProbe is tooling only, never an accepted theorem. No failed draft is accepted. New Round3 snapshot metadata/script is preservation tooling, not previously validated mathematics.

All accepted sources equal the clean replay hashes. external-evidence.json anchors the completed 16-target source-built replay and its full external evidence hash manifest. Installed Lean/core/compiler/runtime and host remain the explicit trust root. No clean rebuild, old-validator rerun, independent kernel certification or mathematical upgrade is claimed by this snapshot.

Frozen validators are path/HEAD/classification-bound. Their historical cached/blocked statuses and output expectations remain unchanged. Checking out this source snapshot does NOT make them portable or make this commit historically validated. CLEAN-RECOVERY.md and the external replay establish the separate recovery result.

Excluded reproducible artifacts: all compiled objects, native outputs, task out/ directories, integration validation/runs/evidence logs and generated inventories, caches, symlinks, and unaccepted DRAFT.md. Exact excluded research paths/hashes are in excluded-paths.json and preserved-before.json. These are retained untouched in the original isolated worktree, not deleted. No unrelated untracked files or credentials are staged. The tracked parent tree is inherited unchanged, including baseline challenge files; these are not research acceptance dependencies.

Historical documentation links are audited in documentation-links.json, including originally dangling relative links. They are not silently repaired. Non-Markdown code-path references to validation outputs likewise refer to excluded historical artifacts, not portable source dependencies. The round-one seal is external at /home/velvet/research-snapshots/unforced-round1-20260909T221339Z (SHA256SUMS digest 192e15dc0ff1cb79cae02a19941e0f816dc194e91123c205153ccf808322a488). Historical /tmp/agent19-validation.JEWFbX is not durable evidence or required for current clean acceptance.

Completed build and research evidence: /home/velvet/research-builds/unforced-round2-clean-20260909T221339Z-evidence-attempt2/. Prior failed preflight evidence: the sibling ending -evidence/. Verified source-built dependencies: /home/velvet/research-builds/unforced-round2-clean-20260909T221339Z/. All are read-only inputs for Round3. Full giant build logs, module enumerations and objects remain there, not in git. Hash preservation suffices; no WORM/sudo gate.
''')
paths.update(str(p.relative_to(ROOT)) for p in OUT.iterdir())
save('selected-paths.json', {p:sha(ROOT/p) for p in sorted(paths)})
paths.add(str((OUT/'selected-paths.json').relative_to(ROOT)))
# Unique temporary index lives outside the active index, inside authorized new tooling output.
with tempfile.TemporaryDirectory(prefix='index-', dir=OUT) as tmp:
    env=os.environ.copy(); env['GIT_INDEX_FILE']=str(Path(tmp)/'index')
    git('read-tree', 'HEAD', env=env)
    subprocess.run(['git','add','--',*sorted(paths)],cwd=ROOT,env=env,check=True)
    assert set(git('diff','--cached','--name-only',env=env).splitlines()) == paths
    tree=git('write-tree',env=env)
    commit=git('commit-tree',tree,'-p',BASE,'-m','Preserve validated isolated unforced research sources; no mathematical upgrade',env=env)
    ref='refs/heads/research/unforced-validated-snapshot-'+datetime.now(timezone.utc).strftime('%Y%m%dT%H%M%S%fZ')
    git('update-ref',ref,commit,'0'*40)
assert git('rev-parse','HEAD') == BASE and sha(index)==index_hash
for p,h in preserved.items():
    assert (('symlink:'+os.readlink(ROOT/p)) if (ROOT/p).is_symlink() else sha(ROOT/p)) == h,p
for line in refs.splitlines():
    r,h=line.split(); assert git('rev-parse',r)==h
save('RECEIPT.json', {'ref':ref,'commit':commit,'tree':tree,'parent':BASE,'selected_paths':len(paths),'accepted_mathematical_sources':14,'frozen_audits':2,'preserved_files':len(preserved),'head_index_prior_refs_and_files_unchanged':True,'receipt_is_post_snapshot':True})
print(json.dumps(json.loads((OUT/'RECEIPT.json').read_text()),indent=2))
