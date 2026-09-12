#!/usr/bin/env python3
"""Read-only preservation/snapshot verification; no historical validator execution."""
import hashlib,json,os,subprocess
from pathlib import Path
ROOT=Path('/home/velvet/worktrees/unforced-restart-20260909T202951Z')
assert Path.cwd()==ROOT
S=ROOT/'docs/unforced-restart/round3/snapshot'
def sha(p):
 with p.open('rb') as f:return hashlib.file_digest(f,'sha256').hexdigest()
def git(*a):return subprocess.check_output(['git',*a],cwd=ROOT)
before=json.loads((S/'preserved-before.json').read_text())
receipt=json.loads((S/'RECEIPT.json').read_text())
assert git('rev-parse','HEAD').decode().strip()==before['head']
index=Path(git('rev-parse','--git-path','index').decode().strip())
if not index.is_absolute():index=ROOT/index
assert sha(index)==before['index_sha256']
for p,h in before['files'].items():
 f=ROOT/p
 assert ('symlink:'+os.readlink(f) if f.is_symlink() else sha(f))==h,p
for line in before['refs']:
 ref,h=line.split();assert git('rev-parse',ref).decode().strip()==h
assert git('rev-parse',receipt['ref']).decode().strip()==receipt['commit']
selected=json.loads((S/'selected-paths.json').read_text())
for p,h in selected.items():
 assert sha(ROOT/p)==h,p
 assert hashlib.sha256(git('show',receipt['commit']+':'+p)).hexdigest()==h,p
for row in json.loads((S/'accepted-clean-hashes.json').read_text()):
 assert hashlib.sha256(git('show',receipt['commit']+':'+row['path'])).hexdigest()==row['sha256']
added=set(git('diff-tree','--no-commit-id','--name-only','-r',receipt['commit']).decode().splitlines())
assert added==set(selected)|{'docs/unforced-restart/round3/snapshot/selected-paths.json'}
forbidden={'.olean','.ilean','.ir','.so','.o','.pyc','.log'}
assert not any(Path(p).suffix in forbidden for p in added)
E=Path('/home/velvet/research-builds/unforced-round2-clean-20260909T221339Z-evidence-attempt2')
e=json.loads((S/'external-evidence.json').read_text())
assert sha(E/'research-evidence-sha256.json')==e['evidence_manifest_sha256']
for p,h in json.loads((E/'research-evidence-sha256.json').read_text()).items():assert sha(E/p)==h,p
src=ROOT/'Research/UnforcedRestart/Round3/WitnessFeasibility/Main.lean'
result=json.loads((src.parent/'out/strict-14ku121j/result.json').read_text())
assert result['exit']==0 and sha(src)==result['source_sha256']
print(json.dumps({'preservation':'PASS','existing_files':len(before['files']),'snapshot':receipt['commit'],'snapshot_paths':len(added),'clean_targets_hash_matched':16,'external_evidence_manifest':'PASS','head_index_prior_refs':'unchanged','focused_witness_source_sha256':sha(src),'focused_status':'exit 0; not aggregate Round3 acceptance'},indent=2))
