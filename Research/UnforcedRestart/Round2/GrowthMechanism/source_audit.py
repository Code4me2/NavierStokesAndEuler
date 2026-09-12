#!/usr/bin/env python3
"""Read-only source checks; writes evidence only beside this script. No Lean/build."""
import hashlib
import json
from pathlib import Path
import subprocess
import tarfile

ROOT = Path('/home/velvet/worktrees/unforced-restart-20260909T202951Z')
OWN = ROOT / 'Research/UnforcedRestart/Round2/GrowthMechanism'
SNAP = Path('/home/velvet/research-snapshots/unforced-round1-20260909T221339Z')
BASE = '597692fa5d55e07d810b2d96ead1a67972585425'
SOURCES = [
 'NavierStokes/AxisymmetricFields.lean', 'NavierStokes/BaseResidual.lean',
 'NavierStokes/CoordinateAlgebra.lean', 'NavierStokes/SimilarityCoordinates.lean',
 'NavierStokes/NaturalCore.lean', 'NavierStokes/NaturalProfile.lean',
 'NavierStokes/ProfileHistories.lean', 'NavierStokes/SlowBorelBase.lean',
 'NavierStokes/EntranceAlignedBase.lean', 'NavierStokes/FinalSlowBase.lean',
 'NavierStokes/GermCandidateAssembly.lean', 'NavierStokes/MixedAxisPreservation.lean',
 'NavierStokes/MixedPeriodicAssembly.lean', 'NavierStokes/TimeLocalization.lean',
 'NavierStokes/ActualCandidateAssembly.lean', 'NavierStokes/PeriodicSobolev.lean',
 'NavierStokes/CandidateConsequences.lean', 'NavierStokes/R3CompactCandidate.lean',
]
def sha(b):
    return hashlib.sha256(b).hexdigest()

def main():
    assert Path(__file__).resolve().parent == OWN
    commands = []
    for cwd, cmd in [
        (SNAP, ['sha256sum', '-c', 'SHA256SUMS']),
        (ROOT, ['git', 'rev-parse', 'HEAD']),
        (ROOT, ['git', 'diff', '--exit-code', BASE, '--']),
        (ROOT, ['git', 'diff', '--cached', '--exit-code']),
    ]:
        p = subprocess.run(cmd, cwd=cwd, capture_output=True, text=True)
        commands.append(dict(cwd=str(cwd), command=cmd, exit=p.returncode,
                             stdout=p.stdout, stderr=p.stderr))
        assert p.returncode == 0, commands[-1]
    assert commands[1]['stdout'].strip() == BASE
    seal = sha((SNAP / 'SHA256SUMS').read_bytes())
    assert seal == '192e15dc0ff1cb79cae02a19941e0f816dc194e91123c205153ccf808322a488'
    sources = []
    for path in SOURCES:
        data = (ROOT / path).read_bytes()
        old = subprocess.run(['git', 'show', BASE + ':' + path], cwd=ROOT,
                             capture_output=True, check=True).stdout
        assert data == old, path
        sources.append(dict(path=path, sha256=sha(data), equals_baseline=True))
    frozen = []
    with tarfile.open(SNAP / 'source-docs.tar.gz', 'r:gz') as archive:
        for member in archive.getmembers():
            path = member.name.removeprefix('./')
            if member.isfile() and path.endswith(('.lean', '.md', '.json', '.py')):
                assert not Path(path).is_absolute() and '..' not in Path(path).parts
                old = archive.extractfile(member).read()
                assert (ROOT / path).read_bytes() == old, path
                frozen.append(dict(path=path, sha256=sha(old)))
    result = dict(status='SOURCE_CHECKS_ONLY', baseline=BASE, snapshot_digest=seal,
                  snapshot_filesystem_immutable=False, commands=commands,
                  baseline_sources=sources, frozen_source_docs=frozen,
                  new_accepted_lean=[], new_axiom_audits=[], compile_commands=[],
                  note='No compilation, clean build, Comparator or new Lean acceptance.')
    (OWN / 'out').mkdir(exist_ok=True)
    (OWN / 'out/source-evidence.json').write_text(json.dumps(result, indent=2) + '\n')
    print(f'SOURCE_CHECKS_ONLY: {len(sources)} baseline sources; {len(frozen)} frozen files; no Lean acceptance')

if __name__ == '__main__':
    main()
