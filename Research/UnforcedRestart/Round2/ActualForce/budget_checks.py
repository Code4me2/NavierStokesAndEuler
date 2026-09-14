#!/usr/bin/env python3
"""Read-only source preservation and exact finite-count checks; NOT a Lean audit.
Run from the authorized worktree. Writes nothing; redirect stdout to owned out/.
No candidate seminorm is numerically evaluated.
"""
from fractions import Fraction
from hashlib import sha256
from math import comb
from pathlib import Path
import json
import tarfile

root = Path.cwd()
assert str(root) == '/home/velvet/worktrees/unforced-restart-20260909T202951Z'
snapshot = Path('/home/velvet/research-snapshots/unforced-round1-20260909T221339Z')
assert sha256((snapshot / 'SHA256SUMS').read_bytes()).hexdigest() == \
    '192e15dc0ff1cb79cae02a19941e0f816dc194e91123c205153ccf808322a488'
checked = []
with tarfile.open(snapshot / 'source-docs.tar.gz', 'r:gz') as archive:
    for item in archive.getmembers():
        if not item.isfile():
            continue
        relative = Path(item.name)
        assert not relative.is_absolute() and '..' not in relative.parts
        path = root / relative
        content = archive.extractfile(item).read()
        assert path.is_file(), str(path)
        assert sha256(content).digest() == sha256(path.read_bytes()).digest(), str(path)
        checked.append(str(relative))

# Ordered coordinate derivatives: 3^j words; Bessel H^k weights binomial(k,j).
weights = {k: [comb(k, j) * 3**j for j in range(k + 1)] for k in range(5)}
assert weights[2] == [1, 6, 9]
assert weights[3] == [1, 9, 27, 27]
# Volume of containing cube is exactly 1/8; cylinder volume is pi/32.
box_volume = Fraction(1, 2)**3
assert box_volume == Fraction(1, 8)
# Number of integer points with max_i |n_i| = r.
for r in range(1, 101):
    assert (2*r + 1)**3 - (2*r - 1)**3 == 24*r*r + 2
# Lattice embedding estimate: 24*zeta(2)/(16*pi^4) + 2*zeta(4)/(16*pi^4).
assert Fraction(24, 16*6) == Fraction(1, 4)
assert Fraction(2, 16*90) == Fraction(1, 720)
print(json.dumps({
    'classification': 'source preservation and exact combinatorics, not Lean/PDE certification',
    'snapshot_files_equal': len(checked),
    'sobolev_squared_bound_coefficients': weights,
    'containing_cube_volume': str(box_volume),
    'actual_cylinder_volume': 'pi/32 (standard Euclidean Lebesgue normalization)',
    'torus_H2_evaluation_constant_squared_upper': '1 + 1/(4*pi^2) + 1/720',
    'actual_force_constants_computed': False,
    'lean_compilations': 0,
    'checked_snapshot_paths': checked,
}, indent=2))
