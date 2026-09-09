# Validation plan

This document records the reproducible gates for this branch. It does not replace the existing trusted Comparator implementation or its configs; it points at the checked-in `ComparatorChallenges/*.json` files and the pinned dependency data already in this repository.

## Local strict gates

Run in the development checkout:

```sh
lake build
lake env lean -DautoImplicit=false -DwarningAsError=true review-notes/round3/Axioms.lean
```

Expected axiom set for each delivered theorem:

```text
[propext, Classical.choice, Quot.sound]
```

The four delivered theorems are:

- `Euler.euler_breakdown_R3`
- `Euler.exists_compact_smooth_euler_singularity`
- `NavierStokes.Comparator.navier_stokes_breakdown_R3`
- `NavierStokes.Comparator.navier_stokes_breakdown_periodic`

## Cold Comparator gate in a fresh sandbox clone

Comparator must be run in a clone where solution modules have never been compiled. Do not run `lake build` or `lake env lean` on solution modules in that clone before Comparator.

Pinned inputs are the files committed in this repository:

- Lean toolchain: `lean-toolchain` (`leanprover/lean4:v4.34.0-rc2`).
- Lake dependencies: `lakefile.toml` and `lake-manifest.json`, including Comparator `19e111e2141cf333c7daff0f64c5f24acc91dd2e`, Mathlib `85e3a25e006c35636f0e53b0e9296caca2685bc0`, and lean4export `cacf989bd75f608700820f6afc595f32e7a99a4d`.
- Comparator configs: `ComparatorChallenges/NavierStokes.json` and `ComparatorChallenges/Euler.json`.

Fresh-clone setup, replacing `<candidate-sha>` with the commit being validated:

```sh
mkdir -p /tmp/navier-comparator-cold
cd /tmp/navier-comparator-cold
git clone https://github.com/Code4me2/NavierStokesAndEuler.git candidate
cd candidate
git fetch origin <candidate-sha>
git checkout --detach <candidate-sha>
git submodule update --init --recursive
elan toolchain install leanprover/lean4:v4.34.0-rc2
lake exe cache get
lake build lean4export comparator
```

External binaries required by the existing trusted gate must be available on `PATH` or through Comparator's documented environment variables:

- `landrun`
- `lean4export` (the Lake-built binary is `.lake/packages/lean4export/.lake/build/bin/lean4export`)
- `nanoda_bin`

Exact Comparator commands:

```sh
systemd-run --property=RestrictAddressFamilies=~AF_UNIX --user --pty -E PATH="$PATH" \
  --working-directory $(pwd) -- \
  bash -c 'lake exe comparator ComparatorChallenges/NavierStokes.json'

systemd-run --property=RestrictAddressFamilies=~AF_UNIX --user --pty -E PATH="$PATH" \
  --working-directory $(pwd) -- \
  bash -c 'lake exe comparator ComparatorChallenges/Euler.json'
```

Expected successful ending for each command:

```text
Your solution is okay!
```

## Deferred optional proposals

The strict build and theorem axiom gates are required for this refactor. Optional future cleanup proposals from the simplification notes and review artifacts are explicitly deferred unless they become correctness issues. In particular, no further dead-code sweeps, no Comparator-definition deduplication, and no changes to protected challenge/definition files are part of this validation plan.
