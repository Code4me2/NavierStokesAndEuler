# Round-three Lean refactor progress

Captured: 2026-09-09T17:07Z-17:35Z UTC, by a continuation agent. No commits, resets, stashes, cleans or pushes were performed.

## Initial repository state

- Working directory: `/home/velvet/Desktop/NavierStokesAndEuler`
- Branch/HEAD at capture: `simplify`, `4cd69e43afae` (`Round 3 stage A: condense the top of both arguments; split the Euler invariant`).
- Upstream relation at capture: `## simplify...fork/simplify [ahead 3]`.
- Last committed round-three stage A: `4cd69e4`.
- Uncommitted source changes at capture: 42 tracked modified files plus untracked `Common.lean`, `Common/`, `Euler/PacketStageSuccessor.lean`, `REVIEW.md`, `SIMPLIFICATIONS.md`, and `review-notes/`.
- This file was written after the external backup, so it is not part of that backup snapshot.

## Preservation backup

Before inspecting diffs or editing, all current working changes were copied externally to:

`/home/velvet/refactor-backups/navier-round3-continuation-20260909T170730Z`

Contents:

- `HEAD.txt`
- `git-status-short.txt`
- `git-status-porcelain-v2.txt`
- `diff-against-HEAD.patch` (`git diff --binary HEAD`)
- `diff-cached-against-HEAD.patch`
- `untracked-files.txt`
- `untracked-nonignored.tar.gz` containing all `git ls-files --others --exclude-standard` entries, including `Common/`, `Common.lean`, `Euler/PacketStageSuccessor.lean`, `REVIEW.md`, `SIMPLIFICATIONS.md`, and `review-notes/`.

## Competing writers check

Best-effort process/handle check before editing found no open writable handles under the repo. There is an old Claude daemon/resume process for the interrupted session and an active Pi workflow process, but no `lake`/`lean`/`git` process writing the tree was observed. Treat the old Claude session as stale unless reactivated.

## What is already committed

- `a9a7ff1`: removed attributed declarations unreachable from the delivered theorems; full build green; four theorem axiom set unchanged.
- `4cd69e4`: round-three stage A; full build green; four theorem axiom set unchanged. Stage A included the Euler top condensation, Navier-Stokes adapter/top rework, and the Euler `GrowthData` split.

## Uncommitted work that appears complete or mostly complete

From the Claude workflow journal and current diffs:

1. **Common library extraction**
   - New `Common` Lean library in `lakefile.toml`, `Common.lean`, `Common/Cutoffs.lean`, `Common/SobolevL6.lean`.
   - Euler and Navier-Stokes cutoff/Sobolev wrappers now import/re-export common statements.
   - Claimed compile-verified by the previous task; current full build reaches and builds these changes before later failures.

2. **Euler maximality route**
   - `Euler/CompactVorticityContradiction.lean` now proves the comparator nonexistence contradiction from `FiniteLifespan.maximal` rather than BKM.
   - Old BKM route preserved in `Euler/Showcase.lean` outside the delivered path.
   - Docs still need updating to stop describing the delivered contradiction as BKM-based.

3. **Navier-Stokes zero alias slot removal**
   - `CycleCoefficients.aliasCoefficients` and corresponding invariant field removed across the cycle state/coherence files.
   - Claimed compile-verified by previous task; current build passes these files before later failures.

## Partial / broken work needing reconciliation

1. **Euler successor unification**
   - New untracked `Euler/PacketStageSuccessor.lean` defines a shared `Stage.Step` and `Stage.next`.
   - `Euler/PacketForwardSuccessor.lean` and `Euler/PacketJoinedSuccessor.lean` now try to package forward/joined choices as `forwardStep`/`joinedStep` and call `P.next`.
   - Current `lake build` fails here:
     - `Euler/PacketForwardSuccessor.lean:65:4` timeout at `whnf`.
     - Because `forwardStep` times out, later projections fail: invalid field `forwardStep`; `P.forwardNext` seen as a value, not a function.
     - `Euler/PacketJoinedSuccessor.lean:69:4` timeout at `whnf`, then invalid field `joinedStep`/`joinedNext` projection errors.
   - Likely fix: make the `Step` structure construction less defeq-heavy. Prefer explicit helper defs for `parent/state/low/renewal` or term-mode proofs with local `have`s, and/or keep the old per-file smallness/renewal defs while sharing only the final `next` assembly. Do not add `set_option maxHeartbeats`.

2. **Navier-Stokes compact-first / periodization rewrite**
   - `NavierStokes/CandidateFromLimits.lean`, `MixedPeriodicAssembly.lean`, and `R3CompactCandidate.lean` contain a partial rewrite: compact whole-space candidate first, periodic candidate by lattice periodization.
   - Current `lake build` fails in `MixedPeriodicAssembly`:
     - `:245:6` rewrite pattern mismatch in `cutVelocity_divergence_free`.
     - `:428:0` timeout at `whnf`.
     - `:467:10` timeout at `isDefEq`.
     - `:528:50` `ContDiffOn.mono` type mismatch (`subset_univ` expected `univ ⊆ univ ×ˢ univ`).
     - `:492:8` kernel unknown constant `NavierStokes.MixedPeriodicAssembly.candidate_of_periodization`, caused by the preceding failed declaration.
   - Likely fix: first repair the local divergence proof by unfolding/changing exactly to `cutVelocity`; then split the large periodization theorem into small named lemmas to avoid defeq timeouts; finally fix the `ContDiffOn.mono` domain argument.

## Protected delivered statements

Do not change the names, namespaces, statement types, challenge modules, or independent copied definitions for:

- `Euler.euler_breakdown_R3` in `Euler/Solution.lean`
- `Euler.exists_compact_smooth_euler_singularity` in `Euler/Solution.lean`
- `NavierStokes.Comparator.navier_stokes_breakdown_R3` in `NavierStokes/ComparatorSolution.lean`
- `NavierStokes.Comparator.navier_stokes_breakdown_periodic` in `NavierStokes/ComparatorSolution.lean`
- `Euler/SolutionDefinitions.lean`
- `NavierStokes/ComparatorDefinitions.lean`
- `ComparatorChallenges/*.lean` and `ComparatorChallenges/*.json`

Comparator independence depends on solution files not importing the challenge modules.

## Bounded continuation plan

1. Keep the backup above immutable. Make a second backup before any destructive reconciliation.
2. Triage with targeted builds before full build:
   - `lake build Euler.PacketStageSuccessor`
   - `lake build Euler.PacketForwardSuccessor Euler.PacketJoinedSuccessor`
   - `lake build NavierStokes.MixedPeriodicAssembly`
3. Fix or back out only the two partial refactors:
   - For Euler, either complete the shared `Step.next` refactor without heartbeat increases, or revert only the successor-unification hunks while preserving stage A and other complete edits.
   - For Navier-Stokes, either complete compact-first periodization in small lemmas, or revert only the compact-first rewrite while preserving Common/P6/top-adapter edits.
4. Once targeted builds pass, run the full strict gate and axiom check below.
5. Refresh docs (`docs/PROOF-OUTLINE.md`, `README.md` if needed, this file or a successor note) to mention `Common/`, the Euler maximality route, and any final status of compact-first/periodization.
6. Only after a green full build and axiom check, consider a local commit. No pushes unless explicitly requested later.

## Validation contract and exact commands

Full strict Lean build (uses `lakefile.toml` strict options: `autoImplicit=false`, `warningAsError=true` for `Common`, `NavierStokes`, `Euler`; `autoImplicit=false` for `ComparatorChallenges`):

```sh
lake build
```

Four delivered-theorem axiom check:

```sh
lake env lean -DautoImplicit=false -DwarningAsError=true review-notes/round3/Axioms.lean
```

`review-notes/round3/Axioms.lean` contains:

```lean
import Euler.Solution
import NavierStokes.ComparatorSolution
#print axioms Euler.euler_breakdown_R3
#print axioms Euler.exists_compact_smooth_euler_singularity
#print axioms NavierStokes.Comparator.navier_stokes_breakdown_R3
#print axioms NavierStokes.Comparator.navier_stokes_breakdown_periodic
```

Expected axiom set for all four: `[propext, Classical.choice, Quot.sound]`.

Comparator gates (must be run in a fresh clone whose solution files have not been compiled, not as root, with `landrun`, `lean4export`, and `nanoda_bin` available):

```sh
lake exe cache get
lake build lean4export comparator

systemd-run --property=RestrictAddressFamilies=~AF_UNIX --user --pty -E PATH="$PATH" \
  --working-directory $(pwd) -- \
  bash -c 'lake exe comparator ComparatorChallenges/NavierStokes.json'

systemd-run --property=RestrictAddressFamilies=~AF_UNIX --user --pty -E PATH="$PATH" \
  --working-directory $(pwd) -- \
  bash -c 'lake exe comparator ComparatorChallenges/Euler.json'
```

Expected successful Comparator ending for each config: `Your solution is okay!`.

## Current validation result

A full `lake build` was run after capture. It is not green. It failed only after building many changed modules; reported failing targets were:

- `NavierStokes.MixedPeriodicAssembly`
- `Euler.PacketForwardSuccessor`
- `Euler.PacketJoinedSuccessor`

Do not run Comparator until the strict full build and axiom check are green.

## Continuation update — Euler successor unification

Updated: 2026-09-09T17:18Z UTC, by Pi continuation agent. No commits, resets, stashes, cleans or pushes were performed.

Scope was intentionally limited to Euler successor files:

- `Euler/PacketStageSuccessor.lean`
- `Euler/PacketForwardSuccessor.lean`
- `Euler/PacketJoinedSuccessor.lean`

What changed:

- Completed the variant-independent successor assembly around `Stage.Step` / `Stage.next`.
- Kept the analytical split between the forward and joined pipelines: forward still packages `earlyRatio`, `forwardInput`, `GeometryForwardChoice`, and the forward no-history child state; joined still packages `badRatio`, `joinedInput`, `GeometryJoinedChoice`, history data, and the joined initial increment theorem.
- Repaired the timeout in `forwardStep` / `joinedStep` without heartbeat increases by storing the child physical estimate as one combined `Step.physical_bounds` field rather than two separately elaborated projections, and by naming `forwardState` / `joinedState` plus `forwardPhysicalBounds` / `joinedPhysicalBounds` before constructing the shared `Step` records. This avoids repeatedly unfolding the geometry choice while checking later fields.

Validation actually run:

```sh
lake build Euler.PacketStageSuccessor Euler.PacketForwardSuccessor Euler.PacketJoinedSuccessor
lake build Euler
lake build
```

Results:

- `lake build Euler.PacketStageSuccessor Euler.PacketForwardSuccessor Euler.PacketJoinedSuccessor` passed.
- `lake build Euler` passed. During this build, Lean printed the expected axiom sets for the two Euler delivered theorems:
  - `Euler.euler_breakdown_R3`: `[propext, Classical.choice, Quot.sound]`
  - `Euler.exists_compact_smooth_euler_singularity`: `[propext, Classical.choice, Quot.sound]`
- Full `lake build` is still not green, but the Euler successor failures are gone. The remaining failure is outside this phase, in `NavierStokes.MixedPeriodicAssembly`.

Residual full-build blockers observed after the Euler fix:

- `NavierStokes/MixedPeriodicAssembly.lean:245:6`: divergence rewrite still does not match the `cutVelocity` / `cutPotential` target.
- `NavierStokes/MixedPeriodicAssembly.lean:428:0`: timeout at `whnf`.
- `NavierStokes/MixedPeriodicAssembly.lean:467:10`: timeout at `isDefEq`.
- `NavierStokes/MixedPeriodicAssembly.lean:528:50`: `ContDiffOn.mono` domain mismatch (`subset_univ` has type `?m ⊆ univ`, expected `univ ⊆ univ ×ˢ univ`).
- `NavierStokes/MixedPeriodicAssembly.lean:492:8`: unknown constant cascade from the failed `candidate_of_periodization` declaration.

Common/integration dependency note for next phase:

- No new Common changes were made. The Euler unification now compiles against the existing Common/library-extraction state. The next phase can focus on the Navier-Stokes compact-first periodization rewrite without needing an Euler-side integration repair.

## Continuation update — Navier-Stokes compact-first periodization integrated

Updated: 2026-09-09T17:27Z UTC, by Pi continuation agent. No commits, resets, stashes, cleans or pushes were performed.

Scope was limited to finishing round-three integration and repairing the interrupted compact-first/periodization refactor.

What changed in this continuation:

- `NavierStokes/MixedPeriodicAssembly.lean`
  - Repaired `cutVelocity_divergence_free` after the direct-field split by changing the goal to the exact unfolded `cutVelocity`/`cutPotential` expression before applying `spatialDivergence_add`.
  - Finished the compact-first direction:
    - `exists_compact_candidate` builds the compact whole-space candidate from the cut fields and residual limits.
    - `periodize_jets` transports jets through lattice periodization via the representative point.
    - `candidate_of_periodization` now assembles the periodic `CandidateProperties` from named small lemmas for initial data, force time support, divergence, Navier-Stokes equation, and speed blow-up, avoiding the previous `whnf`/`isDefEq` timeouts.
    - The all-space `ContDiff` proof for the periodized force was fixed without an invalid `ContDiffOn.mono` domain coercion.
- `NavierStokes/GermCandidateAssembly.lean`
  - `WitnessData` now records the compact candidate produced before periodization (`compact_forcing`, `compact_candidate`) alongside the periodic force and existing consequences.
  - The finite-stage hub constructs both the compact candidate and the periodized candidate from the same scheduled sums, preserving the existing periodic witness data.
- `NavierStokes/ActualCandidateAssembly.lean`
  - The actual `Witness` existential now exposes the compact candidate from the hub while preserving the periodic selected-candidate projection.
- `NavierStokes/R3ActualCandidate.lean`
  - `selected_compact_candidate` now extracts the recorded compact-first candidate instead of calling the removed/obsolete `R3CompactCandidate.of_localized_fields` recovery path.
- Documentation refreshed:
  - `docs/PROOF-OUTLINE.md` now describes the Euler delivered contradiction as the maximality route rather than BKM, and describes the Navier-Stokes compact-first/periodization flow.
  - `README.md` now mentions the shared strict `Common` library in the build description.

Validation actually run after the repairs:

```sh
lake build NavierStokes.MixedPeriodicAssembly
lake build NavierStokes.R3ActualCandidate
lake build
lake env lean -DautoImplicit=false -DwarningAsError=true review-notes/round3/Axioms.lean
```

Results:

- `lake build NavierStokes.MixedPeriodicAssembly`: passed.
- `lake build NavierStokes.R3ActualCandidate`: passed.
- Full strict `lake build`: passed.
  - Expected ComparatorChallenges warnings remained only the four reference-statement `sorry`s.
  - Lean printed the expected axiom sets for the delivered Euler and Navier-Stokes theorems during the build.
- Explicit axiom check passed; all four delivered theorems reported exactly:
  - `[propext, Classical.choice, Quot.sound]`

Residual blockers:

- None for the strict repository build or delivered-theorem axiom check in this working tree.
- Comparator was not run, per the existing note that it must be run in a fresh clone/sandbox where solution files have not been compiled.

Preservation notes:

- The external backup recorded earlier remains untouched.
- No publish/commit/push/reset/stash/clean was performed.
- Optional future dead-code sweeps from `structure-navier-stokes-argument.md` were not attempted.

## Finalization update — review finding addressed

Updated: 2026-09-09T17:31Z UTC, by Pi finalization agent. No pushes, resets, stashes, cleans, or amended commits were performed.

Actions taken after reading `review-notes/pi-round3-review.md`:

- Repaired the only low-severity finding: the stale docstring for
  `NavierStokes.MixedPeriodicAssembly.exists_compact_candidate` now says the compact candidate is
  recorded in witness data before periodization and later extracted by
  `R3CompactCandidate.selected_compact_candidate`.
- Added `docs/VALIDATION-PLAN.md`, a branch-local validation plan with:
  - strict local build and four-theorem axiom commands;
  - exact cold Comparator commands for both `ComparatorChallenges/NavierStokes.json` and
    `ComparatorChallenges/Euler.json`;
  - fresh-clone setup using the pinned `lean-toolchain`, `lakefile.toml`, and
    `lake-manifest.json` inputs;
  - the existing trusted Comparator gate implementation and external `landrun`, `lean4export`,
    and `nanoda_bin` requirements.
- Updated `README.md` to point to the validation plan while leaving `ComparatorChallenges/README.md`
  and all protected challenge/config/definition files unchanged.
- Optional proposals remain explicitly deferred: no additional dead-code sweeps, no
  Comparator-definition deduplication, and no protected statement/config changes are part of this
  finalization.

Residual blockers:

- None known for the strict repository build or delivered-theorem axiom check.
- Cold Comparator runs remain intentionally deferred to a fresh sandbox clone as documented in
  `docs/VALIDATION-PLAN.md`; do not claim Comparator completion until both runs end with
  `Your solution is okay!`.

Final validation actually run after the review-docstring repair:

```sh
lake build
git diff --check
git diff --name-status -- ComparatorChallenges Euler/SolutionDefinitions.lean NavierStokes/ComparatorDefinitions.lean formalization.yaml ComparatorChallenges/README.md
git diff -- '*.lean' | grep -nE '^\+.*\b(sorry|admit|axiom|unsafe|set_option)\b' || true
lake env lean -DautoImplicit=false -DwarningAsError=true review-notes/round3/Axioms.lean
```

Results:

- `lake build` completed successfully (`11087 jobs`). Only the four expected
  `ComparatorChallenges` `sorry` warnings were emitted.
- `git diff --check` was clean.
- Protected challenge/config/definition files listed above had no diff.
- No added Lean lines contained `sorry`, `admit`, `axiom`, `unsafe`, or `set_option`.
- Explicit axiom check reported exactly `[propext, Classical.choice, Quot.sound]` for all four
  delivered theorems.
