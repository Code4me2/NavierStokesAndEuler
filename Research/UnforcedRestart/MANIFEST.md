# Acceptance manifest

Frozen baseline: `597692fa5d55e07d810b2d96ead1a67972585425`. Machine-readable authority: [MANIFEST.json](MANIFEST.json).

**82 theorems + 6 definitions in twelve files.** No accepted result needs an external local-theory axiom: all are proved implications. Applying them to an unforced restart still needs the explicitly unproved [O1–O10](../../docs/unforced-restart/OBLIGATIONS.md).

## Reproduction and exact order

Run `python3 Research/UnforcedRestart/integration/validate.py` from the isolated worktree. The script is standard Python plus existing Git/Lake/Lean commands; it installs nothing and runs no build. All tasks are independent against baseline, so the deterministic serial order below is valid. Aggregate audit is last.

Each invocation is `env LEAN_NUM_THREADS=1 LEAN_PATH=<worktree>/Research/UnforcedRestart/integration/validation/lib lake env lean -j1 -DautoImplicit=false -DwarningAsError=true -o <output>.olean -i <output>.ilean <source>`. Output is `<worktree>/Research/UnforcedRestart/integration/validation/lib/<source-without-.lean>`. No baseline module output is overwritten. Lake supplies its pinned local library paths; the additional research path contains the freshly elaborated modules. Research imports use `Research.UnforcedRestart.«<slug>».Main`.

Exact commands, actual exit codes and inline research axioms: [SUCCESS.json](integration/validation/SUCCESS.json). Direct imports are listed below in source order. [dependencies.json](integration/validation/dependencies.json) enumerates **all 11,108 imported modules in loader order**, their direct source import lines, source/artifact hashes and paths. It is the complete imported-file inventory, not a claim of serial recompilation of every dependency. Baseline/dependency artifacts were already present; no dependency build was necessary.

## Acceptance and dependency coverage

Fresh strict elaboration: all twelve mathematical files plus `integration/Audit.lean`, exit 0. Combined import reveals no namespace/instance/import conflict; no mathematical source was edited.

`Audit.lean` is validation tooling, not a mathematical theorem. It enumerates **every constant** in every imported NavierStokes/Euler/Common/research module by defining-module identity, including generated helpers/constructors/projections, rather than selecting names or relying only on inline probes. It rejects unsafe project constants, challenge imports, or any axiom outside `{propext, Classical.choice, Quot.sound}`. Its own Lean metaprogram has no mathematical exports or proof-producing oracle.

[declarations.tsv](integration/validation/declarations.tsv) records 42,929 complete closures across project/research dependencies. There are 526 imported project/research modules, including empty re-export modules; all of their sources pass the forbidden-construct scan. External library/toolchain modules are all inventoried and their **used** axioms are included transitively in these closures, but unused external metaprogramming constants are not accepted mathematical exports. No `ComparatorChallenges.*` import is allowed. The setup probe and historical output files are not theorem dependencies.

Closure distribution: 38,280 `[propext,Classical.choice,Quot.sound]`; 3,664 `[propext]`; 320 `[propext,Quot.sound]`; 665 `[]`. Each of the 88 named research exports uses all three permitted axioms. No inherited project source option overrides were found. All source/olean hashes are in the dependency inventory, research hashes are frozen below/in JSON. This is cached dependency axiom auditing and fresh research elaboration, **not a clean dependency kernel rebuild or independent Comparator run**.

The script checks fixed HEAD and tracked worktree/index equality to baseline, eleven package pins/working diffs, authorized new paths and nonescaping symlinks; rejects unclassified research `.lean` files, frozen-source mismatches, prohibited source constructs, research option overrides, missing closure prints, compiler failures, unresolved dependency inventory entries, malformed/incomplete coverage and unexpected axioms. Any failure exits nonzero; a stale `SUCCESS.json` is removed before validation. Exact tools are pinned by existing toolchain/configuration, never edited.

## Classification legend

- **A**: actual candidate-to-PDE/admissibility result (candidate contract, or closed construction specialization).
- **B**: conditional PDE reduction/estimate or actual-field calculus/transformation.
- **C**: generic scalar/abstract analytic tool or logical diagnostic; not an NS estimate.
- **D**: unproved research/source discussion; no accepted theorem.

Category A does not claim candidate existence unless the declaration explicitly consumes the closed witness. The closed specialization here is `R3RestartData.actual_candidate_restart_data`; most A lemmas instead assume the exact known candidate contract. Category B includes true integral estimates, but their comparator/PDE hypotheses remain unproved in the intended unforced application. Full statements are frozen at the listed source lines.

## Accepted files and declarations (compile order)

### 1. `actual-forcing-budget/Main.lean`

Source: `Research/UnforcedRestart/actual-forcing-budget/Main.lean`; SHA-256 `190613356966300c5238cf12faf1e84b2aeabc9834e73b2b78237eedd5154f5a`.

Imports: `NavierStokes.R3CompactCandidate`, `NavierStokes.PeriodicForceDecay`, `Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic`.

Namespace: `UnforcedRestart.ActualForcingBudget`. All names below are qualified by this prefix.

| Declaration | Source line | Class |
|---|---:|:---:|
| `compact_jet_bound` | 14 | A |
| `compact_jet_intervalIntegrable` | 24 | A |
| `compact_time_integral_bound` | 38 | A |
| `compact_short_budget` | 56 | A |

Unforced application gaps: O7, O8, O9. These are not extra axioms used by the accepted proofs.

### 2. `difference-equation/Main.lean`

Source: `Research/UnforcedRestart/difference-equation/Main.lean`; SHA-256 `1c5ea8920c64129ecbe814b70ce2fae38ed4dee48deb649fe87669be72ed309a`.

Imports: `NavierStokes.SolutionDifference`.

Namespace: `UnforcedRestart.DifferenceEquation`. All names below are qualified by this prefix.

| Declaration | Source line | Class |
|---|---:|:---:|
| `residual` | 14 | B |
| `residual_one` | 19 | B |
| `difference_forces` | 25 | B |
| `forced_unforced` | 58 | B |
| `unforced_forced` | 78 | B |
| `forced_unforced_on_slab` | 97 | B |
| `divergence_free_difference` | 120 | B |
| `restart_difference_zero` | 130 | C |

Unforced application gaps: O1, O2, O5, O6, O7, O8, O9. These are not extra axioms used by the accepted proofs.

### 3. `energy-comparison/Main.lean`

Source: `Research/UnforcedRestart/energy-comparison/Main.lean`; SHA-256 `f8a731c7768154f737fecf161cd0a2a7d1fdf84314b4ebc5f13ac6e3d4b2615a`.

Imports: `NavierStokes.PeriodicUniqueness`.

Namespace: `UnforcedRestart.EnergyComparison`. All names below are qualified by this prefix.

| Declaration | Source line | Class |
|---|---:|:---:|
| `forced_energy_balance` | 13 | B |
| `forcing_work_le` | 81 | B |
| `forced_energy_rate_le` | 99 | B |

Unforced application gaps: O1, O2, O5, O6, O7, O8, O9. These are not extra axioms used by the accepted proofs.

### 4. `gronwall-threshold/Main.lean`

Source: `Research/UnforcedRestart/gronwall-threshold/Main.lean`; SHA-256 `48b50ff2b26e32007b5c714a42f37e03fe798c8987e13c6080cbf5375a5eb753`.

Imports: `NavierStokes.GronwallInterior`.

Namespace: `UnforcedRestart.GronwallThreshold`. All names below are qualified by this prefix.

| Declaration | Source line | Class |
|---|---:|:---:|
| `weighted_budget` | 16 | C |
| `threshold` | 50 | C |
| `zero_initial_threshold` | 68 | C |

Unforced application gaps: O5, O6, O7, O8, O9. These are not extra axioms used by the accepted proofs.

### 5. `local-theory-obstruction/Main.lean`

Source: `Research/UnforcedRestart/local-theory-obstruction/Main.lean`; SHA-256 `d9919bebd03e1618c0fe621eb12f93cb510b803a435c097fb3612d26e44f53f8`.

Imports: `NavierStokes.MaximalLifespan`.

Namespace: `UnforcedRestart.LocalTheoryObstruction`. All names below are qualified by this prefix.

| Declaration | Source line | Class |
|---|---:|:---:|
| `nonzero_snapshot_not_solution` | 15 | C |
| `unchanged_fields_force_rigidity` | 25 | B |
| `zero_datum_unforced_periodic_is_zero` | 34 | B |

Unforced application gaps: O1, O2, O3, O7, O8. These are not extra axioms used by the accepted proofs.

### 6. `periodic-restart-data/Main.lean`

Source: `Research/UnforcedRestart/periodic-restart-data/Main.lean`; SHA-256 `95423d4e60624a11dcb95901f3e346e0cb8bebc03e3d8af4e670efdfd4f67cb7`.

Imports: `NavierStokes.TimeLocalization`, `NavierStokes.ComparatorBridge`, `NavierStokes.PeriodicLocalization`.

Namespace: `UnforcedRestart.PeriodicRestartData`. All names below are qualified by this prefix.

| Declaration | Source line | Class |
|---|---:|:---:|
| `snapshot_admissible` | 11 | A |
| `candidate_snapshot` | 24 | A |
| `candidate_pressure_snapshot` | 31 | A |
| `periodize_snapshot` | 40 | C |
| `pressure_gauge_periodic` | 46 | C |

Unforced application gaps: O1, O2, O3, O7, O8, O9. These are not extra axioms used by the accepted proofs.

### 7. `pressure-absorption/Main.lean`

Source: `Research/UnforcedRestart/pressure-absorption/Main.lean`; SHA-256 `ed3fe773fc1b9d00998b583c2e0aa66295403f3921a852a715415333b5d3f8c9`.

Imports: `NavierStokes.ResidualCalculus`, `NavierStokes.SolutionDifference`.

Namespace: `UnforcedRestart.PressureAbsorption`. All names below are qualified by this prefix.

| Declaration | Source line | Class |
|---|---:|:---:|
| `residual_sub_pressure` | 11 | B |
| `residual_after_correction` | 21 | B |
| `unforced_iff_gradient` | 29 | B |
| `corrected_pressure_smooth` | 37 | B |
| `corrected_pressure_periodic` | 42 | B |
| `absorb_on` | 51 | B |
| `time_gauge_gradient` | 62 | B |

Unforced application gaps: O3, O4. These are not extra axioms used by the accepted proofs.

### 8. `r3-restart-data/Main.lean`

Source: `Research/UnforcedRestart/r3-restart-data/Main.lean`; SHA-256 `e80024b8013fcd2ff646da06613a307e51f72a7545ec60fedc37d415858d2d84`.

Imports: `NavierStokes.R3CompactCandidate`, `NavierStokes.TimeLocalization`, `NavierStokes.ActualCandidateAssembly`.

Namespace: `UnforcedRestart.R3RestartData`. All names below are qualified by this prefix.

| Declaration | Source line | Class |
|---|---:|:---:|
| `snapshot_smooth` | 13 | A |
| `snapshot_divergence` | 18 | A |
| `fixed_jet_support` | 26 | A |
| `compact_smooth_decay` | 40 | C |
| `snapshot_admissible` | 67 | A |
| `snapshot_compactSupport` | 76 | A |
| `snapshot_energy_integrable` | 87 | A |
| `actual_candidate_restart_data` | 96 | A |

Unforced application gaps: O1, O2, O3, O7, O8, O9. These are not extra axioms used by the accepted proofs.

### 9. `scaling-and-compactness/Main.lean`

Source: `Research/UnforcedRestart/scaling-and-compactness/Main.lean`; SHA-256 `451b85329629a3daeb6e5f9d97e23fa46868705799becfefbde6eeb93d6be9b0`.

Imports: `NavierStokes.ComparatorBridge`, `NavierStokes.BaseResidual`.

Namespace: `UnforcedRestart.ScalingAndCompactness`. All names below are qualified by this prefix.

| Declaration | Source line | Class |
|---|---:|:---:|
| `zoomVelocity` | 11 | C |
| `zoomForce` | 15 | C |
| `viscosity_coefficient` | 19 | C |
| `zoomForce_norm_le` | 23 | C |
| `zoomForce_tendsto` | 32 | C |
| `axis_power` | 44 | C |
| `base_zoom_axis` | 57 | B |

Unforced application gaps: O10. These are not extra axioms used by the accepted proofs.

### 10. `smooth-force-cutoff/Main.lean`

Source: `Research/UnforcedRestart/smooth-force-cutoff/Main.lean`; SHA-256 `accd8d5d4a26244783173ccdf30fe95d0e4c36f2cffa9334dd8662a545cadf02`.

Imports: `NavierStokes.SmoothCutoffs`, `NavierStokes.TimeLocalization`, `NavierStokes.CandidateFromLimits`, `NavierStokes.R3CompactCandidate`.

Namespace: `UnforcedRestart.SmoothForceCutoff`. All names below are qualified by this prefix.

| Declaration | Source line | Class |
|---|---:|:---:|
| `shutdown` | 14 | C |
| `shutdown_smooth` | 17 | C |
| `shutdown_bounds` | 21 | C |
| `shutdown_early` | 26 | C |
| `shutdown_late` | 32 | C |
| `shutdown_derivative_support` | 38 | C |
| `cutForce` | 57 | B |
| `cutForce_smoothOn` | 60 | B |
| `cutForce_early` | 64 | B |
| `cutForce_late` | 68 | B |
| `cutForce_support` | 72 | B |
| `cutForce_periodic` | 79 | B |
| `cutForce_time_support` | 86 | B |
| `cutForce_supportedIn` | 90 | B |
| `compact_candidate_cut_admissible` | 97 | A |
| `old_residual_defect` | 108 | B |
| `old_solves_cut_iff` | 116 | B |

Unforced application gaps: O2, O3, O7, O8, O9. These are not extra axioms used by the accepted proofs.

### 11. `strong-norm-growth-transfer/Main.lean`

Source: `Research/UnforcedRestart/strong-norm-growth-transfer/Main.lean`; SHA-256 `6e5f145d0370b166d095253b9b88f868f7f35b0b1af34bf23db277b3872b1147`.

Imports: `NavierStokes.PeriodicUniqueness`.

Namespace: `UnforcedRestart.StrongNormGrowthTransfer`. All names below are qualified by this prefix.

| Declaration | Source line | Class |
|---|---:|:---:|
| `evaluation_budget` | 9 | C |
| `speed_transfer` | 20 | C |
| `no_periodic_continuous_comparator` | 45 | C |
| `no_continuous_axis_comparator` | 58 | C |

Unforced application gaps: O2, O7, O8, O9. These are not extra axioms used by the accepted proofs.

### 12. `time-translation/Main.lean`

Source: `Research/UnforcedRestart/time-translation/Main.lean`; SHA-256 `48a1957d1b3ee79f9dc9660f3b7e96130f52c173b4ff60ec0ddd9cccc7faf99f`.

Imports: `NavierStokes.SolutionDifference`, `NavierStokes.ComparatorBridge`.

Namespace: `UnforcedRestart.TimeTranslation`. All names below are qualified by this prefix.

| Declaration | Source line | Class |
|---|---:|:---:|
| `shift` | 12 | B |
| `shift_initial` | 15 | C |
| `horizon_pos` | 18 | C |
| `shifted_time_interior` | 20 | C |
| `shift_smooth` | 24 | B |
| `shift_smooth_slab` | 32 | B |
| `shift_spatialDerivative` | 40 | B |
| `shift_divergence` | 43 | B |
| `shift_advection` | 46 | B |
| `shift_laplacian` | 49 | B |
| `shift_gradient` | 52 | B |
| `shift_hasDerivAt` | 56 | B |
| `shift_temporalDerivative` | 62 | B |
| `shift_derivWithin` | 68 | B |
| `shift_residual` | 75 | B |
| `old_time_differentiable` | 85 | B |
| `candidate_shift_equation` | 93 | A |
| `candidate_shift_within_equation` | 101 | A |
| `candidate_shift_unforced` | 111 | B |

Unforced application gaps: O1, O3, O4. These are not extra axioms used by the accepted proofs.

### 13. `integration/Audit.lean` (tooling)

SHA-256 `d6489c268378cb09988a9184efdc5c76941182349dc0bfc9deb63e6ed8431396`. Imports the twelve modules above in the same order, then `Lean.Util.CollectAxioms`. Compiles last, to the same isolated mirrored output root. No additional mathematical result is claimed.

## Excluded/rejected material

No final mathematical source was rejected; no incomplete Lean scratch file remains in the accepted list. The following are **not accepted results/evidence**:

| Material | Reason/status |
|---|---|
| `setup/ImportProbe.lean` | Historical baseline signature/axiom probe; no new theorem; not part of the combined import. |
| Task-local `out/` objects/logs | Historical producer checks, not substitutes for the integration rerun. |
| R³ datum draft | Failed positivity unfolding for a real-power continuity premise; corrected before final accepted source. |
| Periodic datum draft | Missing ContDiff scope and beta-reduced rewrite target; corrected. |
| Translation draft | Derivative chain-rule elaboration needed explicit definitions; corrected. |
| Smooth cutoff draft | Definitional equality/linter issue; corrected without relaxing options. |
| Difference draft | Unnecessary tactic sequencing and zero normalization; corrected. |
| Energy drafts | Inner-product type, equality negation and lambda/continuity elaboration issues; corrected. |
| Gronwall draft | Ambiguous multiplication-order lemma under `open Set`; corrected using positive exponential. |
| Scaling drafts | Real-power rewriting/casts and continuity-map elaboration; corrected. |
| Local-theory draft | Nonexistent `SolutionDifference.zero_residual`; corrected to actual `ProblemStatement.zero_residual`. |
| Pressure, strong-norm, actual-budget tasks | No incomplete final attempts reported; only final frozen sources accepted. |
| `integration/rejected-audit-elaboration.log` | Actual compiler exit 1: audit counter inferred wrong type; explicit Nat annotation fixes tooling only. |
| Initial integration inventory runs | Nonzero validator exits for unresolved Lake source path / quoted research module path; fixed resolver. No success marker accepted from those runs. |
| Terminal force/potential, strong-norm stability, local NS existence, Sobolev embedding application, mixed-norm/FTC/zoom covariance/limit proposals | Unproved D discussion, not accepted Lean. See OBLIGATIONS and task reports. |
| Failed draft error-recovery `sorryAx` diagnostics | Rejected compiler-error output, never accepted closures. Final sources and complete fresh closures contain none. |
| Baseline challenge placeholders | Outside accepted import closure; no claims based on them. |

No resource-limit overrides, custom axioms, sorry/admit, unsafe mathematical exports, native proof shortcuts or hypothesis weakening were introduced. Existing external library metaprogramming remains part of the ordinary Lean trust/provenance boundary, not an independent mathematical verification claim.
