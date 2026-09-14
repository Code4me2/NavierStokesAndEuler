# Periodic-slab integration update — raw O5 checked, clean provenance blocked

The settled-worker ownership transfer and PLAN clarification authorized integration and a serialized focused slot. The integrator implemented `Research/UnforcedRestart/Round2/PeriodicSlab/Main.lean`: `force_energy_continuousOn`, `slab_energy_derivative_le`, `primitive_on_slab`, and `periodic_slab_comparison`. All four pass strict cached-dependency elaboration and the new comprehensive semantic/standard-axiom audit. The final theorem derives its compact-slab gradient bound and both literal FTC primitives, and concludes the actual integrated energy estimate with zero common-datum error. It does not assume that estimate. **Raw-field O5 is now closed at cached-check level**; Comparator O1, clean-source provenance, strong stability, weighted smallness and growth transfer remain open.

Final evidence: `Research/UnforcedRestart/Round2/Integration/runs/20260909T224305Z/`. The candidate-contract actual cell-budget interface is in `Round2/ActualForce/Main.lean`. See [REPORT.md](REPORT.md) and [DEPENDENCIES.md](DEPENDENCIES.md) for exact scope, interfaces and failures. The Markdown draft below remains historical and unaccepted as a separate source. No claim of full endpoint PDE adapters was added.

---

# Historical periodic-slab handoff — O5 not accepted in the worker pass

Owner: periodic-slab. Namespace reserved: `UnforcedRestart.Round2.PeriodicSlab`.

## Status and files

- Read Round2 PLAN, initialization REPORT, snapshot README, baseline README, round-one FINAL-REPORT, OBLIGATIONS, MANIFEST.md, frozen validator, differing-force energy, scalar Gronwall and time-translation sources.
- Snapshot checksum check passed, including the published `SHA256SUMS` digest. This does **not** make the snapshot filesystem-immutable or clear the PLAN gate.
- No coordinator allocation of the single focused Lean slot is present in the supplied handoff or current PLAN/REPORT. No compiler/build/worker was launched independently.
- **No new accepted Lean declarations, no strict compilation, no Round2 axiom audit, no clean-build result, no Comparator/Nanoda run.** O5 remains formally open. This is not a PASS with an empty manifest.

Owned additions:

1. `Research/UnforcedRestart/Round2/PeriodicSlab/DRAFT.md`: exact conditional theorem specification, two unvalidated Lean adapter drafts, complete mathematical FTC assembly, and endpoint analysis. Markdown deliberately prevents unvalidated drafts from entering the accepted Lean set.
2. `Research/UnforcedRestart/Round2/PeriodicSlab/out/preflight/`: snapshot, baseline, index and frozen-source evidence; source SHA-256 inventory.
3. This report.

No baseline/config, frozen source/validator/output, original-checkout, other worker file, global setting, commit or push was modified by this worker.

## Mathematical progress and precise remaining bridge

The finite-slab bridge needs **no new analytic theorem located outside the current imports**. Existing source already proves all major ingredients. The gap is composition plus strict elaboration, not an unavailable PDE estimate. This is a source-backed proof plan, not a formal achievement claim.

Fix ONE `0<t0<1`, `H=1-t0`, `0<S<H`, arbitrary common datum `a`, and the same raw reference/comparator fields. Require joint closed-slab smoothness of both velocities and both pressures, both divergence constraints, periodicity of all four fields, literal viscosity-one forced/unforced residual identities in the interior, and the appropriate within-time boundary equations when packaging a closed-slab solution. A globally smooth hypothetical comparator supplies these inputs only conditionally; this work supplies no existence.

### 1. Derive a coefficient; do not hypothesize the target inequality

`SolutionDifference.exists_gradient_bound` obtains `B_S>0` on the actual compact slab/cube from joint smoothness. Its proof uses `fderivWithin` and `spatialDerivative_eq_within_comp`, so it already handles spatial derivatives at BOTH time endpoints correctly. Set `L(r)=B_S`, a continuous proved majorant. Then `k=2L+1` is an actual coefficient, not an unexplained stability constant. The PLAN integral target permits this nonoptimal constant majorant. Nothing implies uniformity in `S↑H`.

### 2. Derive the actual energy differential inequality

With `w=ur-v`, `r=pr-q`, the already-checked sign is

`∂s w = Δw − Dur(w) − Dw(v) − ∇r + fr`.

`EnergyComparison.forced_energy_rate_le`, with both PDEs substituted, gives

`energyRate + 2D ≤ (2B_S+1)E + g`,

where `E=∫Q |w|²` and `g=∫Q |fr|²`. `dissipation_nonneg` discards `2D`; `energy_hasDerivAt` identifies `energyRate` with the genuine derivative of `E` on `(0,S)`. Both pressure periodicities remain essential. No force periodicity is needed merely to integrate its work on a cube, although the intended periodic candidate has it.

### 3. Prove forcing integrability and literal primitives

`cubeIntegral_continuousOn_Icc` applied to joint continuity of `|fr|²` gives continuity of `g` on `[0,S]`. Spatial integrability comes from `integrable_cube` for each continuous slice. Continuous functions on compact real intervals are interval-integrable, yielding the time integrability of the actual cube norm.

For continuous `c` on `[0,S]`, use the literal `P(s)=∫₀ˢ c(r)dr`. The required mathlib adapter must prove its closed-interval continuity, interior derivative, zero at zero, and subinterval integrability. Exact API subtlety: `continuousOn_primitive_interval` takes `IntegrableOn` on `uIcc`, whereas `integral_hasDerivAt_right` takes `IntervalIntegrable` AND local strong measurability AND `ContinuousAt`. Restrict the closed-interval continuity to the open interval to obtain local measurability; continuity at one point alone is not enough. No global continuity outside the slab is needed.

Apply the adapter first to `k`, defining `A`, and next to `exp(-A)*g`, defining the weighted budget primitive. Neither primitive derivative is a premise of the proposed PDE theorem.

### 4. Close the time integration, including endpoints

`energy_continuousOn` supplies endpoint continuity. `energy_initial_zero` consumes the actual common datum equalities through transitivity, not a zero-datum solution wrapper. Apply `GronwallThreshold.weighted_budget` with the proved derivatives and inequality, and normalize the actual integrals at zero. Multiplication by the positive exponential yields

`E(s) ≤ exp(A(s)) ∫₀ˢ exp(-A(r)) g(r) dr`,

`A(s)=∫₀ˢ (2L(r)+1)dr`, for every `s∈[0,S]`.

This uses squared L² energy throughout: no differentiating `sqrt(E)` at zeros, no assumed energy inequality, no pointwise evaluation inference.

## Endpoint obligations: distinguish what is available from what is uncompiled

| Obligation | Status |
|---|---|
| Full temporal derivative on `(0,S)` from slab smoothness | Baseline `time_differentiable_at_interior`, used by `energy_hasDerivAt`. |
| Continuity of energy at 0 and S | Baseline `energy_continuousOn`; does not assert endpoint full differentiability. |
| Ordinary spatial derivatives at 0 and S, compact gradient bound | Baseline `spatialDerivative_eq_within_comp` and `exists_gradient_bound`. |
| New-zero reference `derivWithin (Ici 0)` forced equation | Frozen `candidate_shift_within_equation`, using old-time interior differentiability. |
| New-zero comparator within-time equation | Must come from an admissible arbitrary-datum comparator contract, or be derived by within-derivative continuity from interior PDE. No new checked adapter here. |
| Comparator endpoint S from only a closed `[0,S]` contract | Left derivative / `derivWithin (Icc 0 S)`, NOT automatically full derivative or `derivWithin (Ici 0)`. |
| Comparator full derivative at S from a common larger `[0,H)` domain | S is interior since S<H; distinct, stronger domain input. |
| Extending interior PDE to closed-slab within PDE by continuity and density | Mathematically justified for jointly smooth slab fields, but the repeated spatial-derivative continuity and residual extension have not been assembled/elaborated here. |
| Actual coefficient/source primitives | Source APIs located; no new compiled FTC wrapper. |

A boundary PDE is not needed to apply interior-derivative Gronwall. It is needed if claiming a full closed-slab solution adapter. The draft explicitly separates those claims instead of silently strengthening `ContDiffOn` to smoothness on an open neighborhood of zero.

## Citation map

Paths are relative to the authorized worktree unless noted. Declaration names are exact; relevant source hashes are in `out/preflight/sources.sha256`.

- `NavierStokes/SolutionDifference.lean`: `slab`, `spatial_smooth`, `spatialDerivative_eq_within_comp` (line 149), `exists_gradient_bound` (164), `time_differentiable_at_interior` (260).
- `NavierStokes/PeriodicUniqueness.lean`: `isCompact_cubeImage`, `energy_continuousOn`, `energy_hasDerivAt`, `energy_initial_zero`, `dissipation_nonneg`; `classical_uniqueness_on_Icc` provides the existing coefficient/slice assembly pattern, but has equal forces and cannot itself prove this comparison.
- `NavierStokes/PeriodicIntegration.lean`: `integrable_cube`, `cubeIntegral_continuousOn_Icc` (259), differentiation under the cube integral (266–316).
- `Research/UnforcedRestart/energy-comparison/Main.lean`: `forced_energy_balance`, `forcing_work_le`, `forced_energy_rate_le`.
- `Research/UnforcedRestart/gronwall-threshold/Main.lean`: `weighted_budget`; its primitive hypotheses still need the FTC assembly above.
- `Research/UnforcedRestart/time-translation/Main.lean`: `shift_smooth_slab`, `candidate_shift_equation`, `candidate_shift_within_equation`.
- `.lake/packages/mathlib/Mathlib/MeasureTheory/Integral/IntervalIntegral/FundThmCalculus.lean`: `intervalIntegral.integral_hasDerivAt_right` (725), `integral_hasDerivWithinAt_right` (867).
- `.lake/packages/mathlib/Mathlib/MeasureTheory/Integral/DominatedConvergence.lean`: `continuousOn_primitive_interval` (468).
- `.lake/packages/mathlib/Mathlib/MeasureTheory/Integral/IntegrableOn.lean`: `ContinuousOn.stronglyMeasurableAtFilter` (852).

## Commands, outcomes, and audit manifest

Executed shell checks from the authorized worktree (redirections exclusively into owned `out/preflight/`):

```sh
mkdir -p Research/UnforcedRestart/Round2/PeriodicSlab/out/preflight
(cd /home/velvet/research-snapshots/unforced-round1-20260909T221339Z && sha256sum SHA256SUMS && sha256sum -c SHA256SUMS)
git diff --exit-code 597692fa5d55e07d810b2d96ead1a67972585425 --
git diff --cached --exit-code
sha256sum Research/UnforcedRestart/Round2/PeriodicSlab/DRAFT.md NavierStokes/PeriodicUniqueness.lean NavierStokes/SolutionDifference.lean NavierStokes/PeriodicIntegration.lean Research/UnforcedRestart/energy-comparison/Main.lean Research/UnforcedRestart/gronwall-threshold/Main.lean Research/UnforcedRestart/time-translation/Main.lean
```

Snapshot, baseline and index commands each exited **0**, with separate `.log`/`.exit` files. SHA-256 inventory command exited 0. A Python SHA-256 comparison of `m['accepted'] + [m['audit'],m['validation_script']]` against the frozen JSON manifest also exited 0; exact compared paths/digests are in `frozen-source-check.log`. The snapshot digest is the published `192e15dc0ff1cb79cae02a19941e0f816dc194e91123c205153ccf808322a488`.

Successful Lean commands: **none**. Failed Lean commands: **none**. Resource-limit probes/build commands: **none**. There was no timeout/OOM or compiler root error to diagnose. No old validator rerun occurred. File inspection used read/search tools, not a dependency build.

Accepted theorem manifest: **none**. Draft names `force_energy_continuousOn` and `slab_energy_derivative_le` in Markdown are expressly unaccepted and must not be enumerated as Lean exports. No Round2 axioms have been checked. The frozen report records allowed closures `{propext, Classical.choice, Quot.sound}` for relevant round-one exports; this worker verified source hashes, not a fresh semantic audit of those objects.

## Handoff / next authorized action

Integrator should allocate the focused compile slot after the relevant gate disposition, then the periodic-slab owner can move a completed draft into its owned Lean directory and elaborate under the prescribed 1 CPU / 6 GiB cgroup, unique module-relative outputs, strict flags and 10-minute timeout. Finish the FTC wrapper and final PDE theorem rather than accepting the derivative adapter alone. Audit every new export and helper; later clean-provenance must rebuild all imported non-core dependencies and research sources without object reuse.

The smallest remaining formal work is the continuous-on-interval FTC tuple and its final composition with the drafted PDE adapter. The extra arbitrary-datum closed-boundary Comparator adapter remains separate O1 work. Neither completion would settle comparator existence, strong-norm stability, actual smallness, growth transfer, or A/B.
