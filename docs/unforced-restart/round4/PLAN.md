# Round4 plan — same selected force, closed unit time interval

**Supervisor review for finalization:** see [SUPERVISOR-REF-ADDENDUM.md](SUPERVISOR-REF-ADDENDUM.md). The sole additional shared Git ref is the separately user-authorized documentation worktree branch, independently checked at its exact expected commit. Preserve historical strict-ref failure receipts; add explicit delta-aware preservation verification allowing only that exact addition, with all old refs/source/index checks unchanged. Do not delete the companion branch or introduce another approval gate.

## Fixed target and conventions

`d := UnforcedRestart.Round3.WitnessFeasibility.selected` throughout. No fresh choice, candidate-contract premise, or force cancellation assumption is admissible in the final theorem.

Exact acceptance statement (namespace openings as in the sources):

```lean
∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ i : Fin 3,
  (∫ y : PeriodicIntegration.Coords,
    WitnessFeasibility.selected.forcing
      (t, PeriodicIntegration.toSpace y) i
    ∂(MeasureTheory.volume.restrict (Set.Icc 0 1))) = 0
```

This is the genuine unit cell: `Coords = Fin 3 → ℝ` with product Lebesgue volume; `Space = EuclideanSpace ℝ (Fin 3)` with Euclidean Lebesgue volume. The explicit continuous linear equivalence is `PeriodicIntegration.toSpace := (EuclideanSpace.equiv (Fin 3) ℝ).symm`, coordinatewise identity. Do not silently identify the normed spaces or their measures. Whole-space compact integrals use `volume : Measure Space`. A measure-preserving transport theorem is required before replacing them by coordinate integrals.

Interior PDE/calculus domain: `0 < t < 1`, all spatial points, including the support boundary. Closed interior slabs justify time differentiation. Endpoint composition at both 0 and 1 uses continuity of the actual selected force integral, never velocity regularity at 1. No assertion beyond [0,1].

## Actual source map / producers

Frozen Round3 modules under `Research/UnforcedRestart/Round3/`:

* `WitnessFeasibility/Main.lean`: `selected`, `.candidate`, `.smooth`, `.schedule`; `potentialSum`, `directSum`, `pressureSum`, `velocity`, `pressure`. All witness obligations are supplied by `selected.candidate`, constructed through `ActualCandidateAssembly.selected_witness`.
* `WitnessFeasibility/Certificates.lean`: `selected_force_eq_residual` on (0,1), exact viscosity-one PDE residual of the selected activated periodic fields.
* `MeanTopology/Main.lean`: `compactVelocity`, `compactVelocity_zero_outside`, `compactVelocity_zero_germ`, `compactVelocity_agreement`, `compactVelocity_smooth_slice`, `compactVelocity_compact_support`, `compactVelocity_divergence_free`, `selected_compact_momentum_zero`, `selected_compact_transport_zero`, `selected_force_mean_continuousOn`.
* `SelectedBridge/Main.lean`: `compactVelocity_smoothAt`, `compactVelocity_contDiffOn_slab`, `compactVelocity_uniform_support`, `compact_component_integral_hasDerivAt`, `selected_compact_temporal_integral_zero`.
* `LocalizedForce/Main.lean`: strict-exterior cut residual and jets only; its unactivated residual must not be substituted for the activated residual on all (0,1).
* `CurlGeometry/Main.lean`: slice-chain-rule and terminal force jets; not a mean-zero producer.

Baseline producers:

* `MixedPeriodicAssembly.activated_periodicPressure_eventuallyEq_cut`: pressure germ of the selected activated compact pressure `activatedPressure (SpatialLocalization.cutPressure (pressureSum selected.schedule))`.
* `MixedPeriodicAssembly.cutPressure_zero_outside`, `SpatialLocalization.isCompact_supportCylinder`, `.isClosed_supportCylinder`, `.supportCylinder_coordinate_bound`: compact pressure support; joint smoothness is obtained by the selected periodic pressure germ on the cylinder and zero germ outside, using `smooth_at_interior selected.candidate.pressure_smooth`.
* `NavierStokesR3.CompactEnergy.integral_partial_eq_zero`, `.compact_partial`, `.compact_component`: derivative cancellation and derivative compactness. `SolutionDifference.spatial_partial_contDiff`, `.component_contDiff`, `.fderiv_component`: smoothness and component adapters.
* `ResidualRegularity.residual_eventuallyEq`: activated residual equality from velocity and pressure germs.
* `PeriodicLocalization.periodize`, `.translate`, `.lattice`, `.periodize_locally_eq_sum`: actual separated lattice construction. `MixedPeriodicAssembly.eq_representative`, `.representative_mem_innerCube` supply global spatial reduction.
* `PeriodicIntegration.toSpace`, `.cubeMeasure`, `.cubeIntegral`: exact cell convention. The exact baseline measure-preservation producer is `PiLp.volume_preserving_toLp (Fin 3)` in Mathlib's `MeasureTheory/Measure/Haar/InnerProductSpace.lean`; `MeasurePreserving.integral_comp` transports the whole-space integral through `toSpace.toHomeomorph.measurableEmbedding`. No selected compact-to-cell integral transport declaration was found in the accepted sources. The separate periodization integral adapter must be proved, not assumed.
* `PeriodicIntegration.cubeIntegral_continuousOn_Icc` and `selected.smooth`: endpoint composition producer once interior cancellation is proved.

## Nonoverlapping ownership and freeze

These are sequential workstreams in this session, not claimed parallel agents:

| Owner | Exclusive new source subtree | Exclusive report | Contract |
|---|---|---|---|
| PressureIntegral | `Research/UnforcedRestart/Round4/PressureIntegral/` | `PressureIntegral.md` here | Selected activated compact pressure: joint/slice smoothness, support, gradient component integrability and zero integral on (0,1). |
| LaplacianIntegral | `Research/UnforcedRestart/Round4/LaplacianIntegral/` | `LaplacianIntegral.md` here | Same `MeanTopology.compactVelocity`: second derivative support/smoothness, actual Laplacian component integrability and zero integral on (0,1). |
| PeriodizationTransport | `Research/UnforcedRestart/Round4/PeriodizationTransport/` | `PeriodizationTransport.md` here | Explicit coordinate measure transport, selected activated residual periodization/cell integral equality; no assumed cancellation. |
| Integration/planner | `Research/UnforcedRestart/Round4/Integration/` | PLAN, FINAL-REPORT, preservation/acceptance receipts | Residual splitting, selected force identity, endpoint closure, exact final theorem and audit. |

Workstreams import only earlier frozen sources, never concurrently moving sibling output. Integration may import outputs only after strict compilation and a source/object hash freeze receipt.

## Preservation / resources / acceptance

External current-state source snapshot: `/home/velvet/research-builds/unforced-round4-preserved-sf3yoys5/source`; manifest adjacent, SHA256 `d1087cfeda45b6cf8d62e5ad8e89e2230cbcd84038c6fabfcf831a27cdee026a`, 3,234 preexisting files inventoried. Snapshot copies are ordinary read-only files/directories; no WORM, sudo, or approval gate. Earlier snapshot `e970490cf8f0cfb41fca101c62702fab7347c17c` covers rounds1/2, NOT Round3.

All preexisting files, original checkout/published proof, baseline Lean/config, historical receipts and manifests are read-only. Only the two Round4 subtrees may be created in this worktree. No commit/push/merge. Reuse `/home/velvet/research-builds/unforced-round2-clean-20260909T221339Z` read-only; no full build, Lake/cache invocation, or dependency rebuild. Frozen earlier research objects are hash-verified against the six-module fresh replay and aggregate receipts. Their read-only re-verifications passed; logs are in new Integration/.

Focused Lean compilations: unique output directory per attempt, one compiler thread, CPU quota 100%, memory cap 6 GiB/no swap, 600-second timeout; `-DautoImplicit=false -DwarningAsError=true`. No sorry/admit/axiom/unsafe, weakened checks or mathematical axiom additions. Print export axiom closures and require only propext/Classical.choice/Quot.sound. Final acceptance additionally requires the exact statement above, no extra hypotheses, all producer obligations discharged, source/object hashes, and unchanged preservation inventory/HEAD/refs/index. A failure of any mathematical link is explicitly a partial failure, not acceptance of the goal.
