# Human lemmas → source interfaces

Baseline: `597692fa5d55e07d810b2d96ead1a67972585425`. All 30 authored human IDs are indexed below. This is a **many-to-many interface map**, not a claim that one declaration proves a whole chapter section. The linked human sections retain additional helper citations, derivations, exact typed records, and obligation IDs.

**Coverage limit and verdict:** “all 30” means only the authored NSC/NSA/EUL IDs, not all source hypotheses or independently indexed scope/interface assertions. The validator recognizes those three prefixes only. No stable SCOPE IDs have been authored; INT-001 and NSA-005's requested scope-ID handoff remain open. Supplemental interface links do not expand the semantic coverage. The supplied second agent reviews support selected conditional calculations, not textbook completeness or a complete source audit. Native NS construction, same-child Euler correction, force extension, pressure recovery and broad-class conversion remain blockers; see [VALIDATION.md](VALIDATION.md).

Each entry specifies the hypothesis boundary: a bundled record means **all its fields**, together with enclosing section parameters and typeclass assumptions, not merely the informal selection listed here. Open independent source review must expand those records and check actual instantiations. Names below are author citations; integration adds lexical checks, not elaborated `#check` results. File links plus fully qualified names are the source anchors (no invented GitHub declaration fragments). Generated record projections are distinguished where needed.

<a id="native-control-supplement"></a>
## Supplemental native-control route (separate baseline and coverage)

[Chapter 05](05-native-weighted-control.md) and its [claim/source/obligation ledger](native-control-validation.md) use baseline `26e896edbdbe1215c0d50ddba24b2b6453646f5f`. Its eight explicit `native-control-*` anchors are distinct from the historical 30 NSC/NSA/EUL IDs. The existing validator checks their links, not semantic claim coverage. No historical obligation is silently closed.

- [BasePhaseGeometry.lean](../../NavierStokes/BasePhaseGeometry.lean) — `NavierStokes.BasePhaseGeometry.FamilyData.phase_estimates`; `NavierStokes.BasePhaseGeometry.FamilyData.modal_errors`; `NavierStokes.BasePhaseGeometry.FamilyData.damping_error`; `NavierStokes.BasePhaseGeometry.FamilyData.construction`.
  Boundary: prepared normalized base/cone/representative data; chapter 05 expands the order-zero producer, not summed-profile existence or all-order base jets.
- [ActualParticularControl.lean](../../NavierStokes/ActualParticularControl.lean) — `NavierStokes.ActualParticularControl.scaled_selected_copy_energy`; `NavierStokes.ActualParticularControl.source_path_bounds`; `NavierStokes.ActualParticularControl.frame_input_jets`.
  Boundary: actual selected geometry, transported slot separation, incoming all-jet residual invariant and primitive frame jets; no assumed projected forcing bound.
- [ParticularWaveBounds.lean](../../NavierStokes/ParticularWaveBounds.lean) — `NavierStokes.ParticularWaveBounds.forced_joint_jet_bound`; `NavierStokes.ParticularWaveBounds.copySolve_jet_bound_from_modal`; `NavierStokes.ParticularWaveBounds.pressure_class`.
  Boundary: energy and input jets on the whole closed path with open-neighborhood smoothness. Numerical modal/ambient bounds are reconstructed; pressure remains class-level with named inverse-normal/frequency inputs.
- [ActualParticularStageControls.lean](../../NavierStokes/ActualParticularStageControls.lean) — `NavierStokes.ActualParticularStageControls.selected_tangent_eq`; `NavierStokes.ActualParticularStageControls.selectedActualControl`; `NavierStokes.ActualParticularStageControls.selected_raw_jets`.
  Boundary: the same initializer, arbitrary active selector and copy, nonzero harmonic, current residual and incoming frequency coherence; not an independently chosen frame or solved-wave premise.

<a id="primitive-derivative-supplement"></a>
## Supplemental primitive-derivative route

[Chapter 06](06-primitive-derivative-bounds.md) supplies relative numerical base/frame/pressure producers for the same selected construction at baseline `26e896e…`. Its [separate claim and exact-file source ledger](primitive-derivative-validation.md) audits ten `primitive-*` claims without adding historical IDs or source-map lexical targets. Finite-profile certificates, incoming residual production and localization remain explicit inputs/debt; chapter 05 and its historical ledger/plan are unchanged.

<a id="delivered-statements"></a>
## Delivered statements and class hypotheses

- [ComparatorSolution.lean](../../NavierStokes/ComparatorSolution.lean) — `NavierStokes.Comparator.navier_stokes_breakdown_R3`; `NavierStokes.Comparator.navier_stokes_breakdown_periodic`.
  Inputs: real `nu`, proof `nu > 0`. Outputs: existential datum and force with the corresponding decay/periodic predicates, and negated existence of velocity/pressure in the corresponding global class. No candidate premise in these public signatures.
- [ComparatorDefinitions.lean](../../NavierStokes/ComparatorDefinitions.lean) — `NavierStokes.Comparator.InitialVelocityConditionDecay`; `NavierStokes.Comparator.InitialVelocityConditionPeriodic`; `NavierStokes.Comparator.ForceConditionDecay`; `NavierStokes.Comparator.ForceConditionPeriodic`; `NavierStokes.Comparator.NavierStokesExistenceAndSmoothness`; `NavierStokes.Comparator.NavierStokesExistenceAndSmoothnessRn`; `NavierStokes.Comparator.NavierStokesExistenceAndSmoothnessPeriodic`.
  Hypotheses: smooth divergence-free datum; all-order polynomial decay or periodicity; joint future smoothness and all-order force decay; equation with right-sided derivative at zero, initial trace, joint future smooth velocity and pressure. Rn additionally requires timewise `MemLp` and a single strict upper energy bound for all t≥0. Periodic requires both scalar pressure and velocity periodic, not an energy field. See the [scope summary](README.md#scope) for the exact decay quantifier patterns.
- [ComparatorR3Theorem.lean](../../NavierStokes/ComparatorR3Theorem.lean) — `NavierStokes.ComparatorBridge.option_C_of_candidate`.
- [ComparatorTheorem.lean](../../NavierStokes/ComparatorTheorem.lean) — `NavierStokes.ComparatorBridge.option_D_of_candidate`.
  Adapter boundary: a compact R3 candidate / periodic candidate, respectively, and positive viscosity; their proof bodies choose zero datum and a rescaled force. These adapters alone do not construct the candidate.
- [Solution.lean](../../Euler/Solution.lean) — `Euler.euler_breakdown_R3`; `Euler.exists_compact_smooth_euler_singularity`.
  No external packet premise. The latter existentially chooses datum, terminal time, velocity and scalar pressure, with compact nonzero datum, positive time ≤1, half-open Sobolev solution, uniform presingular energy, closed-interval existence iff T<T_*, local finite C1/integral bounds, infinite terminal C1 limsup/integral, and broad global exclusion.
- [SolutionDefinitions.lean](../../Euler/SolutionDefinitions.lean) — `Euler.InitialVelocityConditionDecay`; `Euler.EulerExistenceAndSmoothnessR3`; `Euler.SobolevSmoothOn`; `Euler.EulerSobolevExistenceAndSmoothnessR3On`; `Euler.velocityC1Norm`; `Euler.vorticityNorm`.
  Global class: jointly future-smooth velocity/pressure, unforced equation including right-sided zero-time law, divergence, trace, timewise L² and one global energy bound. Lifespan class: all spatial L² jets of velocity and a strong derivative witness continuous on the specified time set; scalar pressure differentiable and time/PDE laws only at interior times. It is not defined as the global class restricted to a time set. Supremum/integral quantities are extended nonnegative ones.

## Navier–Stokes construction

### [NSC-001](02-ns-construction.md#nsc-001) — positive coordinate

- [SimilarityCoordinates.lean](../../NavierStokes/SimilarityCoordinates.lean) — `NavierStokes.SimilarityCoordinates.coordinateQ_spec`; `NavierStokes.SimilarityCoordinates.positive_solution_unique`.
- [PhysicalWaveSum.lean](../../NavierStokes/PhysicalWaveSum.lean) — `NavierStokes.PhysicalWaveSum.physicalQ`.

Boundary: 0<h<1/2, t<1 and real axial coordinate; the positive branch of q−z²q^(2h)=1−t. The root/implicit-function/terminal-limit explanation is a prose deduction from this scalar equation, not an all-order coordinate estimate. Independent calculation review pending.

### [NSC-002](02-ns-construction.md#nsc-002) — profile and Borel base

- [PreparedOutgoing.lean](../../NavierStokes/PreparedOutgoing.lean) — `NavierStokes.PreparedOutgoing.exists_prepared`.
- [NominalConeAssembly.lean](../../NavierStokes/NominalConeAssembly.lean) — `NavierStokes.NominalConeAssembly.exists_nominal_cone`; `NavierStokes.NominalConeAssembly.assembly_exists`.
- [FinalSlowBase.lean](../../NavierStokes/FinalSlowBase.lean) — `NavierStokes.FinalSlowBase.profileData_nonempty`; `NavierStokes.FinalSlowBase.residual_identity`; `NavierStokes.FinalSlowBase.error_jetRate`; `NavierStokes.FinalSlowBase.weighted_jets`.
- [SlowBorelBase.lean](../../NavierStokes/SlowBorelBase.lean) — `NavierStokes.SlowBorelBase.coefficientBundle`; `NavierStokes.SlowBorelBase.slowSum`.

Boundary: prepared/nominal/profile existence endpoints do not assume their desired profiles; `assembly_exists` does assume `PreparedProfile d`. U2 fixes outgoing F, nominal W, certificate H, loop/modulation v, upper, integer budget B, filter l, and `PhysicalApproach` with radius≤`boxRadius W upper`; rates quantify over m and real N≥0. Leading lower/jet bounds need `FullTrueCone v`; `weighted_jets` for the correction does not. Radial support is asserted on the closed η-strip, not outside it. Profile and blown jets are not physical spacetime jets. Supplemental definitions and unresolved interface expansions are mapped in [INTERFACES.md](INTERFACES.md); internal class translation is in [01-scope.md](01-scope.md). Bundle formulas and curl reconstruction are expanded algebra; profile, cone and all-order error are unexpanded OBL-NSC-001–002.

### [NSC-003](02-ns-construction.md#nsc-003) — axis and anchored gauge

- [BaseResidual.lean](../../NavierStokes/BaseResidual.lean) — `NavierStokes.BaseResidual.baseVelocity_at_origin`.
- [FinalSlowBase.lean](../../NavierStokes/FinalSlowBase.lean) — `NavierStokes.FinalSlowBase.leading_origin`; `NavierStokes.FinalSlowBase.axis_tendsto`.
- [TailGaugePotential.lean](../../NavierStokes/TailGaugePotential.lean) — `NavierStokes.TailGaugePotential.finalPotential_sameCurl`; `NavierStokes.TailGaugePotential.finalPotential_awayExtensions`.

Boundary: smooth coefficients, strictly increasing slow schedule, positive leading axial coefficient and vanishing positive-order axial coefficients; actual F,W,H,v,upper,B for the instantiated gauge. The anchor is physical s=1. Curl invariance does not imply invariance after cutoff. Exterior neighborhoods and heat-primitive analysis remain OBL-NSC-003; axis/gauge algebra is expanded.

### [NSC-004](02-ns-construction.md#nsc-004) — weighted classes and ledger

- [WeightedClasses.lean](../../NavierStokes/WeightedClasses.lean) — `NavierStokes.WeightedClasses.StripData`; `NavierStokes.WeightedClasses.MemClass`; `NavierStokes.WeightedClasses.MeanClass`; `NavierStokes.WeightedClasses.WaveClass`.
- [ActualIterationLedger.lean](../../NavierStokes/ActualIterationLedger.lean) — `NavierStokes.ActualIterationLedger.sigma_formula`; `NavierStokes.ActualIterationLedger.inputSigma_formula`; `NavierStokes.ActualIterationLedger.gain_tendsto_atTop`.

Boundary: open strip, positive band scales≤1, slow/edge weights and derivative quantifiers as in (11); fix h>0 before the gain limit. Class definitions and arithmetic are not construction theorems. Actual initialization inherits OBL-NSC-001–002.

### [NSC-005](02-ns-construction.md#nsc-005) — one cycle

- [CorrectionAnalyticStep.lean](../../NavierStokes/CorrectionAnalyticStep.lean) — `NavierStokes.CorrectionAnalyticStep.StaticData`; `NavierStokes.CorrectionAnalyticStep.StepData`; `NavierStokes.CorrectionAnalyticStep.StepResult`; `NavierStokes.CorrectionAnalyticStep.step`.
- [CycleConstruction.lean](../../NavierStokes/CorrectionStep/CycleConstruction.lean) — `NavierStokes.CorrectionStep.CycleParameters.next_alias_error`; `NavierStokes.CorrectionStep.CycleParameters.next_preserve_masses`.
- [SignedStressPrimitive.lean](../../NavierStokes/SignedStressPrimitive.lean) — `NavierStokes.SignedStressPrimitive.physical_angular_divergence`; `NavierStokes.SignedStressPrimitive.physical_axial_divergence`.
- [SignedCovariance.lean](../../NavierStokes/SignedCovariance.lean) — `NavierStokes.SignedCovariance.cross_reconstruct`.

Boundary: all fixed geometry/index/label/rank/context parameters, `StaticData`, `CycleAnalyticInvariant` at σ≥1/5, κ≤1/100000, and the complete `StepData` of U4 (native classes, representations, supports, bounds, common primary and signed assembly, tail matching). Output accuracy σ+1/10. Global primitive statements use a smooth everywhere-positive scale and smooth supported inputs; actual local q requires local-domain instantiation. Residual/covariance/moment algebra is expanded; native estimates and mean-gain closure remain OBL-NSC-004. NSC-006 supplies an independent abstract calculation, not a circular cycle conclusion.

### [NSC-006](02-ns-construction.md#nsc-006) — finite-band defect

- [FiniteHeadClass.lean](../../NavierStokes/FiniteHeadClass.lean) — `NavierStokes.FiniteHeadClass.meanClass_all_exponents`.
- [SignedCrossDefectClass.lean](../../NavierStokes/SignedCrossDefectClass.lean) — `NavierStokes.SignedCrossDefectClass.residual_defects_mem`; `NavierStokes.SignedCrossDefectClass.residual_defects_all_exponents_of_primitive`.

Boundary: already weighted baseline class for the literal defect, zero defect on the open strip for all n≥a fixed tail threshold, positive finitely many earlier scales. Finite rescaling changes the exponent but retains edge weight; constants may depend on target exponent/threshold. Worked conditional deduction, with actual baseline and matching still OBL-NSC-004; not exact early-band matching.

### [NSC-007](02-ns-construction.md#nsc-007) — coherent physical run

- [ActualCyclePreservation.lean](../../NavierStokes/ActualCyclePreservation.lean) — `NavierStokes.ActualCyclePreservation.state_runInvariant`; `NavierStokes.ActualCyclePreservation.state_coherent`.
- [ActualCandidateAssembly.lean](../../NavierStokes/ActualCandidateAssembly.lean) — `NavierStokes.ActualCandidateAssembly.stageRealizations`; `NavierStokes.ActualCandidateAssembly.physicalData`.
- [ActualCycleResidualBounds.lean](../../NavierStokes/ActualCycleResidualBounds.lean) — `NavierStokes.ActualCycleResidualBounds.PhysicalData`.

Boundary: fixed budget B, N0≥geometric threshold and any J; literal iterates and prefixes including index zero, the gauged base and initialized direct field. Realizations are chart germs on valid bands and include differentiability/exterior identities. OBL-NSC-005 is the missing physical transport/overlap/initialization derivation, not a premise freely added to the public producers.

### [NSC-008](02-ns-construction.md#nsc-008) — physical rates

- [ActualCandidateAssembly.lean](../../NavierStokes/ActualCandidateAssembly.lean) — `NavierStokes.ActualCandidateAssembly.estimates`.
- [MixedCandidateAssembly.lean](../../NavierStokes/MixedCandidateAssembly.lean) — `NavierStokes.MixedCandidateAssembly.StageEstimates`.
- [ActualCycleResidualBounds.lean](../../NavierStokes/ActualCycleResidualBounds.lean) — `NavierStokes.ActualCycleResidualBounds.finite_residual_rates`; `NavierStokes.ActualCycleResidualBounds.fixedLoss`.

Boundary: same B,N0 and threshold proof; raw bounds for j≥1 only, constants depending on j,m but loss functions fixed before j,J. Residual producer uses fixed N≥4 and geometric threshold, parameters, invariant for every literal iterate from `initialCycleState`, and `PhysicalData` for those fields. Coordinate-transfer arithmetic is expanded; all-order gluing/loss bounds remain OBL-NSC-006.

### [NSC-009](02-ns-construction.md#nsc-009) — one diagonal

- [CutStageEstimates.lean](../../NavierStokes/CutStageEstimates.lean) — `NavierStokes.CutStageEstimates.cut_product_bound`; `NavierStokes.CutStageEstimates.cutLoss`.
- [MixedCandidateAssembly.lean](../../NavierStokes/MixedCandidateAssembly.lean) — `NavierStokes.MixedCandidateAssembly.StageEstimates.exists_schedule`.
- [ActualCandidateAssembly.lean](../../NavierStokes/ActualCandidateAssembly.lean) — `NavierStokes.ActualCandidateAssembly.selected_witness`.
- [GermCandidateAssembly.lean](../../NavierStokes/GermCandidateAssembly.lean) — `NavierStokes.GermCandidateAssembly.origin_eventually_base`.

Boundary: `StageEstimates`, 0<h<1/2, q_big>0 and arbitrary lower bound for a₀; one schedule for potentials, direct fields and pressures. Raw positive gains pay cutoff/log constants; stage zero is exempt. Finite-prefix plateau is a germ statement. Origin transfer additionally uses actual profile/modulation, initialization and positive-stage axis-zero germs and local angular data. Cutoff/head calculations are expanded; all construction obligations propagate to NSA-001–005.

## Navier–Stokes analysis

### [NSA-001](03-ns-analysis.md#nsa-001) — schedule

- [CutStageEstimates.lean](../../NavierStokes/CutStageEstimates.lean) — `NavierStokes.CutStageEstimates.RawStageBounds`; `NavierStokes.CutStageEstimates.physicalQ_jet_bound`; `NavierStokes.CutStageEstimates.cut_product_bound_of_threshold`.
- [MixedCandidateAssembly.lean](../../NavierStokes/MixedCandidateAssembly.lean) — `NavierStokes.MixedCandidateAssembly.StageEstimates.exists_schedule`.

Boundary: NSC-008–009, one fixed h and run; positive-stage log bounds, monotone unbounded gains, physical q derivative bounds and strict raw-domain gap. Schedule controls finitely many orders m≤j+2 per stage; γ_j=g_j/2. Worked conditional selection; OBL-NSA-001 imports OBL-NSC-001–006.

### [NSA-002](03-ns-analysis.md#nsa-002) — prefix plateau and tails

- [DiagonalJetBounds.lean](../../NavierStokes/DiagonalJetBounds.lean) — `NavierStokes.DiagonalJetBounds.partialPotential_eventuallyEq_uncut`; `NavierStokes.DiagonalJetBounds.potential_tail_jet_bound`.
- [MixedDiagonalResidual.lean](../../NavierStokes/MixedDiagonalResidual.lean) — `NavierStokes.MixedDiagonalResidual.velocity_tail_jetRate`; `NavierStokes.MixedDiagonalResidual.velocityLoss`.

Boundary: cut-stage bounds, fixed finite J including zero, open common cutoff plateau, monotone post-cutoff gain, q≤1. Tail m≤J+3; curl costs one derivative. Expanded geometric-series/head argument; actual same-field identification remains open.

### [NSA-003](03-ns-analysis.md#nsa-003) — residual flatness

- [DiagonalResidual.lean](../../NavierStokes/DiagonalResidual.lean) — `NavierStokes.DiagonalResidual.residualDifference_jetRate`; `NavierStokes.DiagonalResidual.residual_jetRate_of_stages`.
- [MixedDiagonalResidual.lean](../../NavierStokes/MixedDiagonalResidual.lean) — `NavierStokes.MixedDiagonalResidual.physical_vanishingJointJets`.

Boundary: smooth fields on common open presingular domain; background rates through m+1, velocity tail through m+2, pressure tail through m+1, residual rate for the **same** prefix, losses independent of J, divergent gain and q→0. Output ∀m,N≥0 ∃J,C,U with residual derivative≤Cq^N, not one J for all orders and not zero residual. Expanded six-term estimate; OBL-NSA-001/006 and construction obligations remain.

### [NSA-004](03-ns-analysis.md#nsa-004) — endpoint jets and force extension

- [MixedDiagonalExtensions.lean](../../NavierStokes/MixedDiagonalExtensions.lean) — `NavierStokes.MixedDiagonalExtensions.diagonal_awayExtensions_local`.
- [TailGaugePotential.lean](../../NavierStokes/TailGaugePotential.lean) — `NavierStokes.TailGaugePotential.finalPotential_awayExtensions`.
- [JointResidualLimits.lean](../../NavierStokes/JointResidualLimits.lean) — `NavierStokes.JointResidualLimits.boundaryLimits_joint`; `NavierStokes.JointResidualLimits.locallyUniform_of_joint_limits`.
- [CandidateFromLimits.lean](../../NavierStokes/CandidateFromLimits.lean) — `NavierStokes.CandidateFromLimits.tracedResidual_smooth`; `NavierStokes.CandidateFromLimits.force_smooth`; `NavierStokes.CandidateFromLimits.force_boundary_jets`; `NavierStokes.CandidateFromLimits.force_zero_outside`.

Boundary: genuine local off-plane models on q<q_big, one shrinking support constant for all positive stages, actual anchored zeroth model, strict cutoff gap; joint zero residual jets at origin and actual away extensions. Extension consumes limits of actual derivatives, not arbitrary tensors. Common spatial zero regions are preserved. Only force extends. Compatibility explanation is expanded; anchored/raw models (OBL-NSA-002, overlapping NSC-003) and Taylor–Borel locality/convergence (OBL-NSA-003) remain unexpanded.

### [NSA-005](03-ns-analysis.md#nsa-005) — localization, activation, periodization

- [LocalAngularDiagonal.lean](../../NavierStokes/LocalAngularDiagonal.lean) — `NavierStokes.LocalAngularDiagonal.spatialCut_angularSum_divergence`.
- [MixedPeriodicAssembly.lean](../../NavierStokes/MixedPeriodicAssembly.lean) — `NavierStokes.MixedPeriodicAssembly.exists_compact_candidate`; `NavierStokes.MixedPeriodicAssembly.periodized_navier_stokes`; `NavierStokes.MixedPeriodicAssembly.candidate_of_periodization`.
- [GermCandidateAssembly.lean](../../NavierStokes/GermCandidateAssembly.lean) — `NavierStokes.GermCandidateAssembly.origin_eventually_base`.

Boundary: same gauged diagonal and axis-zero germs from NSC-003/007–009, local angular geometry with positive inner support radius, axisymmetric cutoff plateau, actual residual extensions. Activate to zero datum; compact support lies in separated quarter-cubes before periodization. Both pressure and velocity periodize. Curl/product/nonlinear locality calculations are expanded; existence inherits NSC obligations and OBL-NSA-001–003. No independent new schedule is selected.

### [NSA-006](03-ns-analysis.md#nsa-006) — energy deduction, **not packaged**

- [R3CompactCandidate.lean](../../NavierStokes/R3CompactCandidate.lean) — `NavierStokes.R3CompactCandidate.Properties`; `NavierStokes.R3CompactCandidate.of_limits`.

These are candidate **inputs**, not a located theorem of inequality (22). Prose proof assumes ν>0, T_*>0, closed-slab smoothness for every T<T_*, common compact velocity support, div u=0, interior equation, zero datum, and force smooth through T_* with common compact support. Integration by parts plus sqrt(Y+ε²) gives ∥u(T)∥₂≤∫₀ᵀ∥f∥₂ and energy/dissipation≤half the square of that integral. No terminal velocity or strong L² endpoint convergence follows. OBL-NSA-006 review and inherited candidate obligations remain.

### [NSA-007](03-ns-analysis.md#nsa-007) — uniqueness and pressure

- [PeriodicUniqueness.lean](../../NavierStokes/PeriodicUniqueness.lean) — `NavierStokes.PeriodicUniqueness.classical_uniqueness_on_Icc`.
- [WholeSpaceUniqueness.lean](../../NavierStokes/R3/WholeSpaceUniqueness.lean) — `NavierStokesR3.WholeSpaceUniqueness.classical_uniqueness_on_Icc`.
- [PressureRecovery.lean](../../NavierStokes/R3/PressureRecovery.lean) — `NavierStokesR3.PressureRecovery.Hypotheses`; `NavierStokesR3.PressureRecovery.gradient_recovery`.
- [PressureFlux.lean](../../NavierStokes/R3/PressureFlux.lean) — `NavierStokesR3.PressureFlux.exists_uniform_actual_pressure_flux_bound`.
- [ComparisonRateBound.lean](../../NavierStokes/R3/ComparisonRateBound.lean) — `NavierStokesR3.ComparisonRateBound.exists_uniform_flux_absorption`.

Boundary: viscosity one, T>0, smooth velocities and scalar pressures on [0,T], common initial velocity and interior residual, both divergence-free. Periodic: both velocities/pressures periodic. R3: reference compact support uniform on the slab, competitor timewise L² and slab-uniform energy. Pressure recovery uses **both** slab energy bounds (compact smooth reference supplies its own); flux bound also uses uniform reference L³ and tensor L¹ bounds. No pressure decay assumption. Expanded Young absorption does not prove the harmonic/Riesz/commutator inputs: OBL-NSA-004 remains.

### [NSA-008](03-ns-analysis.md#nsa-008) — local-through-terminal nonextension, **repackaging**

- [R3CompactCandidate.lean](../../NavierStokes/R3CompactCandidate.lean) — `NavierStokes.R3CompactCandidate.Properties.not_global_agreement`.

Literal endpoint excludes agreement with a globally future-smooth competitor. The stronger local-through-one formulation is a prose deduction from NSA-007 and compact continuity, not attributed to that literal signature: competitor smooth through one, matching data/force, divergence, and periodic pressure/velocity or L²/slab energy on **each** T<1. Energy constants may depend on T. Candidate origin divergence suffices; no uniform energy near one required. Inherits candidate, pressure and class-bridge obligations; NSA-006 is not necessary for the compact-reference slab bounds.

### [NSA-009](03-ns-analysis.md#nsa-009) — fixed viscosity

- [ComparatorBridge.lean](../../NavierStokes/ComparatorBridge.lean) — `NavierStokes.ComparatorBridge.rescale`; `NavierStokes.ComparatorBridge.rescaledForce`; `NavierStokes.ComparatorBridge.normalized_solution_core`; `NavierStokes.ComparatorBridge.normalized_solution`.

Boundary: fixed ν>0 and original/competitor solution properties for inverse scaling. u_ν=νu(νt), p_ν=ν²p(νt), f_ν=ν²f(νt); core handles equation/smoothness, periodic add-on handles periods; R3 energy adaptation is separate in `option_C_of_candidate`. Expanded chain-rule calculation, constants depend on ν; not an inviscid limit or uniform small-force statement. OBL-NSA-005 still needs full prose-class audit.

### [NSA-010](03-ns-analysis.md#nsa-010) — force removal, **no packaged premise**

No source theorem cited here supplies a force-free terminal interval. The flat nonzero scalar example and quantifier distinction are prose arguments. Conditional restart uses NSA-006–008 **plus** f=0, or f=∇φ in the admissible pressure class, on some [t₀,1); periodic φ must preserve periodic pressure. Shifted data admissibility/comparison must also hold. OBL-NSA-007 is new research for this proposal, not a dependency of forced NS exclusion.

## Euler (independent branch)

### [EUL-001](04-euler.md#eul-001) — two delivered classes

- [Solution.lean](../../Euler/Solution.lean) — `Euler.euler_breakdown_R3`; `Euler.exists_compact_smooth_euler_singularity`.
- [InitialDataBridge.lean](../../Euler/InitialDataBridge.lean) — `Euler.initialVelocityConditionDecay_of_compact`.

Exact classes/signatures are indexed above. Decay adapter assumes smooth compact datum and divergence freedom. Compact-support-to-decay is a displayed prose deduction as well. All construction obligations apply to a human derivation of the existential conclusion; OBL-EUL-006 covers class identification. The private `initialDatum_no_global_solution` in Solution is not a public citation target.

### [EUL-002](04-euler.md#eul-002) — common numerical hierarchy

- [PacketInductionScales.lean](../../Euler/PacketInductionScales.lean) — `EulerPacketInductionScales.Scales`; `EulerPacketInductionScales.exists_scales`.
- [PacketSourceScaleSequence.lean](../../Euler/PacketSourceScaleSequence.lean) — `EulerPacketSourceScaleSequence.timeWidth`; `EulerPacketSourceScaleSequence.previousShear`; `EulerPacketSourceScaleSequence.previousFrequency`.

Boundary: c≥0 and real floor B; choice returns one full `Scales c B` satisfying actual bounds, first-scale and universal frequency guards, summability/renewal budgets. Fixed D,J,X precede n; exceptional base shear/frequency and horizon t_n+2w_n retained. Growth explanation does not check all guards: OBL-EUL-001.

### [EUL-003](04-euler.md#eul-003) — ray and scalar growth

- [ParentEulerState.lean](../../Euler/ParentEulerState.lean) — `EulerParentPacketFrames.Evolution.strain_eq`; `EulerParentPacketFrames.Evolution.curvature_eq`.
- [PacketGrowth.lean](../../Euler/EulerProof/PacketGrowth.lean) — `EulerPacketGrowth.cosh_lower_of_flux_system`; `EulerPacketGrowth.equation30_endpoint_exponential`.

Boundary: actual parent Euler state for physical strain/Hessian identification. Scalar comparison separately assumes 0≤β≤1/2, T≥0, βT²≤1, differentiable V,V₁ and flux F=(1+β²s⁴)V₁, F'=2(1−β²s²)V, V(0)=1,V₁(0)≥0. Endpoint exponential uses 0<β≤1/16 and T=1/sqrt β. Polarization and scalar calculation are expanded; identifying the normalized perturbed ray and physical amplification remains OBL-EUL-002.

### [EUL-004](04-euler.md#eul-004) — exact successor and correction

- [PacketForwardSuccessor.lean](../../Euler/PacketForwardSuccessor.lean) — `EulerPacketInduction.Stage.forwardNext`.
- [PacketJoinedSuccessor.lean](../../Euler/PacketJoinedSuccessor.lean) — `EulerPacketInduction.Stage.joinedNext`; `EulerPacketInduction.Stage.joinedNext_initial_velocity`.
- [ParentGeometryJoinedChoice.lean](../../Euler/ParentGeometryJoinedChoice.lean) — `EulerParentPacketFrames.exists_geometryJoinedChoice`.
- [AllOrderDriftBudget.lean](../../Euler/AllOrderDriftBudget.lean) — `EulerAllOrderDriftCorrection.Budget`.
- [AllOrderDriftCorrection.lean](../../Euler/AllOrderDriftCorrection.lean) — `EulerAllOrderDriftCorrection.Budget.solution_value_common`; `EulerAllOrderDriftCorrection.Budget.fieldTower_energy`; `EulerAllOrderDriftCorrection.Budget.fieldTower_hasDerivAt_pressure`.

Boundary: construction exponent≥required exponent, floor≥common threshold at fixed gradient/Hessian constants, one `Scales`, full `Stage S n`; joined branch n≠0. Geometry choice needs actual smooth parent/input, terminal geometry equality, frequency guard, label bound≤k and parent inverse scale≤k^(3/4). Correction uses one coherent approximation, inverse metric/time derivative and radius path satisfying the **all-order** Budget inequalities displayed in EUL-004 for every order≥6. Weighted Gevrey energy is not H_m. Residual cancellation is expanded algebra, not a solver proof. OBL-EUL-001–003 remain.

### [EUL-005](04-euler.md#eul-005) — sampled gradient growth

- [PacketStageGrowth.lean](../../Euler/PacketStageGrowth.lean) — `EulerPacketInduction.GrowthData.gradient_lower`; `EulerPacketInduction.GrowthData.gradient_atTop`.
- [PacketInfiniteConstruction.lean](../../Euler/PacketInfiniteConstruction.lean) — `EulerPacketInduction.stages`; `EulerPacketInduction.packets`.

Boundary: full `GrowthData` for each exact stage, odd symmetry, activation frame rank-one shear a_n, remainder≤a_n/2 for n≠0 and selected a_n≥n+1. Rank-one triangle inequality is expanded. Producing infinitely many renewable stages needs full `Stage`, not only the minimal growth record; inherits OBL-EUL-001–003.

### [EUL-006](04-euler.md#eul-006) — common compact initial limit

- [PacketInitialScaleSummability.lean](../../Euler/PacketInitialScaleSummability.lean) — `EulerPacketInitialScale.high_summable`; `EulerPacketInitialScale.mean_summable`.
- [PacketGeometryInitialAmplitude.lean](../../Euler/PacketGeometryInitialAmplitude.lean) — `EulerPacketSourceGeometry.Guards.primaryAmplitude_polynomial`.
- [PacketStageInitialLimit.lean](../../Euler/PacketStageInitialLimit.lean) — `EulerPacketInduction.Stage.initialDataLimit_Hm`.
- [PacketInitialSmoothLimit.lean](../../Euler/PacketInitialSmoothLimit.lean) — `EulerPacketInitial.actual_increment_summable`; `EulerPacketInitial.initialLimit_support`.

Boundary: fixed derivative order m, actual high/mean physical majorants with stage-independent polynomial constants, inverse amplification exp(−x_n/8) and mean frequency factor k_n^(−2); joined-history guard and amplitude hypotheses stated in EUL-006. Shift J→J+1,X→x₁ only for the joined tail; retain u₁(0) as base. Actual increment identity and common support are needed for the common smooth solenoidal limit. Elementary summability is expanded, majorants/representative/support still OBL-EUL-002–004.

### [EUL-007](04-euler.md#eul-007) — H4-dependent comparison

- [OrdinaryH3Envelope.lean](../../Euler/OrdinaryH3Envelope.lean) — `EulerOrdinarySobolev.Evolution.h3_stability`.
- [OrdinaryEulerStability.lean](../../Euler/OrdinaryEulerStability.lean) — `EulerOrdinarySobolev.Evolution.referenceNormPath`; `EulerOrdinarySobolev.Evolution.referenceSize`.
- [OrdinaryEulerVaryingHorizon.lean](../../Euler/OrdinaryEulerVaryingHorizon.lean) — `EulerOrdinarySobolev.Evolution.eventually_h3_bound_varying`; `EulerOrdinarySobolev.Evolution.no_gradient_escape_of_initial_tendsto_varying`.
- [PacketStageContradiction.lean](../../Euler/PacketStageContradiction.lean) — `EulerPacketInduction.GrowthData.no_evolution_of_eventually_covering`.

Boundary: one ordinary reference on [0,T], ordinary exact stages on nonnegative horizons eventually≤T, initial H3 convergence, sampled times in stage horizons. Finite reference H4 control fixes the comparison constant; no uniform stage H4 bound. Envelope uses positive ε and eventual smallness; retain original reference bound when restricting. Regularization/bootstrap/embedding contradiction expanded; product/pressure energy inputs remain OBL-EUL-005 and packet application inherits construction obligations.

### [EUL-008](04-euler.md#eul-008) — maximal lifespan

- [PacketFiniteLifespan.lean](../../Euler/PacketFiniteLifespan.lean) — `EulerPacketInduction.initialDatum_local`; `EulerPacketInduction.initialDatum_no_packet_horizon`; `EulerPacketInduction.initialDatum_finite_lifespan`; `EulerPacketInduction.lifespan_le_iInf_horizon`.
- [OrdinaryEulerContinuation.lean](../../Euler/OrdinaryEulerContinuation.lean) — `EulerOrdinarySobolev.FiniteLifespan.no_endpoint`.
- [ComparatorMaximalSolution.lean](../../Euler/ComparatorMaximalSolution.lean) — `Euler.ComparatorBridge.maximal_sobolev_existence_iff`.

Boundary: actual smooth all-order L² solenoidal datum, local theory, uniqueness/restriction/concatenation, nested positive packet horizons and EUL-007 contradiction. Finite-lifespan record and T>0 for the scalar Sobolev iff adapter. Conclusion T_*≤inf T_n, not equality with lim t_n. Nonzeroness via the zero solution is a prose deduction; local/continuation and adapters remain OBL-EUL-005–006.

### [EUL-009](04-euler.md#eul-009) — energy and terminal criteria

- [OrdinaryEulerKineticEnergy.lean](../../Euler/OrdinaryEulerKineticEnergy.lean) — `EulerOrdinarySobolev.Evolution.kineticEnergy_conserved`.
- [OrdinaryEulerContinuation.lean](../../Euler/OrdinaryEulerContinuation.lean) — `EulerOrdinarySobolev.FiniteLifespan.gradient_unbounded_near_endpoint`.
- [OrdinaryLogarithmicGradient.lean](../../Euler/OrdinaryLogarithmicGradient.lean) — `EulerOrdinarySobolev.logarithmic_gradient_bound_solenoidal`.
- [OrdinaryBKMReduction.lean](../../Euler/OrdinaryBKMReduction.lean) — `EulerOrdinarySobolev.Evolution.gradientIntegral_of_vorticity_bound`.
- [OrdinaryEulerBKM.lean](../../Euler/OrdinaryEulerBKM.lean) — `EulerOrdinarySobolev.FiniteLifespan.vorticity_lintegral_eq_top`.

Boundary: ordinary evolution with solenoidal/gradient L² orthogonality and strong time law; finite-lifespan record. Log inequality uses smooth all-order L² solenoidal field and finite W bounding actual curl supremum. BKM uses a uniform bound on all partial vorticity integrals to obtain gradient-integral continuation. Displayed log-Gronwall argument is schematic conditional explanation, not literal differentiation of nonsmooth norm paths. OBL-EUL-005 remains; noncompact velocity support is allowed.

### [EUL-010](04-euler.md#eul-010) — broad-class bridge

- [PacketCurlTransport.lean](../../Euler/PacketCurlTransport.lean) — `EulerParentPacketFrames.Evolution.strain_symmetric_along_label`; `EulerParentPacketFrames.Evolution.curl_eq_zero_along_position`.
- [CanonicalVorticityConfinement.lean](../../Euler/CanonicalVorticityConfinement.lean) — `EulerPacketInduction.packets_vorticity_support`; `EulerPacketInduction.canonical_vorticity_confined`.
- [ComparatorLocalEvolution.lean](../../Euler/ComparatorLocalEvolution.lean) — `Euler.ComparatorBridge.exists_evolution_of_commonCompactCurl`; `Euler.ComparatorBridge.compactCurlLocalUpgrade`; `Euler.ComparatorBridge.comparator_agrees_with_canonical`.
- [CompactVorticityContradiction.lean](../../Euler/CompactVorticityContradiction.lean) — `Euler.ComparatorBridge.no_global_solution_of_confined_vorticity`.

Boundary: exact invertible parent particle geometry, symmetric pressure Hessian, common initial curl support and cumulative displacement bound; shorter canonical slab S<T_*≤T_n for passage by stability. Broad solution has its actual global-class finite energy/smoothness, not assumed derivative bounds. Common compact curl on a closed interval is the upgrade input; persistence supplies it locally. Final contradiction uses finite lifespan plus canonical compact confinement and restarts the hypothetical smooth competitor at T_*, not the singular solution. Transport/endpoint argument expanded; finite-energy truncation, elliptic/time/pressure recovery and adapters remain OBL-EUL-006.

### [EUL-011](04-euler.md#eul-011) — viscous boundary, **no packaged adaptation**

No source theorem here asserts exact positive-viscosity packet stages. This is a conditional reuse of EUL-007's contradiction template and a direct PDE calculation: damping has rate ν|ξ|², with initial frequency k_n/ℓ_n from EUL-002; transported integrated damping must be controlled at one fixed ν. Vorticity diffusion destroys the trajectory zero-preservation implication of EUL-010. Neither impossibility of every viscous adaptation nor existence of one is proved. A replacement cascade and class bridge are new research.

## How to audit this map

For each row, open the named declaration, read its namespace and enclosing section, expand every record hypothesis, then trace the actual argument supplying it. Check that velocity, potential, pressure, schedule and parameter choices refer to the same objects at each interface. Compare the human conclusion direction to the literal theorem before accepting any strengthened formulation. Reviewers should record exact findings in [VALIDATION.md](VALIDATION.md); no missing proof may be replaced with a file-name match. All additional helper citations remain beside the calculations in the chapters.
