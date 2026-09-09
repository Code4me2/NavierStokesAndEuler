import NavierStokes.LabelSupportPreservation
import NavierStokes.HarmonicStructurePreservation
import NavierStokes.LocalResidualGrouping
import NavierStokes.AxisymmetricResidualGrouping
import NavierStokes.MeanBoundsReindex
import NavierStokes.MeanStageRegularity
import NavierStokes.WaveStateRegularity
import NavierStokes.MeanStateRegularity
import NavierStokes.BandReindexedSignedMeanGain
import NavierStokes.PhysicalResidualNaturality
import NavierStokes.UniformBlockBounds
import NavierStokes.UniformHarmonicInteraction
import NavierStokes.LocalizedCurlRealization
import NavierStokes.LocalizedMeanInteraction
import NavierStokes.HarmonicSourceSupport
import NavierStokes.NativePrincipalEquations
import NavierStokes.ParticularCopyBounds
import NavierStokes.SignedCopyBounds
import NavierStokes.LocalizedWaveBounds
import NavierStokes.MovingMomentBounds
import NavierStokes.GaugeDebtIncrement
import NavierStokes.GaugeMassPreservation
import NavierStokes.RankStateBounds
import NavierStokes.SignedMeanGain
import NavierStokes.PeriodizedWaveBounds
import NavierStokes.MeanIncrementBounds
import NavierStokes.HarmonicFields
import NavierStokes.ExponentLedger
import NavierStokes.CorrectionState
import NavierStokes.LinearWaveResidual
import NavierStokes.DefectIncrementBounds
import NavierStokes.HarmonicResidual
import NavierStokes.LiftedMeanResidual
import NavierStokes.MeanChartCompatibility
import NavierStokes.HarmonicCovariance
import NavierStokes.HarmonicMeanInteraction
import NavierStokes.PhysicalMeanDomain
import NavierStokes.SignedWaveUpdate
import NavierStokes.VariableGaugeMean
import NavierStokes.PhysicalResidualBridge
import NavierStokes.LabelSumBounds
import NavierStokes.HarmonicWaveInteraction
import NavierStokes.LocalSignedRequest
import NavierStokes.ParticularWaveAssembly
import NavierStokes.LocalRankDefect
import NavierStokes.StateReindex

/-!
# Exact field bookkeeping for one correction cycle: fields and covariances

The residuals in this file are the differentiated nonlinear fields in (32).
In particular, changing the wave covariance and changing a mean velocity are
not treated as independent black-box state transitions.  Every old/new cross
term is retained in the displayed residual differences.

This is the first part of `NavierStokes.CorrectionStep`, which is now an
aggregator over the parts under `NavierStokes/CorrectionStep/`.  It re-exports
the shared vocabulary (`ScalarField`, `Tensor`, `TensorClass`, the covariance
changes) from `NavierStokes.SignedMeanGain` and the full differential residual
from `NavierStokes.HarmonicResidual.Actual`, and declares the physical chart
representation, the temporal construction, and the gauge mean bookkeeping.
-/

noncomputable section

namespace NavierStokes.CorrectionStep

open Set WeightedClasses MeanIncrementBounds
open scoped ContDiff BigOperators

variable {D : Type} [NormedAddCommGroup D] [NormedSpace ℝ D]

/-! ## Shared vocabulary and covariance changes

The scalar-field and tensor abbreviations, the three literal covariance
changes of (32), the smoothness of an updated mean, the agreement lemmas for
those covariance changes and their mean-class bounds are all declared in
`NavierStokes.SignedMeanGain`, which this file imports.  They are re-exported
here, so one copy of each serves both modules. -/
export SignedMeanGain (ScalarField Tensor thetaCovarianceChange
  axialCovarianceChange radialCovarianceChange smooth_updated
  thetaResidual_covariance_change axialResidual_covariance_change
  gr_covariance_change TensorClass thetaCovarianceChange_mem
  axialCovarianceChange_mem radialCovarianceChange_mem)

/-! ## The full differential residual, before angular averaging

`NavierStokes.HarmonicResidual.Actual` carries the whole additivity calculus
for the exact residual — the generator, the transport terms, the cylindrical
Laplacians, the gradient, the linear residual and the nonlinear residual of a
perturbation of a fixed base.  It is imported here and re-exported unchanged. -/
export HarmonicResidual.Actual (angularGenerator_add transport_add_left
  transport_add_right twiceAlong_add cylindricalLaplacian_add
  cylindricalVectorLaplacian_add gradient_add linearResidual_add
  nonlinearResidual nonlinearResidual_add_sub)

section FullFields

open CorrectionState HarmonicCalculus

noncomputable def radialDirection (c : Context D) (n : ℕ) (x : D × ℝ) : D × ℝ :=
  (c.operators.eR + (c.operators.radialFrequency n * c.operators.radialProfile x.1) •
    c.operators.vR, 0)

noncomputable def axialDirection (c : Context D) (n : ℕ) (_x : D × ℝ) : D × ℝ :=
  (c.operators.epsilon n • c.operators.eZ, 0)

noncomputable def angularDirection (_x : D × ℝ) : D × ℝ := (0, 1)

noncomputable def timeDirection (c : Context D) (n : ℕ) (_x : D × ℝ) : D × ℝ :=
  (c.operators.fastCoefficient n • c.operators.vT - c.operators.epsilon n • c.operators.eT, 0)

noncomputable def complexBase (c : Context D) (n : ℕ) (x : D × ℝ) : ComplexVector :=
  ![(c.base.radial n x.1 : ℂ), (c.base.angular n x.1 : ℂ), (c.base.axial n x.1 : ℂ)]

noncomputable def complexPerturbation (u : State D) (n : ℕ) (x : D × ℝ) : ComplexVector :=
  ![(u.mean.radial n x.1 + u.oscillation n x 0 : ℝ),
    (u.mean.angular n x.1 + u.oscillation n x 1 : ℝ),
    (u.mean.axial n x.1 + u.oscillation n x 2 : ℝ)]

noncomputable def complexPressure (u : State D) (n : ℕ) (x : D × ℝ) : ℂ :=
  (u.totalPressureIncrement n x : ℝ)

noncomputable def virtualDivergence (c : Context D) (n : ℕ) (x : D × ℝ) : Fin 3 → ℝ :=
  ![0, -(c.operators.radialDiv 2 c.virtualTheta n x.1),
    -(c.operators.radialDiv 1 c.virtualAxial n x.1)]

/-- This field uses actual Fréchet derivatives.  The base flat error is
restored once, alongside the negative virtual-stress divergence. -/
noncomputable def fullResidual (c : Context D) (u : State D) : Oscillation D := fun n x i =>
  (nonlinearResidual (c.operators.epsilon n) (fun y : D × ℝ => c.operators.radius y.1)
    (radialDirection c n) angularDirection (axialDirection c n) (timeDirection c n)
    (complexBase c n) (complexPerturbation u n) (complexPressure u n) x i).re +
    virtualDivergence c n x i + u.errors.base n x i


noncomputable def angularMeanVector (f : Oscillation D) : MeanVector D :=
  fun n x i => angularAverage (fun k p => f k p i) n x





end FullFields

section ActualCovariance

open CorrectionState MeasureTheory

def AngularContinuous (u : Oscillation D) : Prop :=
  ∀ n x i, Continuous (fun θ : ℝ => u n (x, θ) i)

omit [NormedAddCommGroup D] [NormedSpace ℝ D] in
theorem AngularContinuous.add {u v : Oscillation D}
    (hu : AngularContinuous u) (hv : AngularContinuous v) : AngularContinuous (u + v) :=
  fun n x i => (hu n x i).add (hv n x i)






end ActualCovariance

section ActualFullUpdate

open CorrectionState HarmonicCalculus








end ActualFullUpdate

section TemporalComposition

open CorrectionState

variable {S : Type} [NormedAddCommGroup S] [NormedSpace ℝ S] [FiniteDimensional ℝ S]

noncomputable def meanBar (f : ScalarField (PressureStream.Lift S)) :
    ScalarField (PressureStream.Lift S) :=
  fun n x => PressureStream.torusAverage (f n) (x.1, x.2.1)






end TemporalComposition

/-! ## One physical field behind the chart family

The predicate below is deliberately stronger than an indexed collection of
unrelated chart solutions.  Every chart is tied to the same physical fields
by specified maps and the manuscript's velocity, pressure, and residual units.
Operator naturality and the concrete chart maps are separate obligations.
-/

section PhysicalRepresentation

open CorrectionState

variable {P : Type}

structure PhysicalFields (P : Type) where
  mean : P → Fin 3 → ℝ
  pressure : P → ℝ
  oscillation : P × ℝ → Fin 3 → ℝ
  oscillatoryPressure : P × ℝ → ℝ
  baseError : P × ℝ → Fin 3 → ℝ
  gaussianError : P × ℝ → Fin 3 → ℝ
  aliasError : P × ℝ → Fin 3 → ℝ


noncomputable def meanComponents (m : Triple D) (n : ℕ) (x : D) : Fin 3 → ℝ :=
  ![m.radial n x, m.angular n x, m.axial n x]


/-- `chart` includes the actual torus covering as well as spatial/time
rescaling. `domain n` specifies where that band is active. -/
structure RepresentsPhysical (chart : ℕ → P → D) (domain : ℕ → Set P)
    (Q : ℕ → ℝ) (A : ℝ) (u : State D) (v : PhysicalFields P) : Prop where
  mean : ∀ n x, x ∈ domain n → ∀ i,
    meanComponents u.mean n (chart n x) i = Q n ^ A * v.mean x i
  pressure : ∀ n x, x ∈ domain n → u.pressure n (chart n x) = Q n ^ (2 * A) * v.pressure x
  oscillation : ∀ n x, x ∈ domain n → ∀ θ i,
    u.oscillation n (chart n x, θ) i = Q n ^ A * v.oscillation (x, θ) i
  oscillatoryPressure : ∀ n x, x ∈ domain n → ∀ θ,
    u.oscillatoryPressure n (chart n x, θ) = Q n ^ (2 * A) * v.oscillatoryPressure (x, θ)
  baseError : ∀ n x, x ∈ domain n → ∀ θ i,
    u.errors.base n (chart n x, θ) i = Q n ^ (2 * A + 1 / 2) * v.baseError (x, θ) i
  gaussianError : ∀ n x, x ∈ domain n → ∀ θ i,
    u.errors.gaussian n (chart n x, θ) i = Q n ^ (2 * A + 1 / 2) * v.gaussianError (x, θ) i
  aliasError : ∀ n x, x ∈ domain n → ∀ θ i,
    u.errors.aliasError n (chart n x, θ) i = Q n ^ (2 * A + 1 / 2) * v.aliasError (x, θ) i



end PhysicalRepresentation

section ExcludedMeanErrors

open CorrectionState MeasureTheory

section
omit [NormedAddCommGroup D] [NormedSpace ℝ D]

theorem angularAverage_add {f g : OscillatoryScalar D}
    (hf : ∀ n x, Continuous (fun θ : ℝ => f n (x, θ)))
    (hg : ∀ n x, Continuous (fun θ : ℝ => g n (x, θ))) :
    angularAverage (f + g) = angularAverage f + angularAverage g := by
  funext n x
  change (∫ θ in (0 : ℝ)..2 * Real.pi, f n (x, θ) + g n (x, θ)) / (2 * Real.pi) = _
  rw [intervalIntegral.integral_add ((hf n x).intervalIntegrable _ _)
    ((hg n x).intervalIntegrable _ _), add_div]
  rfl

theorem angularMeanVector_add {f g : Oscillation D}
    (hf : AngularContinuous f) (hg : AngularContinuous g) :
    angularMeanVector (f + g) = angularMeanVector f + angularMeanVector g := by
  funext n x i
  exact congrFun (congrFun (angularAverage_add (fun n x => hf n x i) (fun n x => hg n x i)) n) x

end


/-- The same cancellation only uses angular continuity on the selected
fiber. No regularity outside the current physical domain is needed. -/
theorem meanGoodResidual_at (c : Context D) (u : State D) (n : ℕ) (x : D) (i : Fin 3)
    (hb : Continuous (fun θ : ℝ => u.errors.base n (x, θ) i))
    (hg : Continuous (fun θ : ℝ => u.errors.gaussian n (x, θ) i))
    (ha : Continuous (fun θ : ℝ => u.errors.aliasError n (x, θ) i)) :
    u.meanGoodResidual c n x i = u.reducedMeanResidual c n x i -
      angularMeanVector u.errors.gaussian n x i - angularMeanVector u.errors.aliasError n x i := by
  change u.reducedMeanResidual c n x i +
    HarmonicResidual.realAngularMean (fun θ => u.errors.base n (x, θ) i) -
    HarmonicResidual.realAngularMean (fun θ =>
      u.errors.base n (x, θ) i + u.errors.gaussian n (x, θ) i +
        u.errors.aliasError n (x, θ) i) = _
  rw [HarmonicResidual.realAngularMean_add (hb.fun_add hg) ha,
    HarmonicResidual.realAngularMean_add hb hg]
  dsimp only [angularMeanVector, angularAverage, HarmonicResidual.realAngularMean,
    HarmonicFields.period]
  ring


end ExcludedMeanErrors

section ActualHarmonicForcing

open CorrectionState






end ActualHarmonicForcing

section ActualMeanAndDivergence

open CorrectionState




noncomputable def meanLift (m : Triple D) : Oscillation D :=
  fun n x => meanComponents m n x.1

noncomputable def meanDivergence (c : Context D) (m : Triple D) : ScalarField D :=
  fun n x => c.operators.dr m.radial n x + m.radial n x / c.operators.radius x +
    c.operators.dz m.axial n x

noncomputable def fullDivergence (c : Context D) (u : State D) : OscillatoryScalar D :=
  fun n => LiftedMeanResidual.realDivergence (fun x => c.operators.radius x.1)
    (radialDirection c n) angularDirection (axialDirection c n) (u.totalVelocity c n)

theorem meanLift_divergence {U : Set D} (hU : IsOpen U)
    (c : Context D) (m : Triple D) (hm : SmoothTriple U m)
    (n : ℕ) {x : D} (hx : x ∈ U) (θ : ℝ) :
    LiftedMeanResidual.realDivergence (fun y => c.operators.radius y.1)
      (radialDirection c n) angularDirection (axialDirection c n) (meanLift m n) (x, θ) =
      meanDivergence c m n x := by
  have hr := ((hm.radial n).contDiffAt (hU.mem_nhds hx)).differentiableAt (by simp)
  have ht := ((hm.angular n).contDiffAt (hU.mem_nhds hx)).differentiableAt (by simp)
  have hz := ((hm.axial n).contDiffAt (hU.mem_nhds hx)).differentiableAt (by simp)
  change HarmonicCalculus.along (LiftedMeanResidual.liftDirection
      (fun y => c.operators.eR + (c.operators.radialFrequency n * c.operators.radialProfile y) •
        c.operators.vR)) (LiftedMeanResidual.liftScalar (m.radial n)) (x, θ) +
    m.radial n x / c.operators.radius x +
    HarmonicCalculus.along LiftedMeanResidual.angularDirection
      (LiftedMeanResidual.liftScalar (m.angular n)) (x, θ) / c.operators.radius x +
    HarmonicCalculus.along (LiftedMeanResidual.liftDirection
      (fun _ => c.operators.epsilon n • c.operators.eZ))
      (LiftedMeanResidual.liftScalar (m.axial n)) (x, θ) = _
  rw [LiftedMeanResidual.along_lift hr, LiftedMeanResidual.theta_lift_zero ht,
    LiftedMeanResidual.along_lift hz]
  simp only [HarmonicCalculus.along, meanDivergence, Operators.dr, graphDerivative,
    Operators.dz, map_add, map_smul, smul_eq_mul, zero_div, add_zero]
  ring

/-- Addition preserves actual cylindrical divergence by the derivative
sum rule. The correction's divergence is a separate explicit summand. -/
theorem fullDivergence_actual_update (c : Context D) (u : State D)
    (m : Triple D) (p : ScalarField D) (w : Oscillation D) (q : OscillatoryScalar D)
    (e : ExcludedErrors D) (n : ℕ) (x : D × ℝ)
    (hu : ∀ i, DifferentiableAt ℝ (fun y => u.totalVelocity c n y i) x)
    (hi : ∀ i, DifferentiableAt ℝ (fun y => meanLift m n y i + w n y i) x) :
    fullDivergence c (u.addIncrement m p w q e) n x = fullDivergence c u n x +
      LiftedMeanResidual.realDivergence (fun y => c.operators.radius y.1)
        (radialDirection c n) angularDirection (axialDirection c n)
        (fun y => meanLift m n y + w n y) x := by
  have hv : (u.addIncrement m p w q e).totalVelocity c n =
      fun y => u.totalVelocity c n y + (meanLift m n y + w n y) := by
    funext y i
    have ht := congrFun (congrFun (congrFun
      (State.totalVelocity_addIncrement u c m p w q e) n) y) i
    simpa only [Pi.add_apply, meanLift, meanComponents, add_assoc] using ht
  unfold fullDivergence
  rw [hv]
  exact LiftedMeanResidual.realDivergence_add _ _ _ _ hu hi

end ActualMeanAndDivergence

section MeanDivergencePreservation

open CorrectionState

theorem meanAddition_fullDivergence {U : Set D} (hU : IsOpen U)
    (c : Context D) (u : State D) (m : Triple D) (p : ScalarField D)
    (q : OscillatoryScalar D) (e : ExcludedErrors D) (hm : SmoothTriple U m)
    (n : ℕ) {x : D} (hx : x ∈ U) (θ : ℝ)
    (hu : ∀ i, DifferentiableAt ℝ (fun y => u.totalVelocity c n y i) (x, θ)) :
    fullDivergence c (u.addIncrement m p 0 q e) n (x, θ) =
      fullDivergence c u n (x, θ) + meanDivergence c m n x := by
  have hi (i : Fin 3) : DifferentiableAt ℝ (fun y => meanLift m n y i) (x, θ) := by
    have hs := LiftedMeanResidual.liftScalar_smooth
      (LiftedMeanResidual.tripleVector_smooth hm n i)
    exact (hs.contDiffAt ((LiftedMeanResidual.cylinder_open hU).mem_nhds
      ⟨hx, mem_univ θ⟩)).differentiableAt (by simp)
  have he := fullDivergence_actual_update c u m p 0 q e n (x, θ) hu
    (fun i => by simpa only [Pi.zero_apply, add_zero] using hi i)
  simp only [Pi.zero_apply, add_zero] at he
  rw [meanLift_divergence hU c m hm n hx θ] at he
  exact he

variable {S : Type} [NormedAddCommGroup S] [NormedSpace ℝ S]


theorem meanDivergence_eq_graph (p : ReconstructionData)
    (epsilon fast : ℕ → ℝ) (axial slowTime : S × PressureStream.Plane)
    (temporal : PressureStream.Plane) (c : Context (PressureStream.Lift S))
    (hcompat : c.operators = graphOperators p epsilon fast axial slowTime temporal)
    (m : Triple (PressureStream.Lift S)) (n : ℕ) (x : PressureStream.Lift S) :
    meanDivergence c m n x =
      PressureStream.graphDivergence (PressureStream.physicalSpeed p.exponent (p.frequency n))
        (0, p.radialDirection) (epsilon n • axial) (m.radial n) (m.axial n) x := by
  unfold meanDivergence
  rw [hcompat, graphOperators_dr, graphOperators_dz]
  rfl

variable [FiniteDimensional ℝ S]






end MeanDivergencePreservation

section CommonTemporalConstruction

open CorrectionState

variable {S : Type} [NormedAddCommGroup S] [NormedSpace ℝ S]

/-- Pressure reconstruction with the prescribed transported radial data
for each band. This is an actual field constructor. -/
noncomputable def reconstructPressureFamily (r : ℕ → ReconstructionData)
    (c : Context (PressureStream.Lift S)) (u : State (PressureStream.Lift S)) :
    State (PressureStream.Lift S) :=
  { u with pressure := fun n => (reconstructPressure (r n) c u).pressure n }




theorem common_fastTime (h : ℝ) (index : ℕ → ℕ) (c : Context (PressureStream.Lift S))
    (hv : c.operators.vT = (0, (0, TorusInverse.vector .temporal)))
    (hf : ∀ n, c.operators.fastCoefficient n =
      ChartScales.Tg ^ index n * ChartScales.Q n ^ (1 + h))
    (f : ScalarField (PressureStream.Lift S)) (n : ℕ) (x : PressureStream.Lift S) :
    c.operators.fastTime f n x = MeanChartCompatibility.fastAtIndex h n (index n) (f n) x := by
  simp only [Operators.fastTime, hv, hf, MeanChartCompatibility.fastAtIndex, PressureStream.graphDz]

variable [FiniteDimensional ℝ S]





end CommonTemporalConstruction

section CommonTemporalScale

open CorrectionState

variable {S : Type} [NormedAddCommGroup S] [NormedSpace ℝ S]



omit [NormedAddCommGroup D] [NormedSpace ℝ D] in
theorem triple_ext {a b : Triple D} (hr : a.radial = b.radial)
    (ht : a.angular = b.angular) (hz : a.axial = b.axial) : a = b := by
  cases a
  cases b
  simp only [Triple.mk.injEq] at *
  exact ⟨hr, ht, hz⟩


variable [FiniteDimensional ℝ S]



end CommonTemporalScale

section HarmonicStateUpdates

open CorrectionState

/-! Adding coefficient families on a fixed label carrier, the carrier predicate
itself, and the oscillation of such a sum all come from
`NavierStokes.LabelSumBounds`; only the pressure and band statements below are
proper to this file. -/
export LabelSumBounds (SameCarrier addBlock addBlock_oscillation)

section
omit [NormedAddCommGroup D] [NormedSpace ℝ D]

theorem addBlock_pressure (a b : HarmonicBlock D) (h : SameCarrier a b) :
    (addBlock a b).oscillatoryPressure = a.oscillatoryPressure + b.oscillatoryPressure := by
  funext n x
  simp only [addBlock, HarmonicBlock.oscillatoryPressure, HarmonicFields.field, HarmonicFields.evaluate_add,
    Complex.add_re, Pi.add_apply, h.frequency, h.phase, h.angular]

theorem addBlock_band {a b : HarmonicBlock D} {N M : ℕ}
    (ha : a.BandLimited N) (hb : b.BandLimited M) :
    (addBlock a b).BandLimited (max N M) :=
  ⟨fun n i => (ha.1 n i |>.mono (le_max_left _ _)).add (hb.1 n i |>.mono (le_max_right _ _)),
    fun n => (ha.2 n |>.mono (le_max_left _ _)).add (hb.2 n |>.mono (le_max_right _ _))⟩

theorem block_angularContinuous (b : HarmonicBlock D) : AngularContinuous b.oscillation :=
  fun n x i => Complex.continuous_re.comp
    (HarmonicFields.field_angular_continuous (b.velocity n i) (b.frequency n)
      (b.phase n) (b.angularFrequency n) x)

end

theorem block_waveBounds_all {s : StripData D} {P : ℕ → D → ℝ} {α : ℝ}
    (b : HarmonicBlock D) (hb : b.WaveBounds s P α)
    (hzero : ∀ n i, b.velocity n i 0 = 0)
    (hP : ∀ n x, x ∈ s.domain → 0 ≤ P n x) :
    ∀ i j, WaveClass s P α (fun n x => b.velocity n i j x) := by
  intro i j
  by_cases hj : j = 0
  · subst j
    have hz : WaveClass s P α (0 : ℕ → D → ℂ) := MemClass.zero (fun n x hx =>
      mul_nonneg (Real.sqrt_nonneg (s.zeta x)) (hP n x hx))
    apply WaveInteractionBounds.class_congr hz
    intro n x hx
    simp only [hzero, Pi.zero_apply]
  · exact hb i j hj



end HarmonicStateUpdates

section SignedTensorRemainder

open CorrectionState MeasureTheory

export LabelSumBounds (symmetricCovariance subBlock subBlock_oscillation)

section
omit [NormedAddCommGroup D] [NormedSpace ℝ D]



theorem subBlock_band {a b : HarmonicBlock D} {N M : ℕ}
    (ha : a.BandLimited N) (hb : b.BandLimited M) :
    (subBlock a b).BandLimited (max N M) :=
  ⟨fun n i => HarmonicResidual.band_sub (ha.1 n i |>.mono (le_max_left _ _))
      (hb.1 n i |>.mono (le_max_right _ _)),
    fun n => HarmonicResidual.band_sub (ha.2 n |>.mono (le_max_left _ _))
      (hb.2 n |>.mono (le_max_right _ _))⟩

end
end SignedTensorRemainder

section ConstructedSignedBlocks

open CorrectionState SignedWaveUpdate

/-- The class of a literal coefficient difference is transported from the
full cylindrical coefficient domain to the actual harmonic blocks. -/
theorem blockOfCoefficients_difference_mem
    {s : StripData (D × ℝ)} {P : ℕ → D × ℝ → ℝ} {α : ℝ}
    (a b : LinearWaveBounds.WaveCoefficients (D × ℝ)) (kp : ℕ → ℤ)
    (hab : WaveClass s P α (fun n x => a.amplitude n x - b.amplitude n x)) :
    (subBlock (blockOfCoefficients a kp) (blockOfCoefficients b kp)).WaveBounds
      (sectionStrip s) (fun n x => P n (x, 0)) α := by
  have hsection := class_zeroSection hab
  intro i j hj
  have hh := conjugatePair_class (CurlClassBounds.class_component hsection i) j
  apply WaveInteractionBounds.class_congr hh
  intro n x hx
  change ErrorHarmonics.conjugatePair 1 (fun x => a.amplitude n (x,0) i - b.amplitude n (x,0) i) j x =
    ErrorHarmonics.conjugatePair 1 (fun x => a.amplitude n (x,0) i) j x -
      ErrorHarmonics.conjugatePair 1 (fun x => b.amplitude n (x,0) i) j x
  simp only [conjugatePair_apply]
  split_ifs <;> simp only [map_sub, map_zero, sub_div] <;> ring




end ConstructedSignedBlocks

section CumulativeWaveUpdates

open CorrectionState


omit [NormedAddCommGroup D] [NormedSpace ℝ D] in
theorem twoWaveUpdates_band {old particular signed : HarmonicBlock D} {N M K : ℕ}
    (ho : old.BandLimited N) (hp : particular.BandLimited M) (hs : signed.BandLimited K) :
    (addBlock (addBlock old particular) signed).BandLimited (max (max N M) K) :=
  addBlock_band (addBlock_band ho hp) hs


end CumulativeWaveUpdates

section LocalCommonClock

open CorrectionState PhysicalMeanDomain

variable {S : Type} [NormedAddCommGroup S] [NormedSpace ℝ S] [FiniteDimensional ℝ S]

theorem temporalAtIndex_local_smooth (h : ℝ) (n i : ℕ) {V : Set S} (hV : IsOpen V)
    {f : PressureStream.Lift S → ℝ} (hf : ContDiffOn ℝ ∞ f (slowDomain V))
    (hp : PeriodicOn V f) :
    ContDiffOn ℝ ∞ (MeanChartCompatibility.temporalAtIndex h n i f) (slowDomain V) := by
  rw [MeanChartCompatibility.temporalAtIndex_eq_native]
  exact contDiffOn_const.mul (PhysicalMeanDomain.desiredIncrement_contDiffOn h n hV hf hp)

/-- The common clock cancels the actual local residual. Localization is
used only to prove a germ identity for the same torus inverse. -/
theorem temporalAtIndex_local_fast (h : ℝ) (n i : ℕ) {V : Set S} (hV : IsOpen V)
    {f : PressureStream.Lift S → ℝ} (hf : ContDiffOn ℝ ∞ f (slowDomain V))
    (hp : PeriodicOn V f) {x : PressureStream.Lift S} (hx : x.2.1 ∈ V) :
    MeanChartCompatibility.fastAtIndex h n i (MeanChartCompatibility.temporalAtIndex h n i f) x =
      -TemporalMeanUpdate.centered f x := by
  obtain ⟨cutoff, _, hsupport, hglobal, he⟩ := exists_fiber_localization hV hx hf
  have hd := ((desiredIncrement_fiberLocal h n).germ he).eventuallyEq x.1 x.2.2
  have hc := ((centered_fiberLocal.germ he).eventuallyEq x.1 x.2.2).self_of_nhds
  have hi : MeanChartCompatibility.temporalAtIndex h n i (localize cutoff f) =ᶠ[nhds x]
      MeanChartCompatibility.temporalAtIndex h n i f := by
    rw [MeanChartCompatibility.temporalAtIndex_eq_native,
      MeanChartCompatibility.temporalAtIndex_eq_native]
    exact hd.mono fun y hy => congrArg (MeanChartCompatibility.commonRatio h n i * ·) hy
  have hsolve := MeanChartCompatibility.temporalAtIndex_fast_cancellation h n i hglobal
    (localize_periodic hsupport hp) x
  simpa only [MeanChartCompatibility.fastAtIndex, PressureStream.graphDz, hi.fderiv_eq, hc] using hsolve

end LocalCommonClock

section GaugeMeanBookkeeping

open CorrectionState VariableGaugeMean

variable {S : Type} [NormedAddCommGroup S] [NormedSpace ℝ S]

noncomputable def gaugeTemporalPressureChange (g : GaugeData S) (h : ℝ) (index : ℕ → ℕ)
    (axial : S × PressureStream.Plane) (c : Context (PressureStream.Lift S))
    (u : State (PressureStream.Lift S)) : ScalarField (PressureStream.Lift S) :=
  (temporalStageState g h index axial c u).pressure - u.pressure

noncomputable def gaugeRankPressureChange (g : GaugeData S) (r : RankData S)
    (axial : S × PressureStream.Plane) (c : Context (PressureStream.Lift S))
    (u : State (PressureStream.Lift S)) : ScalarField (PressureStream.Lift S) :=
  (rankStageState g r axial c u).pressure - u.pressure

theorem gaugeTemporalStage_covariance (g : GaugeData S) (h : ℝ) (index : ℕ → ℕ)
    (axial : S × PressureStream.Plane) (c : Context (PressureStream.Lift S))
    (u : State (PressureStream.Lift S)) :
    (temporalStageState g h index axial c u).covariance = u.covariance := by
  simp only [temporalStageState, reconstructState, State.addIncrement, add_zero]
  rfl

theorem gaugeRankStage_covariance (g : GaugeData S) (r : RankData S)
    (axial : S × PressureStream.Plane) (c : Context (PressureStream.Lift S))
    (u : State (PressureStream.Lift S)) :
    (rankStageState g r axial c u).covariance = u.covariance := by
  simp only [rankStageState, reconstructState, State.addIncrement, add_zero]
  rfl

theorem gaugeTemporalStage_cumulative {s : StripData (PressureStream.Lift S)}
    (g : GaugeData S) (h : ℝ) (index : ℕ → ℕ) (axial : S × PressureStream.Plane)
    (c : Context (PressureStream.Lift S)) (u : State (PressureStream.Lift S)) {H : ℝ}
    (hu : CorrectionState.CumulativeBounds s u)
    (hi : IncrementBounds s H (temporalIncrementState g h index axial c u))
    (hp : MeanClass s H (gaugeTemporalPressureChange g h index axial c u)) (hH : 9 / 10 ≤ H) :
    CorrectionState.CumulativeBounds s (temporalStageState g h index axial c u) := by
  refine ⟨cumulative_updated hu.velocity hi hH, ?_⟩
  have he : (temporalStageState g h index axial c u).pressure =
      u.pressure + gaugeTemporalPressureChange g h index axial c u := by
    unfold gaugeTemporalPressureChange
    abel
  rw [he]
  exact hu.pressure.add (hp.mono_exponent hH)

theorem gaugeRankStage_cumulative {s : StripData (PressureStream.Lift S)}
    (g : GaugeData S) (r : RankData S) (axial : S × PressureStream.Plane)
    (c : Context (PressureStream.Lift S)) (u : State (PressureStream.Lift S)) {H : ℝ}
    (hu : CorrectionState.CumulativeBounds s u)
    (hi : IncrementBounds s H (rankIncrementState g r axial c u))
    (hp : MeanClass s H (gaugeRankPressureChange g r axial c u)) (hH : 9 / 10 ≤ H) :
    CorrectionState.CumulativeBounds s (rankStageState g r axial c u) := by
  refine ⟨cumulative_updated hu.velocity hi hH, ?_⟩
  have he : (rankStageState g r axial c u).pressure =
      u.pressure + gaugeRankPressureChange g r axial c u := by
    unfold gaugeRankPressureChange
    abel
  rw [he]
  exact hu.pressure.add (hp.mono_exponent hH)

end GaugeMeanBookkeeping

section GaugeTemporalResidual

open CorrectionState VariableGaugeMean PhysicalMeanDomain

variable {S : Type} [NormedAddCommGroup S] [NormedSpace ℝ S] [FiniteDimensional ℝ S]

/-- The actual gauge stream may differ from the desired axial inverse;
its entire fast derivative is retained as the named axial alias. -/
theorem gaugeTemporal_fastCancellation {U : Set (PressureStream.Lift S)} (hU : IsOpen U)
    {V : Set S} (hV : IsOpen V) (hUV : ∀ x ∈ U, x.2.1 ∈ V)
    (g : GaugeData S) (h : ℝ) (index : ℕ → ℕ) (axial : S × PressureStream.Plane)
    (c : Context (PressureStream.Lift S)) (u : State (PressureStream.Lift S))
    (hv : c.operators.vT = (0, (0, TorusInverse.vector .temporal)))
    (hfast : ∀ n, c.operators.fastCoefficient n =
      ChartScales.Tg ^ index n * ChartScales.Q n ^ (1 + h))
    (hi : SmoothTriple U (temporalIncrementState g h index axial c u))
    (hθ : ∀ n, ContDiffOn ℝ ∞ (u.thetaResidual c n) (slowDomain V))
    (hz : ∀ n, ContDiffOn ℝ ∞ (u.axialResidual c n) (slowDomain V))
    (hpθ : ∀ n, PeriodicOn V (u.thetaResidual c n))
    (hpz : ∀ n, PeriodicOn V (u.axialResidual c n))
    (n : ℕ) {x : PressureStream.Lift S} (hx : x ∈ U) :
    c.operators.fastTime (temporalIncrementState g h index axial c u).angular n x +
        (u.thetaResidual c n x - meanBar (u.thetaResidual c) n x) = 0 ∧
      c.operators.fastTime (temporalIncrementState g h index axial c u).axial n x +
        (u.axialResidual c n x - meanBar (u.axialResidual c) n x) =
          temporalAliasState g h index c u n (x, 0) 2 := by
  have hθf := temporalAtIndex_local_fast h n (index n) hV (hθ n) (hpθ n) (hUV x hx)
  have hzf := temporalAtIndex_local_fast h n (index n) hV (hz n) (hpz n) (hUV x hx)
  let desired : ScalarField (PressureStream.Lift S) := fun m =>
    MeanChartCompatibility.temporalAtIndex h m (index m) (u.axialResidual c m)
  have hdes : DifferentiableAt ℝ (desired n) x :=
    ((temporalAtIndex_local_smooth h n (index n) hV (hz n) (hpz n)).contDiffAt
      ((slowDomain_open hV).mem_nhds (hUV x hx))).differentiableAt (by simp)
  have hinc : DifferentiableAt ℝ ((temporalIncrementState g h index axial c u).axial n) x :=
    ((hi.axial n).contDiffAt (hU.mem_nhds hx)).differentiableAt (by simp)
  have hd : HasFDerivAt (temporalAxialDifference g h index c u n)
      (fderiv ℝ (desired n) x -
        fderiv ℝ ((temporalIncrementState g h index axial c u).axial n) x) x :=
    hdes.hasFDerivAt.sub hinc.hasFDerivAt
  have he : c.operators.fastTime (temporalAxialDifference g h index c u) n x =
      c.operators.fastTime desired n x -
        c.operators.fastTime (temporalIncrementState g h index axial c u).axial n x := by
    simp only [Operators.fastTime, hd.fderiv, _root_.sub_apply, mul_sub]
  constructor
  · rw [common_fastTime h index c hv hfast]
    change MeanChartCompatibility.fastAtIndex h n (index n)
      (MeanChartCompatibility.temporalAtIndex h n (index n) (u.thetaResidual c n)) x + _ = 0
    rw [hθf]
    simp only [TemporalMeanUpdate.centered, meanBar]
    ring
  · have hdesired : c.operators.fastTime desired n x =
        -(u.axialResidual c n x - meanBar (u.axialResidual c) n x) := by
      rw [common_fastTime h index c hv hfast]
      exact hzf
    change _ = -c.operators.fastTime (temporalAxialDifference g h index c u) n x
    rw [he, hdesired]
    ring

theorem gaugeTemporalStage_theta_exact {U : Set (PressureStream.Lift S)} (hU : IsOpen U)
    {V : Set S} (hV : IsOpen V) (hUV : ∀ x ∈ U, x.2.1 ∈ V)
    (g : GaugeData S) (h : ℝ) (index : ℕ → ℕ) (axial : S × PressureStream.Plane)
    (c : Context (PressureStream.Lift S)) (u : State (PressureStream.Lift S))
    (hv : c.operators.vT = (0, (0, TorusInverse.vector .temporal)))
    (hfast : ∀ n, c.operators.fastCoefficient n =
      ChartScales.Tg ^ index n * ChartScales.Q n ^ (1 + h))
    (hprofile : ContDiffOn ℝ ∞ c.operators.radialProfile U)
    (hb : SmoothTriple U c.base) (hm : SmoothTriple U u.mean)
    (hi : SmoothTriple U (temporalIncrementState g h index axial c u))
    (hW : ∀ i j, SmoothOn U (u.covariance i j))
    (hθ : ∀ n, ContDiffOn ℝ ∞ (u.thetaResidual c n) (slowDomain V))
    (hz : ∀ n, ContDiffOn ℝ ∞ (u.axialResidual c n) (slowDomain V))
    (hpθ : ∀ n, PeriodicOn V (u.thetaResidual c n))
    (hpz : ∀ n, PeriodicOn V (u.axialResidual c n)) :
    Agree U ((temporalStageState g h index axial c u).thetaResidual c)
      (meanBar (u.thetaResidual c) + thetaRemainder c.operators c.base u.mean
        (temporalIncrementState g h index axial c u)) := by
  have he := thetaResidual_change hU c.operators hprofile hb hm hi u.covariance hW c.virtualTheta
  have hnew : (temporalStageState g h index axial c u).thetaResidual c =
      MeanIncrementBounds.thetaResidual c.operators c.base
        (updated u.mean (temporalIncrementState g h index axial c u)) u.covariance c.virtualTheta := by
    simp [State.thetaResidual, temporalStageState,
      reconstructState, State.addIncrement]
    rfl
  intro n x hx
  have hc := (gaugeTemporal_fastCancellation hU hV hUV g h index axial c u hv hfast
    hi hθ hz hpθ hpz n hx).1
  have he' := he n hx
  rw [hnew]
  simp only [Pi.add_apply, Pi.sub_apply] at he' ⊢
  change _ - u.thetaResidual c n x = _ at he'
  linarith

theorem gaugeTemporalStage_axial_exact {U : Set (PressureStream.Lift S)} (hU : IsOpen U)
    {V : Set S} (hV : IsOpen V) (hUV : ∀ x ∈ U, x.2.1 ∈ V)
    (g : GaugeData S) (h : ℝ) (index : ℕ → ℕ) (axial : S × PressureStream.Plane)
    (c : Context (PressureStream.Lift S)) (u : State (PressureStream.Lift S))
    (hv : c.operators.vT = (0, (0, TorusInverse.vector .temporal)))
    (hfast : ∀ n, c.operators.fastCoefficient n =
      ChartScales.Tg ^ index n * ChartScales.Q n ^ (1 + h))
    (hprofile : ContDiffOn ℝ ∞ c.operators.radialProfile U)
    (hb : SmoothTriple U c.base) (hm : SmoothTriple U u.mean)
    (hi : SmoothTriple U (temporalIncrementState g h index axial c u))
    (hW : ∀ i j, SmoothOn U (u.covariance i j))
    (hp : SmoothOn U u.pressure)
    (hnp : SmoothOn U (temporalStageState g h index axial c u).pressure)
    (hθ : ∀ n, ContDiffOn ℝ ∞ (u.thetaResidual c n) (slowDomain V))
    (hz : ∀ n, ContDiffOn ℝ ∞ (u.axialResidual c n) (slowDomain V))
    (hpθ : ∀ n, PeriodicOn V (u.thetaResidual c n))
    (hpz : ∀ n, PeriodicOn V (u.axialResidual c n)) :
    Agree U (fun n x => (temporalStageState g h index axial c u).axialResidual c n x -
      temporalAliasState g h index c u n (x, 0) 2)
      (meanBar (u.axialResidual c) + axialRemainder c.operators c.base u.mean
        (temporalIncrementState g h index axial c u) (gaugeTemporalPressureChange g h index axial c u)) := by
  have he := axialResidual_change hU c.operators hprofile hb hm hi u.covariance hW u.pressure
    (gaugeTemporalPressureChange g h index axial c u) c.virtualAxial hp (hnp.sub hp)
  have hpressure : u.pressure + gaugeTemporalPressureChange g h index axial c u =
      (temporalStageState g h index axial c u).pressure := by
    unfold gaugeTemporalPressureChange
    abel
  have hnew : (temporalStageState g h index axial c u).axialResidual c =
      MeanIncrementBounds.axialResidual c.operators c.base
        (updated u.mean (temporalIncrementState g h index axial c u)) u.covariance
        (u.pressure + gaugeTemporalPressureChange g h index axial c u) c.virtualAxial := by
    rw [hpressure]
    simp [State.axialResidual, temporalStageState,
      reconstructState, State.addIncrement]
    rfl
  intro n x hx
  have hc := (gaugeTemporal_fastCancellation hU hV hUV g h index axial c u hv hfast
    hi hθ hz hpθ hpz n hx).2
  have he' := he n hx
  rw [hnew]
  simp only [Pi.add_apply, Pi.sub_apply] at he' ⊢
  change _ - u.axialResidual c n x = _ at he'
  linarith

end GaugeTemporalResidual

section GaugeTemporalGain

open CorrectionState VariableGaugeMean PhysicalMeanDomain

variable {S : Type} [NormedAddCommGroup S] [NormedSpace ℝ S] [FiniteDimensional ℝ S]

/-- The actual variable-gauge temporal update has the same differentiated
mean remainder as the fixed-gauge update. Its axial alias remains explicit. -/
theorem gaugeTemporalStage_mean_gain {s : StripData (PressureStream.Lift S)}
    {V : Set S} (hV : IsOpen V) (hUV : ∀ x ∈ s.domain, x.2.1 ∈ V)
    (g : GaugeData S) (h : ℝ) (index : ℕ → ℕ) (axial : S × PressureStream.Plane)
    (c : Context (PressureStream.Lift S)) (u : State (PressureStream.Lift S)) {H κ β : ℝ}
    (hv : c.operators.vT = (0, (0, TorusInverse.vector .temporal)))
    (hfast : ∀ n, c.operators.fastCoefficient n =
      ChartScales.Tg ^ index n * ChartScales.Q n ^ (1 + h))
    (ho : OperatorBounds s c.operators κ) (hb : BaseBounds s c.base)
    (hu : CorrectionState.CumulativeBounds s u)
    (hi : IncrementBounds s H (temporalIncrementState g h index axial c u))
    (hdp : MeanClass s H (gaugeTemporalPressureChange g h index axial c u))
    (hW : ∀ i j, SmoothOn s.domain (u.covariance i j))
    (hbarθ : MeanClass s β (meanBar (u.thetaResidual c)))
    (hbarz : MeanClass s β (meanBar (u.axialResidual c)))
    (hθ : ∀ n, ContDiffOn ℝ ∞ (u.thetaResidual c n) (slowDomain V))
    (hz : ∀ n, ContDiffOn ℝ ∞ (u.axialResidual c n) (slowDomain V))
    (hpθ : ∀ n, PeriodicOn V (u.thetaResidual c n))
    (hpz : ∀ n, PeriodicOn V (u.axialResidual c n))
    (hH : 9 / 10 ≤ H) (hβ : β ≤ H + 1 - 2 * κ) :
    MeanClass s β ((temporalStageState g h index axial c u).thetaResidual c) ∧
      MeanClass s β (fun n x => (temporalStageState g h index axial c u).axialResidual c n x -
        temporalAliasState g h index c u n (x, 0) 2) := by
  have hnp : SmoothOn s.domain (temporalStageState g h index axial c u).pressure := by
    have he : (temporalStageState g h index axial c u).pressure =
        u.pressure + gaugeTemporalPressureChange g h index axial c u := by
      unfold gaugeTemporalPressureChange
      abel
    rw [he]
    exact fun n => (hu.pressure.smooth n).add (hdp.smooth n)
  constructor
  · apply class_congr (hbarθ.add ((thetaRemainder_mem ho hb hu.velocity hi hH).mono_exponent hβ))
    exact gaugeTemporalStage_theta_exact s.isOpen_domain hV hUV g h index axial c u hv hfast
      (ho.radialProfile.smooth 0) hb.smooth hu.velocity.smooth hi.smooth hW hθ hz hpθ hpz
  · apply class_congr (hbarz.add ((axialRemainder_mem ho hb hu.velocity hi hH hdp).mono_exponent hβ))
    exact gaugeTemporalStage_axial_exact s.isOpen_domain hV hUV g h index axial c u hv hfast
      (ho.radialProfile.smooth 0) hb.smooth hu.velocity.smooth hi.smooth hW hu.pressure.smooth hnp
      hθ hz hpθ hpz


end GaugeTemporalGain

section GaugeAliasBookkeeping

open CorrectionState VariableGaugeMean

variable {S : Type} [NormedAddCommGroup S] [NormedSpace ℝ S]

noncomputable def gaugeRefreshPressureAlias (g : GaugeData S)
    (c : Context (PressureStream.Lift S)) (old current : State (PressureStream.Lift S)) :
    State (PressureStream.Lift S) :=
  { current with errors := { current.errors with aliasError :=
      current.errors.aliasError + (pressureAliasState g c current - pressureAliasState g c old) } }










end GaugeAliasBookkeeping

end NavierStokes.CorrectionStep
