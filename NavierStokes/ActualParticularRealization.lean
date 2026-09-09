import NavierStokes.CorrectionStep
import NavierStokes.CyclePhysicalPrefixes

/-!
# Cartesian realization of the actual reference particular update

The source is the current state's literal harmonic residual.  The common
solve, its transported cutoff, its curl correction, and its finite harmonic
assembly are retained in the realization.
-/

noncomputable section

open Set Filter Function
open scoped Topology ContDiff BigOperators

namespace NavierStokes.ActualParticularRealization

open HarmonicCalculus ParticularWaveAssembly ParticularWaveBounds
open CurlClassBounds hiding ComplexVector
open CorrectionState

abbrev Parameter := PhysicalParticularWave.Parameter
abbrev Plane := TorusInverse.Plane
abbrev Associated := Parameter × Plane
abbrev WaveSpace := PhysicalParticularWave.WaveSpace

section Reindex

variable {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]


theorem curl_pull (e : E ≃ₗᵢ[ℝ] F) (R : F → ℝ) (Vr Vθ Vz : F → F)
    (a : F → ComplexVector) :
    cylindricalCurl (fun x => R (e x)) (StateReindex.vector e Vr) (StateReindex.vector e Vθ)
      (StateReindex.vector e Vz) (fun x => a (e x)) = fun x => cylindricalCurl R Vr Vθ Vz a (e x) := by
  funext x
  simp only [cylindricalCurl, StateReindex.along_pull_component]


/-- Phase agreement on a neighborhood suffices for the complete curl
correction; no global continuation of the phase identity is required. -/
theorem realizedCoefficient_phase_germ {Φ Ψ : E → ℝ} {x : E} (hΦ : Φ =ᶠ[𝓝 x] Ψ)
    (K : ℝ) (R : E → ℝ) (Vr Vθ Vz : E → E) (a : E → ComplexVector) :
    realizedCoefficient K R Vr Vθ Vz Φ a =ᶠ[𝓝 x] realizedCoefficient K R Vr Vθ Vz Ψ a := by
  have hc : coefficient R Vr Vθ Vz Φ a =ᶠ[𝓝 x] coefficient R Vr Vθ Vz Ψ a := by
    filter_upwards [hΦ.fderiv (𝕜 := ℝ)] with y hy
    simp only [coefficient, phaseNormal, along, hy]
  filter_upwards [ParticularWaveAssembly.curl_germ hc R Vr Vθ Vz] with y hy
  simp only [realizedCoefficient, curlRemainder_eq, hy]

end Reindex


noncomputable def corrected (D : AssemblyData Parameter) (s : WeightedClasses.StripData Associated)
    (h : ℝ) (gap : ℕ → ℕ) (j : ℤ) : LinearWaveBounds.WaveCoefficients WaveSpace :=
  (CorrectionStep.ParticularParameters.fromReference D h gap).wave s
    D.context D.state D.carrierBlock D.gaussianInput D.aliasInput j

/-- Only the primitive radius and differential directions are matched.
No solved coefficient or output field occurs in this record. -/
structure TargetChart (D : AssemblyData Parameter) (s : WeightedClasses.StripData Associated)
    (h : ℝ) (n i : ℕ) : Prop where
  radius : (fun x => D.background.radius n (PhysicalParticularWave.waveEquiv x)) =
    PhysicalResidualBridge.ScaledGraph.radius
  radial : StateReindex.vector PhysicalParticularWave.waveEquiv (D.directions.radialField n) =
    (PhysicalResidualBridge.commonGraph (ChartScales.Q n) h i).radial
  angular : StateReindex.vector PhysicalParticularWave.waveEquiv (fun _ => D.directions.angular) =
    PhysicalResidualBridge.ScaledGraph.angular
  axial : StateReindex.vector PhysicalParticularWave.waveEquiv
    (D.directions.axialField (CorrectionStep.ParticularParameters.nativeStrip s) n) =
      (PhysicalResidualBridge.commonGraph (ChartScales.Q n) h i).axial

section Band

variable (D : AssemblyData Parameter) (s : WeightedClasses.StripData Associated)
  (h : ℝ) (gap : ℕ → ℕ) (n i : ℕ)
  (H : PhysicalResidualNaturality.BandCoherence D h (ChartScales.Q_pos n)
    (ChartScales.Q_pos D.reference.band) i (gap n) n)
  (hn : PhysicalResidualNaturality.PositiveSupport D.carrierBlock D.gaussianInput D.aliasInput n)
  (hr : PhysicalResidualNaturality.PositiveSupport D.carrierBlock D.gaussianInput D.aliasInput D.reference.band)








end Band

/-! ## The literal finite harmonic block -/




section Assembly

variable (D : AssemblyData Parameter) (s : WeightedClasses.StripData Associated)
  (h : ℝ) (gap : ℕ → ℕ)

open CopyAngularInvariance





variable (n i : ℕ)
  (H : PhysicalResidualNaturality.BandCoherence D h (ChartScales.Q_pos n)
    (ChartScales.Q_pos D.reference.band) i (gap n) n)
  (hn : PhysicalResidualNaturality.PositiveSupport D.carrierBlock D.gaussianInput D.aliasInput n)
  (hr : PhysicalResidualNaturality.PositiveSupport D.carrierBlock D.gaussianInput D.aliasInput D.reference.band)



end Assembly

/-! ## Primitive frame matching -/


/-! ## One fixed Cartesian reference label -/

section Physical

open ProblemStatement PhysicalParticularWave

variable (D : AssemblyData Parameter) (s : WeightedClasses.StripData Associated)
  (h : ℝ) (gap : ℕ → ℕ) (n i : ℕ)
  (H : PhysicalResidualNaturality.BandCoherence D h (ChartScales.Q_pos n)
    (ChartScales.Q_pos D.reference.band) i (gap n) n)
  (hn : PhysicalResidualNaturality.PositiveSupport D.carrierBlock D.gaussianInput D.aliasInput n)
  (hr : PhysicalResidualNaturality.PositiveSupport D.carrierBlock D.gaussianInput D.aliasInput D.reference.band)
  (T : TargetChart D s h n i)
  {N : ℕ} {α κ : ℝ} (C : D.controls N α κ)
  (hstrip : D.strip = CorrectionStep.ParticularParameters.nativeStrip s)



end Physical

/-! ## The cycle's actual coordinate layout -/




section CyclePhysical

open ProblemStatement PhysicalParticularWave CyclePhysicalPrefixes

variable (D : AssemblyData Parameter) (s : WeightedClasses.StripData Associated)
  (h : ℝ) (gap : ℕ → ℕ) (n i : ℕ)
  (H : PhysicalResidualNaturality.BandCoherence D h (ChartScales.Q_pos n)
    (ChartScales.Q_pos D.reference.band) i (gap n) n)
  (hn : PhysicalResidualNaturality.PositiveSupport D.carrierBlock D.gaussianInput D.aliasInput n)
  (hr : PhysicalResidualNaturality.PositiveSupport D.carrierBlock D.gaussianInput D.aliasInput D.reference.band)
  (T : TargetChart D s h n i)
  {N : ℕ} {α κ : ℝ} (C : D.controls N α κ)
  (hstrip : D.strip = CorrectionStep.ParticularParameters.nativeStrip s)
  {I : ℕ} (hcover : i + gap n = I)
  (Href : ReferenceChart D h (ChartScales.Q D.reference.band) I)
  {U : Set Parameter} (hU : IsOpen U) (R : ∀ j ∈ modes N, ReferenceODE D j U)
  {delta : ℝ} (hdelta : 0 < delta) (chart : PolarCharts.Index)




end CyclePhysical

/-! ## Binding to the current cycle inputs -/

/-- These are equalities of the current input fields and primitive solver
data. There is no equality of a solved field in the interface. -/
structure CurrentInputs {ι : Type} (D : AssemblyData Parameter)
    (p : CorrectionStep.CycleParameters ι) (v : CorrectionStep.CycleCoefficients ι)
    (c : Context CorrectionStep.CyclePoint) (u : State CorrectionStep.CyclePoint)
    (l : ι) (h : ℝ) (gap : ℕ → ℕ) : Prop where
  context : D.context = StateReindex.context CorrectionStep.cycleAssoc.symm c
  state : D.state = StateReindex.state CorrectionStep.cycleAssoc.symm u
  carrier : D.carrierBlock = StateReindex.block CorrectionStep.cycleAssoc.symm (v.blocks l)
  gaussian : D.gaussianInput = StateReindex.blockCoefficients CorrectionStep.cycleAssoc.symm (v.gaussian l)
  aliasError : D.aliasInput = StateReindex.blockCoefficients CorrectionStep.cycleAssoc.symm (v.aliasCoefficients l)
  parameters : p.particular l = CorrectionStep.ParticularParameters.fromReference D h gap


/-! ## Full-variable transport of the curl correction -/

section FullVariable

variable {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Primitive spatial scaling on an open set. Angular differentiation has
unit scale and the two spatial directions have scale `l`. -/
structure SpatialScaling (Γ : E → F) (r : E → ℝ) (R : F → ℝ)
    (Sr Sθ Sz : E → E) (Vr Vθ Vz : F → F) (l : ℝ) (U : Set E) : Prop where
  isOpen : IsOpen U
  scale_ne : l ≠ 0
  radius_ne : ∀ x ∈ U, r x ≠ 0
  differentiable : ∀ x ∈ U, DifferentiableAt ℝ Γ x
  radial : ∀ x ∈ U, fderiv ℝ Γ x (Sr x) = l • Vr (Γ x)
  angular : ∀ x ∈ U, fderiv ℝ Γ x (Sθ x) = Vθ (Γ x)
  axial : ∀ x ∈ U, fderiv ℝ Γ x (Sz x) = l • Vz (Γ x)
  radius : ∀ x ∈ U, R (Γ x) = l * r x

variable {Γ : E → F} {r : E → ℝ} {R : F → ℝ}
  {Sr Sθ Sz : E → E} {Vr Vθ Vz : F → F} {l : ℝ} {U : Set E}
  (G : SpatialScaling Γ r R Sr Sθ Sz Vr Vθ Vz l U)
  {Φ : F → ℝ} {a : F → ComplexVector} {K L b : ℝ} (c : ℝ)
  (hK : K ≠ 0) (hb : b ≠ 0) (hKL : K * b = L)
  (hΦ : ∀ y ∈ U, DifferentiableAt ℝ Φ (Γ y))
  {x : E} (hx : x ∈ U)
  (hB : ∀ k, DifferentiableAt ℝ (fun y => coefficient R Vr Vθ Vz Φ a y k) (Γ x))

include G hK hb hKL hΦ hx hB



end FullVariable

namespace SpatialScaling

open PhysicalParticularWave


end SpatialScaling

section LiftedReference

open ProblemStatement PhysicalParticularWave

variable (D : AssemblyData Parameter) {h Qr : ℝ} {I : ℕ}
  (H : ReferenceChart D h Qr I) {j : ℤ} {α κ : ℝ}
  (C : LocalControl D.reference D.charts D.context D.state D.carrierBlock
    D.gaussianInput D.aliasInput j D.background D.copy D.strip D.directions α κ)




end LiftedReference

section FullBand

open ProblemStatement PhysicalParticularWave

variable (D : AssemblyData Parameter) {h Q Qr : ℝ} (hQ : 0 < Q) (hQr : 0 < Qr)
  (i gap : ℕ) (H : ReferenceChart D h Qr (i + gap)) {j : ℤ} {α κ : ℝ}
  (C : LocalControl D.reference D.charts D.context D.state D.carrierBlock
    D.gaussianInput D.aliasInput j D.background D.copy D.strip D.directions α κ)
  {K : ℝ} (hK : K ≠ 0) {U : Set Parameter} (hU : IsOpen U) (R : ReferenceODE D j U)


end FullBand





section ActualReferenceFields

open ProblemStatement PhysicalParticularWave

variable (D : AssemblyData Parameter) (s : WeightedClasses.StripData Associated)
  (h : ℝ) (gap : ℕ → ℕ) (n i : ℕ)
  (H : PhysicalResidualNaturality.BandCoherence D h (ChartScales.Q_pos n)
    (ChartScales.Q_pos D.reference.band) i (gap n) n)
  (hn : PhysicalResidualNaturality.PositiveSupport D.carrierBlock D.gaussianInput D.aliasInput n)
  (hr : PhysicalResidualNaturality.PositiveSupport D.carrierBlock D.gaussianInput D.aliasInput D.reference.band)
  (T : TargetChart D s h n i)
  (Href : ReferenceChart D h (ChartScales.Q D.reference.band) (i + gap n))
  {U : Set Parameter} (hU : IsOpen U)





end ActualReferenceFields

/-! ## Direct consumers for the current correction step -/

section CurrentCycle

open ProblemStatement PhysicalParticularWave CyclePhysicalPrefixes

variable {ι : Type} {D : AssemblyData Parameter}
  {p : CorrectionStep.CycleParameters ι} {v : CorrectionStep.CycleCoefficients ι}
  {c : Context CorrectionStep.CyclePoint} {u : State CorrectionStep.CyclePoint}
  {label : ι} {h : ℝ} {gap : ℕ → ℕ} (J : CurrentInputs D p v c u label h gap)
  (n i : ℕ)
  (H : PhysicalResidualNaturality.BandCoherence D h (ChartScales.Q_pos n)
    (ChartScales.Q_pos D.reference.band) i (gap n) n)
  (hn : PhysicalResidualNaturality.PositiveSupport D.carrierBlock D.gaussianInput D.aliasInput n)
  (hr : PhysicalResidualNaturality.PositiveSupport D.carrierBlock D.gaussianInput D.aliasInput D.reference.band)
  {α κ : ℝ} (C : D.controls v.residualBand α κ)



end CurrentCycle


section LocalIdentity

open ProblemStatement PhysicalParticularWave CyclePhysicalPrefixes

variable (D : AssemblyData Parameter) (s : WeightedClasses.StripData Associated)
  (h : ℝ) (gap : ℕ → ℕ) (n i : ℕ)
  (H : PhysicalResidualNaturality.BandCoherence D h (ChartScales.Q_pos n)
    (ChartScales.Q_pos D.reference.band) i (gap n) n)
  (hn : PhysicalResidualNaturality.PositiveSupport D.carrierBlock D.gaussianInput D.aliasInput n)
  (hr : PhysicalResidualNaturality.PositiveSupport D.carrierBlock D.gaussianInput D.aliasInput D.reference.band)
  (T : TargetChart D s h n i)
  {N : ℕ} {α κ : ℝ} (C : D.controls N α κ)
  (hstrip : D.strip = CorrectionStep.ParticularParameters.nativeStrip s)
  {I : ℕ} (hcover : i + gap n = I)
  (Href : ReferenceChart D h (ChartScales.Q D.reference.band) I)
  {U : Set Parameter} (hU : IsOpen U) (R : ∀ j ∈ modes N, ReferenceODE D j U)
  {delta : ℝ} (hdelta : 0 < delta) (chart : PolarCharts.Index)



end LocalIdentity

end NavierStokes.ActualParticularRealization
