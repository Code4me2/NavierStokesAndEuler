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
abbrev Cylinder := PhysicalParticularWave.Cylinder

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

noncomputable def raw (D : AssemblyData Parameter) (h : ℝ) (gap : ℕ → ℕ) (j : ℤ) :
    LinearWaveBounds.WaveCoefficients WaveSpace :=
  ((CorrectionStep.ParticularParameters.fromReference D h gap).copyData
    D.context D.state D.carrierBlock D.gaussianInput D.aliasInput j).common

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

noncomputable def block (D : AssemblyData Parameter) (s : WeightedClasses.StripData Associated)
    (h : ℝ) (gap : ℕ → ℕ) (N : ℕ) : HarmonicBlock Associated :=
  (CorrectionStep.ParticularParameters.fromReference D h gap).updateBlock s
    D.context D.state D.carrierBlock D.gaussianInput D.aliasInput N



section Assembly

variable (D : AssemblyData Parameter) (s : WeightedClasses.StripData Associated)
  (h : ℝ) (gap : ℕ → ℕ)

open CopyAngularInvariance

theorem corrected_amplitude_invariant (j : ℤ)
    (B : BackgroundControl (CorrectionStep.ParticularParameters.nativeStrip s)
      D.directions D.background D.carrierBlock j) (n : ℕ) :
    Invariant (((0 : Parameter), (1 : ℝ)), (0 : Plane))
      ((corrected D s h gap j).amplitude n) := by
  have ha : Invariant D.directions.angular ((raw D h gap j).amplitude n) := by
    rw [B.angular]
    change Invariant _ (((CorrectionStep.ParticularParameters.fromReference D h gap).copyData
      D.context D.state D.carrierBlock D.gaussianInput D.aliasInput j).common.amplitude n)
    rw [CorrectionStep.ParticularParameters.common_amplitude]
    exact angleLift_invariant _
  have hphi := actualCarrier_affine D.background D.carrierBlock j n
  rw [← B.angular] at hphi ⊢
  exact realizedCoefficient_invariant (B.radius_invariant n) (B.radial_invariant n)
    (Invariant.const _) (B.axial_invariant n) hphi ha ((j : ℝ) * D.carrierBlock.frequency n)

theorem corrected_pressure_invariant {n : ℕ} (j : ℤ)
    (hK : (j : ℝ) * D.carrierBlock.frequency n ≠ 0) :
    Invariant (((0 : Parameter), (1 : ℝ)), (0 : Plane))
      ((corrected D s h gap j).pressure n) := by
  change Invariant _ (((CorrectionStep.ParticularParameters.fromReference D h gap).copyData
    D.context D.state D.carrierBlock D.gaussianInput D.aliasInput j).common.pressure n)
  rw [CorrectionStep.ParticularParameters.common_pressure _ _ _ _ _ _ _ _ hK]
  exact angleLift_invariant _

theorem block_velocity_represents {N : ℕ}
    (B : ∀ j ∈ modes N, BackgroundControl (CorrectionStep.ParticularParameters.nativeStrip s)
      D.directions D.background D.carrierBlock j)
    (hf : ∀ m, D.carrierBlock.frequency m ≠ 0) (n : ℕ) (x : Associated × ℝ) (k : Fin 3) :
    (block D s h gap N).oscillation n x k =
      ∑ j ∈ modes N, (vectorMode ((corrected D s h gap j).frequency n)
        ((corrected D s h gap j).phase n) ((corrected D s h gap j).amplitude n)
          (angleShuffle x) k).re := by
  rw [block, CorrectionStep.ParticularParameters.updateBlock, assembledBlock_value]
  apply Finset.sum_congr rfl
  intro j hj
  have hi := invariant_angleShuffle (corrected_amplitude_invariant D s h gap j (B j hj) n) x.1 x.2
  change Complex.re (_ * _) = ((corrected D s h gap j).amplitude n (angleShuffle x) k *
    carrier ((actualCarrier D.background D.carrierBlock j).frequency n)
      ((actualCarrier D.background D.carrierBlock j).phase n) (angleShuffle x)).re
  rw [actualCarrier_character D.background D.carrierBlock j hf n x, hi]
  rfl

theorem block_pressure_represents {N : ℕ}
    (hj : ∀ j ∈ modes N, j ≠ 0) (hf : ∀ m, D.carrierBlock.frequency m ≠ 0)
    (n : ℕ) (x : Associated × ℝ) :
    (block D s h gap N).oscillatoryPressure n x =
      ∑ j ∈ modes N, (mode ((corrected D s h gap j).frequency n)
        ((corrected D s h gap j).phase n) ((corrected D s h gap j).pressure n) (angleShuffle x)).re := by
  rw [block, CorrectionStep.ParticularParameters.updateBlock, assembledBlock_pressure_value]
  apply Finset.sum_congr rfl
  intro j hmem
  have hK : (j : ℝ) * D.carrierBlock.frequency n ≠ 0 :=
    mul_ne_zero (by exact_mod_cast hj j hmem) (hf n)
  have hi := invariant_angleShuffle (corrected_pressure_invariant D s h gap j hK) x.1 x.2
  change Complex.re (_ * _) = ((corrected D s h gap j).pressure n (angleShuffle x) *
    carrier ((actualCarrier D.background D.carrierBlock j).frequency n)
      ((actualCarrier D.background D.carrierBlock j).phase n) (angleShuffle x)).re
  rw [actualCarrier_character D.background D.carrierBlock j hf n x, hi]
  rfl

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

noncomputable def cycleBlock (D : AssemblyData Parameter) (s : WeightedClasses.StripData Associated)
    (h : ℝ) (gap : ℕ → ℕ) (N : ℕ) : HarmonicBlock CorrectionStep.CyclePoint :=
  StateReindex.block CorrectionStep.cycleAssoc (block D s h gap N)



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

theorem CurrentInputs.particularBlock {ι : Type} {D : AssemblyData Parameter}
    {p : CorrectionStep.CycleParameters ι} {v : CorrectionStep.CycleCoefficients ι}
    {c : Context CorrectionStep.CyclePoint} {u : State CorrectionStep.CyclePoint}
    {l : ι} {h : ℝ} {gap : ℕ → ℕ} (J : CurrentInputs D p v c u l h gap) :
    p.particularBlock v c u l = cycleBlock D
      (reindexStrip CorrectionStep.cycleAssoc.symm p.strip) h gap v.residualBand := by
  unfold CorrectionStep.CycleParameters.particularBlock cycleBlock block
  rw [J.parameters, J.context, J.state, J.carrier, J.gaussian, J.aliasError]

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

/-- The Cartesian image of the actual common-chart domain and valid
polar branch; no extension of the raw formulas beyond this set is used. -/
noncomputable def physicalDomain (D : AssemblyData Parameter) (h : ℝ) (n i gap : ℕ)
    (U : Set Parameter) (delta : ℝ) (chart : PolarCharts.Index) : Set ProblemStatement.SpaceTime :=
  (fun z : ProblemStatement.SpaceTime => (z.1, CylindricalResidual.chart z.2)) ''
    ((PhysicalResidualBridge.commonGraph (ChartScales.Q n) h i).source
      (PhysicalParticularWave.bandDomain D h (ChartScales.Q n) (ChartScales.Q D.reference.band) gap U) ∩
        PhysicalCurlCovariance.validCylindrical delta chart)

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
