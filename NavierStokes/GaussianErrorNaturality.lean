import NavierStokes.CorrectionStep

/-!
# Naturality of the actual Gaussian cutoff error

The error is the sum of differentiated-cutoff terms and the uncovered
source. Both terms are transported from their primitive data before the
copy sum is taken.
-/

noncomputable section

namespace NavierStokes.GaussianErrorNaturality

open Set Filter Function HarmonicCalculus LinearWaveBounds
open scoped Topology ContDiff

section CopyTransport

variable {D E I : Type} [NormedAddCommGroup D] [NormedSpace ℝ D]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem fast_cutoff_transport (Γ : D →L[ℝ] E)
    (d : GraphDirections D) (dr : GraphDirections E)
    (a : PeriodizedWaveBounds.CopyData D I) (b : PeriodizedWaveBounds.CopyData E I)
    (n nr : ℕ) (rate : ℝ) (i : I) (x : D)
    (hcutoff : a.cutoff n i = fun y => b.cutoff nr i (Γ y))
    (hfast : Γ (d.fastField n x) = rate • dr.fastField nr (Γ x))
    (hdiff : DifferentiableAt ℝ (b.cutoff nr i) (Γ x)) :
    d.Dfast (fun m => a.cutoff m i) n x =
      rate * dr.Dfast (fun m => b.cutoff m i) nr (Γ x) := by
  have hc := hdiff.hasFDerivAt.comp x Γ.hasFDerivAt
  simp only [Function.comp_def] at hc
  simp only [GraphDirections.Dfast, along, hcutoff, hc.fderiv,
    ContinuousLinearMap.comp_apply, hfast, map_smul, smul_eq_mul]

theorem cutoffSum_transport (Γ : D →L[ℝ] E)
    (a : PeriodizedWaveBounds.CopyData D I) (b : PeriodizedWaveBounds.CopyData E I)
    (n nr : ℕ) (x : D)
    (hcutoff : ∀ i, a.cutoff n i x = b.cutoff nr i (Γ x)) :
    a.cutoffSum n x = b.cutoffSum nr (Γ x) := by
  exact tsum_congr hcutoff

theorem localTail_transport (Γ : D →L[ℝ] E)
    (d : GraphDirections D) (dr : GraphDirections E)
    (a : PeriodizedWaveBounds.CopyData D I) (b : PeriodizedWaveBounds.CopyData E I)
    (n nr : ℕ) (rate c : ℝ) (i : I) (x : D)
    (hcutoff : a.cutoff n i = fun y => b.cutoff nr i (Γ y))
    (hfast : Γ (d.fastField n x) = rate • dr.fastField nr (Γ x))
    (hdiff : DifferentiableAt ℝ (b.cutoff nr i) (Γ x))
    (hamplitude : dr.Dfast (fun m => b.cutoff m i) nr (Γ x) ≠ 0 →
      a.amplitude n i x = c • b.amplitude nr i (Γ x)) :
    a.localTail d n i x = (rate * c) • b.localTail dr nr i (Γ x) := by
  unfold PeriodizedWaveBounds.CopyData.localTail
  rw [fast_cutoff_transport Γ d dr a b n nr rate i x hcutoff hfast hdiff]
  by_cases hz : dr.Dfast (fun m => b.cutoff m i) nr (Γ x) = 0
  · simp [hz]
  · rw [hamplitude hz, smul_smul, smul_smul]
    congr 1
    ring

/-- Only copies with a nonzero differentiated reference cutoff need an
amplitude comparison. No exterior continuation of a Volterra solve is assumed. -/
theorem globalTail_transport (Γ : D →L[ℝ] E)
    (d : GraphDirections D) (dr : GraphDirections E)
    (a : PeriodizedWaveBounds.CopyData D I) (b : PeriodizedWaveBounds.CopyData E I)
    (n nr : ℕ) (rate c : ℝ) (x : D)
    (hcutoff : ∀ i, a.cutoff n i = fun y => b.cutoff nr i (Γ y))
    (hfast : Γ (d.fastField n x) = rate • dr.fastField nr (Γ x))
    (hdiff : ∀ i, DifferentiableAt ℝ (b.cutoff nr i) (Γ x))
    (hamplitude : ∀ i, dr.Dfast (fun m => b.cutoff m i) nr (Γ x) ≠ 0 →
      a.amplitude n i x = c • b.amplitude nr i (Γ x)) :
    a.globalTail d n x = (rate * c) • b.globalTail dr nr (Γ x) := by
  change (∑' i, a.localTail d n i x) = (rate * c) • ∑' i, b.localTail dr nr i (Γ x)
  calc
    _ = ∑' i, (rate * c) • b.localTail dr nr i (Γ x) := tsum_congr fun i =>
      localTail_transport Γ d dr a b n nr rate c i x (hcutoff i) hfast (hdiff i) (hamplitude i)
    _ = _ := tsum_const_smul'' (rate * c)

/-- Full transport of the actual Gaussian error, including the source
on the part of the domain uncovered by native cutoffs. -/
theorem globalGaussian_transport (Γ : D →L[ℝ] E)
    (d : GraphDirections D) (dr : GraphDirections E)
    (a : PeriodizedWaveBounds.CopyData D I) (b : PeriodizedWaveBounds.CopyData E I)
    (n nr : ℕ) (rate c : ℝ) (x : D)
    (hcutoff : ∀ i, a.cutoff n i = fun y => b.cutoff nr i (Γ y))
    (hfast : Γ (d.fastField n x) = rate • dr.fastField nr (Γ x))
    (hdiff : ∀ i, DifferentiableAt ℝ (b.cutoff nr i) (Γ x))
    (hamplitude : ∀ i, dr.Dfast (fun m => b.cutoff m i) nr (Γ x) ≠ 0 →
      a.amplitude n i x = c • b.amplitude nr i (Γ x))
    (hsource : a.source n x = (rate * c) • b.source nr (Γ x)) :
    a.globalGaussian d n x = (rate * c) • b.globalGaussian dr nr (Γ x) := by
  rw [PeriodizedWaveBounds.CopyData.globalGaussian,
    globalTail_transport Γ d dr a b n nr rate c x hcutoff hfast hdiff hamplitude,
    cutoffSum_transport Γ a b n nr x (fun i => congrFun (hcutoff i) x), hsource]
  simp only [PeriodizedWaveBounds.CopyData.globalGaussian, smul_add, smul_smul]
  congr 1
  congr 1
  ring

end CopyTransport

section ReferenceData

open CommonCoverSolve TorusInverse ParticularWaveAssembly ParticularWaveBounds
open CorrectionState

abbrev Parameter := PhysicalParticularWave.Parameter
abbrev WaveSpace := PhysicalParticularWave.WaveSpace
abbrev Cylinder := PhysicalParticularWave.Cylinder

/-- The full native change of variables, conjugate to the actual
cylindrical change of band and common cover. -/
noncomputable def waveChange (h Q Qr : ℝ) (gap : ℕ) : WaveSpace →L[ℝ] WaveSpace :=
  PhysicalParticularWave.waveEquiv.toContinuousLinearEquiv.toContinuousLinearMap.comp
    ((PhysicalParticularWave.cylinderChange h Q Qr gap).comp
      PhysicalParticularWave.waveEquiv.symm.toContinuousLinearEquiv.toContinuousLinearMap)

@[simp] theorem waveChange_apply (h Q Qr : ℝ) (gap : ℕ) (x : WaveSpace) :
    waveChange h Q Qr gap x =
      ((PhysicalParticularWave.parameterChange h Q Qr x.1.1, x.1.2), coverPower gap x.2) := rfl

theorem waveChange_waveEquiv (h Q Qr : ℝ) (gap : ℕ) (x : Cylinder) :
    waveChange h Q Qr gap (PhysicalParticularWave.waveEquiv x) =
      PhysicalParticularWave.waveEquiv (PhysicalParticularWave.cylinderChange h Q Qr gap x) := rfl


noncomputable def nativeData (D : AssemblyData Parameter) (h : ℝ) (gap : ℕ → ℕ) (j : ℤ) :
    PeriodizedWaveBounds.CopyData WaveSpace Frequency :=
  (CorrectionStep.ParticularParameters.fromReference D h gap).copyData
    D.context D.state D.carrierBlock D.gaussianInput D.aliasInput j


theorem copyData_amplitude (p : CorrectionStep.ParticularParameters Parameter)
    (C : Context (Parameter × Plane)) (u : State (Parameter × Plane))
    (b : HarmonicBlock (Parameter × Plane))
    (G A : HarmonicResidual.BlockCoefficients (Parameter × Plane))
    (j : ℤ) (n : ℕ) (copy : Frequency) (x : WaveSpace) :
    (p.copyData C u b G A j).amplitude n copy x =
      complexCopyVelocity (p.tangent j n) (residualSource C u b G A j n)
        (p.geometry n) (p.length_pos n).le copy (x.1.1, x.2) :=
  complexCopyVelocity_angle (p.tangent j n) (residualSource C u b G A j n)
    (p.geometry n) (p.length_pos n).le copy x.1.1 x.1.2 x.2



/-- A nonzero actual directional derivative is supported in any closed
set supporting the original cutoff. -/
theorem along_ne_zero_mem_closed {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : E → ℝ} {K : Set E} (hK : IsClosed K) (hf : support f ⊆ K)
    (V : E → E) {x : E} (hx : along V f x ≠ 0) : x ∈ K := by
  have hd : x ∈ support (fderiv ℝ f) := by
    intro hz
    apply hx
    simp only [along, hz, _root_.zero_apply]
  exact (closure_minimal hf hK) (support_fderiv_subset ℝ hd)



theorem interval_congr {E : Type} (F : (a b : ℝ) → a ≤ b → E)
    {a b c d : ℝ} (hab : a ≤ b) (hcd : c ≤ d) (ha : a = c) (hb : b = d) :
    F a b hab = F c d hcd := by
  subst_vars
  rfl

theorem complexCopyVelocity_zeroEntry
    (t : TangentData Parameter ProblemStatement.Space) (f : Parameter × Plane → ComplexVector)
    (parameter : Parameter → Parameter) (g : Geometry) (gap : ℕ)
    (L rate amplitude normalScale : ℝ) (hL : 0 < L) (hrate : 0 < rate) (hnormal : normalScale ≠ 0)
    {U : Set Parameter} (hA : ContinuousOn t.linearData.coefficient (U ×ˢ univ))
    (hB : ContinuousOn t.linearData.forcingMap (U ×ˢ univ))
    (hf : ContinuousOn f (U ×ˢ univ)) (q : Parameter) (hq : parameter q ∈ U)
    (copy : Frequency) (Y : Plane)
    (hslot : ((CopySolveCompatibility.transportGeometry g gap 0 rate hrate.ne').coordinates copy Y).2 ∈
      Icc 0 (L / rate)) :
    complexCopyVelocity (ScaledTangentTransport.transportTangent t parameter gap 0 rate amplitude normalScale)
      (ScaledTangentTransport.transportSource f parameter gap rate amplitude)
      (CopySolveCompatibility.transportGeometry g gap 0 rate hrate.ne') (div_pos hL hrate).le copy (q, Y) =
        amplitude • complexCopyVelocity t f g hL.le copy (parameter q, coverPower gap Y) := by
  have he := ScaledTangentTransport.complexCopyVelocity_transport t f parameter g (div_pos hL hrate).le
    gap 0 rate amplitude normalScale hrate hnormal hA hB hf q hq copy Y hslot
  refine he.trans (congrArg (fun z : ComplexVector => amplitude • z) ?_)
  apply interval_congr (fun a b hab => complexCopyVelocity t f g (a := a) (b := b) hab
    copy (parameter q, coverPower gap Y)) _ _ (by ring)
  field_simp ; simp

end ReferenceData

section ActualReference

open CommonCoverSolve TorusInverse ParticularWaveAssembly ParticularWaveBounds
open CorrectionState PhysicalParticularWave






end ActualReference

section HarmonicAssembly

open CommonCoverSolve TorusInverse ParticularWaveAssembly ParticularWaveBounds
open CorrectionState PhysicalParticularWave
open scoped BigOperators




end HarmonicAssembly

end NavierStokes.GaussianErrorNaturality
