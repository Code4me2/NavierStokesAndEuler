import NavierStokes.LocalSignedRequest
import NavierStokes.PhysicalParticularWave
import NavierStokes.PrimaryFieldAssembly
import NavierStokes.PhysicalResidualNaturality
import NavierStokes.PeriodicPhaseAssembly

/-!
# Signed quotient waves from one physical primary reference

The signed numerator is the actual current-state stress request.  All
band views use the same absolute-lift primary pulse and covariance
matrix.  Compatibility is proved before restriction to a physical graph.
-/

noncomputable section

namespace NavierStokes.PhysicalSignedWave

open Set Function Filter Matrix HarmonicCalculus WeightedClasses
open ProblemStatement CommonCoverSolve TorusInverse
open scoped ContDiff Topology InnerProductSpace BigOperators

abbrev Mat2 := SmoothCovariance.Mat2
abbrev Vec2 := SmoothCovariance.Vec2
abbrev Point := LocalSignedRequest.Point
abbrev Cylinder := PhysicalResidualBridge.Cylinder

noncomputable def fastTranslate (x : Cylinder) (k : TorusInverse.Frequency) : Cylinder :=
  ((x.1.1, (x.1.2.1, x.1.2.2 + TorusAverages.latticePoint k)), x.2)

section QuotientAlgebra

theorem weights_smul_target (H : Mat2) (T : Vec2) (a : ℝ) :
    SmoothCovariance.weights H (a • T) = a • SmoothCovariance.weights H T := by
  ext j
  fin_cases j <;> simp [SmoothCovariance.weights, SmoothCovariance.cramerNumerator, smul_eq_mul] <;> ring

theorem inverse_smul_target (H : Mat2) (T : Vec2) (a : ℝ) :
    H⁻¹.mulVec (a • T) = a • H⁻¹.mulVec T := by
  ext j
  simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two, Pi.smul_apply, smul_eq_mul]
  ring

theorem amplitudes_square_scale (H : Mat2) (T : Vec2) {a : ℝ} (ha : 0 ≤ a) :
    SmoothCovariance.amplitudes H (a ^ 2 • T) = a • SmoothCovariance.amplitudes H T := by
  ext j
  simp only [SmoothCovariance.amplitudes, weights_smul_target, Pi.smul_apply, smul_eq_mul]
  rw [Real.sqrt_mul (sq_nonneg a), Real.sqrt_sq ha]

/-- Both the signed numerator and the original primary target acquire the
same squared scale.  The quotient is therefore multiplied by the positive
scale, including points where its totalized denominator is zero. -/
theorem increment_square_scale (H : Mat2) (T R : Vec2) {a : ℝ} (ha : 0 < a) (j : Fin 2) :
    SignedCovariance.increment H (a ^ 2 • T) (a ^ 2 • R) j =
      a * SignedCovariance.increment H T R j := by
  simp only [SignedCovariance.increment, inverse_smul_target,
    amplitudes_square_scale H T ha.le, Pi.smul_apply, smul_eq_mul]
  by_cases hb : SmoothCovariance.amplitudes H T j = 0
  · simp only [hb, mul_zero, div_zero]
  · field_simp

noncomputable def coefficientScale (epsilon referenceEpsilon velocityScale : ℝ) : ℝ :=
  velocityScale * Real.sqrt referenceEpsilon / Real.sqrt epsilon

theorem coefficientScale_pos {epsilon referenceEpsilon velocityScale : ℝ}
    (he : 0 < epsilon) (hr : 0 < referenceEpsilon) (hv : 0 < velocityScale) :
    0 < coefficientScale epsilon referenceEpsilon velocityScale :=
  div_pos (mul_pos hv (Real.sqrt_pos.mpr hr)) (Real.sqrt_pos.mpr he)

theorem coefficientScale_square {epsilon referenceEpsilon velocityScale : ℝ}
    (he : 0 < epsilon) (hr : 0 ≤ referenceEpsilon) :
    coefficientScale epsilon referenceEpsilon velocityScale ^ 2 =
      velocityScale ^ 2 * referenceEpsilon / epsilon := by
  unfold coefficientScale
  rw [div_pow, mul_pow, Real.sq_sqrt hr, Real.sq_sqrt he.le]

theorem sqrt_mul_coefficientScale {epsilon referenceEpsilon velocityScale : ℝ}
    (he : 0 < epsilon) :
    Real.sqrt epsilon * coefficientScale epsilon referenceEpsilon velocityScale =
      velocityScale * Real.sqrt referenceEpsilon := by
  unfold coefficientScale
  field_simp

/-- The primary square root and the signed inverse quotient have exactly
the same velocity scaling.  The matrix and column are unchanged. -/
theorem primary_scalar_scale (H : Mat2) (T : Vec2) (mask : ℝ)
    {epsilon referenceEpsilon velocityScale : ℝ}
    (he : 0 < epsilon) (hr : 0 < referenceEpsilon) (hv : 0 < velocityScale) (j : Fin 2) :
    PartitionedCovariance.amplitude epsilon mask H
      (coefficientScale epsilon referenceEpsilon velocityScale ^ 2 • T) j =
      velocityScale * PartitionedCovariance.amplitude referenceEpsilon mask H T j := by
  unfold PartitionedCovariance.amplitude
  rw [amplitudes_square_scale H T (coefficientScale_pos he hr hv).le]
  simp only [Pi.smul_apply, smul_eq_mul]
  have h := sqrt_mul_coefficientScale (referenceEpsilon := referenceEpsilon)
    (velocityScale := velocityScale) he
  calc
    _ = (Real.sqrt epsilon * coefficientScale epsilon referenceEpsilon velocityScale) *
        SmoothCovariance.amplitudes H T j * mask := by ring
    _ = _ := by rw [h]; ring

theorem signed_scalar_scale (H : Mat2) (T R : Vec2) (mask : ℝ)
    {epsilon referenceEpsilon velocityScale : ℝ}
    (he : 0 < epsilon) (hr : 0 < referenceEpsilon) (hv : 0 < velocityScale) (j : Fin 2) :
    Real.sqrt epsilon * SignedCovariance.increment H
      (coefficientScale epsilon referenceEpsilon velocityScale ^ 2 • T)
      (coefficientScale epsilon referenceEpsilon velocityScale ^ 2 • R) j * mask =
      velocityScale * (Real.sqrt referenceEpsilon * SignedCovariance.increment H T R j * mask) := by
  rw [increment_square_scale H T R (coefficientScale_pos he hr hv)]
  have h := sqrt_mul_coefficientScale (referenceEpsilon := referenceEpsilon)
    (velocityScale := velocityScale) he
  calc
    _ = (Real.sqrt epsilon * coefficientScale epsilon referenceEpsilon velocityScale) *
        SignedCovariance.increment H T R j * mask := by ring
    _ = _ := by rw [h]; ring

/-- With request twice the target, the literal signed quotient is exactly
the primary square root. This also holds at totalized zero denominators. -/
theorem increment_twice_target (H : Mat2) (T : Vec2) (j : Fin 2) :
    SignedCovariance.increment H T ((2 : ℝ) • T) j = SmoothCovariance.amplitudes H T j := by
  by_cases hd : H.det = 0
  · have hi : H⁻¹ = 0 := Matrix.nonsing_inv_apply_not_isUnit H (by simp [hd])
    simp [SignedCovariance.increment, hi, SmoothCovariance.amplitudes,
      SmoothCovariance.weights, hd]
  · rw [SignedCovariance.increment, inverse_smul_target,
      SmoothCovariance.inverse_formula H T hd]
    simp only [Pi.smul_apply, smul_eq_mul, SmoothCovariance.amplitudes]
    by_cases hw : 0 ≤ SmoothCovariance.weights H T j
    · by_cases hz : SmoothCovariance.weights H T j = 0
      · simp [hz]
      · have hp : 0 < SmoothCovariance.weights H T j := lt_of_le_of_ne hw (Ne.symm hz)
        apply (div_eq_iff (mul_ne_zero (by norm_num) (Real.sqrt_pos.mpr hp).ne')).2
        nlinarith [Real.sq_sqrt hw]
    · rw [Real.sqrt_eq_zero_of_nonpos (le_of_not_ge hw)]
      simp

end QuotientAlgebra

/-! ## A concrete periodic reference phase with native clock germs -/

structure ReferencePhase where
  geometry : CommonCoverSolve.Geometry
  window : PeriodicPhaseAssembly.ClockWindow
  epsilon : ℝ
  axialFrequency : ℝ
  radialFrequency : ℝ
  angularMode : ℤ
  F : PeriodicPhaseAssembly.Parameter → ℝ
  G : PeriodicPhaseAssembly.Parameter → ℝ

namespace ReferencePhase

variable (C : ReferencePhase)

noncomputable def phase (K : ℝ) (x : Cylinder) : ℝ :=
  PeriodicPhaseAssembly.angularLift
    (PeriodicPhaseAssembly.profilePhase C.geometry C.window.cutoff C.epsilon
      (C.angularMode / K) C.axialFrequency C.radialFrequency C.F C.G)
    (C.angularMode / K) (PhysicalParticularWave.waveEquiv x)

noncomputable def nativePhase (K : ℝ) (copy : TorusInverse.Frequency) (x : Cylinder) : ℝ :=
  PhaseCalculus.phase C.epsilon (C.angularMode / K) C.axialFrequency C.radialFrequency
    (fun p => C.F (p.1, (p.2.2, p.2.1))) (fun p => C.G (p.1, (p.2.2, p.2.1)))
    ((x.1.1, x.1.2.1), (x.2, (C.geometry.coordinates copy x.1.2.2).2))


theorem phase_periodic (K : ℝ) (x : Cylinder) (k : TorusInverse.Frequency) :
    C.phase K (fastTranslate x k) = C.phase K x := by
  exact PeriodicPhaseAssembly.fullPhase_periodic C.geometry C.window.cutoff
    (PeriodicPhaseAssembly.profileIntercept C.epsilon C.axialFrequency C.radialFrequency)
    (PeriodicPhaseAssembly.profileRate (C.angularMode / K) C.axialFrequency C.F C.G)
    (C.angularMode / K) (x.1.1, (x.1.2.1.2, x.1.2.1.1)) x.2 x.1.2.2 k



theorem phase_smooth (K : ℝ) (hF : ContDiff ℝ ∞ C.F) (hG : ContDiff ℝ ∞ C.G) :
    ContDiff ℝ ∞ (C.phase K) := by
  apply (PeriodicPhaseAssembly.angularLift_contDiff ?_ _).comp
    PhysicalParticularWave.waveEquiv.contDiff
  exact PeriodicPhaseAssembly.phase_contDiff C.geometry C.window
    ((contDiff_const.mul contDiff_snd.snd).add (contDiff_const.mul contDiff_fst))
    ((contDiff_const.mul hF).add (contDiff_const.mul hG))

noncomputable def base (a : LinearWaveBounds.WaveCoefficients Cylinder) :
    LinearWaveBounds.WaveCoefficients Cylinder :=
  { a with phase := fun n => C.phase (a.frequency n) }

end ReferencePhase

section ActualRequest

/-- The primitive is taken from the actual current-state residual on
every radius and fast coordinate of the stated slow fiber.  Graph-only
agreement is not used in this theorem. -/
theorem fullRequest_chart (s sr : StripData Point) (P : SignedStressPrimitive.Patch)
    (coord coordr : ℝ) (c cr : CorrectionState.Context Point)
    (u ur : CorrectionState.State Point) (n nr : ℕ)
    {l : ℝ} (hl : 0 < l) (C : LocalSignedRequest.Plane →L[ℝ] LocalSignedRequest.Plane)
    (gap : ℕ) (sourceScale : ℝ) (t : LocalSignedRequest.Plane)
    (hq : 0 < SimilarityCoordinates.coordinateQ coord t)
    {V : Set LocalSignedRequest.Plane} (hV : IsOpen V) (ht : C t ∈ V)
    (hθ : ContDiffOn ℝ ∞ (ur.thetaResidual cr nr) (PhysicalMeanDomain.slowDomain V))
    (hz : ContDiffOn ℝ ∞ (ur.axialResidual cr nr) (PhysicalMeanDomain.slowDomain V))
    (hpθ : PhysicalMeanDomain.PeriodicOn V (ur.thetaResidual cr nr))
    (hpz : PhysicalMeanDomain.PeriodicOn V (ur.axialResidual cr nr))
    (hlength : Real.sqrt (SimilarityCoordinates.coordinateQ coordr (C t)) =
      l * Real.sqrt (SimilarityCoordinates.coordinateQ coord t))
    (heθ : ∀ r Y, u.thetaResidual c n (r, (t, Y)) =
      sourceScale * ur.thetaResidual cr nr (l * r, (C t, TemporalMeanUpdate.coverMap gap Y)))
    (hez : ∀ r Y, u.axialResidual c n (r, (t, Y)) =
      sourceScale * ur.axialResidual cr nr (l * r, (C t, TemporalMeanUpdate.coverMap gap Y)))
    (r : ℝ) (Y : LocalSignedRequest.Plane) (angle : ℝ) :
    LocalSignedRequest.fullRequest s P coord c u n ((r, (t, Y)), angle) =
      (sourceScale / l * sr.epsilon nr / s.epsilon n) •
        LocalSignedRequest.fullRequest sr P coordr cr ur nr
          ((l * r, (C t, TemporalMeanUpdate.coverMap gap Y)), angle) := by
  have h1 := LocalSignedRequest.physicalBarSigma_chart P 2 hl hq C gap sourceScale
    hV ht hθ hpθ hlength heθ r
  have h2 := LocalSignedRequest.physicalBarSigma_chart P 1 hl hq C gap sourceScale
    hV ht hz hpz hlength hez r
  have hn := (s.epsilon_pos n).ne'
  have hr := (sr.epsilon_pos nr).ne'
  ext j
  fin_cases j
  · simp [LocalSignedRequest.fullRequest, LocalSignedRequest.normalizedRequest,
    LocalSignedRequest.requestedStress, smul_eq_mul, h1] ;
    field_simp [hl.ne']
  · simp [LocalSignedRequest.fullRequest, LocalSignedRequest.normalizedRequest,
    LocalSignedRequest.requestedStress, smul_eq_mul, h2] ;
    field_simp [hl.ne']

theorem source_over_radial {Q Qr : ℝ} (hQ : 0 < Q) (hQr : 0 < Qr) (h : ℝ) :
    PhysicalParticularWave.sourceWeight h Q Qr / PhysicalParticularWave.ratioPower Q Qr (1 / 2) =
      PhysicalParticularWave.velocityWeight h Q Qr ^ 2 := by
  unfold PhysicalParticularWave.sourceWeight PhysicalParticularWave.velocityWeight
  rw [PhysicalParticularWave.ratioPower_div hQ hQr, pow_two,
    PhysicalParticularWave.ratioPower_mul hQ hQr]
  congr 1
  ring

theorem physical_request_factor {Q Qr epsilon referenceEpsilon : ℝ}
    (hQ : 0 < Q) (hQr : 0 < Qr) (he : 0 < epsilon) (hr : 0 ≤ referenceEpsilon) (h : ℝ) :
    (PhysicalParticularWave.sourceWeight h Q Qr /
      PhysicalParticularWave.ratioPower Q Qr (1 / 2)) * referenceEpsilon / epsilon =
      coefficientScale epsilon referenceEpsilon (PhysicalParticularWave.velocityWeight h Q Qr) ^ 2 := by
  rw [coefficientScale_square he hr, source_over_radial hQ hQr]

end ActualRequest

/-! ## The actual current-state request on the full free lift -/

noncomputable def slowChange (h Q Qr : ℝ) : LocalSignedRequest.Plane →L[ℝ] LocalSignedRequest.Plane :=
  ((PhysicalParticularWave.ratioPower Q Qr 1) • ContinuousLinearMap.id ℝ ℝ).prodMap
    ((PhysicalParticularWave.ratioPower Q Qr (CoordinateAlgebra.D h)) • ContinuousLinearMap.id ℝ ℝ)

noncomputable def requestChart (h : ℝ) {Q Qr : ℝ} (hQ : 0 < Q) (hQr : 0 < Qr)
    (gap : ℕ) : Point ≃L[ℝ] Point :=
  (PhysicalResidualTZ.swapSlow.toContinuousLinearEquiv.trans
    (PhysicalResidualNaturality.chartEquiv h hQ hQr gap)).trans
      PhysicalResidualTZ.swapSlow.toContinuousLinearEquiv

theorem requestChart_apply (h : ℝ) {Q Qr : ℝ} (hQ : 0 < Q) (hQr : 0 < Qr)
    (gap : ℕ) (x : Point) :
    requestChart h hQ hQr gap x =
      (PhysicalParticularWave.ratioPower Q Qr (1 / 2) * x.1,
        (slowChange h Q Qr x.2.1, TemporalMeanUpdate.coverMap gap x.2.2)) := by
  rw [MeanChartCompatibility.coverMap_eq_coverPower]
  rfl

theorem ratioPower_eq_div_rpow {Q Qr : ℝ} (hQ : 0 < Q) (hQr : 0 < Qr) (p : ℝ) :
    PhysicalParticularWave.ratioPower Q Qr p = (Q / Qr) ^ p := by
  exact (Real.div_rpow hQ.le hQr.le p).symm

theorem slowChange_coordinateQ {h Q Qr : ℝ} (hh : 0 < h) (hh1 : h < 1 / 2)
    (hQ : 0 < Q) (hQr : 0 < Qr) {t : LocalSignedRequest.Plane} (ht : 0 < t.1) :
    SimilarityCoordinates.coordinateQ (2 * h) (slowChange h Q Qr t) =
      (Q / Qr) * SimilarityCoordinates.coordinateQ (2 * h) t := by
  have he := SimilarityHomogeneity.coordinateQ_scale_h hh hh1 (div_pos hQ hQr) ht (z := t.2)
  change SimilarityCoordinates.coordinateQ (2 * h)
      (PhysicalParticularWave.ratioPower Q Qr 1 * t.1,
        PhysicalParticularWave.ratioPower Q Qr (CoordinateAlgebra.D h) * t.2) = _
  simpa only [ratioPower_eq_div_rpow hQ hQr, Real.rpow_one] using he

theorem slowChange_length {h Q Qr : ℝ} (hh : 0 < h) (hh1 : h < 1 / 2)
    (hQ : 0 < Q) (hQr : 0 < Qr) {t : LocalSignedRequest.Plane} (ht : 0 < t.1) :
    Real.sqrt (SimilarityCoordinates.coordinateQ (2 * h) (slowChange h Q Qr t)) =
      PhysicalParticularWave.ratioPower Q Qr (1 / 2) *
        Real.sqrt (SimilarityCoordinates.coordinateQ (2 * h) t) := by
  rw [slowChange_coordinateQ hh hh1 hQ hQr ht, Real.sqrt_mul (div_pos hQ hQr).le,
    Real.sqrt_eq_rpow, ratioPower_eq_div_rpow hQ hQr]

/-- The strip and input coordinates are moved together. Its epsilon is
definitionally the epsilon of the same full-angle wave strip. -/
noncomputable def stateStrip (s : StripData Cylinder) : StripData Point :=
  SignedWaveUpdate.sectionStrip (ParticularWaveBounds.reindexStrip PhysicalResidualTZ.swapCylinder s)

noncomputable def stateRequest (s : StripData Cylinder) (P : SignedStressPrimitive.Patch)
    (h : ℝ) (c : CorrectionState.Context Point) (u : CorrectionState.State Point) :
    ℕ → Cylinder → Vec2 :=
  fun n x => LocalSignedRequest.fullRequest (stateStrip s) P (2 * h) c u n
    (PhysicalResidualTZ.swapCylinder x)

theorem stateRequest_invariant (s : StripData Cylinder) (P : SignedStressPrimitive.Patch)
    (h : ℝ) (c : CorrectionState.Context Point) (u : CorrectionState.State Point) (n : ℕ) :
    CopyAngularInvariance.Invariant (0, 1) (stateRequest s P h c u n) := by
  intro x t
  simp [stateRequest, LocalSignedRequest.fullRequest, PhysicalResidualTZ.swapCylinder_apply]

/-- Naturality of the actual request is a consequence of primitive
current-state and background coherence on an open free-lift neighborhood
containing the whole integration fiber. No residual or quotient
compatibility is a hypothesis. -/
theorem fullRequest_of_state (s sr : StripData Point) (P : SignedStressPrimitive.Patch)
    {h Q Qr : ℝ} (hh : 0 < h) (hh1 : h < 1 / 2) (hQ : 0 < Q) (hQr : 0 < Qr)
    (c cr : CorrectionState.Context Point) (u ur : CorrectionState.State Point)
    (n nr gap : ℕ) {W : Set Point} (hW : IsOpen W)
    (H : PhysicalResidualNaturality.StateOn W (requestChart h hQ hQr gap)
      (PhysicalParticularWave.velocityWeight h Q Qr)
      (PhysicalParticularWave.ratioPower Q Qr (1 / 2)) u ur n nr)
    (G : PhysicalResidualNaturality.ContextOn W (requestChart h hQ hQr gap)
      (PhysicalParticularWave.velocityWeight h Q Qr)
      (PhysicalParticularWave.ratioPower Q Qr (1 / 2)) c cr n nr)
    (t : LocalSignedRequest.Plane) (ht : 0 < t.1)
    (hfiber : ∀ r Y, (r, (t, Y)) ∈ W)
    {V : Set LocalSignedRequest.Plane} (hV : IsOpen V) (htV : slowChange h Q Qr t ∈ V)
    (hθ : ContDiffOn ℝ ∞ (ur.thetaResidual cr nr) (PhysicalMeanDomain.slowDomain V))
    (hz : ContDiffOn ℝ ∞ (ur.axialResidual cr nr) (PhysicalMeanDomain.slowDomain V))
    (hpθ : PhysicalMeanDomain.PeriodicOn V (ur.thetaResidual cr nr))
    (hpz : PhysicalMeanDomain.PeriodicOn V (ur.axialResidual cr nr))
    (r : ℝ) (Y : LocalSignedRequest.Plane) (angle : ℝ) :
    LocalSignedRequest.fullRequest s P (2 * h) c u n ((r, (t, Y)), angle) =
      coefficientScale (s.epsilon n) (sr.epsilon nr)
        (PhysicalParticularWave.velocityWeight h Q Qr) ^ 2 •
      LocalSignedRequest.fullRequest sr P (2 * h) cr ur nr
        (requestChart h hQ hQr gap (r, (t, Y)), angle) := by
  have hl := PhysicalParticularWave.ratioPower_pos hQ hQr (1 / 2)
  have hθeq (r : ℝ) (Y : LocalSignedRequest.Plane) := H.thetaResidual G hW hl.ne' (r, (t, Y)) (hfiber r Y)
  have hzeq (r : ℝ) (Y : LocalSignedRequest.Plane) := H.axialResidual G hW hl.ne' (r, (t, Y)) (hfiber r Y)
  simp only [requestChart_apply, PhysicalResidualNaturality.weight_source hQ hQr] at hθeq hzeq
  have he := fullRequest_chart s sr P (2 * h) (2 * h) c cr u ur n nr hl
    (slowChange h Q Qr) gap (PhysicalParticularWave.sourceWeight h Q Qr) t
    (SimilarityCoordinates.coordinateQ_spec (by linarith) (by linarith) ht).1 hV htV hθ hz hpθ hpz
    (slowChange_length hh hh1 hQ hQr ht) hθeq hzeq r Y angle
  rw [physical_request_factor hQ hQr (s.epsilon_pos n) (sr.epsilon_pos nr).le] at he
  simpa only [requestChart_apply] using he


section CoefficientTransport

variable {D E : Type} [NormedAddCommGroup D] [NormedSpace ℝ D]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Exact pointwise transport of the literal signed quotient coefficient
from primitive matrix, targets, mask and primary fundamental identities. -/
theorem signedVector_transport (s : StripData D) (sr : StripData E)
    (H : ℕ → D → Mat2) (Hr : ℕ → E → Mat2)
    (T R : ℕ → D → Vec2) (Tr Rr : ℕ → E → Vec2)
    (mask : ℕ → D → ℝ) (maskr : ℕ → E → ℝ)
    (v : ℕ → D → Space) (vr : ℕ → E → Space)
    (n nr : ℕ) (x : D) (xr : E) {c : ℝ} (hc : 0 < c)
    (hH : H n x = Hr nr xr)
    (hT : T n x = coefficientScale (s.epsilon n) (sr.epsilon nr) c ^ 2 • Tr nr xr)
    (hR : R n x = coefficientScale (s.epsilon n) (sr.epsilon nr) c ^ 2 • Rr nr xr)
    (hm : mask n x = maskr nr xr) (hv : v n x = vr nr xr) (j : Fin 2) :
    SignedWaveUpdate.signedVector s H T R mask v j n x =
      c • SignedWaveUpdate.signedVector sr Hr Tr Rr maskr vr j nr xr := by
  simp only [SignedWaveUpdate.signedVector, SignedWaveUpdate.signedScalar,
    hH, hT, hR, hm, hv]
  rw [signed_scalar_scale (Hr nr xr) (Tr nr xr) (Rr nr xr) (maskr nr xr)
    (s.epsilon_pos n) (sr.epsilon_pos nr) hc j]
  rw [smul_smul]

theorem homogeneousPressure_scale (K Kr rate c normalScale : ℝ)
    (hK : K ≠ 0) (hKr : Kr ≠ 0) (hs : normalScale ≠ 0)
    (N Ndot v Av : Space) :
    Complex.I * (TangentProjection.pressureCoefficient (normalScale • N)
      ((normalScale * rate) • Ndot) (c • v) ((rate * c) • Av) 0 : ℂ) / (K : ℂ) =
        ((rate * c / normalScale) * (Kr / K)) •
          (Complex.I * (TangentProjection.pressureCoefficient N Ndot v Av 0 : ℂ) / (Kr : ℂ)) := by
  have hk : (K : ℂ) ≠ 0 := by exact_mod_cast hK
  have hkr : (Kr : ℂ) ≠ 0 := by exact_mod_cast hKr
  have hns : (normalScale : ℂ) ≠ 0 := by exact_mod_cast hs
  rw [show (0 : Space) = (rate * c) • (0 : Space) by simp,
    NormalScaling.pressureCoefficient_rescale N Ndot v Av 0 rate c hs]
  simp only [smul_zero, Complex.ofReal_mul, Complex.ofReal_div, Complex.real_smul]
  field_simp

end CoefficientTransport

/-! ## One actual primary pulse family, reused in every view -/

/-- Only primary construction data and background fields are stored.
The pulse, covariance matrix, square roots and signed quotients are all
computed by the existing constructors. -/
structure PrimaryData (U : PhaseJetBounds.Domain ℕ PhaseCalculus.Slow) where
  strip : StripData Cylinder
  base : LinearWaveBounds.WaveCoefficients Cylinder
  directions : LinearWaveBounds.GraphDirections Cylinder
  pulse : Fin 2 → PrimaryPulseBounds.PhaseConstruction U
  prefactor : Fin 2 → ℕ → ℝ
  coordinate : ℕ → Cylinder → PhaseCalculus.Slow × ℝ
  target : ℕ → Cylinder → Vec2
  mask : ℕ → Cylinder → ℝ
  normalMotion : ℕ → Cylinder → Space
  action : ℕ → Cylinder → Space →L[ℝ] Space

namespace PrimaryData

variable {U : PhaseJetBounds.Domain ℕ PhaseCalculus.Slow} (B : PrimaryData U)


noncomputable def matrix : ℕ → Cylinder → Mat2 :=
  SignedWaveUpdate.phaseMatrix B.pulse B.prefactor B.coordinate

noncomputable def fundamental (j : Fin 2) : ℕ → Cylinder → Space :=
  SignedWaveUpdate.phaseFundamental B.pulse B.coordinate j

/-- The single Gaussian slot cutoff of this primary pulse. -/
noncomputable def cutoff (n : ℕ) (x : Cylinder) : ℝ :=
  GaussianTailFlat.profile (B.coordinate n x).2

noncomputable def coefficients (request : ℕ → Cylinder → Vec2) (j : Fin 2) :
    LinearWaveBounds.WaveCoefficients Cylinder :=
  SignedWaveUpdate.coefficients B.base B.strip B.directions B.matrix B.target request B.mask
    (B.fundamental j) B.normalMotion B.action j

noncomputable def primaryVector (j : Fin 2) (n : ℕ) (x : Cylinder) : Space :=
  PartitionedCovariance.amplitude (B.strip.epsilon n) (B.mask n x) (B.matrix n x)
    (B.target n x) j • B.fundamental j n x

noncomputable def primaryCoefficients (j : Fin 2) : LinearWaveBounds.WaveCoefficients Cylinder :=
  SignedWaveUpdate.homogeneousCoefficients B.base B.strip B.directions
    (B.primaryVector j) B.normalMotion B.action

noncomputable def primaryRequest : ℕ → Cylinder → Vec2 := fun n x => (2 : ℝ) • B.target n x

theorem primaryVector_eq_signed (j : Fin 2) :
    B.primaryVector j = SignedWaveUpdate.signedVector B.strip B.matrix B.target B.primaryRequest
      B.mask (B.fundamental j) j := by
  funext n x
  simp only [primaryVector, SignedWaveUpdate.signedVector, SignedWaveUpdate.signedScalar,
    primaryRequest, increment_twice_target, PartitionedCovariance.amplitude]

theorem primaryCoefficients_eq_signed (j : Fin 2) :
    B.primaryCoefficients j = B.coefficients B.primaryRequest j := by
  unfold primaryCoefficients coefficients SignedWaveUpdate.coefficients
  rw [B.primaryVector_eq_signed j]


/-- The same reference carrier is pulled back before multiplication by
the target band's frequency. All other background fields remain inputs. -/
noncomputable def viewBase (background : LinearWaveBounds.WaveCoefficients Cylinder)
    (frequency : ℕ → ℝ) (view : ℕ → Cylinder → Cylinder) (reference : ℕ) :
    LinearWaveBounds.WaveCoefficients Cylinder :=
  { background with
    frequency := frequency
    phase := fun n x => (B.base.frequency reference / frequency n) *
      B.base.phase reference (view n x) }

noncomputable def viewTarget (s : StripData Cylinder) (velocity : ℕ → ℝ)
    (view : ℕ → Cylinder → Cylinder) (reference : ℕ) : ℕ → Cylinder → Vec2 :=
  fun n x => coefficientScale (s.epsilon n) (B.strip.epsilon reference) (velocity n) ^ 2 •
    B.target reference (view n x)

noncomputable def viewCutoff (view : ℕ → Cylinder → Cylinder) (reference : ℕ) :
    ℕ → Cylinder → ℝ := fun n x => B.cutoff reference (view n x)

/-- Each view calls the actual signed quotient constructor, with the same
reference pulse and matrix. Its request may be the literal current-state
request and is not replaced by an independently chosen signed wave. -/
noncomputable def viewCoefficients (s : StripData Cylinder)
    (d : LinearWaveBounds.GraphDirections Cylinder)
    (background : LinearWaveBounds.WaveCoefficients Cylinder)
    (frequency velocity clock normal : ℕ → ℝ) (view : ℕ → Cylinder → Cylinder)
    (reference : ℕ) (request : ℕ → Cylinder → Vec2) (j : Fin 2) :
    LinearWaveBounds.WaveCoefficients Cylinder :=
  SignedWaveUpdate.coefficients (B.viewBase background frequency view reference) s d
    (fun n x => B.matrix reference (view n x)) (B.viewTarget s velocity view reference) request
    (fun n x => B.mask reference (view n x))
    (fun n x => B.fundamental j reference (view n x))
    (fun n x => (normal n * clock n) • B.normalMotion reference (view n x))
    (fun n x => clock n • B.action reference (view n x)) j


theorem view_signedVector (s : StripData Cylinder) (velocity : ℕ → ℝ)
    (view : ℕ → Cylinder → Cylinder) (reference n : ℕ)
    (request referenceRequest : ℕ → Cylinder → Vec2) (j : Fin 2) (x : Cylinder)
    (hc : 0 < velocity n)
    (hrequest : request n x = coefficientScale (s.epsilon n) (B.strip.epsilon reference)
      (velocity n) ^ 2 • referenceRequest reference (view n x)) :
    SignedWaveUpdate.signedVector s (fun n x => B.matrix reference (view n x))
      (B.viewTarget s velocity view reference) request (fun n x => B.mask reference (view n x))
      (fun n x => B.fundamental j reference (view n x)) j n x =
        velocity n • SignedWaveUpdate.signedVector B.strip B.matrix B.target referenceRequest
          B.mask (B.fundamental j) j reference (view n x) :=
  signedVector_transport s B.strip _ _ _ _ _ _ _ _ _ _ n reference x (view n x) hc
    rfl rfl hrequest rfl rfl j

theorem view_amplitude (s : StripData Cylinder) (d : LinearWaveBounds.GraphDirections Cylinder)
    (background : LinearWaveBounds.WaveCoefficients Cylinder)
    (frequency velocity clock normal : ℕ → ℝ) (view : ℕ → Cylinder → Cylinder)
    (reference n : ℕ) (request referenceRequest : ℕ → Cylinder → Vec2) (j : Fin 2)
    (x : Cylinder) (hc : 0 < velocity n)
    (hrequest : request n x = coefficientScale (s.epsilon n) (B.strip.epsilon reference)
      (velocity n) ^ 2 • referenceRequest reference (view n x)) :
    (B.viewCoefficients s d background frequency velocity clock normal view reference request j).amplitude n x =
      velocity n • (B.coefficients referenceRequest j).amplitude reference (view n x) := by
  change CurlClassBounds.complexify _ = velocity n • CurlClassBounds.complexify _
  rw [B.view_signedVector s velocity view reference n request referenceRequest j x hc hrequest,
    map_smul]


theorem view_pressure (s : StripData Cylinder) (d : LinearWaveBounds.GraphDirections Cylinder)
    (background : LinearWaveBounds.WaveCoefficients Cylinder)
    (frequency velocity clock normal : ℕ → ℝ) (view : ℕ → Cylinder → Cylinder)
    (reference n : ℕ) (request referenceRequest : ℕ → Cylinder → Vec2) (j : Fin 2)
    (x : Cylinder) (hc : 0 < velocity n) (hK : frequency n ≠ 0)
    (hKr : B.base.frequency reference ≠ 0) (hs : normal n ≠ 0)
    (hrequest : request n x = coefficientScale (s.epsilon n) (B.strip.epsilon reference)
      (velocity n) ^ 2 • referenceRequest reference (view n x))
    (hN : (B.viewBase background frequency view reference).normal s d n x =
      normal n • B.base.normal B.strip B.directions reference (view n x)) :
    (B.viewCoefficients s d background frequency velocity clock normal view reference request j).pressure n x =
      ((clock n * velocity n / normal n) * (B.base.frequency reference / frequency n)) •
        (B.coefficients referenceRequest j).pressure reference (view n x) := by
  have hv := B.view_signedVector s velocity view reference n request referenceRequest j x hc hrequest
  change Complex.I * (TangentProjection.pressureCoefficient
      ((B.viewBase background frequency view reference).normal s d n x)
      ((normal n * clock n) • B.normalMotion reference (view n x))
      _ ((clock n • B.action reference (view n x)) _) 0 : ℂ) / (frequency n : ℂ) = _
  rw [hN, hv]
  simp only [_root_.smul_apply, map_smul, smul_smul]
  rw [mul_comm (velocity n) (clock n)]
  exact homogeneousPressure_scale (frequency n) (B.base.frequency reference) (clock n)
    (velocity n) (normal n) hK hKr hs _ _ _ _


noncomputable def viewPrimaryVector (s : StripData Cylinder) (velocity : ℕ → ℝ)
    (view : ℕ → Cylinder → Cylinder) (reference : ℕ) (j : Fin 2) (n : ℕ) (x : Cylinder) : Space :=
  PartitionedCovariance.amplitude (s.epsilon n) (B.mask reference (view n x))
    (B.matrix reference (view n x)) (B.viewTarget s velocity view reference n x) j •
      B.fundamental j reference (view n x)


noncomputable def viewPrimaryCoefficients (s : StripData Cylinder)
    (d : LinearWaveBounds.GraphDirections Cylinder)
    (background : LinearWaveBounds.WaveCoefficients Cylinder)
    (frequency velocity clock normal : ℕ → ℝ) (view : ℕ → Cylinder → Cylinder)
    (reference : ℕ) (j : Fin 2) : LinearWaveBounds.WaveCoefficients Cylinder :=
  SignedWaveUpdate.homogeneousCoefficients (B.viewBase background frequency view reference) s d
    (B.viewPrimaryVector s velocity view reference j)
    (fun n x => (normal n * clock n) • B.normalMotion reference (view n x))
    (fun n x => clock n • B.action reference (view n x))


/-- Regularity on one reference native cell. Every entry concerns the
original coordinate, target, current request, mask or phase/frame input;
there is no regularity assumption on a solved wave. -/
structure Regular (request : ℕ → Cylinder → Vec2) (reference : ℕ) (column : Fin 2) : Prop where
  coordinate : ContDiffOn ℝ ∞ (B.coordinate reference) B.strip.domain
  coordinate_mem : ∀ x ∈ B.strip.domain,
    B.coordinate reference x ∈ U.carrier reference ×ˢ Ioo (0 : ℝ) 1
  prefactor : ∀ j, PhaseJetBounds.PolynomialJets U (fun n _ => B.prefactor j n)
  target : ∀ j, ContDiffOn ℝ ∞ (fun x => B.target reference x j) B.strip.domain
  request : ∀ j, ContDiffOn ℝ ∞ (fun x => request reference x j) B.strip.domain
  mask : ContDiffOn ℝ ∞ (B.mask reference) B.strip.domain
  cone : ∀ x ∈ B.strip.domain,
    SmoothCovariance.StrictCone (B.matrix reference x) (B.target reference x)
  phase : ContDiffOn ℝ ∞ (B.base.phase reference) B.strip.domain
  normal_ne : ∀ x ∈ B.strip.domain, B.base.normal B.strip B.directions reference x ≠ 0
  normal_frame : ∀ x, x ∈ B.strip.domain →
    B.base.normal B.strip B.directions reference x =
      ((B.pulse column).frame reference).normal ((B.coordinate reference x).1,
        (B.pulse column).L reference * (B.coordinate reference x).2)

namespace Regular

variable {B} {request : ℕ → Cylinder → Vec2} {reference : ℕ} {column : Fin 2}
  (H : B.Regular request reference column)

include H


theorem matrix_smooth (i j : Fin 2) :
    ContDiffOn ℝ ∞ (fun x => B.matrix reference x i j) B.strip.domain := by
  have hm := PrimaryPulseBounds.primaryCovariance_entry_polynomial U B.prefactor
    (fun j => (B.pulse j).frame) (fun j => (B.pulse j).lam) (fun j => (B.pulse j).u)
    (fun j => (B.pulse j).L) H.prefactor (fun j => (B.pulse j).pulse_jets)
    (fun j => (B.pulse j).lam_pos) (fun j => (B.pulse j).u_pos) (fun j => (B.pulse j).L_pos) i j
  exact (hm.smooth reference).comp H.coordinate.fst (fun x hx => (H.coordinate_mem x hx).1)

theorem fundamental_smooth (j : Fin 2) :
    ContDiffOn ℝ ∞ (B.fundamental j reference) B.strip.domain :=
  ((B.pulse j).pulse_jets.smooth reference).comp H.coordinate H.coordinate_mem

theorem cutoff_smooth : ContDiffOn ℝ ∞ (B.cutoff reference) B.strip.domain :=
  GaussianTailFlat.profile_contDiff.comp_contDiffOn H.coordinate.snd

theorem signedScalar_smooth (j : Fin 2) :
    ContDiffOn ℝ ∞ (SignedWaveUpdate.signedScalar B.strip B.matrix B.target request B.mask j reference)
      B.strip.domain := by
  have hi := SmoothCovariance.contDiffOn_inverse_solution H.matrix_smooth H.request
    (fun x hx => (H.cone x hx).det_ne_zero) j
  have ha := SmoothCovariance.contDiffOn_amplitudes H.matrix_smooth H.target H.cone j
  have hd : ∀ x ∈ B.strip.domain, 2 * SmoothCovariance.amplitudes
      (B.matrix reference x) (B.target reference x) j ≠ 0 := by
    intro x hx
    exact mul_ne_zero (by norm_num) ((H.cone x hx).amplitudes_pos j).ne'
  exact (contDiffOn_const.mul (hi.div (contDiffOn_const.mul ha) hd)).mul H.mask

theorem amplitude_smooth (j : Fin 2) :
    ContDiffOn ℝ ∞ ((B.coefficients request j).amplitude reference) B.strip.domain :=
  CurlClassBounds.complexify.contDiff.comp_contDiffOn
    ((H.signedScalar_smooth j).smul (H.fundamental_smooth j))





end Regular

/-- Angular conditions concern the original phase, coordinate and scalar
inputs. In particular the signed coefficient's invariance is a theorem. -/
structure Angular (request : ℕ → Cylinder → Vec2) (reference : ℕ) where
  mode : ℤ
  phase : CopyAngularInvariance.AffinePhase (0, 1) (mode / B.base.frequency reference)
    (B.base.phase reference)
  coordinate : CopyAngularInvariance.Invariant (0, 1) (B.coordinate reference)
  target : CopyAngularInvariance.Invariant (0, 1) (B.target reference)
  request : CopyAngularInvariance.Invariant (0, 1) (request reference)
  mask : CopyAngularInvariance.Invariant (0, 1) (B.mask reference)
  normalMotion : CopyAngularInvariance.Invariant (0, 1) (B.normalMotion reference)
  action : CopyAngularInvariance.Invariant (0, 1) (B.action reference)




noncomputable def raw (request : ℕ → Cylinder → Vec2) (j : Fin 2) (reference : ℕ) :
    Cylinder → ComplexVector := ((B.coefficients request j).withCutoff B.cutoff).amplitude reference

noncomputable def rawPressure (request : ℕ → Cylinder → Vec2) (j : Fin 2) (reference : ℕ) :
    Cylinder → ℂ := ((B.coefficients request j).withCutoff B.cutoff).pressure reference

theorem raw_invariant {request : ℕ → Cylinder → Vec2} {reference : ℕ}
    (H : B.Angular request reference) (j : Fin 2) :
    CopyAngularInvariance.Invariant (0, 1) (B.raw request j reference) := by
  intro x t
  simp only [raw, coefficients, SignedWaveUpdate.coefficients, SignedWaveUpdate.homogeneousCoefficients,
    LinearWaveBounds.WaveCoefficients.withCutoff, cutoff, SignedWaveUpdate.signedVector,
    SignedWaveUpdate.signedScalar, matrix, SignedWaveUpdate.phaseMatrix, PrimaryPulseBounds.chartCovariance,
    fundamental, SignedWaveUpdate.phaseFundamental,
    H.coordinate x t, H.target x t, H.request x t, H.mask x t]

end PrimaryData

/-- Literal background chart operators, before any wave is formed. -/
structure ChartGeometry (a : LinearWaveBounds.WaveCoefficients Cylinder)
    (s : StripData Cylinder) (d : LinearWaveBounds.GraphDirections Cylinder)
    (n : ℕ) (h Q : ℝ) (cover : ℕ) : Prop where
  radius : a.radius n = PhysicalResidualBridge.ScaledGraph.radius
  radial : d.radialField n = (PhysicalResidualBridge.commonGraph Q h cover).radial
  angular : (fun _ => d.angular) = PhysicalResidualBridge.ScaledGraph.angular
  axial : d.axialField s n = (PhysicalResidualBridge.commonGraph Q h cover).axial

theorem ChartGeometry.normal {a : LinearWaveBounds.WaveCoefficients Cylinder}
    {s : StripData Cylinder} {d : LinearWaveBounds.GraphDirections Cylinder}
    {n cover : ℕ} {h Q : ℝ} (G : ChartGeometry a s d n h Q cover) :
    a.normal s d n = phaseNormal PhysicalResidualBridge.ScaledGraph.radius
      (PhysicalResidualBridge.commonGraph Q h cover).radial PhysicalResidualBridge.ScaledGraph.angular
      (PhysicalResidualBridge.commonGraph Q h cover).axial (a.phase n) := by
  unfold LinearWaveBounds.WaveCoefficients.normal
  rw [G.radius, G.radial, G.angular, G.axial]

theorem ChartGeometry.corrected_wave {a : LinearWaveBounds.WaveCoefficients Cylinder}
    {s : StripData Cylinder} {d : LinearWaveBounds.GraphDirections Cylinder}
    {n cover : ℕ} {h Q : ℝ} (G : ChartGeometry a s d n h Q cover)
    (cutoff : ℕ → Cylinder → ℝ) :
    vectorMode (a.frequency n) (a.phase n) ((a.corrected s d cutoff).amplitude n) =
      vectorMode (a.frequency n) (a.phase n)
        (CurlClassBounds.realizedCoefficient (a.frequency n) PhysicalResidualBridge.ScaledGraph.radius
          (PhysicalResidualBridge.commonGraph Q h cover).radial PhysicalResidualBridge.ScaledGraph.angular
          (PhysicalResidualBridge.commonGraph Q h cover).axial (a.phase n)
          ((a.withCutoff cutoff).amplitude n)) := by
  change vectorMode (a.frequency n) (a.phase n)
      (CurlClassBounds.realizedCoefficient (a.frequency n) (a.radius n) (d.radialField n)
        (fun _ => d.angular) (d.axialField s n) (a.phase n) ((a.withCutoff cutoff).amplitude n)) = _
  rw [G.radius, G.radial, G.angular, G.axial]

theorem ChartGeometry.normal_invariant {a : LinearWaveBounds.WaveCoefficients Cylinder}
    {s : StripData Cylinder} {d : LinearWaveBounds.GraphDirections Cylinder}
    {n cover : ℕ} {h Q slope : ℝ} (G : ChartGeometry a s d n h Q cover)
    (hphi : CopyAngularInvariance.AffinePhase (0, 1) slope (a.phase n)) :
    CopyAngularInvariance.Invariant (0, 1) (a.normal s d n) := by
  rw [G.normal]
  apply CopyAngularInvariance.phaseNormal_invariant (hΦ := hphi)
  · intro x t
    simp [PhysicalResidualBridge.ScaledGraph.radius]
  · intro x t
    simp [PhysicalResidualBridge.ScaledGraph.radial]
  · exact CopyAngularInvariance.Invariant.const _
  · exact CopyAngularInvariance.Invariant.const _

namespace PrimaryData

variable {U : PhaseJetBounds.Domain ℕ PhaseCalculus.Slow} (B : PrimaryData U) (reference : ℕ)

theorem rawPressure_invariant {request : ℕ → Cylinder → Vec2}
    (H : B.Angular request reference) {h Q : ℝ} {cover : ℕ}
    (G : ChartGeometry B.base B.strip B.directions reference h Q cover) (j : Fin 2) :
    CopyAngularInvariance.Invariant (0, 1) (B.rawPressure request j reference) := by
  have hn := G.normal_invariant H.phase
  intro x t
  simp only [rawPressure, coefficients, SignedWaveUpdate.coefficients,
    SignedWaveUpdate.homogeneousCoefficients, LinearWaveBounds.WaveCoefficients.withCutoff,
    cutoff, ParticularWaveBounds.projectedPressure, SignedWaveUpdate.signedVector,
    SignedWaveUpdate.signedScalar, matrix, SignedWaveUpdate.phaseMatrix,
    PrimaryPulseBounds.chartCovariance, fundamental, SignedWaveUpdate.phaseFundamental,
    H.coordinate x t, H.target x t, H.request x t, H.mask x t, H.normalMotion x t,
    H.action x t, hn x t]

/-- One physical reference scale and cover for this primary column. Band
backgrounds are primitive data; frequency, phase, target, pulse, cutoff,
normal motion and action of each view are constructed below. -/
structure Views (B : PrimaryData U) (reference : ℕ) where
  exponent : ℝ
  referenceScale : ℝ
  referenceScale_pos : 0 < referenceScale
  referenceCover : ℕ
  scale : ℕ → ℝ
  scale_pos : ∀ n, 0 < scale n
  cover : ℕ → ℕ
  cover_le : ∀ n, cover n ≤ referenceCover
  frequency : ℕ → ℝ
  frequency_ne : ∀ n, frequency n ≠ 0
  strip : StripData Cylinder
  directions : LinearWaveBounds.GraphDirections Cylinder
  background : LinearWaveBounds.WaveCoefficients Cylinder

namespace Views

variable {B reference} (V : B.Views reference)

noncomputable def map (n : ℕ) : Cylinder →L[ℝ] Cylinder :=
  PhysicalParticularWave.cylinderChange V.exponent (V.scale n) V.referenceScale
    (V.referenceCover - V.cover n)

noncomputable def velocity (n : ℕ) : ℝ :=
  PhysicalParticularWave.velocityWeight V.exponent (V.scale n) V.referenceScale

noncomputable def clock (n : ℕ) : ℝ :=
  PhysicalParticularWave.clockWeight V.exponent (V.scale n) V.referenceScale

noncomputable def normal (n : ℕ) : ℝ :=
  PhysicalParticularWave.normalWeight (V.scale n) V.referenceScale (V.frequency n) (B.base.frequency reference)

noncomputable def coefficients (request : ℕ → Cylinder → Vec2) (j : Fin 2) :
    LinearWaveBounds.WaveCoefficients Cylinder :=
  B.viewCoefficients V.strip V.directions V.background V.frequency V.velocity V.clock V.normal
    (fun n => V.map n) reference request j

noncomputable def cutoff : ℕ → Cylinder → ℝ := B.viewCutoff (fun n => V.map n) reference

noncomputable def exactCoefficients (request : ℕ → Cylinder → Vec2) (j : Fin 2) :
    LinearWaveBounds.WaveCoefficients Cylinder :=
  (V.coefficients request j).corrected V.strip V.directions V.cutoff


theorem map_fastTranslate (n : ℕ) (x : Cylinder) (k : TorusInverse.Frequency) :
    V.map n (fastTranslate x k) =
      fastTranslate (V.map n x) (CommonCoverSolve.coverIndex (V.referenceCover - V.cover n) k) := by
  simp only [map, fastTranslate, PhysicalParticularWave.cylinderChange_apply,
    PhysicalParticularWave.chartChange_apply, map_add, CommonCoverSolve.coverPower_lattice]

theorem phase_periodic (request : ℕ → Cylinder → Vec2) (j : Fin 2)
    (hp : ∀ x k, B.base.phase reference (fastTranslate x k) = B.base.phase reference x)
    (n : ℕ) (x : Cylinder) (k : TorusInverse.Frequency) :
    (V.coefficients request j).phase n (fastTranslate x k) = (V.coefficients request j).phase n x := by
  change (B.base.frequency reference / V.frequency n) * B.base.phase reference (V.map n (fastTranslate x k)) =
    (B.base.frequency reference / V.frequency n) * B.base.phase reference (V.map n x)
  rw [V.map_fastTranslate, hp]


theorem normal_transport
    (G : ChartGeometry B.base B.strip B.directions reference V.exponent V.referenceScale V.referenceCover)
    (n : ℕ)
    (H : ChartGeometry (B.viewBase V.background V.frequency (fun n => V.map n) reference)
      V.strip V.directions n V.exponent (V.scale n) (V.cover n))
    {x : Cylinder} (hx : 0 < x.1.1)
    (hΦ : DifferentiableAt ℝ (B.base.phase reference) (V.map n x)) :
    (B.viewBase V.background V.frequency (fun n => V.map n) reference).normal V.strip V.directions n x =
      V.normal n • B.base.normal B.strip B.directions reference (V.map n x) := by
  rw [G.normal, H.normal]
  have he := PhysicalParticularWave.phaseNormal_chartChange (V.scale_pos n) V.referenceScale_pos
    V.exponent (V.cover n) (V.referenceCover - V.cover n) (V.frequency n) (B.base.frequency reference) hx hΦ
  simp only [Nat.add_sub_of_le (V.cover_le n)] at he
  exact he



noncomputable def physicalPhase : SpaceTime → ℝ :=
  fun z => B.base.phase reference
    ((PhysicalResidualBridge.commonGraph V.referenceScale V.exponent V.referenceCover).map z)

noncomputable def physicalRaw (referenceRequest : ℕ → Cylinder → Vec2) (j : Fin 2) :
    SpaceTime → ComplexVector :=
  fun z => V.referenceScale ^ (-CoordinateAlgebra.A V.exponent) • B.raw referenceRequest j reference
    ((PhysicalResidualBridge.commonGraph V.referenceScale V.exponent V.referenceCover).map z)

noncomputable def referencePotential (referenceRequest : ℕ → Cylinder → Vec2) (j : Fin 2) :
    SpaceTime → ComplexVector :=
  PhysicalCurlCovariance.referencePotential (B.base.frequency reference) V.physicalPhase
    (V.physicalRaw referenceRequest j)

/-- One Cartesian potential is chosen from the reference band and cover,
and each actual band wave will be identified with its curl. -/
noncomputable def physicalPotential (referenceRequest : ℕ → Cylinder → Vec2)
    (j : Fin 2) (delta : ℝ) : VelocityField :=
  PhysicalCurlCovariance.globalCartesianPotential delta (V.referencePotential referenceRequest j)

noncomputable def physicalVelocity (referenceRequest : ℕ → Cylinder → Vec2)
    (j : Fin 2) (delta : ℝ) : VelocityField :=
  SpatialCurl.spatialCurl (V.physicalPotential referenceRequest j delta)

theorem physicalGraph_add_angle (z : SpaceTime) (t : ℝ) :
    (PhysicalResidualBridge.commonGraph V.referenceScale V.exponent V.referenceCover).map
      (z + t • ((0 : ℝ), coordinateVector 1)) =
    (PhysicalResidualBridge.commonGraph V.referenceScale V.exponent V.referenceCover).map z +
      t • ((0 : PhysicalResidualBridge.Lift), (1 : ℝ)) := by
  ext <;> simp [PhysicalResidualBridge.ScaledGraph.map, coordinateVector, smul_eq_mul]


noncomputable def wave (request : ℕ → Cylinder → Vec2) (j : Fin 2) (n : ℕ) :
    Cylinder → ComplexVector :=
  vectorMode (V.frequency n) ((V.coefficients request j).phase n)
    (CurlClassBounds.realizedCoefficient (V.frequency n) PhysicalResidualBridge.ScaledGraph.radius
      (PhysicalResidualBridge.commonGraph (V.scale n) V.exponent (V.cover n)).radial
      PhysicalResidualBridge.ScaledGraph.angular
      (PhysicalResidualBridge.commonGraph (V.scale n) V.exponent (V.cover n)).axial
      ((V.coefficients request j).phase n) (((V.coefficients request j).withCutoff V.cutoff).amplitude n))

theorem wave_eq_exact (request : ℕ → Cylinder → Vec2) (j : Fin 2) (n : ℕ)
    (H : ChartGeometry (B.viewBase V.background V.frequency (fun n => V.map n) reference)
      V.strip V.directions n V.exponent (V.scale n) (V.cover n)) :
    V.wave request j n = vectorMode ((V.exactCoefficients request j).frequency n)
      ((V.exactCoefficients request j).phase n) ((V.exactCoefficients request j).amplitude n) := by
  have H' : ChartGeometry (V.coefficients request j) V.strip V.directions n V.exponent
      (V.scale n) (V.cover n) := ⟨H.radius, H.radial, H.angular, H.axial⟩
  exact (H'.corrected_wave V.cutoff).symm





/-! ## Pressure is transported from the same reference coefficient -/

noncomputable def physicalPressureCoefficient (referenceRequest : ℕ → Cylinder → Vec2)
    (j : Fin 2) : SpaceTime → ℂ :=
  fun z => V.referenceScale ^ (-(2 * CoordinateAlgebra.A V.exponent)) •
    B.rawPressure referenceRequest j reference
      ((PhysicalResidualBridge.commonGraph V.referenceScale V.exponent V.referenceCover).map z)

noncomputable def complexPhysicalPressure (referenceRequest : ℕ → Cylinder → Vec2)
    (j : Fin 2) : SpaceTime → ℂ :=
  mode (B.base.frequency reference) V.physicalPhase (V.physicalPressureCoefficient referenceRequest j)

noncomputable def physicalPressure (referenceRequest : ℕ → Cylinder → Vec2)
    (j : Fin 2) (delta : ℝ) : PressureField :=
  fun z => PhysicalCurlCovariance.globalCartesianPotential delta
    (PhysicalParticularWave.pressureVector (V.complexPhysicalPressure referenceRequest j)) z 2

noncomputable def pressureMode (request : ℕ → Cylinder → Vec2) (j : Fin 2) (n : ℕ) :
    Cylinder → ℂ :=
  mode (V.frequency n) ((V.coefficients request j).phase n)
    (((V.coefficients request j).withCutoff V.cutoff).pressure n)

theorem complexPhysicalPressure_periodic {referenceRequest : ℕ → Cylinder → Vec2}
    (A : B.Angular referenceRequest reference) (hK : B.base.frequency reference ≠ 0)
    (G : ChartGeometry B.base B.strip B.directions reference V.exponent V.referenceScale V.referenceCover)
    (j : Fin 2) (t r z : ℝ) :
    Function.Periodic (fun angle => V.complexPhysicalPressure referenceRequest j
      (t, AxisymmetricResidual.pack r angle z)) (2 * Real.pi) := by
  have hphi : CopyAngularInvariance.AffinePhase ((0 : ℝ), coordinateVector 1)
      (A.mode / B.base.frequency reference) V.physicalPhase := by
    intro x a
    unfold physicalPhase
    rw [V.physicalGraph_add_angle]
    exact A.phase _ a
  have hp : CopyAngularInvariance.Invariant ((0 : ℝ), coordinateVector 1)
      (V.physicalPressureCoefficient referenceRequest j) := by
    intro x a
    unfold physicalPressureCoefficient
    rw [V.physicalGraph_add_angle, B.rawPressure_invariant reference A G j _ a]
  have hf : B.base.frequency reference * (A.mode / B.base.frequency reference) = (A.mode : ℝ) := by
    field_simp
  intro angle
  have he := PhysicalParticularWave.mode_fullTurn A.mode hphi hp hf
    (t, AxisymmetricResidual.pack r angle z)
  simpa only [complexPhysicalPressure, PhysicalParticularWave.angle_translate_pack] using he

theorem physicalPressure_forward {referenceRequest : ℕ → Cylinder → Vec2}
    (A : B.Angular referenceRequest reference) (hK : B.base.frequency reference ≠ 0)
    (G : ChartGeometry B.base B.strip B.directions reference V.exponent V.referenceScale V.referenceCover)
    (j : Fin 2) {delta : ℝ} (hdelta : 0 < delta) (chart : PolarCharts.Index) {z : SpaceTime}
    (hz : z ∈ PhysicalCurlCovariance.validCylindrical delta chart) :
    V.physicalPressure referenceRequest j delta (z.1, CylindricalResidual.chart z.2) =
      (V.complexPhysicalPressure referenceRequest j z).re := by
  have hper (t r z : ℝ) : Function.Periodic
      (fun angle => PhysicalParticularWave.pressureVector (V.complexPhysicalPressure referenceRequest j)
        (t, AxisymmetricResidual.pack r angle z)) (2 * Real.pi) := by
    intro angle
    simp only [PhysicalParticularWave.pressureVector,
      V.complexPhysicalPressure_periodic A hK G j t r z angle]
  have he := (PhysicalCurlCovariance.globalCartesianPotential_forward_germ hdelta chart
    (PhysicalParticularWave.pressureVector (V.complexPhysicalPressure referenceRequest j)) hper hz).eq_of_nhds
  unfold physicalPressure
  rw [he]
  simp [CylindricalResidual.frame_apply, PhysicalCurlCovariance.realVector,
    PhysicalParticularWave.pressureVector]



theorem pressureMode_eq_exact (request : ℕ → Cylinder → Vec2) (j : Fin 2) (n : ℕ) :
    V.pressureMode request j n = HarmonicCalculus.mode ((V.exactCoefficients request j).frequency n)
      ((V.exactCoefficients request j).phase n) ((V.exactCoefficients request j).pressure n) := rfl

/-! ## The primary coefficient is an exact specialization -/

noncomputable def primaryRequest : ℕ → Cylinder → Vec2 :=
  fun n x => (2 : ℝ) • B.viewTarget V.strip V.velocity (fun n => V.map n) reference n x

noncomputable def primaryCoefficients (j : Fin 2) : LinearWaveBounds.WaveCoefficients Cylinder :=
  B.viewPrimaryCoefficients V.strip V.directions V.background V.frequency V.velocity V.clock V.normal
    (fun n => V.map n) reference j


theorem primaryCoefficients_eq_signed (j : Fin 2) :
    V.primaryCoefficients j = V.coefficients V.primaryRequest j := by
  have he : B.viewPrimaryVector V.strip V.velocity (fun n => V.map n) reference j =
      SignedWaveUpdate.signedVector V.strip
        (fun n x => B.matrix reference (V.map n x))
        (B.viewTarget V.strip V.velocity (fun n => V.map n) reference) V.primaryRequest
        (fun n x => B.mask reference (V.map n x))
        (fun n x => B.fundamental j reference (V.map n x)) j := by
    funext n x
    simp only [viewPrimaryVector, SignedWaveUpdate.signedVector, SignedWaveUpdate.signedScalar,
      primaryRequest, increment_twice_target, PartitionedCovariance.amplitude]
  unfold primaryCoefficients viewPrimaryCoefficients coefficients viewCoefficients
    SignedWaveUpdate.coefficients
  rw [he]







/-! ## Bind the constructor to the literal current-state request -/

/-- All coherence fields concern the current state, background and
integration domain before the signed wave is constructed. -/
structure StateData (V : B.Views reference) where
  patch : SignedStressPrimitive.Patch
  context : CorrectionState.Context Point
  referenceContext : CorrectionState.Context Point
  current : CorrectionState.State Point
  referenceState : CorrectionState.State Point
  exponent_pos : 0 < V.exponent
  exponent_lt_half : V.exponent < 1 / 2
  domain : ℕ → Set Point
  domain_open : ∀ n, IsOpen (domain n)
  state_coherent : ∀ n, PhysicalResidualNaturality.StateOn (domain n)
    (requestChart V.exponent (V.scale_pos n) V.referenceScale_pos (V.referenceCover - V.cover n))
    (V.velocity n) (PhysicalParticularWave.ratioPower (V.scale n) V.referenceScale (1 / 2))
    current referenceState n reference
  context_coherent : ∀ n, PhysicalResidualNaturality.ContextOn (domain n)
    (requestChart V.exponent (V.scale_pos n) V.referenceScale_pos (V.referenceCover - V.cover n))
    (V.velocity n) (PhysicalParticularWave.ratioPower (V.scale n) V.referenceScale (1 / 2))
    context referenceContext n reference
  time_pos : ∀ x ∈ V.strip.domain, 0 < x.1.2.1.2
  fibers : ∀ n x, x ∈ V.strip.domain → ∀ r Y,
    (r, ((x.1.2.1.2, x.1.2.1.1), Y)) ∈ domain n
  referenceSlow : ℕ → Set LocalSignedRequest.Plane
  referenceSlow_open : ∀ n, IsOpen (referenceSlow n)
  referenceSlow_mem : ∀ n x, x ∈ V.strip.domain →
    slowChange V.exponent (V.scale n) V.referenceScale (x.1.2.1.2, x.1.2.1.1) ∈ referenceSlow n
  reference_theta_smooth : ∀ n, ContDiffOn ℝ ∞ (referenceState.thetaResidual referenceContext reference)
    (PhysicalMeanDomain.slowDomain (referenceSlow n))
  reference_axial_smooth : ∀ n, ContDiffOn ℝ ∞ (referenceState.axialResidual referenceContext reference)
    (PhysicalMeanDomain.slowDomain (referenceSlow n))
  reference_theta_periodic : ∀ n, PhysicalMeanDomain.PeriodicOn (referenceSlow n)
    (referenceState.thetaResidual referenceContext reference)
  reference_axial_periodic : ∀ n, PhysicalMeanDomain.PeriodicOn (referenceSlow n)
    (referenceState.axialResidual referenceContext reference)

namespace StateData

variable {V} (D : V.StateData)

noncomputable def request : ℕ → Cylinder → Vec2 :=
  stateRequest V.strip D.patch V.exponent D.context D.current

noncomputable def referenceRequest : ℕ → Cylinder → Vec2 :=
  stateRequest B.strip D.patch V.exponent D.referenceContext D.referenceState




end StateData

end Views

end PrimaryData

end NavierStokes.PhysicalSignedWave
