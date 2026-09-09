import NavierStokes.BaseChartJets
import NavierStokes.UniformPrimaryWeights
import NavierStokes.FinalSlowBase

/-!
# The actual normalized radial base component

The radial coefficient is obtained from the same summed curl base and the
same admissible schedule as the angular and axial coefficients.  Its small
factor is `Q^h`.  The exact stream formula includes the factor `1/2` in
`AxisymmetricFields.velocity_zero`.
-/

noncomputable section

namespace NavierStokes.BaseRadialJets

open Set Filter Function BaseChartJets PhaseJetBounds PrimaryPulseBounds
open scoped ContDiff Topology BigOperators

abbrev Slow := PhaseCalculus.Slow

noncomputable def averageSequence (d : SlowBorelBase.Coefficients) : ℕ → Inner → ℝ :=
  fun j => ProfileHistories.average (d.axial j)

theorem averageSequence_eq_component (C : ℝ) (d : SlowBorelBase.Coefficients) :
    averageSequence d = SlowBorelBase.bundleComponent C d 0 := by
  funext j w
  rfl

theorem averageSequence_smooth {d : SlowBorelBase.Coefficients}
    (hd : SlowBorelBase.SmoothCoefficients d) (j : ℕ) : ContDiff ℝ ∞ (averageSequence d j) :=
  SlowBorelBase.average_smooth (hd.axial j)

theorem averageSequence_admissible {a : ℕ → ℕ} {h C : ℝ}
    {d : SlowBorelBase.Coefficients} {K : Set Inner} (hd : SlowBorelBase.SmoothCoefficients d)
    (ha : SlowBorelBase.AdmissibleScales h (SlowBorelBase.coefficientBundle C d) K a) :
    SlowBorelBase.AdmissibleScales h (averageSequence d) K a := by
  rw [averageSequence_eq_component C d]
  exact SlowBorelBase.admissible_component hd ha 0

noncomputable def bandInput (h Q : ℝ) (p : Slow) : Chart :=
  (1 - Q * p.2.2, (Q * p.1 ^ 2 / 2, Q ^ CoordinateAlgebra.D h * p.2.1))

theorem bandInput_eq (h Q : ℝ) (p : Slow) :
    bandInput h Q p = SimilarityHomogeneity.physicalScale h Q (physicalInput p) := by
  apply Prod.ext
  · change 1 - Q * p.2.2 = 1 - Q * (1 - (1 - p.2.2))
    ring
  · apply Prod.ext
    · change Q * p.1 ^ 2 / 2 = Q * (p.1 ^ 2 / 2)
      ring
    · rfl

theorem bandInput_smooth (h Q : ℝ) : ContDiff ℝ ∞ (bandInput h Q) :=
  (contDiff_const.sub (contDiff_const.mul contDiff_snd.snd)).prodMk
    (((contDiff_const.mul (contDiff_fst.pow 2)).div_const 2).prodMk
      (contDiff_const.mul contDiff_snd.fst))

theorem bandInput_deriv_Z (h Q : ℝ) (p : Slow) :
    fderiv ℝ (bandInput h Q) p (0, (1, 0)) = (0, (0, Q ^ CoordinateAlgebra.D h)) := by
  have hc : HasDerivAt (fun t : ℝ => (p.1, (p.2.1 + t, p.2.2))) (0, (1, 0)) 0 :=
    (hasDerivAt_const 0 p.1).prodMk
      (((hasDerivAt_id 0).const_add p.2.1).prodMk (hasDerivAt_const 0 p.2.2))
  have hd := ((bandInput_smooth h Q).differentiable (by simp)).differentiableAt.hasFDerivAt.comp_hasDerivAt 0 hc
  have hd' : HasDerivAt (fun t : ℝ => bandInput h Q (p.1, (p.2.1 + t, p.2.2)))
      (0, (0, Q ^ CoordinateAlgebra.D h)) 0 := by
    have hdZ := ((hasDerivAt_id 0).const_add p.2.1).const_mul (Q ^ CoordinateAlgebra.D h)
    have hfull := (hasDerivAt_const 0 (1 - Q * p.2.2)).prodMk
      ((hasDerivAt_const 0 (Q * p.1 ^ 2 / 2)).prodMk hdZ)
    simpa only [bandInput, mul_one, id_eq] using hfull
  simpa only [add_zero] using hd.unique hd'

/-- Full normalized average stream; no new coefficient sequence or cutoff
schedule is chosen. -/
noncomputable def normalizedStream (a : ℕ → ℕ) (h : ℝ) (d : SlowBorelBase.Coefficients)
    (Q : ℝ) (p : Slow) : ℝ :=
  axialFactor h p * SlowBorelBase.slowSum a h (averageSequence d)
    (SlowBorelBase.scaleMap Q (normalizedCoordinates h p))

theorem normalizedStream_eq {a : ℕ → ℕ} {h C Q : ℝ}
    (hh : 0 < h) (hh1 : h < 1 / 2) (hQ : 0 < Q)
    (d : SlowBorelBase.Coefficients) {p : Slow} (hT : 0 < p.2.2) :
    normalizedStream a h d Q p = Q ^ CoordinateAlgebra.A h *
      SlowBorelBase.streamFactor a h C d (bandInput h Q p) := by
  rw [bandInput_eq]
  unfold SlowBorelBase.streamFactor SlowBorelBase.physicalProfile
  rw [physicalChart_band hh hh1 hQ hT, ← averageSequence_eq_component]
  simp only [SlowBorelBase.scaleMap_apply, smul_eq_mul]
  rw [← mul_assoc, normalized_power hQ (normalizedCoordinates_q_pos hh hh1 hT)]
  rfl


/-- Chain rule for the actual physical axial coordinate. -/
theorem normalizedStream_deriv_Z {a : ℕ → ℕ} (ha : StrictMono a) {h C Q : ℝ}
    (hh : 0 < h) (hh1 : h < 1 / 2) (hQ : 0 < Q)
    {d : SlowBorelBase.Coefficients} (hd : SlowBorelBase.SmoothCoefficients d)
    {p : Slow} (hT : 0 < p.2.2) :
    PhaseCalculus.slowZ (normalizedStream a h d Q) p =
      Q ^ CoordinateAlgebra.A h * Q ^ CoordinateAlgebra.D h *
        AxisymmetricFields.partialZ (SlowBorelBase.streamFactor a h C d) (bandInput h Q p) := by
  have ht : (bandInput h Q p).1 < 1 := by
    change 1 - Q * p.2.2 < 1
    linarith [mul_pos hQ hT]
  have hs := (SlowBorelBase.physicalProfile_smoothAt ha hh hh1
    (SlowBorelBase.bundleComponent_smooth hd C 0) (-CoordinateAlgebra.A h) ht).differentiableAt (by simp)
  change DifferentiableAt ℝ (SlowBorelBase.streamFactor a h C d) (bandInput h Q p) at hs
  have he : normalizedStream a h d Q =ᶠ[𝓝 p]
      (fun q => Q ^ CoordinateAlgebra.A h * SlowBorelBase.streamFactor a h C d (bandInput h Q q)) := by
    filter_upwards [(isOpen_lt continuous_const continuous_snd.snd).mem_nhds hT] with q hq
    exact normalizedStream_eq hh hh1 hQ d hq
  have hb := ((bandInput_smooth h Q).differentiable (by simp)).differentiableAt (x := p) |>.hasFDerivAt
  have hder := (hs.hasFDerivAt.comp p hb).const_mul (Q ^ CoordinateAlgebra.A h)
  simp only [Function.comp_apply] at hder
  unfold PhaseCalculus.slowZ
  rw [he.fderiv_eq, hder.fderiv]
  simp only [_root_.smul_apply, ContinuousLinearMap.comp_apply,
    smul_eq_mul, bandInput_deriv_Z]
  have hez : ((0, (0, Q ^ CoordinateAlgebra.D h)) : Chart) =
      Q ^ CoordinateAlgebra.D h • (0, (0, 1)) := by simp
  rw [hez, map_smul]
  simp only [smul_eq_mul, AxisymmetricFields.partialZ]
  ring

noncomputable def reducedRadial (a : ℕ → ℕ) (h : ℝ) (d : SlowBorelBase.Coefficients)
    (Q : ℝ) (p : Slow) : ℝ :=
  -(p.1 / 2) * PhaseCalculus.slowZ (normalizedStream a h d Q) p

/-- Literal normalized radial component of the constructed curl base. -/
noncomputable def radial (a : ℕ → ℕ) (h C : ℝ) (d : SlowBorelBase.Coefficients)
    (Q : ℝ) (p : Slow) : ℝ :=
  Q ^ CoordinateAlgebra.A h * SlowBorelBase.baseVelocity a h C d (bandPoint h Q p) 0

theorem radial_eq {a : ℕ → ℕ} (ha : StrictMono a) {h C Q : ℝ}
    (hh : 0 < h) (hh1 : h < 1 / 2) (hQ : 0 < Q)
    {d : SlowBorelBase.Coefficients} (hd : SlowBorelBase.SmoothCoefficients d)
    {p : Slow} (hT : 0 < p.2.2) :
    radial a h C d Q p = Q ^ h * reducedRadial a h d Q p := by
  have ht := bandPoint_time (h := h) hQ hT
  have hH := (SlowBorelBase.physicalProfile_smoothAt ha hh hh1
    (SlowBorelBase.bundleComponent_smooth hd C 0) (-CoordinateAlgebra.A h)
    (p := AxisymmetricFields.profilePoint (bandPoint h Q p).1 (bandPoint h Q p).2) ht).differentiableAt (by simp)
  have hK := (SlowBorelBase.physicalProfile_smoothAt ha hh hh1
    (SlowBorelBase.bundleComponent_smooth hd C 1) (1 / 2 - CoordinateAlgebra.A h)
    (p := AxisymmetricFields.profilePoint (bandPoint h Q p).1 (bandPoint h Q p).2) ht).differentiableAt (by simp)
  have hv := AxisymmetricFields.velocity_zero (SlowBorelBase.streamFactor a h C d)
    (SlowBorelBase.swirlPotential a h C d) (bandPoint h Q p).1 (bandPoint h Q p).2 hH hK
  change SlowBorelBase.baseVelocity a h C d (bandPoint h Q p) 0 =
    -(Real.sqrt Q * p.1) * AxisymmetricFields.partialZ (SlowBorelBase.streamFactor a h C d)
      (AxisymmetricFields.profilePoint (bandPoint h Q p).1 (bandPoint h Q p).2) / 2 + 0 * _ at hv
  rw [zero_mul, add_zero, bandPoint_profile hQ.le, ← bandInput_eq] at hv
  have hpow : Real.sqrt Q = Q ^ h * Q ^ CoordinateAlgebra.D h := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_add hQ]
    congr 1
    unfold CoordinateAlgebra.D
    ring
  unfold radial reducedRadial
  rw [hv, normalizedStream_deriv_Z ha hh hh1 hQ hd hT, hpow]
  ring





/-- A band-only nonnegative factor is an exact envelope and has no slow
derivatives. This does not divide by any vanishing spatial weight. -/
theorem scalar_envelope {ι E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (D : Domain ι E) (w : ι → ℝ) (hw : ∀ i, 0 ≤ w i) :
    EnvelopeJets (unitScale D) (fun i _ => w i) (fun i _ => w i) := by
  apply uniform_envelope D.isOpen hw (fun _ => contDiffOn_const)
  intro j
  refine ⟨1, zero_lt_one, fun i x hx => ?_⟩
  cases j with
  | zero => simpa only [norm_iteratedFDeriv_zero, Real.norm_eq_abs, one_mul] using le_of_eq (abs_of_nonneg (hw i))
  | succ j => simp only [iteratedFDeriv_succ_const, Pi.zero_apply, norm_zero, one_mul]; exact hw i





section FinalBase

variable {F : OutgoingProfile.Profile} {W : NominalProfile.Witness F}
  (H : NominalConeAssembly.Certificate W) {ld : ModulatedProfileAssembly.LoopData W}
  (v : ModulatedProfileAssembly.Witness ld)



end FinalBase

end NavierStokes.BaseRadialJets
