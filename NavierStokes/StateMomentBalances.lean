import NavierStokes.CorrectionState
import NavierStokes.IntegratedMeanBalances
import NavierStokes.MeanMomentBounds
import NavierStokes.DefectIncrementBounds
import NavierStokes.SignedStressPrimitive

/-!
# Actual state moment balances

Auxiliary torus averaging, radial integration, and the pressure constructor
connect the literal state residual to its actual slow debt derivatives.
-/

noncomputable section

namespace NavierStokes.StateMomentBalances

open Set Filter MeasureTheory CorrectionState
open scoped BigOperators ContDiff Topology

variable {S : Type} [NormedAddCommGroup S] [NormedSpace ℝ S]

noncomputable def meanBar (f : ScalarField (Lift S)) : ScalarField (Lift S) :=
  fun n => MeanMomentBounds.liftedTorusAverage (f n)

namespace AuxiliaryAverage


variable {S : Type} [NormedAddCommGroup S] [NormedSpace ℝ S]

/-- Coordinates ordered to match the two actual interval integrals. -/
noncomputable def unshuffle : (((ℝ × S) × ℝ) × ℝ) →L[ℝ] Lift S where
  toFun x := (x.1.1.1, (x.1.1.2, (x.2, x.1.2)))
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  cont := continuous_fst.fst.fst.prodMk
    (continuous_fst.fst.snd.prodMk (continuous_snd.prodMk continuous_fst.snd))

noncomputable def slowProjection : Lift S →L[ℝ] (ℝ × S) where
  toFun x := (x.1, x.2.1)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  cont := continuous_fst.prodMk continuous_snd.fst

theorem pullback_derivative {f : Lift S → ℝ} (hf : ContDiff ℝ ∞ f)
    (x v : ((ℝ × S) × ℝ) × ℝ) :
    fderiv ℝ (f ∘ unshuffle) x v = fderiv ℝ f (unshuffle x) (unshuffle v) := by
  rw [((hf.differentiable (by simp) _).hasFDerivAt.comp x unshuffle.hasFDerivAt).fderiv]
  rfl

theorem pullback_periodic {f : Lift S → ℝ} (hp : PressureStream.TorusPeriodicLift f) :
    IntegratedMeanBalances.TorusPeriodic (f ∘ unshuffle) := by
  constructor
  · intro x
    simpa [unshuffle, Function.comp_def] using
      hp x.1.1.1 x.1.1.2 (x.2, x.1.2) (1, 0)
  · intro x
    simpa [unshuffle, Function.comp_def] using
      hp x.1.1.1 x.1.1.2 (x.2, x.1.2) (0, 1)

theorem average_slowDerivative {f : Lift S → ℝ} (hf : ContDiff ℝ ∞ f)
    (v x : ℝ × S) :
    PressureStream.torusAverage (fun y => fderiv ℝ f y (v.1, (v.2, 0))) x =
      fderiv ℝ (PressureStream.torusAverage f) x v := by
  have hF : ContDiff ℝ ∞ (f ∘ unshuffle) := hf.comp (unshuffle (S := S)).contDiff
  have h := IntegratedMeanBalances.torusAverage_fderiv hF x v
  have he : IntegratedMeanBalances.slowPartial v (f ∘ unshuffle) =
      (fun y => fderiv ℝ f (unshuffle y) (v.1, (v.2, 0))) := by
    funext y
    exact pullback_derivative hf y ((v, 0), 0)
  rw [he] at h
  exact h.symm

theorem average_torusDerivative {f : Lift S → ℝ} (hf : ContDiff ℝ ∞ f)
    (hp : PressureStream.TorusPeriodicLift f) (v : PressureStream.Plane) (x : ℝ × S) :
    PressureStream.torusAverage (fun y => fderiv ℝ f y (0, (0, v))) x = 0 := by
  have hF : ContDiff ℝ ∞ (f ∘ unshuffle) := hf.comp (unshuffle (S := S)).contDiff
  have h := IntegratedMeanBalances.torusAverage_torusPartial_zero v hF (pullback_periodic hp) x
  have he : IntegratedMeanBalances.torusPartial v (f ∘ unshuffle) =
      (fun y => fderiv ℝ f (unshuffle y) (0, (0, v))) := by
    funext y
    exact pullback_derivative hf y ((0, v.2), v.1)
  rw [he] at h
  exact h

omit [NormedSpace ℝ S] in
theorem average_add {f g : Lift S → ℝ} (hf : Continuous f) (hg : Continuous g)
    (x : ℝ × S) :
    PressureStream.torusAverage (fun y => f y + g y) x =
      PressureStream.torusAverage f x + PressureStream.torusAverage g x := by
  change FourierAlias.torusMean (fun Y => f (x.1, (x.2, Y)) + g (x.1, (x.2, Y))) =
    FourierAlias.torusMean (fun Y => f (x.1, (x.2, Y))) +
      FourierAlias.torusMean (fun Y => g (x.1, (x.2, Y)))
  exact FourierAlias.torusMean_add
    (hf.comp (continuous_const.prodMk (continuous_const.prodMk continuous_id)))
    (hg.comp (continuous_const.prodMk (continuous_const.prodMk continuous_id)))

/-- The actual torus mean commutes with fixed slow derivatives and removes
the periodic directions. This does not assume a commuting inverse. -/
theorem average_derivative {f : Lift S → ℝ} (hf : ContDiff ℝ ∞ f)
    (hp : PressureStream.TorusPeriodicLift f) (v x : Lift S) :
    PressureStream.torusAverage (fun y => fderiv ℝ f y v) (x.1, x.2.1) =
      fderiv ℝ (MeanMomentBounds.liftedTorusAverage f) x v := by
  have hv : v = (v.1, (v.2.1, (0 : PressureStream.Plane))) + (0, (0, v.2.2)) := by simp
  have he : (fun y => fderiv ℝ f y v) =
      (fun y => fderiv ℝ f y (v.1, (v.2.1, (0 : PressureStream.Plane))) +
        fderiv ℝ f y (0, (0, v.2.2))) := by
    funext y
    conv_lhs => rw [hv, map_add]
  rw [he, average_add
    ((hf.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const).continuous
    ((hf.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const).continuous,
    average_slowDerivative hf (v.1, v.2.1) (x.1, x.2.1),
    average_torusDerivative hf hp v.2.2 (x.1, x.2.1), add_zero]
  have hbar : MeanMomentBounds.liftedTorusAverage f =
      PressureStream.torusAverage f ∘ slowProjection := rfl
  rw [hbar, (((PressureStream.torusAverage_contDiff hf).differentiable (by simp) _).hasFDerivAt.comp
    x slowProjection.hasFDerivAt).fderiv]
  rfl

omit [NormedAddCommGroup S] [NormedSpace ℝ S] in
theorem average_const_mul (c : ℝ) (f : Lift S → ℝ) (x : ℝ × S) :
    PressureStream.torusAverage (fun y => c * f y) x = c * PressureStream.torusAverage f x := by
  simp [PressureStream.torusAverage, PressureStream.torusInner,
    intervalIntegral.integral_const_mul]

theorem average_linear {f : Lift S → ℝ} (hf : ContDiff ℝ ∞ f)
    (hp : PressureStream.TorusPeriodicLift f) (v w : Lift S)
    (a b : ℝ × S → ℝ) (x : Lift S) :
    PressureStream.torusAverage (fun y => fderiv ℝ f y v +
      a (y.1, y.2.1) * fderiv ℝ f y w + b (y.1, y.2.1) * f y) (x.1, x.2.1) =
      fderiv ℝ (MeanMomentBounds.liftedTorusAverage f) x v +
        a (x.1, x.2.1) * fderiv ℝ (MeanMomentBounds.liftedTorusAverage f) x w +
        b (x.1, x.2.1) * MeanMomentBounds.liftedTorusAverage f x := by
  have hv : Continuous (fun y => fderiv ℝ f y v) :=
    ((hf.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const).continuous
  have hw : Continuous (fun y => fderiv ℝ f y w) :=
    ((hf.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const).continuous
  have he : PressureStream.torusAverage (fun y => fderiv ℝ f y v +
      a (y.1, y.2.1) * fderiv ℝ f y w + b (y.1, y.2.1) * f y) (x.1, x.2.1) =
    PressureStream.torusAverage (fun y => fderiv ℝ f y v +
      a (x.1, x.2.1) * fderiv ℝ f y w + b (x.1, x.2.1) * f y) (x.1, x.2.1) :=
    PressureStream.torusAverage_congr_slice _ (fun _ => rfl)
  rw [he, average_add (hv.fun_add (continuous_const.fun_mul hw)) (continuous_const.fun_mul hf.continuous),
    average_add hv (continuous_const.fun_mul hw), average_const_mul, average_const_mul,
    average_derivative hf hp, average_derivative hf hp]
  rfl

theorem meanBar_dz (o : MeanIncrementBounds.Operators (Lift S))
    (f : ScalarField (Lift S)) (hf : ∀ n, ContDiff ℝ ∞ (f n))
    (hp : ∀ n, PressureStream.TorusPeriodicLift (f n)) :
    meanBar (o.dz f) = o.dz (meanBar f) := by
  funext n x
  change PressureStream.torusAverage (fun y => o.epsilon n * fderiv ℝ (f n) y o.eZ)
    (x.1, x.2.1) = _
  rw [average_const_mul, average_derivative (hf n) (hp n)]
  rfl

theorem meanBar_radialDiv (o : MeanIncrementBounds.Operators (Lift S))
    (hradius : o.radius = Prod.fst)
    (hprofile : ∀ R z Y, o.radialProfile (R, (z, Y)) = o.radialProfile (R, (z, 0)))
    (f : ScalarField (Lift S)) (hf : ∀ n, ContDiff ℝ ∞ (f n))
    (hp : ∀ n, PressureStream.TorusPeriodicLift (f n)) (c : ℝ) :
    meanBar (o.radialDiv c f) = o.radialDiv c (meanBar f) := by
  funext n x
  have he : o.radialDiv c f n = fun y => fderiv ℝ (f n) y o.eR +
      (o.radialFrequency n * o.radialProfile (y.1, (y.2.1, 0))) * fderiv ℝ (f n) y o.vR +
      (c * y.1⁻¹) * f n y := by
    funext y
    simp only [MeanIncrementBounds.Operators.radialDiv, MeanIncrementBounds.Operators.dr,
      WeightedClasses.graphDerivative, MeanIncrementBounds.Operators.invRadius,
      hradius, Pi.add_apply, Pi.mul_apply, Pi.smul_apply, smul_eq_mul]
    rw [hprofile y.1 y.2.1 y.2.2]
    ring
  change PressureStream.torusAverage (o.radialDiv c f n) (x.1, x.2.1) = _
  rw [he, average_linear (hf n) (hp n) o.eR o.vR
    (fun z => o.radialFrequency n * o.radialProfile (z.1, (z.2, 0))) (fun z => c * z.1⁻¹) x]
  simp only [MeanIncrementBounds.Operators.radialDiv, MeanIncrementBounds.Operators.dr,
    WeightedClasses.graphDerivative, MeanIncrementBounds.Operators.invRadius,
    hradius, Pi.add_apply, Pi.mul_apply, Pi.smul_apply, smul_eq_mul]
  rw [hprofile x.1 x.2.1 x.2.2]
  have hb : MeanMomentBounds.liftedTorusAverage (f n) = meanBar f n := rfl
  rw [hb]
  ring_nf

theorem meanBar_add (f g : ScalarField (Lift S))
    (hf : ∀ n, ContDiff ℝ ∞ (f n)) (hg : ∀ n, ContDiff ℝ ∞ (g n)) :
    meanBar (f + g) = meanBar f + meanBar g := by
  funext n x
  exact average_add (hf n).continuous (hg n).continuous _

theorem meanBar_sub (f g : ScalarField (Lift S))
    (hf : ∀ n, ContDiff ℝ ∞ (f n)) (hg : ∀ n, ContDiff ℝ ∞ (g n)) :
    meanBar (f - g) = meanBar f - meanBar g := by
  funext n x
  exact PressureStream.torusAverage_sub (hf n).continuous (hg n).continuous _

theorem radialDiv_sub (o : MeanIncrementBounds.Operators (Lift S)) (c : ℝ)
    (f g : ScalarField (Lift S)) (hf : ∀ n, ContDiff ℝ ∞ (f n))
    (hg : ∀ n, ContDiff ℝ ∞ (g n)) :
    o.radialDiv c (f - g) = o.radialDiv c f - o.radialDiv c g := by
  funext n x
  have hd := fderiv_fun_sub ((hf n).differentiable (by simp) x) ((hg n).differentiable (by simp) x)
  change fderiv ℝ (f n - g n) x = _ at hd
  simp only [MeanIncrementBounds.Operators.radialDiv, MeanIncrementBounds.Operators.dr,
    WeightedClasses.graphDerivative, Pi.add_apply, Pi.sub_apply, hd,
    _root_.sub_apply, Pi.smul_apply, Pi.mul_apply, smul_eq_mul]
  ring

/-- The torus-mean flux identity used for the initial improved bar estimate. -/
theorem meanBar_fluxBalance {a b : ℝ} (ha : 0 < a)
    (o : MeanIncrementBounds.Operators (Lift S)) (ho : DefectIncrementBounds.PositiveOperators o)
    (hprofile : ∀ R z Y, o.radialProfile (R, (z, Y)) = o.radialProfile (R, (z, 0)))
    (R A T : ScalarField (Lift S)) (c : ℝ)
    (hR : DefectIncrementBounds.Shell a b R) (hA : DefectIncrementBounds.Shell a b A)
    (hT : DefectIncrementBounds.Shell a b T)
    (hpR : ∀ n, PressureStream.TorusPeriodicLift (R n))
    (hpA : ∀ n, PressureStream.TorusPeriodicLift (A n))
    (hpT : ∀ n, PressureStream.TorusPeriodicLift (T n)) :
    meanBar (o.radialDiv c R + o.dz A - o.radialDiv c T) =
      o.radialDiv c (meanBar R - meanBar T) +
        o.dz (meanBar A) := by
  have hrc := hR.radialDiv ha ho c
  have hac := hA.dz o
  have htc := hT.radialDiv ha ho c
  rw [meanBar_sub (o.radialDiv c R + o.dz A) (o.radialDiv c T)
      (fun n => (hrc.smooth n).add (hac.smooth n)) htc.smooth,
    meanBar_add (o.radialDiv c R) (o.dz A) hrc.smooth hac.smooth,
    meanBar_radialDiv o ho.radius_eq hprofile R hR.smooth hpR c,
    meanBar_radialDiv o ho.radius_eq hprofile T hT.smooth hpT c,
    meanBar_dz o A hA.smooth hpA,
    radialDiv_sub o c (meanBar R) (meanBar T)
      (fun n => MeanMomentBounds.liftedTorusAverage_contDiff (hR.smooth n))
      (fun n => MeanMomentBounds.liftedTorusAverage_contDiff (hT.smooth n))]
  abel


end AuxiliaryAverage

namespace AuxiliaryAverage

theorem periodic_directional {f : Lift S → ℝ}
    (hp : PressureStream.TorusPeriodicLift f) (v : Lift S) :
    PressureStream.TorusPeriodicLift (fun x => fderiv ℝ f x v) := by
  intro R s Y k
  let a : Lift S := (0, (0, ((k.1 : ℝ), (k.2 : ℝ))))
  have he : (fun x : Lift S => f (x + a)) = f := by
    funext x
    simpa [a, Prod.add_def] using hp x.1 x.2.1 x.2.2 k
  have hd := congrArg (fun g : Lift S → ℝ => fderiv ℝ g (R, (s, Y))) he
  rw [fderiv_comp_add_right] at hd
  simpa [a, Prod.add_def] using congrArg (fun L : Lift S →L[ℝ] ℝ => L v) hd

theorem periodic_dr (o : MeanIncrementBounds.Operators (Lift S))
    (hprofile : ∀ R z Y, o.radialProfile (R, (z, Y)) = o.radialProfile (R, (z, 0)))
    {f : ScalarField (Lift S)} (hp : ∀ n, PressureStream.TorusPeriodicLift (f n)) :
    ∀ n, PressureStream.TorusPeriodicLift (o.dr f n) := by
  intro n R s Y k
  simp only [MeanIncrementBounds.Operators.dr, WeightedClasses.graphDerivative,
    periodic_directional (hp n) o.eR R s Y k,
    periodic_directional (hp n) o.vR R s Y k]
  rw [hprofile R s _, hprofile R s Y]

theorem periodic_dz (o : MeanIncrementBounds.Operators (Lift S))
    {f : ScalarField (Lift S)} (hp : ∀ n, PressureStream.TorusPeriodicLift (f n)) :
    ∀ n, PressureStream.TorusPeriodicLift (o.dz f n) := by
  intro n R s Y k
  simp only [MeanIncrementBounds.Operators.dz, periodic_directional (hp n) o.eZ R s Y k]

theorem meanBar_dr (o : MeanIncrementBounds.Operators (Lift S))
    (hradius : o.radius = Prod.fst)
    (hprofile : ∀ R z Y, o.radialProfile (R, (z, Y)) = o.radialProfile (R, (z, 0)))
    (f : ScalarField (Lift S)) (hf : ∀ n, ContDiff ℝ ∞ (f n))
    (hp : ∀ n, PressureStream.TorusPeriodicLift (f n)) :
    meanBar (o.dr f) = o.dr (meanBar f) := by
  simpa only [MeanIncrementBounds.Operators.radialDiv, zero_smul, add_zero] using
    meanBar_radialDiv o hradius hprofile f hf hp 0


omit [NormedAddCommGroup S] [NormedSpace ℝ S] in
theorem average_radial_mul (c : ℝ → ℝ) (f : Lift S → ℝ) (x : ℝ × S) :
    PressureStream.torusAverage (fun y => c y.1 * f y) x =
      c x.1 * PressureStream.torusAverage f x := by
  simp only [PressureStream.torusAverage, PressureStream.torusInner,
    intervalIntegral.integral_const_mul]

theorem meanBar_time (o : MeanIncrementBounds.Operators (Lift S))
    (f : ScalarField (Lift S)) (hf : ∀ n, ContDiff ℝ ∞ (f n))
    (hp : ∀ n, PressureStream.TorusPeriodicLift (f n)) :
    meanBar (o.time f) = o.time (meanBar f) := by
  funext n x
  have ht : Continuous (fun y => -(o.epsilon n * fderiv ℝ (f n) y o.eT)) :=
    (continuous_const.mul (((hf n).fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const).continuous).neg
  have hv : Continuous (fun y => o.fastCoefficient n * fderiv ℝ (f n) y o.vT) :=
    continuous_const.mul (((hf n).fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const).continuous
  change PressureStream.torusAverage (fun y => -(o.epsilon n * fderiv ℝ (f n) y o.eT) +
    o.fastCoefficient n * fderiv ℝ (f n) y o.vT) (x.1, x.2.1) = _
  rw [average_add ht hv]
  simp_rw [← neg_mul]
  rw [average_const_mul, average_const_mul, average_derivative (hf n) (hp n),
    average_derivative (hf n) (hp n)]
  simp only [MeanIncrementBounds.Operators.time, MeanIncrementBounds.Operators.slowTime,
    MeanIncrementBounds.Operators.fastTime, meanBar, Pi.add_apply, neg_mul]

theorem meanBar_viscosity {a b : ℝ} (ha : 0 < a)
    (o : MeanIncrementBounds.Operators (Lift S)) (ho : DefectIncrementBounds.PositiveOperators o)
    (hprofile : ∀ R z Y, o.radialProfile (R, (z, Y)) = o.radialProfile (R, (z, 0)))
    (f : ScalarField (Lift S)) (hf : DefectIncrementBounds.Shell a b f)
    (hp : ∀ n, PressureStream.TorusPeriodicLift (f n)) (c : ℝ) :
    meanBar (o.viscosity c f) = o.viscosity c (meanBar f) := by
  have hrd := hf.dr ha ho
  have hrr := hrd.dr ha ho
  have hri := hrd.inv_mul ha ho
  have hzz := (hf.dz o).dz o
  have hii := ((hf.inv_mul ha ho).inv_mul ha ho).smul c
  have hd := meanBar_dr o ho.radius_eq hprofile f hf.smooth hp
  have hdd := meanBar_dr o ho.radius_eq hprofile (o.dr f) hrd.smooth
    (periodic_dr o hprofile hp)
  rw [hd] at hdd
  have hz := meanBar_dz o f hf.smooth hp
  have hzzbar := meanBar_dz o (o.dz f) (hf.dz o).smooth (periodic_dz o hp)
  rw [hz] at hzzbar
  funext n x
  have hric : Continuous (fun y => o.invRadius n y * o.dr f n y) := (hri.smooth n).continuous
  have hiic : Continuous (fun y => c * (o.invRadius n y * (o.invRadius n y * f n y))) :=
    (hii.smooth n).continuous
  change PressureStream.torusAverage (fun y => o.epsilon n *
      (o.dr (o.dr f) n y + o.invRadius n y * o.dr f n y +
        o.dz (o.dz f) n y - c * (o.invRadius n y * (o.invRadius n y * f n y))))
      (x.1, x.2.1) = _
  rw [average_const_mul,
    PressureStream.torusAverage_sub (((hrr.smooth n).continuous.fun_add hric).fun_add (hzz.smooth n).continuous)
      hiic,
    average_add ((hrr.smooth n).continuous.fun_add hric) (hzz.smooth n).continuous,
    average_add (hrr.smooth n).continuous hric]
  simp only [MeanIncrementBounds.Operators.invRadius, ho.radius_eq]
  rw [average_radial_mul, average_const_mul, average_radial_mul, average_radial_mul]
  change o.epsilon n * (meanBar (o.dr (o.dr f)) n x + x.1⁻¹ * meanBar (o.dr f) n x +
    meanBar (o.dz (o.dz f)) n x - c * (x.1⁻¹ * (x.1⁻¹ * meanBar f n x))) = _
  rw [hdd, hd, hzzbar]
  simp only [MeanIncrementBounds.Operators.viscosity, MeanIncrementBounds.Operators.invRadius,
    ho.radius_eq]

end AuxiliaryAverage

/-! ## Explicit graph operators acting on the actual torus means -/

noncomputable def averaged (f : ScalarField (Lift S)) : ℕ → ℝ × S → ℝ :=
  fun n => PressureStream.torusAverage (f n)

noncomputable def liftSlow (f : ℕ → ℝ × S → ℝ) : ScalarField (Lift S) :=
  fun n x => f n (x.1, x.2.1)

noncomputable def nativeOperators (r : ReconstructionData) (ε fast : ℕ → ℝ)
    (z t : S) (v : PressureStream.Plane) : MeanIncrementBounds.Operators (Lift S) :=
  graphOperators r ε fast (z, 0) (t, 0) v

theorem nativeOperators_positive (r : ReconstructionData) (ε fast : ℕ → ℝ)
    (z t : S) (v : PressureStream.Plane) :
    DefectIncrementBounds.PositiveOperators (nativeOperators r ε fast z t v) := by
  refine ⟨rfl, ?_⟩
  change ContDiffOn ℝ ∞ (fun x : Lift S => r.exponent * x.1 ^ (r.exponent - 1))
    DefectIncrementBounds.positiveDomain
  exact contDiffOn_const.mul (contDiffOn_fst.rpow_const_of_ne (fun _ hx => (ne_of_gt hx)))

omit [NormedSpace ℝ S] in
theorem nativeOperators_profile (r : ReconstructionData) (ε fast : ℕ → ℝ)
    (z t : S) (v : PressureStream.Plane) (R : ℝ) (s : S) (Y : PressureStream.Plane) :
    (nativeOperators r ε fast z t v).radialProfile (R, (s, Y)) =
      (nativeOperators r ε fast z t v).radialProfile (R, (s, 0)) := rfl

noncomputable def radialPartial (F : ℝ × S → ℝ) (x : ℝ × S) : ℝ :=
  fderiv ℝ F x (1, 0)

theorem radialPartial_smooth {F : ℝ × S → ℝ} (hF : ContDiff ℝ ∞ F) :
    ContDiff ℝ ∞ (radialPartial F) :=
  (hF.fderiv_right (by simp)).clm_apply contDiff_const

theorem radialPartial_eq_deriv {F : ℝ × S → ℝ} (hF : ContDiff ℝ ∞ F) (R : ℝ) (s : S) :
    radialPartial F (R, s) = deriv (fun q => F (q, s)) R := by
  have hd := ((hF.differentiable (by simp)) (R, s)).hasFDerivAt.comp_hasDerivAt R
    ((hasDerivAt_id R).prodMk (hasDerivAt_const R s))
  exact hd.deriv.symm

theorem radialPartial_twice_eq_deriv {F : ℝ × S → ℝ} (hF : ContDiff ℝ ∞ F) (R : ℝ) (s : S) :
    radialPartial (radialPartial F) (R, s) = deriv (deriv (fun q => F (q, s))) R := by
  rw [radialPartial_eq_deriv (radialPartial_smooth hF)]
  congr 1
  funext q
  exact radialPartial_eq_deriv hF q s

theorem fderiv_liftSlow {F : ℕ → ℝ × S → ℝ} (hF : ∀ n, ContDiff ℝ ∞ (F n))
    (n : ℕ) (x v : Lift S) :
    fderiv ℝ (liftSlow F n) x v = fderiv ℝ (F n) (x.1, x.2.1) (v.1, v.2.1) := by
  have hd := (((hF n).differentiable (by simp)) (x.1, x.2.1)).hasFDerivAt.comp x
    AuxiliaryAverage.slowProjection.hasFDerivAt
  rw [show liftSlow F n = F n ∘ AuxiliaryAverage.slowProjection from rfl, hd.fderiv]
  rfl

theorem native_dr_lift (r : ReconstructionData) (ε fast : ℕ → ℝ) (z t : S)
    (v : PressureStream.Plane) {F : ℕ → ℝ × S → ℝ} (hF : ∀ n, ContDiff ℝ ∞ (F n)) :
    (nativeOperators r ε fast z t v).dr (liftSlow F) = liftSlow (fun n => radialPartial (F n)) := by
  funext n x
  simp only [MeanIncrementBounds.Operators.dr, WeightedClasses.graphDerivative,
    nativeOperators, graphOperators, fderiv_liftSlow hF]
  simp [liftSlow, radialPartial, show ((0 : ℝ), (0 : S)) = (0 : ℝ × S) from rfl]

theorem native_dz_lift (r : ReconstructionData) (ε fast : ℕ → ℝ) (z t : S)
    (v : PressureStream.Plane) {F : ℕ → ℝ × S → ℝ} (hF : ∀ n, ContDiff ℝ ∞ (F n)) :
    (nativeOperators r ε fast z t v).dz (liftSlow F) =
      liftSlow (fun n x => ε n * IntegratedMeanBalances.parameterPartial z (F n) x) := by
  funext n x
  simp only [MeanIncrementBounds.Operators.dz, nativeOperators, graphOperators, fderiv_liftSlow hF]
  rfl

theorem native_time_lift (r : ReconstructionData) (ε fast : ℕ → ℝ) (z t : S)
    (v : PressureStream.Plane) {F : ℕ → ℝ × S → ℝ} (hF : ∀ n, ContDiff ℝ ∞ (F n)) :
    (nativeOperators r ε fast z t v).time (liftSlow F) =
      liftSlow (fun n x => -ε n * IntegratedMeanBalances.parameterPartial t (F n) x) := by
  funext n x
  simp only [MeanIncrementBounds.Operators.time, MeanIncrementBounds.Operators.slowTime,
    MeanIncrementBounds.Operators.fastTime, Pi.add_apply, nativeOperators, graphOperators,
    fderiv_liftSlow hF]
  simp [liftSlow, IntegratedMeanBalances.parameterPartial, neg_mul, show ((0 : ℝ), (0 : S)) = (0 : ℝ × S) from rfl]

theorem parameterPartial_const_mul {F : ℝ × S → ℝ} (hF : ContDiff ℝ ∞ F)
    (c : ℝ) (v : S) :
    IntegratedMeanBalances.parameterPartial v (fun x => c * F x) =
      fun x => c * IntegratedMeanBalances.parameterPartial v F x := by
  funext x
  unfold IntegratedMeanBalances.parameterPartial
  rw [(((hF.differentiable (by simp)) x).hasFDerivAt.const_mul c).fderiv]
  rfl

theorem native_radialDiv_lift (r : ReconstructionData) (ε fast : ℕ → ℝ) (z t : S)
    (v : PressureStream.Plane) {F : ℕ → ℝ × S → ℝ} (hF : ∀ n, ContDiff ℝ ∞ (F n))
    (c : ℝ) (n : ℕ) (x : Lift S) :
    (nativeOperators r ε fast z t v).radialDiv c (liftSlow F) n x =
      IntegratedMeanBalances.radialDivergence c (fun q => F n (q, x.2.1)) x.1 := by
  simp only [MeanIncrementBounds.Operators.radialDiv,
    Pi.add_apply, Pi.smul_apply, Pi.mul_apply, smul_eq_mul]
  rw [native_dr_lift r ε fast z t v hF]
  simp only [ liftSlow,
    MeanIncrementBounds.Operators.invRadius, nativeOperators, graphOperators]
  rw [radialPartial_eq_deriv (hF n)]
  simp only [IntegratedMeanBalances.radialDivergence, div_eq_mul_inv, mul_assoc]

theorem native_viscosity_lift (r : ReconstructionData) (ε fast : ℕ → ℝ) (z t : S)
    (v : PressureStream.Plane) {F : ℕ → ℝ × S → ℝ} (hF : ∀ n, ContDiff ℝ ∞ (F n))
    (c : ℝ) (n : ℕ) (x : Lift S) :
    (nativeOperators r ε fast z t v).viscosity c (liftSlow F) n x =
      ε n * (deriv (deriv (fun q => F n (q, x.2.1))) x.1 +
        deriv (fun q => F n (q, x.2.1)) x.1 / x.1 +
        ε n ^ 2 * IntegratedMeanBalances.parameterPartial z
          (IntegratedMeanBalances.parameterPartial z (F n)) (x.1, x.2.1) -
        c * F n (x.1, x.2.1) / x.1 ^ 2) := by
  have hr := native_dr_lift r ε fast z t v hF
  have hrr := native_dr_lift r ε fast z t v (fun n => radialPartial_smooth (hF n))
  have hz := native_dz_lift r ε fast z t v hF
  have hzz := native_dz_lift r ε fast z t v
    (F := fun n x => ε n * IntegratedMeanBalances.parameterPartial z (F n) x)
    (fun n => contDiff_const.mul
    (IntegratedMeanBalances.parameterPartial_smooth z (hF n)))
  simp only [MeanIncrementBounds.Operators.viscosity, hr, hrr, hz, hzz]
  simp only [liftSlow,
    parameterPartial_const_mul (IntegratedMeanBalances.parameterPartial_smooth z (hF n)),
    radialPartial_eq_deriv (hF n), radialPartial_twice_eq_deriv (hF n),
    MeanIncrementBounds.Operators.invRadius, nativeOperators, graphOperators]
  simp only [div_eq_mul_inv]
  ring

noncomputable def fluxResidual (o : MeanIncrementBounds.Operators (Lift S)) (d k : ℝ)
    (u R Z T : ScalarField (Lift S)) : ScalarField (Lift S) :=
  o.time u + o.radialDiv d R + o.dz Z - o.viscosity k u - o.radialDiv d T

theorem meanBar_fluxResidual {a b : ℝ} (ha : 0 < a)
    (o : MeanIncrementBounds.Operators (Lift S)) (ho : DefectIncrementBounds.PositiveOperators o)
    (hprofile : ∀ R z Y, o.radialProfile (R, (z, Y)) = o.radialProfile (R, (z, 0)))
    (d k : ℝ) {u R Z T : ScalarField (Lift S)}
    (hu : DefectIncrementBounds.Shell a b u) (hR : DefectIncrementBounds.Shell a b R)
    (hZ : DefectIncrementBounds.Shell a b Z) (hT : DefectIncrementBounds.Shell a b T)
    (pu : ∀ n, PressureStream.TorusPeriodicLift (u n))
    (pR : ∀ n, PressureStream.TorusPeriodicLift (R n))
    (pZ : ∀ n, PressureStream.TorusPeriodicLift (Z n))
    (pT : ∀ n, PressureStream.TorusPeriodicLift (T n)) :
    meanBar (fluxResidual o d k u R Z T) =
      fluxResidual o d k (meanBar u) (meanBar R) (meanBar Z) (meanBar T) := by
  have hut := hu.time o
  have hRd := hR.radialDiv ha ho d
  have hZd := hZ.dz o
  have huv := hu.viscosity ha ho k
  have hTd := hT.radialDiv ha ho d
  simp only [fluxResidual]
  rw [AuxiliaryAverage.meanBar_sub _ _ (((hut.add hRd).add hZd).sub huv).smooth hTd.smooth,
    AuxiliaryAverage.meanBar_sub _ _ ((hut.add hRd).add hZd).smooth huv.smooth,
    AuxiliaryAverage.meanBar_add _ _ (hut.add hRd).smooth hZd.smooth,
    AuxiliaryAverage.meanBar_add _ _ hut.smooth hRd.smooth,
    AuxiliaryAverage.meanBar_time o u hu.smooth pu,
    AuxiliaryAverage.meanBar_radialDiv o ho.radius_eq hprofile R hR.smooth pR,
    AuxiliaryAverage.meanBar_dz o Z hZ.smooth pZ,
    AuxiliaryAverage.meanBar_viscosity ha o ho hprofile u hu pu,
    AuxiliaryAverage.meanBar_radialDiv o ho.radius_eq hprofile T hT.smooth pT]

noncomputable def balance (ε : ℝ) (z t : S) (d k : ℝ)
    (u R Z T : ℝ × S → ℝ) (x : ℝ × S) : ℝ :=
  -ε * IntegratedMeanBalances.parameterPartial t u x +
    IntegratedMeanBalances.radialDivergence d (fun q => R (q, x.2)) x.1 +
    ε * IntegratedMeanBalances.parameterPartial z Z x -
    ε * (deriv (deriv (fun q => u (q, x.2))) x.1 +
      deriv (fun q => u (q, x.2)) x.1 / x.1 +
      ε ^ 2 * IntegratedMeanBalances.parameterPartial z
        (IntegratedMeanBalances.parameterPartial z u) x - k * u x / x.1 ^ 2) -
    IntegratedMeanBalances.radialDivergence d (fun q => T (q, x.2)) x.1

theorem averaged_fluxResidual {a b : ℝ} (ha : 0 < a)
    (r : ReconstructionData) (ε fast : ℕ → ℝ) (z t : S) (v : PressureStream.Plane)
    (d k : ℝ) {u R Z T : ScalarField (Lift S)}
    (hu : DefectIncrementBounds.Shell a b u) (hR : DefectIncrementBounds.Shell a b R)
    (hZ : DefectIncrementBounds.Shell a b Z) (hT : DefectIncrementBounds.Shell a b T)
    (pu : ∀ n, PressureStream.TorusPeriodicLift (u n))
    (pR : ∀ n, PressureStream.TorusPeriodicLift (R n))
    (pZ : ∀ n, PressureStream.TorusPeriodicLift (Z n))
    (pT : ∀ n, PressureStream.TorusPeriodicLift (T n)) (n : ℕ) (x : ℝ × S) :
    averaged (fluxResidual (nativeOperators r ε fast z t v) d k u R Z T) n x =
      balance (ε n) z t d k (averaged u n) (averaged R n) (averaged Z n) (averaged T n) x := by
  have hh := congrFun (congrFun (meanBar_fluxResidual ha _
    (nativeOperators_positive r ε fast z t v) (nativeOperators_profile r ε fast z t v)
    d k hu hR hZ hT pu pR pZ pT) n) (x.1, (x.2, 0))
  have hb (f : ScalarField (Lift S)) : meanBar f = liftSlow (averaged f) := rfl
  simp only [hb, fluxResidual, Pi.add_apply, Pi.sub_apply] at hh
  rw [native_time_lift r ε fast z t v (F := averaged u)
      (fun n => PressureStream.torusAverage_contDiff (hu.smooth n)),
    native_radialDiv_lift r ε fast z t v (F := averaged R)
      (fun n => PressureStream.torusAverage_contDiff (hR.smooth n)),
    native_dz_lift r ε fast z t v (F := averaged Z)
      (fun n => PressureStream.torusAverage_contDiff (hZ.smooth n)),
    native_viscosity_lift r ε fast z t v (F := averaged u)
      (fun n => PressureStream.torusAverage_contDiff (hu.smooth n)),
    native_radialDiv_lift r ε fast z t v (F := averaged T)
      (fun n => PressureStream.torusAverage_contDiff (hT.smooth n))] at hh
  exact hh

noncomputable def angularBalanceAlong (ε : ℝ) (z t : S) (u R Z T : ℝ × S → ℝ)
    (x : ℝ × S) : ℝ :=
  -ε * IntegratedMeanBalances.parameterPartial t u x +
    IntegratedMeanBalances.radialDivergence 2 (fun q => R (q, x.2)) x.1 +
    ε * IntegratedMeanBalances.parameterPartial z Z x -
    ε * (IntegratedMeanBalances.angularRadialViscosity (fun q => u (q, x.2)) x.1 +
      ε ^ 2 * IntegratedMeanBalances.parameterPartial z
        (IntegratedMeanBalances.parameterPartial z u) x) -
    IntegratedMeanBalances.radialDivergence 2 (fun q => T (q, x.2)) x.1

noncomputable def axialBalanceAlong (ε : ℝ) (z t : S) (u R Z T : ℝ × S → ℝ)
    (x : ℝ × S) : ℝ :=
  -ε * IntegratedMeanBalances.parameterPartial t u x +
    IntegratedMeanBalances.radialDivergence 1 (fun q => R (q, x.2)) x.1 +
    ε * IntegratedMeanBalances.parameterPartial z Z x -
    ε * (IntegratedMeanBalances.axialRadialViscosity (fun q => u (q, x.2)) x.1 +
      ε ^ 2 * IntegratedMeanBalances.parameterPartial z
        (IntegratedMeanBalances.parameterPartial z u) x) -
    IntegratedMeanBalances.radialDivergence 1 (fun q => T (q, x.2)) x.1

theorem balance_angular (ε : ℝ) (z t : S) (u R Z T : ℝ × S → ℝ) :
    balance ε z t 2 1 u R Z T = angularBalanceAlong ε z t u R Z T := by
  funext x
  simp only [balance, angularBalanceAlong, IntegratedMeanBalances.angularRadialViscosity]
  ring

theorem balance_axial (ε : ℝ) (z t : S) (u R Z T : ℝ × S → ℝ) :
    balance ε z t 1 0 u R Z T = axialBalanceAlong ε z t u R Z T := by
  funext x
  simp [balance, axialBalanceAlong, IntegratedMeanBalances.axialRadialViscosity]



section MomentIntegration

open IntegratedMeanBalances

structure RadialShell (a b : ℝ) (F : (ℝ × S → ℝ)) : Prop where
  smooth : ContDiff ℝ ∞ F
  supported : RadialAlias.RadiallySupported a b F

theorem RadialShell.partial {a b : ℝ} {F : (ℝ × S → ℝ)} (hF : RadialShell a b F)
    (v : S) : RadialShell a b (parameterPartial v F) :=
  ⟨parameterPartial_smooth v hF.smooth, parameterPartial_supported v hF.supported⟩


theorem RadialShell.slice_smooth {a b : ℝ} {F : (ℝ × S → ℝ)} (hF : RadialShell a b F)
    (p : S) : ContDiff ℝ ∞ (fun r => F (r, p)) :=
  radial_slice_smooth hF.smooth p

theorem RadialShell.slice_compact {a b : ℝ} {F : (ℝ × S → ℝ)} (hF : RadialShell a b F)
    (p : S) : HasCompactSupport (fun r => F (r, p)) :=
  radial_slice_compact hF.supported p

theorem RadialShell.weighted_integrable {a b : ℝ} {F : (ℝ × S → ℝ)} (hF : RadialShell a b F)
    (n : ℕ) (p : S) : Integrable (fun r => r ^ n * F (r, p)) :=
  IntegratedMeanBalances.weighted_integrable (hF.slice_smooth p).continuous (hF.slice_compact p) n


theorem integrated_angular_along {a b : ℝ} (ε : ℝ) (z t : S)
    {v radialFlux axialFlux virtualFlux : (ℝ × S → ℝ)}
    (hv : RadialShell a b v) (hr : RadialShell a b radialFlux)
    (hz : RadialShell a b axialFlux) (hT : RadialShell a b virtualFlux)
    (hmass : radialMoment 2 v = 0) (p : S) :
    radialMoment 2 (angularBalanceAlong ε z t v radialFlux axialFlux virtualFlux) p =
      ε * fderiv ℝ (radialMoment 2 axialFlux) p z := by
  have halg := moment_balance_algebra 2 (-ε) ε (ε ^ 2)
    (fun r => parameterPartial t v (r, p))
    (radialDivergence 2 (fun r => radialFlux (r, p)))
    (fun r => parameterPartial z axialFlux (r, p))
    (angularRadialViscosity (fun r => v (r, p)))
    (fun r => parameterPartial z (parameterPartial z v) (r, p))
    (radialDivergence 2 (fun r => virtualFlux (r, p)))
    ((hv.partial t).weighted_integrable 2 p)
    (angular_divergence_integrable (hr.slice_smooth p) (hr.slice_compact p))
    ((hz.partial z).weighted_integrable 2 p)
    (angular_viscosity_integrable (hv.slice_smooth p) (hv.slice_compact p))
    (((hv.partial z).partial z).weighted_integrable 2 p)
    (angular_divergence_integrable (hT.slice_smooth p) (hT.slice_compact p))
  have ht := zero_mass_parameterPartial hv.smooth hv.supported 2 hmass p t
  have hzz := zero_mass_parameterPartial_twice hv.smooth hv.supported 2 hmass p z z
  have hd := radialMoment_parameterPartial hz.smooth hz.supported 2 p z
  change moment 2 _ = _
  simp only [angularBalanceAlong]
  rw [halg, moment_angular_divergence (hr.slice_smooth p) (hr.slice_compact p),
    moment_angular_divergence (hT.slice_smooth p) (hT.slice_compact p),
    moment_angular_viscosity (hv.slice_smooth p) (hv.slice_compact p)]
  change (-ε) * radialMoment 2 (parameterPartial t v) p + 0 +
    ε * radialMoment 2 (parameterPartial z axialFlux) p -
    ε * (0 + ε ^ 2 * radialMoment 2 (parameterPartial z (parameterPartial z v)) p) - 0 = _
  rw [ht, hzz, ← hd]
  ring


theorem integrated_axial_along {a b : ℝ} (ε : ℝ) (z t : S)
    {γ radialFlux axialFlux virtualFlux : (ℝ × S → ℝ)}
    (hγ : RadialShell a b γ) (hr : RadialShell a b radialFlux)
    (hz : RadialShell a b axialFlux)
    (hT : RadialShell a b virtualFlux)
    (hmass : radialMoment 1 γ = 0) (p : S) :
    radialMoment 1 (axialBalanceAlong ε z t γ radialFlux axialFlux virtualFlux) p =
      ε * fderiv ℝ (radialMoment 1 axialFlux) p z := by
  have halg := moment_balance_algebra 1 (-ε) ε (ε ^ 2)
    (fun r => parameterPartial t γ (r, p))
    (radialDivergence 1 (fun r => radialFlux (r, p)))
    (fun r => parameterPartial z axialFlux (r, p))
    (axialRadialViscosity (fun r => γ (r, p)))
    (fun r => parameterPartial z (parameterPartial z γ) (r, p))
    (radialDivergence 1 (fun r => virtualFlux (r, p)))
    ((hγ.partial t).weighted_integrable 1 p)
    (by simpa only [pow_one] using axial_divergence_integrable (hr.slice_smooth p) (hr.slice_compact p))
    ((hz.partial z).weighted_integrable 1 p)
    (by simpa only [pow_one] using axial_viscosity_integrable (hγ.slice_smooth p) (hγ.slice_compact p))
    (((hγ.partial z).partial z).weighted_integrable 1 p)
    (by simpa only [pow_one] using axial_divergence_integrable (hT.slice_smooth p) (hT.slice_compact p))
  have ht := zero_mass_parameterPartial hγ.smooth hγ.supported 1 hmass p t
  have hzz := zero_mass_parameterPartial_twice hγ.smooth hγ.supported 1 hmass p z z
  have hd := radialMoment_parameterPartial hz.smooth hz.supported 1 p z
  change moment 1 _ = _
  simp only [axialBalanceAlong]
  rw [halg, moment_axial_divergence (hr.slice_smooth p) (hr.slice_compact p),
    moment_axial_divergence (hT.slice_smooth p) (hT.slice_compact p),
    moment_axial_viscosity (hγ.slice_smooth p) (hγ.slice_compact p)]
  change (-ε) * radialMoment 1 (parameterPartial t γ) p + 0 +
    ε * radialMoment 1 (parameterPartial z axialFlux) p -
    ε * (0 + ε ^ 2 * radialMoment 1 (parameterPartial z (parameterPartial z γ)) p) - 0 = _
  rw [ht, hzz, ← hd]
  ring


theorem averaged_radialShell {a b : ℝ} {f : ScalarField (Lift S)}
    (hf : DefectIncrementBounds.Shell a b f) (n : ℕ) :
    RadialShell a b (averaged f n) :=
  ⟨PressureStream.torusAverage_contDiff (hf.smooth n),
    PressureStream.torusAverage_supported (hf.supported n)⟩

end MomentIntegration

/-! ## Literal state fluxes and actual debt identities -/

noncomputable def thetaRadialFlux (c : Context (Lift S)) (u : State (Lift S)) : ScalarField (Lift S) :=
  MeanIncrementBounds.thetaRadial c.base u.mean + u.covariance 0 1

noncomputable def thetaAxialFlux (c : Context (Lift S)) (u : State (Lift S)) : ScalarField (Lift S) :=
  MeanIncrementBounds.thetaAxial c.base u.mean + u.covariance 2 1

noncomputable def axialRadialFlux (c : Context (Lift S)) (u : State (Lift S)) : ScalarField (Lift S) :=
  MeanIncrementBounds.axialRadial c.base u.mean + u.covariance 0 2

noncomputable def axialAxialFlux (c : Context (Lift S)) (u : State (Lift S)) : ScalarField (Lift S) :=
  MeanIncrementBounds.axialAxial c.base u.mean + u.covariance 2 2

/-- Regularity of the actual pointwise fields; no averaged equation or moment
identity is included among the premises. -/
structure FluxInputs (a b : ℝ) (u R Z T : ScalarField (Lift S)) : Prop where
  velocity : DefectIncrementBounds.Shell a b u
  radial : DefectIncrementBounds.Shell a b R
  axial : DefectIncrementBounds.Shell a b Z
  stress : DefectIncrementBounds.Shell a b T
  velocity_periodic : ∀ n, PressureStream.TorusPeriodicLift (u n)
  radial_periodic : ∀ n, PressureStream.TorusPeriodicLift (R n)
  axial_periodic : ∀ n, PressureStream.TorusPeriodicLift (Z n)
  stress_periodic : ∀ n, PressureStream.TorusPeriodicLift (T n)



omit [NormedAddCommGroup S] [NormedSpace ℝ S] in
theorem state_radialMoment_eq (k : ℕ) (f : ScalarField (Lift S)) (n : ℕ) (s : S) :
    CorrectionState.radialMoment k f n s =
      IntegratedMeanBalances.radialMoment k (averaged f n) s :=
  MeanMomentBounds.pressureMass_radialWeighted k (f n) s





















/-! ## Actual all-jet debt bounds yield the improved signed bump order -/

section ClassBounds

open WeightedClasses MeanMomentBounds SignedStressPrimitive



noncomputable def slowProjection : Lift S →L[ℝ] S :=
  (ContinuousLinearMap.fst ℝ S PressureStream.Plane).comp
    (ContinuousLinearMap.snd ℝ ℝ (S × PressureStream.Plane))

theorem norm_slowProjection_le : ‖slowProjection (S := S)‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro x
  change ‖x.2.1‖ ≤ 1 * ‖x‖
  simp only [one_mul, Prod.norm_def]
  exact (le_max_left _ _).trans (le_max_right _ _)










end ClassBounds

end NavierStokes.StateMomentBalances
