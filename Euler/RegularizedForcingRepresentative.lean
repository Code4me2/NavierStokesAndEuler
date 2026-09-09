import Euler.RegularizedEnergyFamily
import Euler.TimeLpMultiplier

/-! Literal almost-everywhere representatives of the limiting actual word forcing.

Merged in from the former module `Euler.TimeForcingRepresentative`: `timeLinearForcing_ae`.
-/

/-! Actual representatives of linear source, transport, and pressure combinations in Bochner time spaces. -/

noncomputable section

namespace EulerTimeLp

open MeasureTheory Set EulerVolterraConvolution

variable {E V W H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedAddCommGroup W] [NormedSpace ℝ W]
  [NormedAddCommGroup H] [NormedSpace ℝ H]

/-- A genuine sum of fixed spatial and time-dependent operator actions has its literal pointwise representative. -/
theorem timeLinearForcing_ae (T : ℝ) (hT : 0 ≤ T) (D : E →L[ℝ] H) (B : V →L[ℝ] W)
    (A : C(Icc (0 : ℝ) T, W →L[ℝ] H)) (G : C(Icc (0 : ℝ) T, H →L[ℝ] H))
    (U : TimeLp T V) (F P : TimeLp T E) :
    (((D.compLpL 2 (timeMeasure T) F + timeMultiplier T hT A (B.compLpL 2 (timeMeasure T) U) +
      timeMultiplier T hT G (D.compLpL 2 (timeMeasure T) P)) : TimeLp T H) : ℝ → H) =ᵐ[timeMeasure T]
      fun t => D (F t) + A (projIcc 0 T hT t) (B (U t)) + G (projIcc 0 T hT t) (D (P t)) := by
  let DF := D.compLpL 2 (timeMeasure T) F
  let BU := B.compLpL 2 (timeMeasure T) U
  let DP := D.compLpL 2 (timeMeasure T) P
  let AB := timeMultiplier T hT A BU
  let GP := timeMultiplier T hT G DP
  filter_upwards [Lp.coeFn_add (DF+AB) GP, Lp.coeFn_add DF AB,
    D.coeFn_compLpL F, B.coeFn_compLpL U, D.coeFn_compLpL P,
    timeMultiplier_ae T hT A BU, timeMultiplier_ae T hT G DP] with t h1 h2 h3 h4 h5 h6 h7
  change (DF+AB+GP) t = _
  simp only [Pi.add_apply] at h1 h2
  rw [h1,h2,h3,h6,h7,h4,h5]
  rfl

end EulerTimeLp
end

noncomputable section

namespace EulerRegularizedForcingRepresentative

open MeasureTheory Set EulerLiftedGradientSpace EulerCylinderSobolevSpace EulerMildTopWord
  EulerRegularizedForcingWord EulerRegularizedEnergyFamily EulerTimeFamily EulerTimeLp
  EulerVolterraConvolution EulerWeightedForcingTime EulerFiniteMetricEnergy
open scoped Topology

variable (period : ℝ) [Fact (0 < period)]

/-- The limiting word forcing has exactly the differentiated-source plus transport plus pressure representative. -/
theorem forcingWordTime_ae {q m : ℕ} (hm : m ≤ q+1) (w : Fin m → Fin 4) (T : ℝ) (hT : 0 ≤ T)
    (A : C(Icc (0 : ℝ) T, SobolevSpace period 1 →L[ℝ] LiftL2 period))
    (G : C(Icc (0 : ℝ) T, LiftL2 period →L[ℝ] LiftL2 period))
    (U : TimeLp T (SobolevSpace period (2+q))) (F P : TimeLp T (SobolevSpace period (q+1))) :
    (forcingWordTime period hm w T hT A G U F P : ℝ → LiftL2 period) =ᵐ[timeMeasure T]
      fun t => word period (F t) hm w + A (projIcc 0 T hT t)
        (boundedWordBlock period 1 m (by omega : 1+m ≤ 2+q) w (U t)) +
        G (projIcc 0 T hT t) (word period (P t) hm w) := by
  exact timeLinearForcing_ae T hT
    (wordOperator period (⟨⟨m,Nat.lt_succ_of_le hm⟩,w⟩ : SobolevWord (q+1)))
    (boundedWordBlock period 1 m (by omega : 1+m ≤ 2+q) w) A G U F P

/-- The limiting finite family has its literal actual word forcing at every component almost everywhere. -/
theorem forcingFamilyTime_ae {α β : Type*} [Fintype β] {q : ℕ}
    (d : α → β → ℕ) (w : ∀ i j, Fin (d i j) → Fin 4) (hd : ∀ i j, d i j ≤ q+1)
    (T : ℝ) (hT : 0 ≤ T)
    (A : C(Icc (0 : ℝ) T, SobolevSpace period 1 →L[ℝ] LiftL2 period))
    (G : C(Icc (0 : ℝ) T, LiftL2 period →L[ℝ] LiftL2 period))
    (U : TimeLp T (SobolevSpace period (2+q))) (F P : TimeLp T (SobolevSpace period (q+1))) (i : α) :
    (forcingFamilyTime period d w hd T hT A G U F P i : ℝ → β → LiftL2 period) =ᵐ[timeMeasure T]
      fun t j => word period (F t) (hd i j) (w i j) + A (projIcc 0 T hT t)
        (boundedWordBlock period 1 (d i j) (by have := hd i j; omega : 1+d i j ≤ 2+q) (w i j) (U t)) +
        G (projIcc 0 T hT t) (word period (P t) (hd i j) (w i j)) := by
  filter_upwards [familyTime_ae T (fun j => forcingWordTime period (hd i j) (w i j) T hT A G U F P),
    ae_all_iff.mpr (fun j => forcingWordTime_ae period (hd i j) (w i j) T hT A G U F P)] with t h1 h2
  change familyTime T _ t = _
  rw [h1]
  exact funext h2

/-- The limiting weighted forcing is the genuine finite sum of norms of the literal differentiated PDE forcing. -/
theorem weighted_forcing_ae {α β : Type*} [Fintype α] [Fintype β] {q : ℕ}
    (d : α → β → ℕ) (w : ∀ i j, Fin (d i j) → Fin 4) (hd : ∀ i j, d i j ≤ q+1)
    (T : ℝ) (hT : 0 ≤ T) (weights : α → C(Icc (0 : ℝ) T, ℝ))
    (A : C(Icc (0 : ℝ) T, SobolevSpace period 1 →L[ℝ] LiftL2 period))
    (G : C(Icc (0 : ℝ) T, LiftL2 period →L[ℝ] LiftL2 period))
    (U : TimeLp T (SobolevSpace period (2+q))) (F P : TimeLp T (SobolevSpace period (q+1))) :
    (weightedForcingTime T hT weights (forcingFamilyTime period d w hd T hT A G U F P) : ℝ → ℝ) =ᵐ[timeMeasure T]
      fun t => ∑ i, extendPath T hT (weights i) t * familyNorm (fun j =>
        word period (F t) (hd i j) (w i j) + A (projIcc 0 T hT t)
          (boundedWordBlock period 1 (d i j) (by have := hd i j; omega : 1+d i j ≤ 2+q) (w i j) (U t)) +
          G (projIcc 0 T hT t) (word period (P t) (hd i j) (w i j))) := by
  filter_upwards [weightedForcingTime_ae T hT weights (forcingFamilyTime period d w hd T hT A G U F P),
    ae_all_iff.mpr (fun i => forcingFamilyTime_ae period d w hd T hT A G U F P i)] with t h1 h2
  rw [h1]
  exact Finset.sum_congr rfl (fun i _ => congrArg (fun v : β → LiftL2 period =>
    extendPath T hT (weights i) t * familyNorm v) (h2 i))

end EulerRegularizedForcingRepresentative
