import Euler.HeatMaximalCauchy
import Euler.RegularizedMildEquation
import Euler.TimeLpMap

/-! Genuine maximal spatial regularity of the actual viscous mild solution, proved by strong Cauchy limits. -/

noncomputable section

namespace EulerHeatMaximalRegularity

open MeasureTheory Set EulerLiftedGradientSpace EulerCylinderSobolevSpace EulerSobolevHeat
  EulerSobolevLaplacian EulerTimeLp EulerVolterraConvolution EulerRegularizedMildEquation
  EulerHeatMaximalCauchy EulerHeatMaximalEstimate
open scoped Topology

variable (period : ℝ) [Fact (0 < period)]

/-- The actual regularized mild solutions are strongly Cauchy in Bochner L² time with two derivatives. -/
theorem regularized_mild_cauchy (T : ℝ) (hT : 0 ≤ T) (ν : ℝ) (hν : 0 < ν)
    (u₀ : SobolevSpace period 1) (f : C(Icc (0 : ℝ) T, SobolevSpace period 0))
    (u : C(Icc (0 : ℝ) T, SobolevSpace period 1))
    (hsol : ∀ t : Icc (0 : ℝ) T,
      u t = heatOperator period 1 (2*ν*t.val).toNNReal u₀ +
        ∫ r in (0 : ℝ)..t.val, heatKernel period 0 ν hν r (extendPath T hT f (t.val-r))) :
    CauchySeq (fun n => higherTime period T hT (regularizedState period T n u)) := by
  apply heat_H2_cauchy period T hT ν hν (fun n => regularizedState period T n u)
    (fun n => regularizedForcing period T n f)
    (regularizedState_first_time_derivative period T hT ν hν u₀ f u hsol)
  · exact (regularizedState_low_tendsto period T u).cauchySeq
  · exact (pathLp_tendsto T hT _ _ (regularizedForcing_value_tendsto period T f)).cauchySeq

/-- The strong higher-order limit has exactly the original lower-order field almost everywhere in time. -/
theorem regularized_limit_restriction (T : ℝ) (hT : 0 ≤ T)
    (u : C(Icc (0 : ℝ) T, SobolevSpace period 1)) (U : TimeLp T (SobolevSpace period 2))
    (hU : Filter.Tendsto (fun n => higherTime period T hT (regularizedState period T n u)) Filter.atTop (𝓝 U)) :
    ((fun t => truncateOperator period 1 (U t)) =ᵐ[timeMeasure T] extendPath T hT u) := by
  have hlow := regularizedState_low_tendsto period T u
  have hrestrict : Filter.Tendsto (fun n => (truncateOperator period 1).compLeftContinuous ℝ (Icc (0 : ℝ) T)
      ((truncateOperator period 2).compLeftContinuous ℝ (Icc (0 : ℝ) T) (regularizedState period T n u))) Filter.atTop (𝓝 u) := by
    convert hlow using 1
    funext n
    apply ContinuousMap.ext
    intro t
    apply value_injective period
    rfl
  exact limit_restriction_ae T hT (truncateOperator period 1)
    (fun n => (truncateOperator period 2).compLeftContinuous ℝ (Icc (0 : ℝ) T) (regularizedState period T n u)) u U hU hrestrict


/-- Completeness of actual H² Bochner space constructs its strong Cauchy limit. -/
theorem exists_H2_time_limit (T : ℝ) (u : ℕ → TimeLp T (SobolevSpace period 2)) (hu : CauchySeq u) :
    ∃ U : TimeLp T (SobolevSpace period 2), Filter.Tendsto u Filter.atTop (𝓝 U) :=
  cauchySeq_tendsto_of_complete hu

/-- Strong completion constructs the higher-order limit of the concrete mild-solution approximations. -/
theorem exists_regularized_mild_limit (T : ℝ) (hT : 0 ≤ T) (ν : ℝ) (hν : 0 < ν)
    (u₀ : SobolevSpace period 1) (f : C(Icc (0 : ℝ) T, SobolevSpace period 0))
    (u : C(Icc (0 : ℝ) T, SobolevSpace period 1))
    (hsol : ∀ t : Icc (0 : ℝ) T,
      u t = heatOperator period 1 (2*ν*t.val).toNNReal u₀ +
        ∫ r in (0 : ℝ)..t.val, heatKernel period 0 ν hν r (extendPath T hT f (t.val-r))) :
    ∃ U : TimeLp T (SobolevSpace period 2),
      Filter.Tendsto (fun n => higherTime period T hT (regularizedState period T n u)) Filter.atTop (𝓝 U) := by
  have hc : CauchySeq (fun n => higherTime period T hT (regularizedState period T n u)) :=
    regularized_mild_cauchy period T hT ν hν u₀ f u hsol
  exact exists_H2_time_limit period T (fun n => higherTime period T hT (regularizedState period T n u)) hc

/-- The actual viscous mild solution with H¹ values and continuous L² source has two full spatial derivatives in L² time.
The higher-regularity element is constructed in the complete Bochner space and identified with the original field almost everywhere. -/
theorem viscous_mild_maximal_regularity (T : ℝ) (hT : 0 ≤ T) (ν : ℝ) (hν : 0 < ν)
    (u₀ : SobolevSpace period 1) (f : C(Icc (0 : ℝ) T, SobolevSpace period 0))
    (u : C(Icc (0 : ℝ) T, SobolevSpace period 1))
    (hsol : ∀ t : Icc (0 : ℝ) T,
      u t = heatOperator period 1 (2*ν*t.val).toNNReal u₀ +
        ∫ r in (0 : ℝ)..t.val, heatKernel period 0 ν hν r (extendPath T hT f (t.val-r))) :
    ∃ U : TimeLp T (SobolevSpace period 2),
      ((fun t => truncateOperator period 1 (U t)) =ᵐ[timeMeasure T] extendPath T hT u) ∧
      Filter.Tendsto (fun n => higherTime period T hT (regularizedState period T n u)) Filter.atTop (𝓝 U) := by
  refine (exists_regularized_mild_limit period T hT ν hν u₀ f u hsol).imp ?_
  intro U hU
  exact ⟨regularized_limit_restriction period T hT u U hU, hU⟩


end EulerHeatMaximalRegularity
