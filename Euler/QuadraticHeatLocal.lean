import Euler.QuadraticCoefficients

/-! Positive-time existence for the actual projected quadratic cylinder correction equation. -/

noncomputable section

namespace EulerQuadraticSource

open MeasureTheory Set EulerCylinderSobolevSpace EulerSobolevHeat
open scoped Topology

/-- Inclusion of a shorter initial time interval into a prescribed positive interval. -/
def timeInclusion {T S : ℝ} (hTS : T ≤ S) : C(Icc (0 : ℝ) T, Icc (0 : ℝ) S) where
  toFun t := ⟨t.val, t.property.1, t.property.2.trans hTS⟩
  continuous_toFun := continuous_subtype_val.subtype_mk _

variable (period : ℝ) [Fact (0 < period)]

local instance sobolevGroup (q : ℕ) : NormedAddCommGroup (SobolevSpace period q) := inferInstance
local instance sobolevRealSpace (q : ℕ) : NormedSpace ℝ (SobolevSpace period q) := inferInstance

/-- The genuine heat Duhamel expression for continuous projected quadratic coefficients. -/
def quadraticDuhamel {q : ℕ} (ν : ℝ) (hν : 0 < ν) {S T : ℝ} (hT : 0 ≤ T) (hTS : T ≤ S)
    (C : Coefficients (Icc (0 : ℝ) S) (SobolevSpace period (q+1)) (SobolevSpace period q))
    (u₀ : SobolevSpace period (q+1)) (u : C(Icc (0 : ℝ) T, SobolevSpace period (q+1)))
    (t : Icc (0 : ℝ) T) : SobolevSpace period (q+1) :=
  heatOperator period (q+1) (2*ν*t.val).toNNReal u₀ +
    ∫ τ in (0 : ℝ)..t.val, heatKernel period q ν hν τ
      (C.apply (timeInclusion hTS (projIcc 0 T hT (t.val-τ))) (u (projIcc 0 T hT (t.val-τ))))


end EulerQuadraticSource
