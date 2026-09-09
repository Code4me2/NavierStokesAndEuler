import Euler.CylinderTimeRegularity

/-! Exact ordinary derivatives of the raw covering field of a smooth cylinder representative. -/

noncomputable section

namespace EulerCylinderSmoothOrbit

open Set ContinuousLinearMap EulerSmoothLimit EulerLiftedGradientSpace
  EulerMetricTransport EulerTransportDerivatives EulerLiftedWeakDerivative
open scoped ContDiff

variable (P : ℝ) [Fact (0 < P)]
  {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

omit [Fact (0 < P)] [NormedAddCommGroup V] [NormedSpace ℝ V] in
theorem coverField_eq_local (f : LiftDomain P → V) :
    (fun z : LiftTangent => f (z.1,(z.2 : AddCircle P))) = localFieldLift P f 0 := by
  funext z
  simp only [localFieldLift, Prod.fst_zero, Prod.snd_zero, zero_add]

omit [Fact (0 < P)] in
theorem coverField_fderiv (f : LiftDomain P → V) (z : LiftTangent) :
    fderiv ℝ (fun y : LiftTangent => f (y.1,(y.2 : AddCircle P))) z =
      fieldFDeriv P f (z.1,(z.2 : AddCircle P)) := by
  rw [coverField_eq_local]
  exact (fderiv_localFieldLift_cover P f z).symm

omit [Fact (0 < P)] in
theorem coverField_contDiff (f : LiftDomain P → V)
    (hf : ∀ x, ContDiff ℝ ∞ (localFieldLift P f x)) :
    ContDiff ℝ ∞ (fun z : LiftTangent => f (z.1,(z.2 : AddCircle P))) := by
  rw [coverField_eq_local]
  exact hf 0


end EulerCylinderSmoothOrbit
