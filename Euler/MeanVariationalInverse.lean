import Euler.TerminalTimePrimitive
import Euler.MeanSolenoidalSpace
import Euler.MeanVariationalOperator

/-!
# A genuine mean time-variational inverse on ordinary spatial L²

The Hilbert variable is the time derivative of the physical displacement η.
Terminal integration constructs η, and the closed constraints require
`FInv(t) η(t)` to be an actual ordinary-space solenoidal field at every time.
The exact initial form is `M0 + L A`, not a replacement boundary condition.

The lower bound for this given boundary operator on solenoidal fields remains
an explicit input.  In the source it must be proved from the concrete cutoff
operator and harmonic localization.  This file does not claim that step, the
strong interior equation, or the initial derivative boundary identity.  The
recovered `z=FInv η` is continuous here; its H¹ regularity additionally uses the
source's C¹-in-time inverse deformation.
-/

noncomputable section


namespace EulerMeanVariationalInverse

open MeasureTheory Set InnerProductSpace ContinuousLinearMap
  EulerTimeLp EulerTerminalTimePrimitive EulerMeanSolenoidal
  EulerTransverseVariationalInverse

/-- Derivatives whose actual terminal primitives obey the solenoidal label constraint. -/
def meanDerivatives (T : ℝ) (hT : 0 ≤ T)
    (FInv : C(Icc (0 : ℝ) T, L2 →L[ℝ] L2)) : Submodule ℝ (TimeLp T L2) where
  carrier := {u | ∀ t, FInv t (terminalPrimitive T hT u t) ∈ solenoidalSpace}
  zero_mem' := by
    intro t
    simp only [map_zero, ContinuousMap.zero_apply, Submodule.zero_mem]
  add_mem' := by
    intro u v hu hv t
    simpa only [map_add, ContinuousMap.add_apply] using solenoidalSpace.add_mem (hu t) (hv t)
  smul_mem' := by
    intro a u hu t
    simpa only [map_smul, ContinuousMap.smul_apply] using solenoidalSpace.smul_mem a (hu t)

/-- Every genuine absolutely continuous terminal-zero path with an L² derivative
and the label-solenoidal constraint is represented in this Hilbert space. -/
theorem derivative_mem_of_ac (T : ℝ) (hT : 0 ≤ T)
    (FInv : C(Icc (0 : ℝ) T, L2 →L[ℝ] L2)) (u : TimeLp T L2) (η : ℝ → L2)
    (hη : AbsolutelyContinuousOnInterval η 0 T)
    (hder : ∀ᵐ t ∂timeMeasure T, HasDerivAt η (u t) t) (hterminal : η T = 0)
    (hsolenoidal : ∀ t : Icc (0 : ℝ) T, FInv t (η t) ∈ solenoidalSpace) :
    u ∈ meanDerivatives T hT FInv := by
  intro t
  change FInv t (realPrimitive T u t) ∈ solenoidalSpace
  rw [← eq_realPrimitive_of_ac_hasDerivAt_ae T hT u η hη hder hterminal t t.property]
  exact hsolenoidal t

/-- Every time constraint is the preimage of the actual closed solenoidal subspace. -/
theorem meanDerivatives_closed (T : ℝ) (hT : 0 ≤ T)
    (FInv : C(Icc (0 : ℝ) T, L2 →L[ℝ] L2)) :
    IsClosed (meanDerivatives T hT FInv : Set (TimeLp T L2)) := by
  change IsClosed {u : TimeLp T L2 | ∀ t, FInv t (terminalPrimitive T hT u t) ∈ solenoidalSpace}
  rw [Set.ofPred_forall]
  apply isClosed_iInter
  intro t
  exact gradientSpace.isClosed_orthogonal.preimage
    ((FInv t).continuous.comp (evaluation T hT t).continuous)

/-- The genuine closed constraint space is a complete Hilbert space. -/
instance meanDerivatives_complete (T : ℝ) (hT : 0 ≤ T)
    (FInv : C(Icc (0 : ℝ) T, L2 →L[ℝ] L2)) :
    CompleteSpace (meanDerivatives T hT FInv) :=
  (meanDerivatives_closed T hT FInv).completeSpace_coe

/-- The actual displacement primitive, restricted to the mean constraint space. -/
def meanPrimitive (T : ℝ) (hT : 0 ≤ T)
    (FInv : C(Icc (0 : ℝ) T, L2 →L[ℝ] L2)) :
    meanDerivatives T hT FInv →L[ℝ] TimeLp T L2 :=
  (primitiveTimeLp T hT).comp (meanDerivatives T hT FInv).subtypeL

/-- The actual initial trace on that same constraint space. -/
def meanTrace (T : ℝ) (hT : 0 ≤ T)
    (FInv : C(Icc (0 : ℝ) T, L2 →L[ℝ] L2)) :
    meanDerivatives T hT FInv →L[ℝ] L2 :=
  (initialTrace T hT).comp (meanDerivatives T hT FInv).subtypeL

/-- The sharp source Poincaré estimate survives restriction to the constraint space. -/
theorem meanPrimitive_norm_sq (T : ℝ) (hT : 0 ≤ T)
    (FInv : C(Icc (0 : ℝ) T, L2 →L[ℝ] L2)) (u : meanDerivatives T hT FInv) :
    ‖meanPrimitive T hT FInv u‖^2 ≤ T^2/2*‖u‖^2 :=
  primitiveTimeLp_norm_sq_le T hT (u : TimeLp T L2)

/-- The source initial trace estimate is an estimate of this literal trace. -/
theorem meanTrace_norm_sq (T : ℝ) (hT : 0 ≤ T)
    (FInv : C(Icc (0 : ℝ) T, L2 →L[ℝ] L2)) (u : meanDerivatives T hT FInv) :
    ‖meanTrace T hT FInv u‖^2 ≤ T*‖u‖^2 :=
  initialTrace_norm_sq_le T hT (u : TimeLp T L2)

/-- The normalization of the deformation makes the initial physical trace solenoidal. -/
theorem meanTrace_mem (T : ℝ) (hT : 0 ≤ T)
    (FInv : C(Icc (0 : ℝ) T, L2 →L[ℝ] L2))
    (hF0 : FInv ⟨0, le_rfl, hT⟩ = ContinuousLinearMap.id ℝ L2)
    (u : meanDerivatives T hT FInv) : meanTrace T hT FInv u ∈ solenoidalSpace := by
  have hu := u.property ⟨0, le_rfl, hT⟩
  rwa [hF0, id_apply] at hu

/-- Only the boundary lower bound on actual solenoidal traces is needed. -/
theorem meanTrace_boundary (T : ℝ) (hT : 0 ≤ T)
    (FInv : C(Icc (0 : ℝ) T, L2 →L[ℝ] L2))
    (M0 A : L2 →L[ℝ] L2) (L B : ℝ)
    (hF0 : FInv ⟨0, le_rfl, hT⟩ = ContinuousLinearMap.id ℝ L2)
    (hboundary : ∀ z : L2, z ∈ solenoidalSpace →
      -B*‖z‖^2 ≤ ⟪M0 z, z⟫_ℝ+L*⟪A z, z⟫_ℝ)
    (u : meanDerivatives T hT FInv) :
    -B*‖meanTrace T hT FInv u‖^2 ≤
      ⟪(M0+L • A) (meanTrace T hT FInv u), meanTrace T hT FInv u⟫_ℝ := by
  simpa only [add_apply, smul_apply, inner_add_left, real_inner_smul_left] using
    hboundary (meanTrace T hT FInv u) (meanTrace_mem T hT FInv hF0 u)






variable (T : ℝ) (hT : 0 ≤ T)
  (FInv : C(Icc (0 : ℝ) T, L2 →L[ℝ] L2))
  (H : C(Icc (0 : ℝ) T, L2 →L[ℝ] L2)) (M0 A : L2 →L[ℝ] L2)
  (L K B : ℝ) (hK : 0 ≤ K) (hB : 0 ≤ B)
  (hF0 : FInv ⟨0, le_rfl, hT⟩ = ContinuousLinearMap.id ℝ L2)
  (hH : ∀ t z, ⟪H t z, z⟫_ℝ ≤ K*‖z‖^2)
  (hboundary : ∀ z : L2, z ∈ solenoidalSpace →
    -B*‖z‖^2 ≤ ⟪M0 z, z⟫_ℝ+L*⟪A z, z⟫_ℝ)
  (hsmall : K*(T^2/2)+B*T ≤ 1/2)

/-- The mean forcing-to-displacement-derivative map is constructed by Lax--Milgram. -/
def meanSolver : TimeLp T L2 →L[ℝ] meanDerivatives T hT FInv :=
  EulerMeanVariationalOperator.meanSolver (meanPrimitive T hT FInv) (meanTrace T hT FInv)
    (timeMultiplier T hT H) (M0+L • A) (T^2/2) T K B hK hB
    (meanPrimitive_norm_sq T hT FInv) (meanTrace_norm_sq T hT FInv)
    (timeMultiplier_quadratic_upper T hT H K hH)
    (meanTrace_boundary T hT FInv M0 A L B hF0 hboundary) hsmall








/-- The exact mean form with the two original initial boundary terms. -/
theorem meanSolver_weak (f : TimeLp T L2) (v : meanDerivatives T hT FInv) :
    let u := meanSolver T hT FInv H M0 A L K B hK hB hF0 hH hboundary hsmall f
    ⟪(u : TimeLp T L2), (v : TimeLp T L2)⟫_ℝ-
      ⟪timeMultiplier T hT H (meanPrimitive T hT FInv u), meanPrimitive T hT FInv v⟫_ℝ+
      ⟪M0 (meanTrace T hT FInv u), meanTrace T hT FInv v⟫_ℝ+
      L*⟪A (meanTrace T hT FInv u), meanTrace T hT FInv v⟫_ℝ =
      -⟪f, meanPrimitive T hT FInv v⟫_ℝ := by
  simpa only [meanSolver, Submodule.coe_inner, add_apply, smul_apply, inner_add_left,
    real_inner_smul_left, add_assoc] using
    EulerMeanVariationalOperator.meanSolver_weak (meanPrimitive T hT FInv) (meanTrace T hT FInv)
      (timeMultiplier T hT H) (M0+L • A) (T^2/2) T K B hK hB
      (meanPrimitive_norm_sq T hT FInv) (meanTrace_norm_sq T hT FInv)
      (timeMultiplier_quadratic_upper T hT H K hH)
      (meanTrace_boundary T hT FInv M0 A L B hF0 hboundary) hsmall f v





end EulerMeanVariationalInverse
