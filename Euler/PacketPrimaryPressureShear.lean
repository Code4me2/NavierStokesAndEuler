import Euler.PacketPrimaryScaling
import Euler.PacketGraphHessian

/-! The leading pressure tensor of the actual joined primary.  Both angular
derivatives below are derivatives of its constructed scalar pressure. -/

noncomputable section

namespace EulerPacketPrimaryPressure

open Set InnerProductSpace ContinuousLinearMap EulerSmoothLimit
  EulerLiftedGradientSpace EulerTransversePacketProvider EulerTransversePacketPrimary
  EulerPacketTerminalDatum EulerPacketPrimaryFactorization EulerPacketPrimaryShear
  EulerSpatialCutoffs EulerPeriodicProfile EulerPacketGraphHessian
  EulerGraphPullback EulerPacketInverseFlowGevrey
open scoped ContDiff

variable {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  {D : Data U} (τ : ℝ) (hτ : 0 < τ) (hτT : τ < D.T)
  (B : HistoryData (D.initial τ hτ hτT.le))
  (δ : ℝ) (hδ : 0 < δ) (ξ : U) (hs : tsupport innerCutoff ⊆ D.support)

def coefficient (a : ℝ) (t : Icc (0 : ℝ) D.T) (x : Space) : ℝ :=
  -(2*a*⟪D.normal.field t x,
    D.M.field t x (canonicalVelocity τ hτ hτT B ξ hs t x)⟫_ℝ)/‖D.normal.field t x‖^2

theorem scalar_hasDerivAt (a : ℝ) (t : Icc (0 : ℝ) D.T) (x : Space) (θ : ℝ) :
    HasDerivAt (fun s => scalar τ hτ hτT B (initialData D δ hδ (a • ξ) hs) (t,(x,s)))
      (coefficient τ hτ hτT B ξ hs a t x * profile δ θ) θ := by
  have he : (fun s => scalar τ hτ hτT B (initialData D δ hδ (a • ξ) hs) (t,(x,s))) =
      fun s : ℝ => pressureField τ hτ hτT B (initialData D δ hδ (a • ξ) hs) t
        (x,(s : AddCircle period)) :=
    funext (scalar_eq_pressureField τ hτ hτT B _ t x)
  rw [he]
  have ha := pressureField_angle τ hτ hτT B (initialData D δ hδ (a • ξ) hs) t x θ
  have hv := vector_terminal_smul τ hτ hτT B δ hδ ξ hs a t x θ
  rw [vector_factorization_canonical τ hτ hτT B δ hδ ξ hs t x θ] at hv
  simp only [vector,Data.clamp_coe] at hv
  have hr : normalResidual τ hτ hτT B (initialData D δ hδ (a • ξ) hs) t
      (x,(θ : AddCircle period)) = coefficient τ hτ hτT B ξ hs a t x * profile δ θ := by
    unfold normalResidual
    rw [hv]
    simp only [coefficient,map_smul,inner_smul_right]
    ring
  exact hr ▸ ha

theorem scalar_deriv (a : ℝ) (t : Icc (0 : ℝ) D.T) (x : Space) (θ : ℝ) :
    deriv (fun s => scalar τ hτ hτT B (initialData D δ hδ (a • ξ) hs) (t,(x,s))) θ =
      coefficient τ hτ hτT B ξ hs a t x * profile δ θ :=
  (scalar_hasDerivAt τ hτ hτT B δ hδ ξ hs a t x θ).deriv

theorem scalar_deriv_hasDerivAt (a : ℝ) (t : Icc (0 : ℝ) D.T) (x : Space) (θ : ℝ) :
    HasDerivAt
      (deriv (fun s => scalar τ hτ hτT B (initialData D δ hδ (a • ξ) hs) (t,(x,s))))
      (coefficient τ hτ hτT B ξ hs a t x * deriv (profile δ) θ) θ := by
  have he := funext (scalar_deriv τ hτ hτT B δ hδ ξ hs a t x)
  rw [he]
  exact ((profile_contDiff δ hδ).differentiable (by simp) θ).hasDerivAt.const_mul _

theorem scalar_second_deriv (a : ℝ) (t : Icc (0 : ℝ) D.T) (x : Space) (θ : ℝ) :
    deriv (deriv (fun s => scalar τ hτ hτT B
      (initialData D δ hδ (a • ξ) hs) (t,(x,s)))) θ =
      coefficient τ hτ hτT B ξ hs a t x * deriv (profile δ) θ :=
  (scalar_deriv_hasDerivAt τ hτ hτT B δ hδ ξ hs a t x θ).deriv


def physicalPressure (a k : ℝ) (t : Icc (0 : ℝ) D.T) (Y : Space → Space) (x : Space) : ℝ :=
  k⁻¹^2 * scalar τ hτ hτT B (initialData D δ hδ (a • ξ) hs)
    (t,(Y x,k*⟪D.m₀,Y x⟫_ℝ))




end EulerPacketPrimaryPressure
