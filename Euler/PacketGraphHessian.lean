import Euler.PacketContinuousInverse
import Euler.PacketCylinderPressureLocality

/-! Differentiating an actual oscillatory scalar pressure through the
inverse flow. The principal Hessian is the angular second derivative
times the square of the transported normal. -/

noncomputable section

namespace EulerPacketGraphHessian

open Set InnerProductSpace ContinuousLinearMap EulerSmoothLimit EulerGraphPullback
  EulerLiftedGradientSpace
open scoped ContDiff

def spatialGradient (q : LiftTangent → ℝ) (z : LiftTangent) : Space :=
  (toDual ℝ Space).symm ((fderiv ℝ q z).comp (inl ℝ Space ℝ))

def angularDerivative (q : LiftTangent → ℝ) (z : LiftTangent) : ℝ :=
  fderiv ℝ q z (0,1)


theorem angularDerivative_contDiff {q : LiftTangent → ℝ} (hq : ContDiff ℝ ∞ q) :
    ContDiff ℝ ∞ (angularDerivative q) :=
  (contDiff_infty_iff_fderiv.mp hq).2.clm_apply contDiff_const

theorem angularDerivative_eq_deriv {q : LiftTangent → ℝ} {z : LiftTangent}
    (hq : DifferentiableAt ℝ q z) :
    angularDerivative q z = deriv (fun θ => q (z.1,θ)) z.2 := by
  exact ((hq.hasFDerivAt.comp_hasDerivAt z.2
    ((hasDerivAt_const z.2 z.1).prodMk (hasDerivAt_id z.2))).deriv).symm

theorem angularSecond_eq_deriv {q : LiftTangent → ℝ} (hq : ContDiff ℝ ∞ q)
    (z : LiftTangent) :
    angularDerivative (angularDerivative q) z =
      deriv (deriv (fun θ => q (z.1,θ))) z.2 := by
  rw [angularDerivative_eq_deriv ((angularDerivative_contDiff hq).differentiable (by simp) z)]
  congr 1
  funext θ
  exact angularDerivative_eq_deriv (hq.differentiable (by simp) (z.1,θ))

theorem graph_decomposition (k : ℝ) (m v : Space) :
    graphMap k m v = (v,0)+(k*⟪m,v⟫_ℝ) • (0,1) := by
  ext i <;> simp [graphMap_apply]

theorem gradient_graph {q : LiftTangent → ℝ} (k : ℝ) (m x : Space)
    (hq : DifferentiableAt ℝ q (graphMap k m x)) :
    gradient (fun y => q (graphMap k m y)) x =
      spatialGradient q (graphMap k m x)+
        (k*angularDerivative q (graphMap k m x)) • m := by
  apply ext_inner_right ℝ
  intro v
  have hd : fderiv ℝ (fun y => q (graphMap k m y)) x =
      (fderiv ℝ q (graphMap k m x)).comp (graphMap k m) :=
    (hq.hasFDerivAt.comp x (graphMap k m).hasFDerivAt).fderiv
  rw [inner_gradient_left,hd]
  simp only [comp_apply,inner_add_left,real_inner_smul_left,spatialGradient,toDual_symm_apply,
    inl_apply,graph_decomposition,map_add,map_smul,smul_eq_mul,angularDerivative]
  ring


def transportedNormal (m : Space) (J : Space → Space →L[ℝ] Space) (x : Space) : Space :=
  (J x).adjoint m





end EulerPacketGraphHessian
