import Euler.PhysicalGraphFlowBounds
import Euler.SmoothL2GevreyCalculus
import Euler.SmoothFlowCoefficientPaths

/-! Uniform bounds needed for composition with the physical graph flow.
The small lifted displacement controls positive derivatives of the
physical coordinate change without a physical-frequency Grönwall bound. -/

noncomputable section

namespace EulerPhysicalGraphFlowBounds.Data

open Set MeasureTheory ContinuousLinearMap EulerLiftedGradientSpace EulerSmoothBanachFlow
  EulerSmoothFlowGevrey EulerGraphInvariantFlow EulerPhysicalGraphGevrey
  EulerCylinderGraphGevrey EulerGevrey
open scoped ContDiff

variable {P T : ℝ} [Fact (0 < P)] (G : Data P T)

theorem displacement_sup_bound (k : ℝ) (m : Vector3) (ell : ℝ)
    (hell : 0 < ell) (hell1 : ell ≤ 1) (t : Icc (0 : ℝ) T) :
    HasSupBound (G.displacementField k m ell hell t).field (G.B*T)
      (ell⁻¹*(4*G.R*graphFactor k m)) := by
  intro n x
  apply physicalField_sup_bound P _ _ _ k m (T*G.C) G.velocityRadius
    (mul_nonneg G.time_nonneg G.C_nonneg) G.velocityRadius_nonneg _ _ ell hell hell1
    (fst ℝ Vector3 ℝ) (norm_fst_le ..) (G.B*T) (4*G.R)
  intro j z
  have he : (fun y => displacementFamily T G.time_nonneg G.A y t) =
      displacement T G.time_nonneg G.A t := by
    funext y
    simp only [displacement,EulerVolterraConvolution.extendPath,projIcc_of_mem G.time_nonneg t.property]
  rw [← he]
  exact displacementFamily_jet_bound T G.time_nonneg G.A G.B G.R G.B_nonneg G.R_pos G.small
    G.sup_bound j t z

theorem velocity_sup_bound (k : ℝ) (m : Vector3) (ell : ℝ)
    (hell : 0 < ell) (hell1 : ell ≤ 1) (t : Icc (0 : ℝ) T) :
    HasSupBound (G.velocityField k m ell hell t).field G.B
      (ell⁻¹*(flowRadius G.B G.R T G.R*graphFactor k m)) := by
  intro n x
  apply physicalField_sup_bound P _ _ _ k m G.C G.velocityRadius
    G.C_nonneg G.velocityRadius_nonneg _ _ ell hell hell1
    (fst ℝ Vector3 ℝ) (norm_fst_le ..) G.B (flowRadius G.B G.R T G.R)
  exact fun j z => materialVelocity_bound T G.time_nonneg G.A G.B G.R
    G.B_nonneg G.R_pos G.small G.sup_bound j t z

variable (k : ℝ) (m : Vector3) (hgraph : ∀ t z, graphConstraint k m (G.A.field t z)=0)


end EulerPhysicalGraphFlowBounds.Data
