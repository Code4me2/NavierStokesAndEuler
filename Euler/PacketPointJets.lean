import Euler.EulerProof
import Euler.PacketResidualGrades

/-! The linear and bilinear packet operators on actual space-time value/derivative jets. -/

noncomputable section


namespace EulerPacketPointJets

open EulerSmoothLimit InnerProductSpace EulerFiniteGrades
open scoped ContDiff

abbrev Domain := ℝ × (Space × ℝ)
abbrev Jet (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] := E × (Domain →L[ℝ] E)
abbrev VectorJet := Jet Space
abbrev ScalarJet := Jet ℝ

def timeDirection : Domain := (1, (0, 0))
def angleDirection : Domain := (0, (0, 1))

def spatialInjection : Space →L[ℝ] Domain :=
  (0 : Space →L[ℝ] ℝ).prod ((ContinuousLinearMap.id ℝ Space).prod (0 : Space →L[ℝ] ℝ))


def linearPart (M : Space →L[ℝ] Space) : VectorJet →ₗ[ℝ] Space where
  toFun J := J.2 timeDirection + M J.1
  map_add' J K := by simp [add_add_add_comm]
  map_smul' c J := by simp [smul_add]

def slowPressure (FInv : Space →L[ℝ] Space) : ScalarJet →ₗ[ℝ] Space where
  toFun J := FInv.adjoint ((toDual ℝ Space).symm (J.2.comp spatialInjection))
  map_add' J K := by simp [ContinuousLinearMap.add_comp]
  map_smul' c J := by simp [ContinuousLinearMap.smul_comp]

def fastPressure (m : Space) : ScalarJet →ₗ[ℝ] Space where
  toFun J := J.2 angleDirection • m
  map_add' J K := by simp [add_smul]
  map_smul' c J := by simp [smul_smul]

def slowAdvection (FInv : Space →L[ℝ] Space) : VectorJet →ₗ[ℝ] VectorJet →ₗ[ℝ] Space where
  toFun J :=
    { toFun := fun K => K.2 (spatialInjection (FInv J.1))
      map_add' K H := by simp
      map_smul' c K := by simp }
  map_add' J K := by
    apply LinearMap.ext
    intro H
    simp
  map_smul' c J := by
    apply LinearMap.ext
    intro K
    simp

def fastAdvection (m : Space) : VectorJet →ₗ[ℝ] VectorJet →ₗ[ℝ] Space where
  toFun J :=
    { toFun := fun K => ⟪m, J.1⟫_ℝ • K.2 angleDirection
      map_add' K H := by simp [smul_add]
      map_smul' c K := by simp [smul_smul, mul_comm] }
  map_add' J K := by
    apply LinearMap.ext
    intro H
    simp [inner_add_right, add_smul]
  map_smul' c J := by
    apply LinearMap.ext
    intro K
    simp [inner_smul_right, smul_smul]

def fieldSum {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (M : ℕ) (κ : ℝ) (u : ℕ → Domain → E) (z : Domain) : E :=
  evaluate M κ (fun n => u n z)




end EulerPacketPointJets
