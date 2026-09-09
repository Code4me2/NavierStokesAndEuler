import Euler.LpOperatorField
import Euler.BoundedFieldTimeDerivative

/-!
# Actual rectangular L² frame paths and their time derivatives

The coefficient-to-operator map is a contraction on supported Hilbert spaces.
Continuous coefficient paths and their literal pointwise time derivatives
therefore give genuine operator paths and derivatives. Frame lower bounds,
quadratic upper bounds and pointwise composition identities pass to these
actual L² operators without a support-margin constant.
-/

noncomputable section

namespace EulerLpOperatorField

open Set MeasureTheory ContinuousLinearMap InnerProductSpace EulerLpSupportedSubspace
  EulerVolterraConvolution
open scoped BoundedContinuousFunction

variable {α E F : Type*} [TopologicalSpace α] [MeasurableSpace α] [BorelSpace α]
  [SecondCountableTopology α] (μ : Measure α) (S : Set α) (hS : MeasurableSet S)
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]

private local instance : NormedAddCommGroup (E →L[ℝ] F) := inferInstance
private local instance : NormedSpace ℝ (E →L[ℝ] F) := inferInstance
private local instance : NormedAddCommGroup (α →ᵇ E →L[ℝ] F) := inferInstance
private local instance : NormedSpace ℝ (α →ᵇ E →L[ℝ] F) := inferInstance
private local instance : NormedAddCommGroup (supportedSpace (V := E) μ S hS) := inferInstance
private local instance : NormedSpace ℝ (supportedSpace (V := E) μ S hS) := inferInstance
private local instance : NormedAddCommGroup (supportedSpace (V := F) μ S hS) := inferInstance
private local instance : NormedSpace ℝ (supportedSpace (V := F) μ S hS) := inferInstance
private local instance : NormedAddCommGroup
    (supportedSpace (V := E) μ S hS →L[ℝ] supportedSpace (V := F) μ S hS) := inferInstance
private local instance : NormedSpace ℝ
    (supportedSpace (V := E) μ S hS →L[ℝ] supportedSpace (V := F) μ S hS) := inferInstance

/-- Linearity in the actual rectangular coefficient field. -/
theorem supported_add (A B : α →ᵇ E →L[ℝ] F) :
    supported μ S hS (A+B) = supported μ S hS A + supported μ S hS B := by
  apply ContinuousLinearMap.ext
  intro u
  apply Subtype.ext
  change full μ (A+B) (u : Lp E 2 μ) = full μ A (u : Lp E 2 μ) + full μ B (u : Lp E 2 μ)
  rw [full_add]
  rfl

theorem supported_smul (r : ℝ) (A : α →ᵇ E →L[ℝ] F) :
    supported μ S hS (r • A) = r • supported μ S hS A := by
  apply ContinuousLinearMap.ext
  intro u
  apply Subtype.ext
  change full μ (r • A) (u : Lp E 2 μ) = r • full μ A (u : Lp E 2 μ)
  rw [full_smul]
  rfl

/-- The literal linear dependence of the supported multiplier on its coefficient. -/
def supportedLinear : (α →ᵇ E →L[ℝ] F) →ₗ[ℝ]
    (supportedSpace (V := E) μ S hS →L[ℝ] supportedSpace (V := F) μ S hS) where
  toFun := supported μ S hS
  map_add' := supported_add μ S hS
  map_smul' := supported_smul μ S hS

/-- The real coefficient-to-L²-operator map on the supported spaces. -/
def supportedMap : (α →ᵇ E →L[ℝ] F) →L[ℝ]
    (supportedSpace (V := E) μ S hS →L[ℝ] supportedSpace (V := F) μ S hS) where
  toLinearMap := supportedLinear μ S hS
  cont := AddMonoidHomClass.continuous_of_bound (supportedLinear μ S hS) 1 (fun A => by
    change ‖supported μ S hS A‖ ≤ 1*‖A‖
    simpa only [one_mul] using
      supported_norm μ S hS A ‖A‖ (norm_nonneg _) (fun x _ => A.norm_coe_le_norm x))



variable {K : Type*} [TopologicalSpace K] [CompactSpace K]

/-- The actual rectangular coefficient map uniformly along a compact time set. -/
def supportedPathMap : C(K,α →ᵇ E →L[ℝ] F) →L[ℝ]
    C(K,supportedSpace (V := E) μ S hS →L[ℝ] supportedSpace (V := F) μ S hS) :=
  (supportedMap (E := E) (F := F) μ S hS).compLeftContinuous ℝ K

omit [CompactSpace K] in
@[simp] theorem supportedPathMap_apply (A : C(K,α →ᵇ E →L[ℝ] F)) (t : K) :
    supportedPathMap μ S hS A t = supported μ S hS (A t) := rfl



section Derivative

variable [CompleteSpace F]
  (T : ℝ) (hT : 0 ≤ T) (A A' : C(Icc (0 : ℝ) T,α →ᵇ E →L[ℝ] F))


end Derivative


end EulerLpOperatorField
