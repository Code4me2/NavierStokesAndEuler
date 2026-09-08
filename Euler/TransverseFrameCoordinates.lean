import Euler.TransverseVariationalOperator

/-!
# Recovering the source's transverse coordinates

The moving plane with normal `(F⁻¹)* m₀` is exactly the image under `F` of
the fixed plane `m₀⊥`.  Orthogonal projection gives a bounded coordinate map,
and on the moving plane its reconstruction is the identity.  These are
coefficient identities, not assumptions about a differential inverse.
-/

noncomputable section

namespace EulerTransverseFrameCoordinates

open InnerProductSpace ContinuousLinearMap

variable {E U : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup U] [InnerProductSpace ℝ U]

/-- The fixed reference transverse plane. -/
abbrev referencePlane (m₀ : E) : Submodule ℝ E := (ℝ ∙ m₀)ᗮ

/-- The actual pulled-back normal used by the packet construction. -/
def movingNormal (F : E ≃L[ℝ] E) (m₀ : E) : E := F.symm.toContinuousLinearMap.adjoint m₀

/-- Bounded recovery of fixed-plane coordinates from a physical displacement. -/
def coordinates (F : E ≃L[ℝ] E) (m₀ : E) : E →L[ℝ] referencePlane m₀ :=
  (referencePlane m₀).orthogonalProjectionOnto.comp F.symm.toContinuousLinearMap

/-- Moving tangency is exactly fixed-plane membership after applying `F⁻¹`. -/
theorem tangent_iff (F : E ≃L[ℝ] E) (m₀ η : E) :
    ⟪movingNormal F m₀, η⟫_ℝ = 0 ↔ F.symm η ∈ referencePlane m₀ := by
  rw [Submodule.mem_orthogonal_singleton_iff_inner_right]
  unfold movingNormal
  rw [adjoint_inner_left]
  rfl

/-- Reconstructing a tangent displacement from its recovered coordinates is exact. -/
theorem reconstruct (F : E ≃L[ℝ] E) (m₀ η : E)
    (hη : ⟪movingNormal F m₀, η⟫_ℝ = 0) :
    F (coordinates F m₀ η : E) = η := by
  have hm : F.symm η ∈ referencePlane m₀ := (tangent_iff F m₀ η).1 hη
  have hp := (referencePlane m₀).orthogonalProjectionOnto_mem_subspace_eq_self
    (⟨F.symm η, hm⟩ : referencePlane m₀)
  change F ((referencePlane m₀).orthogonalProjectionOnto (F.symm η) : E) = η
  rw [hp]
  exact F.apply_symm_apply η



/-- Any orthonormal identification with the fixed plane gives the source's `R⊥` coordinates. -/
def frameCoordinates (F : E ≃L[ℝ] E) (m₀ : E)
    (R : U ≃ₗᵢ[ℝ] referencePlane m₀) : E →L[ℝ] U :=
  R.symm.toContinuousLinearEquiv.toContinuousLinearMap.comp (coordinates F m₀)

/-- The full source reconstruction `η = F R⊥ ξ` follows from moving tangency. -/
theorem frame_reconstruct (F : E ≃L[ℝ] E) (m₀ η : E)
    (R : U ≃ₗᵢ[ℝ] referencePlane m₀) (hη : ⟪movingNormal F m₀, η⟫_ℝ = 0) :
    F (R (frameCoordinates F m₀ R η) : E) = η := by
  change F (R (R.symm (coordinates F m₀ η)) : E) = η
  rw [R.apply_symm_apply]
  exact reconstruct F m₀ η hη


section Paths

variable {X : Type*} [TopologicalSpace X]

/-- Applying a continuous inverse-frame path produces actual continuous
transverse coordinates, not separate incompatible pointwise choices. -/
def coordinatePath (m₀ : E) (R : U ≃ₗᵢ[ℝ] referencePlane m₀)
    (A : C(X, E →L[ℝ] E)) (η : C(X, E)) : C(X, U) :=
  ⟨fun t => R.symm ((referencePlane m₀).orthogonalProjectionOnto (A t (η t))),
    R.symm.continuous.comp ((referencePlane m₀).orthogonalProjectionOnto.continuous.comp
      (A.continuous.clm_apply η.continuous))⟩




end Paths

end EulerTransverseFrameCoordinates
