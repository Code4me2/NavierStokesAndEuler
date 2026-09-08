import Euler.PacketInitialGeometry
import Euler.TransverseHistoryLipschitz

/-!
The actual fixed-terminal history estimate controls the scaled neighbor
initial velocity.  The loss `ε⁻¹` comes from the specified coordinate
rescaling and is independent of the oscillation frequency.
-/

noncomputable section


namespace EulerPacketMovingFrame

open Set EulerSmoothLimit EulerPacketNormalizedPrimary EulerPacketRay
  InnerProductSpace ContinuousLinearMap
  EulerTimeLp EulerVolterraConvolution EulerTimeH1FrameTransport
  EulerTransverseEndpointCoordinates EulerTransverseHistoryBounds

theorem frame_pair_difference_le {p q x y : Space} {ε D : ℝ}
    (hp : ‖p‖ = 1) (hq : ‖q‖ = 1) (hε : 0 < ε) (hε1 : ε ≤ 1) (hxy : ‖x-y‖ ≤ D) :
    |⟪p,x⟫_ℝ/ε-⟪p,y⟫_ℝ/ε|+|⟪q,x⟫_ℝ-⟪q,y⟫_ℝ| ≤ 2*D/ε := by
  have hp' : |⟪p,x-y⟫_ℝ| ≤ ‖x-y‖ := by
    simpa only [hp, one_mul] using abs_real_inner_le_norm p (x-y)
  have hq' : |⟪q,x-y⟫_ℝ| ≤ ‖x-y‖ := by
    simpa only [hq, one_mul] using abs_real_inner_le_norm q (x-y)
  have hU : |⟪p,x⟫_ℝ/ε-⟪p,y⟫_ℝ/ε| ≤ ‖x-y‖/ε := by
    rw [← sub_div, ← inner_sub_right, abs_div, abs_of_pos hε]
    exact div_le_div_of_nonneg_right hp' hε.le
  have hV : |⟪q,x⟫_ℝ-⟪q,y⟫_ℝ| ≤ ‖x-y‖/ε := by
    rw [← inner_sub_right]
    apply hq'.trans
    exact (le_div_iff₀ hε).mpr (mul_le_of_le_one_right (norm_nonneg _) hε1)
  have hD := div_le_div_of_nonneg_right hxy hε.le
  calc
    _ ≤ D/ε+D/ε := add_le_add (hU.trans hD) (hV.trans hD)
    _ = 2*D/ε := by ring

theorem scaledVelocity_initial_difference_le {m v x y : ℝ → Space}
    {t₀ a ε D : ℝ} (hm0 : m t₀ ≠ 0) (hv0 : v t₀ ≠ 0)
    (hε : 0 < ε) (hε1 : ε ≤ 1) (hxy : ‖x t₀-y t₀‖ ≤ D) :
    |scaledVelocity m v x t₀ a ε 0 0-scaledVelocity m v y t₀ a ε 0 0|+
      |scaledVelocity m v x t₀ a ε 0 1-scaledVelocity m v y t₀ a ε 0 1| ≤ 2*D/ε := by
  simpa [scaledVelocity, movingVelocity, physicalTime, normalizedFrame, frame,
    velocityScale, Fin.ext_iff] using
      frame_pair_difference_le (unit_norm hm0) (unit_norm hv0) hε hε1 hxy

theorem scaled_inner_difference_le {p x y : Space} {b D : ℝ}
    (hp : ‖p‖ = 1) (hb : 0 < b) (hxy : ‖x-y‖ ≤ D) :
    |⟪p,x⟫_ℝ/b-⟪p,y⟫_ℝ/b| ≤ D/b := by
  rw [← sub_div, ← inner_sub_right, abs_div, abs_of_pos hb]
  apply div_le_div_of_nonneg_right _ hb.le
  exact ((abs_real_inner_le_norm p (x-y)).trans_eq (by rw [hp, one_mul])).trans hxy

theorem scaledRay_initial_difference_le {m v x y : ℝ → Space} {s₀ t₀ a ε D : ℝ}
    (hs₀ : 0 < s₀) (hm0 : m t₀ ≠ 0) (hv0 : v t₀ ≠ 0) (hmv : ⟪m t₀,v t₀⟫_ℝ = 0)
    (hε : 0 < ε) (hε1 : ε ≤ 1) (hxy : ‖x t₀-y t₀‖ ≤ D) :
    norm3 (scaledRay m v x s₀ t₀ a ε 0 0-scaledRay m v y s₀ t₀ a ε 0 0)
      (scaledRay m v x s₀ t₀ a ε 0 1-scaledRay m v y s₀ t₀ a ε 0 1)
      (scaledRay m v x s₀ t₀ a ε 0 2-scaledRay m v y s₀ t₀ a ε 0 2) ≤
        3*D/(s₀*ε) := by
  have hn := (frame_orthonormal (unit (m t₀)) (unit (v t₀))
    (unit_inner_self hm0) (unit_inner_self hv0) (unit_inner_zero hmv)).norm_eq_one 2
  have hpn := scaled_inner_difference_le (unit_norm hm0) hs₀ hxy
  have hqn := scaled_inner_difference_le (unit_norm hv0) (mul_pos hs₀ hε) hxy
  have hnn := scaled_inner_difference_le hn hs₀ hxy
  have hD0 : 0 ≤ D := (norm_nonneg _).trans hxy
  have hden : D/s₀ ≤ D/(s₀*ε) := div_le_div_of_nonneg_left hD0 (mul_pos hs₀ hε)
    (mul_le_of_le_one_right hs₀.le hε1)
  have hall := add_le_add (add_le_add (hpn.trans hden) hqn) (hnn.trans hden)
  have hthree : D/(s₀*ε)+D/(s₀*ε)+D/(s₀*ε) = 3*D/(s₀*ε) := by ring
  rw [hthree] at hall
  simpa [norm3, scaledRay, movingRay, physicalTime, normalizedFrame, frame, rayScale,
    Fin.ext_iff] using hall

/-- A physical initial-ray error around the chosen normal becomes the
source's scaled ray error with the fixed factor `(s₀ ε)⁻¹`. -/
theorem scaledRay_initial_error {m v r : ℝ → Space} {s₀ t₀ a ε D : ℝ}
    (hs₀ : 0 < s₀) (hm0 : m t₀ ≠ 0) (hv0 : v t₀ ≠ 0) (hmv : ⟪m t₀,v t₀⟫_ℝ = 0)
    (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hr : ‖r t₀-s₀ • EulerPacketCrossProduct.cross (unit (m t₀)) (unit (v t₀))‖ ≤ D) :
    norm3 (scaledRay m v r s₀ t₀ a ε 0 0) (scaledRay m v r s₀ t₀ a ε 0 1)
      (scaledRay m v r s₀ t₀ a ε 0 2-1) ≤ 3*D/(s₀*ε) := by
  let r₀ : ℝ → Space := fun _ => s₀ • EulerPacketCrossProduct.cross (unit (m t₀)) (unit (v t₀))
  have hi : scaledRay m v r₀ s₀ t₀ a ε 0 = ![0,0,1] :=
    scaledRay_initial (ne_of_gt hs₀) hm0 hv0 hmv rfl
  have h := scaledRay_initial_difference_le (a := a) hs₀ hm0 hv0 hmv hε hε1 (y := r₀) hr
  simpa [hi] using h

variable {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]


variable (T : ℝ) (hT : 0 ≤ T)
  (Q Q₁ : C(Icc (0 : ℝ) T, U →L[ℝ] Space))
  (H : C(Icc (0 : ℝ) T, Space →L[ℝ] Space))
  (c : ℝ) (hc : 0 < c) (hQ : ∀ t ξ, c*‖ξ‖^2 ≤ ‖Q t ξ‖^2)
  (hd : ∀ t : Icc (0:ℝ) T, HasDerivWithinAt (extendPath T hT Q) (Q₁ t) (Icc (0:ℝ) T) t)
  (K : ℝ) (hK : 0 ≤ K) (hH : ∀ t z, ⟪H t z,z⟫_ℝ ≤ K*‖z‖^2)
  (hsmall : K*(T^2/2) ≤ 1/2)
  (P P₁ : C(Icc (0:ℝ) T, U →L[ℝ] Space))
  (G : C(Icc (0:ℝ) T, Space →L[ℝ] Space))
  (hP : ∀ t ξ, c*‖ξ‖^2 ≤ ‖P t ξ‖^2)
  (hp : ∀ t : Icc (0:ℝ) T, HasDerivWithinAt (extendPath T hT P) (P₁ t) (Icc (0:ℝ) T) t)
  (hG : ∀ t z, ⟪G t z,z⟫_ℝ ≤ K*‖z‖^2)


end EulerPacketMovingFrame
