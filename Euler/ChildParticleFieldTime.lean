import Euler.ChildParticleTime
import Euler.ChildParticleFieldBounds

/-! The L² child fields used in the estimates are exactly the actual
first and second time derivatives of the composed particle map. -/

noncomputable section

namespace EulerChildParticleTime

open Set EulerSmoothLimit

variable {T : ℝ}

/-- Compatibility of two actual realizations of the six input fields.
These are literal value identities, not derivative or output assumptions. -/
structure Representation (G : Icc (0 : ℝ) T → EulerChildParticleFieldBounds.Data)
    (P P₁ P₂ D D₁ D₂ : SmoothTimeField (Icc (0 : ℝ) T) Space Space) : Prop where
  parentDisplacement : ∀ t x, (G t).parentDisplacement.field x=P.field t x
  parentVelocity : ∀ t x, (G t).parentVelocity.field x=P₁.field t x
  parentAcceleration : ∀ t x, (G t).parentAcceleration.field x=P₂.field t x
  displacement : ∀ t x, (G t).displacement.field x=D.field t x
  velocity : ∀ t x, (G t).velocity.field x=D₁.field t x
  acceleration : ∀ t x, (G t).acceleration.field x=D₂.field t x

namespace Representation

variable {G : Icc (0 : ℝ) T → EulerChildParticleFieldBounds.Data}
  {P P₁ P₂ D D₁ D₂ : SmoothTimeField (Icc (0 : ℝ) T) Space Space}
  (H : Representation G P P₁ P₂ D D₁ D₂)

include H

theorem childDisplacement (t : Icc (0 : ℝ) T) (x : Space) :
    (G t).childDisplacement.field x=(EulerChildParticleTime.displacement P D).field t x := by
  rw [EulerChildParticleFieldBounds.Data.childDisplacement_apply,displacement_apply]
  simp only [EulerChildParticleFieldBounds.Data.inner,H.parentDisplacement,H.displacement]

theorem childVelocity (t : Icc (0 : ℝ) T) (x : Space) :
    (G t).childVelocity.field x=(EulerChildParticleTime.velocity P P₁ D D₁).field t x := by
  rw [EulerChildParticleFieldBounds.Data.childVelocity_apply,velocity_apply]
  have he : (G t).parentDisplacement.field = (P.field t : Space → Space) :=
    funext (H.parentDisplacement t)
  simp only [EulerChildParticleFieldBounds.Data.inner,he,H.parentVelocity,H.displacement,H.velocity]

theorem childAcceleration (t : Icc (0 : ℝ) T) (x : Space) :
    (G t).childAcceleration.field x=(EulerChildParticleTime.acceleration P P₁ P₂ D D₁ D₂).field t x := by
  rw [EulerChildParticleFieldBounds.Data.childAcceleration_apply,acceleration_apply]
  have he : (G t).parentDisplacement.field = (P.field t : Space → Space) :=
    funext (H.parentDisplacement t)
  have he₁ : (G t).parentVelocity.field = (P₁.field t : Space → Space) :=
    funext (H.parentVelocity t)
  simp only [EulerChildParticleFieldBounds.Data.inner,he,he₁,
    H.parentAcceleration,H.displacement,H.velocity,H.acceleration]

variable {hT : 0 ≤ T}




end Representation
end EulerChildParticleTime
