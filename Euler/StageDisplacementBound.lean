import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Confinement by summable changes of particle labels

The packet construction composes particle maps as `Xₙ₊₁ = Xₙ ∘ Yₙ`.
Bounding the displacement of this composition costs the sum of the two
displacements, without a derivative bound on `Xₙ`. Consequently summable
changes of labels confine the images of every fixed initial ball uniformly
over all stages, including when the velocity gradients are unbounded.

The horizon predicate permits the time intervals to shrink with the stage.
The hypotheses below are explicit: this file does not yet assert their
instantiation for the packet choices made by the development.
-/

namespace Euler.ComparatorBridge

open Finset Set

variable {E : Type*} [NormedAddCommGroup E]


omit [NormedAddCommGroup E] in
/-- A transported quantity that starts supported in `K` remains supported in
the region containing its transported labels. Only preservation of zero is
needed; the transported quantity need not be constant along trajectories. -/
theorem support_subset_of_transport {F : Type*} [Zero F]
    (X Y : E → E) (w₀ w : E → F) {K L : Set E}
    (hright : ∀ x, X (Y x) = x) (hmap : MapsTo X K L)
    (hinitial : Function.support w₀ ⊆ K)
    (htransport : ∀ a, w₀ a = 0 → w (X a) = 0) :
    Function.support w ⊆ L := by
  classical
  intro x hx
  by_contra houtside
  have ha : Y x ∉ K := fun hy => houtside (hright x ▸ hmap hy)
  have hzero : w₀ (Y x) = 0 := by
    by_contra hne
    exact ha (hinitial (Function.mem_support.mpr hne))
  have h := htransport (Y x) hzero
  rw [hright x] at h
  exact (Function.mem_support.mp hx) h

variable {Time : Type*} (H : ℕ → Time → Prop)
  (X Y : ℕ → Time → E → E) (M : ℝ) (δ : ℕ → ℝ)
  (hbase : ∀ t, H 0 t → ∀ x, ‖X 0 t x - x‖ ≤ M)
  (hnest : ∀ n t, H (n + 1) t → H n t)
  (hstep : ∀ n t, H (n + 1) t → ∀ x, X (n + 1) t x = X n t (Y n t x))
  (hsmall : ∀ n t, H (n + 1) t → ∀ x, ‖Y n t x - x‖ ≤ δ n)






end Euler.ComparatorBridge
