import Euler.GevreyOrderZero
import Euler.EulerCorrectionEquation

/-! Exact transport/order-zero splitting of the constructed correction source and its actual pressure. -/

noncomputable section

namespace EulerGevreyOrderZero

open MeasureTheory InnerProductSpace EulerLiftedGradientSpace EulerCylinderSobolevSpace EulerCylinderSobolev
  EulerSpatialSobolevInverse EulerSobolevL2Product EulerH6Nonlinear EulerH6Pressure EulerJetProductBounds
  EulerPacketWeights EulerSobolevGevreyOperators EulerSobolevCoefficientPressure EulerVectorCylinder
  EulerCorrectionOperators EulerSobolevTransport
open scoped Topology

variable (period : ℝ) [Fact (0 < period)]

local instance splitGroup (q : ℕ) : NormedAddCommGroup (SobolevSpace period q) := inferInstance
local instance splitSpace (q : ℕ) : NormedSpace ℝ (SobolevSpace period q) := inferInstance
local instance splitBilinearGroup (q : ℕ) : SeminormedAddCommGroup
    (SobolevSpace period (q+1) →L[ℝ] SobolevSpace period (q+1) →L[ℝ] SobolevSpace period q) := inferInstance



/-- Exact splitting of the actual nonlinear increment into top transport plus the order-zero source. -/
theorem correction_split_identity {s : ℕ} (hs : 6 ≤ s)
    (L : Fin 4 → Vector3 →L[ℝ] ℝ) (hL : ∀ i, ‖L i‖ ≤ 1)
    (C0 : SobolevSpace period s →L[ℝ] SobolevSpace period s)
    (C : Fin 3 → SobolevSpace period s →L[ℝ] SobolevSpace period s)
    (background e : SobolevSpace period (s+1)) (r : SobolevSpace period s) :
    r + linearize (eulerBilinear period hs L hL C) (C0.comp (truncateOperator period s)) background e +
      eulerBilinear period hs L hL C e e =
      transportBilinear period hs L hL (background+e) e +
        orderZeroSource period hs L hL C0 C background r (truncateOperator period s e) := by
  have hzero : orderZeroSource period hs L hL C0 C background r (truncateOperator period s e) =
      r + transportBilinear period hs L hL e background + C0 (truncateOperator period s e) +
        algebraicBilinear period hs C background e + algebraicBilinear period hs C e background +
          algebraicBilinear period hs C e e := by
    simp only [orderZeroSource, backgroundDrift, algebraicAt, transportBilinear_apply,
      algebraicBilinear_apply, coordinateProduct_apply]
  have halg : r + linearize (eulerBilinear period hs L hL C) (C0.comp (truncateOperator period s)) background e +
      eulerBilinear period hs L hL C e e =
      transportBilinear period hs L hL (background+e) e +
        (r + transportBilinear period hs L hL e background + C0 (truncateOperator period s e) +
          algebraicBilinear period hs C background e + algebraicBilinear period hs C e background +
            algebraicBilinear period hs C e e) := by
    simp only [linearize_apply, eulerBilinear, add_apply, map_add, ContinuousLinearMap.comp_apply]
    abel
  exact halg.trans (congrArg (fun a => transportBilinear period hs L hL (background+e) e + a) hzero.symm)

/-- Actual finite weighted Sobolev norms are invariant under sign. -/
theorem weightedNorm_neg {s : ℕ} (q N : ℕ) (hN : N+q ≤ s) (ρ : ℝ) (u : SobolevSpace period s) :
    weightedNorm period q N ρ (-u) = weightedNorm period q N ρ u := by
  apply Finset.sum_congr rfl
  intro n hn
  congr 1
  unfold blockNorm
  apply Finset.sum_congr rfl
  intro r hr
  rw [levelNorm_eq_words, levelNorm_eq_words]
  apply Finset.sum_congr rfl
  intro w _
  have hnr : n+r ≤ s := by have := Finset.mem_range.mp hn; have := Finset.mem_range.mp hr; omega
  rw [toJet_word period (-u) hnr, toJet_word period u hnr]
  change ‖-u.val ⟨⟨n+r, by omega⟩,w⟩‖ = ‖u.val ⟨⟨n+r, by omega⟩,w⟩‖
  exact norm_neg _


/-- The solver's actual raw source has exactly the transport/order-zero decomposition used by the energy estimate. -/
theorem correctionData_rawSource_split {s : ℕ} {T : Type*} [TopologicalSpace T]
    (D : CorrectionData period s T) (hs : 6 ≤ s) (t : T) (e : SobolevSpace period (s+1)) :
    D.rawSource period hs t e =
      transportBilinear period hs (velocityComponents D.κ D.direction)
        (velocityComponents_norm D.κ D.direction D.scale_bound D.direction_bound) (D.approximation t+e) e +
      orderZeroSource period hs (velocityComponents D.κ D.direction)
        (velocityComponents_norm D.κ D.direction D.scale_bound D.direction_bound)
        (coefficientSobolevOperator period (D.linear.jet t))
        (fun i => coefficientSobolevOperator period ((D.quadratic i).jet t))
        (D.approximation t) (D.residual t) (truncateOperator period s e) :=
  correction_split_identity period hs _ _ _ _ _ _ _


end EulerGevreyOrderZero
