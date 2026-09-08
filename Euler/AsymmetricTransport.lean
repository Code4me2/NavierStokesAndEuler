import Euler.SobolevTransport
import Euler.GevreyOrderZero

/-! The actual asymmetric Sobolev transport map needed for the parabolic source upgrade. -/

noncomputable section

namespace EulerAsymmetricTransport

open EulerLiftedGradientSpace EulerCylinderSobolevSpace EulerSobolevL2Product EulerSobolevTransport
  EulerGevreyOrderZero
open scoped Topology

variable (period : ℝ) [Fact (0 < period)]

local instance asymmetricGroup (q : ℕ) : NormedAddCommGroup (SobolevSpace period q) := inferInstance
local instance asymmetricSpace (q : ℕ) : NormedSpace ℝ (SobolevSpace period q) := inferInstance

/-- Actual transport Hs×H^(s+1)→Hs; the coefficient velocity needs no extra derivative. -/
def asymmetricTransport {s : ℕ} (hs : 6 ≤ s)
    (L : Fin 4 → Vector3 →L[ℝ] ℝ) (hL : ∀ i, ‖L i‖ ≤ 1) :
    SobolevSpace period s →L[ℝ] SobolevSpace period (s+1) →L[ℝ] SobolevSpace period s :=
  ∑ i : Fin 4, (productHqBilinear period hs (L i) (hL i)).bilinearComp
    (ContinuousLinearMap.id ℝ (SobolevSpace period s)) (derivativeOperator period s i)

/-- The literal scalar-times-derivative formula of asymmetric transport. -/
theorem asymmetricTransport_apply {s : ℕ} (hs : 6 ≤ s)
    (L : Fin 4 → Vector3 →L[ℝ] ℝ) (hL : ∀ i, ‖L i‖ ≤ 1)
    (u : SobolevSpace period s) (v : SobolevSpace period (s+1)) :
    asymmetricTransport period hs L hL u v = ∑ i : Fin 4,
      productHq period hs (L i) (hL i) u (derivativeOperator period s i v) := by
  simp only [asymmetricTransport, sum_apply, ContinuousLinearMap.bilinearComp_apply,
    ContinuousLinearMap.id_apply, productHqBilinear_apply]

/-- The asymmetric map agrees with the already constructed genuine transport on common inputs. -/
theorem asymmetricTransport_eq {s : ℕ} (hs : 6 ≤ s)
    (L : Fin 4 → Vector3 →L[ℝ] ℝ) (hL : ∀ i, ‖L i‖ ≤ 1)
    (u v : SobolevSpace period (s+1)) :
    asymmetricTransport period hs L hL (truncateOperator period s u) v = transportBilinear period hs L hL u v := by
  rw [asymmetricTransport_apply, transportBilinear_apply]




end EulerAsymmetricTransport
