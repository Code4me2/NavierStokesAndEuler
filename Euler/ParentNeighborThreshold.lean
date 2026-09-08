import Euler.ParentHistoryFrequencyGuard
import Euler.ParentPacketNeighborScaleGuard

/-! Fixed coefficient thresholds for the literal neighboring-label guard.
The history reciprocal is derived from the initial geometric step, and
the only parent size input is the already constructed parent's label bound. -/

noncomputable section

namespace EulerParentNeighborThreshold

open Real EulerParentNeighborCost EulerPacketSourceScaleSequence
  EulerParentHistoryFrequency

def forwardThreshold : ℝ := constant*4^degree

def joinedThreshold (CM CH : ℝ) : ℝ :=
  (constant*(2*(1+CM+CH))^degree)*4^degree

def commonThreshold (CM CH : ℝ) : ℝ :=
  max forwardThreshold (joinedThreshold CM CH)

def requiredExponent : ℕ := 80*degree+1

theorem degree_le_requiredExponent : degree ≤ requiredExponent := by
  unfold requiredExponent
  omega

theorem forwardThreshold_le_common (CM CH : ℝ) :
    forwardThreshold ≤ commonThreshold CM CH := le_max_left _ _

theorem joinedThreshold_le_common (CM CH : ℝ) :
    joinedThreshold CM CH ≤ commonThreshold CM CH := le_max_right _ _


end EulerParentNeighborThreshold

namespace EulerParentPacketFrames.LabelData

open Set Real EulerSmoothLimit EulerTransverseFrameCoordinates EulerTransversePacketProvider
  EulerPacketSourceGeometry EulerParentNeighborCost EulerPacketSourceScaleSequence
  EulerPacketSourceScaleActual EulerParentNeighborThreshold EulerParentHistoryFrequency
  EulerPacketNestedHorizons EulerPacketBaseGuardScales

variable {G : Parent} (L : LabelData G)

theorem strainDifferenceCost_power :
    L.strainDifferenceCost ≤ constant*(1+L.K)^degree := by
  simpa only [envelope,formula,strainDifferenceCost,mul_zero,add_zero] using
    envelope_power L.K 0 0 0 0 0 (zero_le_one.trans L.K_one)
      le_rfl le_rfl le_rfl le_rfl le_rfl

theorem strainDifferenceCost_monomial (k : ℝ) (c : ℕ)
    (hk : 1 ≤ k) (hKk : L.K ≤ k^80)
    (hcost : forwardThreshold ≤ k) (hc : requiredExponent ≤ c) :
    L.strainDifferenceCost ≤ k^c := by
  have hconst := constant_pos
  have hn : degree ≤ c := degree_le_requiredExponent.trans hc
  have he : 80*degree+1 ≤ c := hc
  have hb := polynomial_le_monomial constant L.K 0 0 k 1 degree 80 c
    hconst.le (zero_le_one.trans L.K_one) le_rfl le_rfl hk le_rfl hKk
    (pow_nonneg (zero_le_one.trans hk) 80) zero_le_one hcost he hn
  exact L.strainDifferenceCost_power.trans (by
    simpa only [add_zero,one_pow,mul_one] using hb)

theorem forward_neighbor_error_of_source_scales (J D : ℕ) (hJ : 3 ≤ J)
    (X ρ : ℝ) (hX : 1 ≤ X)
    (hbase : X^D ≤ exp (X/((J-1 : ℕ) : ℝ)^4)) (n c : ℕ)
    (hρ : 0 ≤ ρ) (hρ1 : ρ ≤ 1)
    (hKk : L.K ≤ previousFrequency J D X n^80)
    (hcost : forwardThreshold ≤ previousFrequency J D X n)
    (hc : requiredExponent ≤ c) (hscale : G.ell ≤ supportScale J X n) :
    L.strainDifferenceCost*G.ell*ρ ≤ neighborError J D X (c : ℝ) n := by
  have hk := previousFrequency_one_le J D hJ X hX hbase n
  have hh : 1 ≤ previousShear J X n := by
    cases n with
    | zero => exact one_le_pow₀ hX
    | succ n =>
      apply one_le_exp
      exact div_nonneg
        ((zero_le_one.trans hX).trans
          (EulerPacketSourceParameterScales.sequence_initial_le J (by omega) X
            (zero_le_one.trans hX) n)) (by positivity)
  have hb := L.strainDifferenceCost_monomial (previousFrequency J D X n) c hk hKk hcost hc
  have hkn : 0 ≤ previousFrequency J D X n^c := pow_nonneg (zero_le_one.trans hk) c
  have hhn : 0 ≤ previousShear J X n^c := pow_nonneg (zero_le_one.trans hh) c
  have hb' : L.strainDifferenceCost ≤ previousFrequency J D X n^c*previousShear J X n^c :=
    hb.trans (le_mul_of_one_le_right hkn (one_le_pow₀ hh))
  have hprod : 0 ≤ previousFrequency J D X n^c*previousShear J X n^c := mul_nonneg hkn hhn
  calc
    _ ≤ (previousFrequency J D X n^c*previousShear J X n^c)*G.ell*ρ :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hb' G.ell_pos.le) hρ
    _ ≤ (previousFrequency J D X n^c*previousShear J X n^c)*G.ell := by
      simpa only [mul_one] using mul_le_mul_of_nonneg_left hρ1
        (mul_nonneg hprod G.ell_pos.le)
    _ ≤ (previousFrequency J D X n^c*previousShear J X n^c)*supportScale J X n :=
      mul_le_mul_of_nonneg_left hscale hprod
    _ = neighborError J D X (c : ℝ) n := by
      simp only [neighborError,rpow_natCast]
      ring

variable {U : Type} [NormedAddCommGroup U] [InnerProductSpace ℝ U]
  (m : Space) (hm : ‖m‖=1) (R : U ≃ₗᵢ[ℝ] referencePlane m)
  (S : Set Space) (hS : IsCompact S) (H : LowBounds G)
  (τ : ℝ) (hτ : 0 < τ) (hτT : τ < G.T)
  (P : ParentFrame (G.transverseData m hm R S hS) τ)


end EulerParentPacketFrames.LabelData
