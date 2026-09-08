import Euler.BaseEulerGevrey

/-! A single factorial budget for every base datum with |β|≤1.
In particular this covers β=x₀⁻² with x₀≥1, independently of the
eventual frequency and iteration scales. -/

noncomputable section

namespace EulerBaseDatum

open Set EulerSmoothLimit EulerGevrey EulerLpTranslation EulerPacketPiola
  EulerPacketParentLabelBounds EulerMeanClassicalWordBounds EulerParameterWordGevrey

def uniformAmplitude : ℝ := 1+‖curlOperator‖*(3*(3*cutoffAmplitude*(24*2))*256)

theorem uniformAmplitude_pos : 0 < uniformAmplitude := by
  have h := cutoffAmplitude_nonneg
  unfold uniformAmplitude
  positivity

theorem velocityAmplitude_le_uniform (β : ℝ) (hβ : |β| ≤ 1) :
    velocityAmplitude (linear β) ≤ uniformAmplitude := by
  have hL : ‖linear β‖ ≤ 2 := (linear_norm β).trans (by linarith)
  have hc := cutoffAmplitude_nonneg
  calc
    velocityAmplitude (linear β) ≤ ‖curlOperator‖*(3*(3*cutoffAmplitude*(24*2))*256) := by
      unfold velocityAmplitude potentialAmplitude
      gcongr
    _ ≤ uniformAmplitude := by unfold uniformAmplitude; linarith


def uniformL2Amplitude : ℝ := uniformAmplitude*volumeFactor

theorem uniformL2Amplitude_nonneg : 0 ≤ uniformL2Amplitude :=
  mul_nonneg uniformAmplitude_pos.le volumeFactor_nonneg

theorem field_uniform_jet (β : ℝ) (hβ : |β| ≤ 1) :
    (field (linear β)).HasJetBound uniformL2Amplitude 1024 :=
  (field_jet_bound (linear β)).mono
    (mul_nonneg (velocityAmplitude_nonneg _) volumeFactor_nonneg) (by norm_num)
    (mul_le_mul_of_nonneg_right (velocityAmplitude_le_uniform β hβ) volumeFactor_nonneg) le_rfl







end EulerBaseDatum
