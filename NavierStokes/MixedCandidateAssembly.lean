import NavierStokes.MixedDiagonalResidual
import NavierStokes.MixedDiagonalExtensions
import NavierStokes.LocalAngularDiagonal

/-!
# Candidate assembly from the actual finite-stage obligations

The inputs here concern raw increments, their finite uncut prefixes, and
their local endpoint models. The scale sequence, infinite residual limits,
away extensions, divergence and blow-up are then derived for the same sums.

This is a conditional consumer. It does not construct the complete
correction iteration or supply the finite-stage estimates it requires.
-/

noncomputable section

namespace NavierStokes.MixedCandidateAssembly

open Set Filter ProblemStatement
open JointResidualLimits (OneSidedExtension)
open DiagonalResidual (JetRate)
open scoped Topology ContDiff

universe u

/-- The quantitative obligations are all on the raw fields or finite
prefixes. In particular no infinite residual limit is a field here. -/
structure StageEstimates (h qbig : ℝ) (A B : ℕ → VelocityField)
    (P : ℕ → PressureField) where
  potential_smooth : ∀ j, ContDiffOn ℝ ∞ (A j) (CutStageEstimates.physicalSublevel h qbig)
  direct_smooth : ∀ j, ContDiffOn ℝ ∞ (B j) (CutStageEstimates.physicalSublevel h qbig)
  pressure_smooth : ∀ j, ContDiffOn ℝ ∞ (P j) (CutStageEstimates.physicalSublevel h qbig)
  gain : ℕ → ℝ
  gain_zero : 0 ≤ gain 0
  gain_pos : ∀ j, 1 ≤ j → 0 < gain j
  gain_mono : Monotone gain
  gain_top : Tendsto gain atTop atTop
  potentialLoss : ℕ → ℝ
  directLoss : ℕ → ℝ
  pressureLoss : ℕ → ℝ
  potentialConstant : ℕ → ℕ → ℝ
  directConstant : ℕ → ℕ → ℝ
  pressureConstant : ℕ → ℕ → ℝ
  potentialLog : ℕ → ℕ → ℝ
  directLog : ℕ → ℕ → ℝ
  pressureLog : ℕ → ℕ → ℝ
  potential_bound : CutStageEstimates.RawStageBounds (PhysicalWaveSum.physicalQ h)
    A gain potentialLoss potentialConstant potentialLog
    (PhysicalWaveSum.preterminal ∩ CutStageEstimates.physicalSublevel h qbig)
  direct_bound : CutStageEstimates.RawStageBounds (PhysicalWaveSum.physicalQ h)
    B gain directLoss directConstant directLog
    (PhysicalWaveSum.preterminal ∩ CutStageEstimates.physicalSublevel h qbig)
  pressure_bound : CutStageEstimates.RawStageBounds (PhysicalWaveSum.physicalQ h)
    P gain pressureLoss pressureConstant pressureLog
    (PhysicalWaveSum.preterminal ∩ CutStageEstimates.physicalSublevel h qbig)
  backgroundLoss : ℕ → ℝ
  residualLoss : ℕ → ℝ
  finite_background : ∀ J m,
    JetRate (𝓝[SpacetimeEndpoint.openPast 1] (1, (0 : Space))) (PhysicalWaveSum.physicalQ h)
      (MixedDiagonalResidual.uncutVelocity A B J) m (-backgroundLoss m)
  finite_residual : ∀ J m,
    JetRate (𝓝[SpacetimeEndpoint.openPast 1] (1, (0 : Space))) (PhysicalWaveSum.physicalQ h)
      (fun z => navierStokesResidual (MixedDiagonalResidual.uncutVelocity A B J)
        (DiagonalJetBounds.uncutPrefix P (J + 1)) z.1 z.2) m (gain J - residualLoss m)

theorem StageEstimates.exists_schedule {h qbig : ℝ}
    {A B : ℕ → VelocityField} {P : ℕ → PressureField}
    (E : StageEstimates h qbig A B P) (hh : 0 < h) (hh1 : h < 1 / 2)
    (hqbig : 0 < qbig) (lower : ℕ) :
    ∃ a : ℕ → ℕ, lower ≤ a 0 ∧ (∀ j, 0 < a j) ∧
      (∀ j, 2 * a j ≤ a (j + 1)) ∧ StrictMono a ∧
      Tendsto (fun j => (a j : ℝ)) atTop atTop ∧
      (∀ j, 1 / (a j : ℝ) < qbig) ∧
      MixedDiagonalSchedule.ThreeSmoothSums a h A B P ∧
      JointResidualLimits.VanishingJointJets
        (MixedDiagonalResidual.residual (fun j => (a j : ℝ)) (PhysicalWaveSum.physicalQ h) A B P) := by
  have hS : ∀ᶠ z in 𝓝[SpacetimeEndpoint.openPast 1] (1, (0 : Space)),
      z ∈ PhysicalWaveSum.preterminal := by
    filter_upwards [self_mem_nhdsWithin] with z hz
    exact hz.1
  obtain ⟨a, hal, hap, had, ham, hat, hrecip, _, hs, hz⟩ :=
    MixedDiagonalResidual.exists_physical_schedule_residual_zero hh hh1 hqbig
      PhysicalWaveSum.preterminal_open (Subset.refl _) hS
      E.potential_smooth E.direct_smooth E.pressure_smooth
      E.gain E.potentialLoss E.directLoss E.pressureLoss E.backgroundLoss E.residualLoss
      E.potentialConstant E.directConstant E.pressureConstant
      E.potentialLog E.directLog E.pressureLog
      E.potential_bound E.direct_bound E.pressure_bound
      E.gain_zero E.gain_pos E.gain_mono E.gain_top E.finite_background E.finite_residual lower
  exact ⟨a, hal, hap, had, ham, hat, hrecip, hs, hz⟩

section ActualBase

variable {F : OutgoingProfile.Profile} {W : NominalProfile.Witness F}
    (H : NominalConeAssembly.Certificate W) {ld : ModulatedProfileAssembly.LoopData W}
    (v : ModulatedProfileAssembly.Witness ld)


/-- Pressure is recorded as the actual base plus its initialization
change, followed by the pressure differences of full correction stages. -/
noncomputable def pressureStages (upper : ℝ) (bandFloor : ℕ)
    (initial : PressureField) (stages : ℕ → PressureField) : ℕ → PressureField :=
  fun j w => if j = 0 then FinalSlowBase.pressure H v upper bandFloor w + initial w
    else stages (j - 1) w

theorem pressureStages_zero (upper : ℝ) (bandFloor : ℕ)
    (initial : PressureField) (stages : ℕ → PressureField) (w : SpaceTime) :
    pressureStages H v upper bandFloor initial stages 0 w =
      FinalSlowBase.pressure H v upper bandFloor w + initial w := by
  simp [pressureStages]

theorem pressureStages_succ (upper : ℝ) (bandFloor : ℕ)
    (initial : PressureField) (stages : ℕ → PressureField) (j : ℕ) :
    pressureStages H v upper bandFloor initial stages (j + 1) = stages j := by
  funext w
  simp only [pressureStages, Nat.add_eq_zero_iff, Nat.one_ne_zero, and_false, ite_false,
    Nat.add_sub_cancel]


end ActualBase

end NavierStokes.MixedCandidateAssembly
