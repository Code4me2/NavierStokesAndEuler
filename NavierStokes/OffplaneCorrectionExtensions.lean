import NavierStokes.AnnularEndpoint
import NavierStokes.VariableGaugeMean
import NavierStokes.PeriodicPhaseAssembly

/-!
# Primitive correction formulas at a nonzero axial endpoint

The positive stable branch of the similarity coordinate continues across
`T = 0` when `Z ≠ 0`.  This file uses that branch in the actual moving-radius
mean operations.  Agreement of primitive data is on whole slow fibers,
because radial and torus integrals are nonlocal on each such fiber.
-/

noncomputable section

namespace NavierStokes.OffplaneCorrectionExtensions

open Set Filter Function
open scoped Topology ContDiff BigOperators

abbrev Slow := PressureStream.Plane
abbrev Lift := PressureStream.Lift Slow

noncomputable def stableQ (coord : ℝ) (s : Slow) : ℝ :=
  (PositiveRepresentatives.stableInverse coord s).1

noncomputable def stableLength (coord : ℝ) (s : Slow) : ℝ := Real.sqrt (stableQ coord s)






theorem stableQ_eq_coordinateQ {coord : ℝ} (hc : 0 < coord) (hc1 : coord < 1)
    {s : Slow} (hs : 0 < s.1) : stableQ coord s = SimilarityCoordinates.coordinateQ coord s := by
  exact congrArg Prod.fst (PositiveRepresentatives.stableInverse_eq_inverseMap hc hc1 hs)

theorem stableLength_eq_qLength {coord : ℝ} (hc : 0 < coord) (hc1 : coord < 1)
    {s : Slow} (hs : 0 < s.1) : stableLength coord s = VariableGaugeMean.qLength coord s := by
  exact congrArg Real.sqrt (stableQ_eq_coordinateQ hc hc1 hs)

/-- A neighborhood on which the moving radial interval has fixed positive
inner and finite outer bounds.  These bounds are constructed from the
actual stable branch below. -/
structure Window (coord a b : ℝ) where
  carrier : Set Slow
  isOpen : IsOpen carrier
  stable : carrier ⊆ PositiveRepresentatives.stableTarget coord
  lower : ℝ
  upper : ℝ
  lower_pos : 0 < lower
  lower_lt_upper : lower < upper
  left : ∀ s ∈ carrier, lower ≤ stableLength coord s * a
  right : ∀ s ∈ carrier, stableLength coord s * b ≤ upper



namespace Window

variable {coord a b : ℝ} (W : Window coord a b)




end Window

/-- Positive time is restricted only in the agreement assertion.  The
continued formulas themselves are defined on the full stable neighborhood. -/
noncomputable def positiveSlow : Set Slow := {s | 0 < s.1}


def FiberAgreement {V : Type*} (U : Set Slow) (F f : Lift → V) : Prop :=
  EqOn F f (PhysicalMeanDomain.slowDomain (U ∩ positiveSlow))

















namespace Window

variable {coord a b : ℝ} (W : Window coord a b)
    (hc : 0 < coord) (hc1 : coord < 1)

include hc hc1






end Window

section ExactAgreement

variable {coord : ℝ} (hc : 0 < coord) (hc1 : coord < 1)
    {U : Set Slow} {F f : Lift → ℝ} (he : FiberAgreement U F f)

include hc hc1 he







end ExactAgreement

/-- A full-fiber primitive continuation.  Constructors below obtain such
data from explicit positive-q models, then preserve it through the actual
nonlocal mean operations. -/
structure SupportedContinuation {coord a b : ℝ} (W : Window coord a b) (f : Lift → ℝ) where
  value : Lift → ℝ
  smooth : ContDiffOn ℝ ∞ value (PhysicalMeanDomain.slowDomain W.carrier)
  supported : VariableGaugeMean.SupportedGauge a b (stableLength coord) W.carrier value
  agrees : FiberAgreement W.carrier value f

namespace SupportedContinuation

variable {coord a b : ℝ} {W : Window coord a b} (hc : 0 < coord) (hc1 : coord < 1)







end SupportedContinuation

namespace SupportedContinuation

variable {coord a b : ℝ} {W : Window coord a b}






end SupportedContinuation

section ReferenceODE

variable {P Q V E : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
    [NormedAddCommGroup Q] [NormedSpace ℝ Q]
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]






end ReferenceODE

section ContinuedReferenceODE

variable {V E : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]











end ContinuedReferenceODE

section ContinuedPhase


end ContinuedPhase

section FullReferenceCarrier

variable {V E : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]




end FullReferenceCarrier

section RankModels





end RankModels

section PhysicalFields

abbrev Space := ProblemStatement.Space
abbrev SpaceTime := ProblemStatement.SpaceTime















namespace SupportedContinuation

variable {coord a b : ℝ} {W : Window coord a b} {f : Lift → ℝ}




end SupportedContinuation






end PhysicalFields

section DiagonalCutoffs

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

noncomputable def physicalQExtension (h : ℝ) (w : SpaceTime) : ℝ :=
  (EndpointCoordinates.cartesianExtension h w).1

theorem physicalQExtension_eq {h : ℝ} (hh : 0 < h) (hh1 : h < 1 / 2)
    {w : SpaceTime} (ht : w.1 < 1) : physicalQExtension h w = PhysicalWaveSum.physicalQ h w :=
  congrArg Prod.fst (EndpointCoordinates.cartesianExtension_eq_physical hh hh1 ht)

/-- Only finitely many stages survive near a positive-q endpoint.  Their
extensions are combined with the same scalar cutoffs and the same schedule.
The preceding model/mean constructors supply the finite-stage extensions. -/
theorem diagonal_extension {h : ℝ} (hh : 0 < h) (hh1 : h < 1 / 2)
    {a : ℕ → ℝ} (ha : Tendsto a atTop atTop) {F : ℕ → SpaceTime → V}
    {x : Space} (hx : x 2 ≠ 0)
    (he : ∀ j, Nonempty (JointResidualLimits.OneSidedExtension (F j) x)) :
    Nonempty (JointResidualLimits.OneSidedExtension
      (SolenoidalDiagonal.potentialSum a (PhysicalWaveSum.physicalQ h) F) x) := by
  classical
  obtain ⟨U, hU, hxU, hUD, _, _, hqU⟩ := EndpointCoordinates.cartesian_endpoint_neighborhood hh hh1 hx
  obtain ⟨N, hN⟩ := SmoothCutoffs.scaledCutoffs_zero_on_common_neighborhood a ha
    (EndpointCoordinates.endpointRoot_pos (2 * h) hx)
  let e : ∀ j, JointResidualLimits.OneSidedExtension (F j) x := fun j => Classical.choice (he j)
  let D : Set SpaceTime := U ∩ ⋂ j ∈ Finset.range N, (e j).domain
  have hD : IsOpen D := hU.inter (isOpen_biInter_finset fun j _ => (e j).isOpen)
  have hxD : (1, x) ∈ D := ⟨hxU, mem_iInter.mpr fun j => mem_iInter.mpr fun _ => (e j).mem⟩
  have hsub (j : ℕ) (hj : j ∈ Finset.range N) : D ⊆ (e j).domain :=
    fun w hw => mem_iInter.mp (mem_iInter.mp hw.2 j) hj
  have hq : ContDiffOn ℝ ∞ (physicalQExtension h) D :=
    (EndpointCoordinates.cartesianExtension_smoothOn hh hh1).fst.mono (fun _ hw => hUD hw.1)
  refine ⟨{
    value := fun w => ∑ j ∈ Finset.range N,
      SmoothCutoffs.scaledCutoff (a j) (physicalQExtension h w) • (e j).value w
    domain := D
    isOpen := hD
    mem := hxD
    smooth := ?_
    agrees := ?_ }⟩
  · apply ContDiffOn.sum
    intro j hj
    exact ((SmoothCutoffs.scaledCutoff_contDiff (a j)).comp_contDiffOn hq).smul
      ((e j).smooth.mono (hsub j hj))
  · intro w hw
    have hqt := physicalQExtension_eq hh hh1 hw.2.1
    have hlow : EndpointCoordinates.endpointRoot (2 * h) (x 2) / 2 < PhysicalWaveSum.physicalQ h w := by
      rw [← hqt]
      exact (hqU w hw.1.1).1
    have hsum : SolenoidalDiagonal.potentialSum a (PhysicalWaveSum.physicalQ h) F w =
        ∑ j ∈ Finset.range N, SolenoidalDiagonal.cutStage a (PhysicalWaveSum.physicalQ h) F j w := by
      apply tsum_eq_sum
      intro j hj
      simp only [SolenoidalDiagonal.cutStage, hN j
        (Nat.le_of_not_gt (by simpa only [Finset.mem_range] using hj)) _ hlow, zero_smul]
    rw [hsum]
    apply Finset.sum_congr rfl
    intro j hj
    change SmoothCutoffs.scaledCutoff (a j) (physicalQExtension h w) • (e j).value w =
      SmoothCutoffs.scaledCutoff (a j) (PhysicalWaveSum.physicalQ h w) • F j w
    rw [hqt, (e j).agrees ⟨hsub j hj hw.1, hw.2⟩]

end DiagonalCutoffs



end NavierStokes.OffplaneCorrectionExtensions
