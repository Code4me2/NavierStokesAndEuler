import NavierStokes.NaturalProfile
import NavierStokes.SimilarityCoordinates
import NavierStokes.AxisymmetricFields
import NavierStokes.SmoothParameterIntegral
import NavierStokes.BlowupImplication

/-!
# The physical natural core

The core is the actual Cartesian curl of meridional and swirl potentials
obtained from the natural profiles. All regularity assertions are on the
explicit open physical domain where those profiles have been constructed.
No assertion about the regularity of the final Navier--Stokes force is made.
-/

noncomputable section

open Set Filter MeasureTheory
open scoped Topology ContDiff Interval BigOperators

namespace NavierStokes.NaturalCore

open ProblemStatement AxisymmetricFields

noncomputable def physicalQ (h : ℝ) (p : ProfilePoint) : ℝ :=
  SimilarityCoordinates.coordinateQ (2 * h) (1 - p.1, p.2.2)

noncomputable def physicalEta (h : ℝ) (p : ProfilePoint) : ℝ :=
  SimilarityCoordinates.coordinateEta (2 * h) (1 - p.1, p.2.2)















theorem physicalQ_at_zero_z {h : ℝ} (hh : 0 < h) (hh1 : h < 1 / 2)
    {t : ℝ} (ht : t < 1) (s : ℝ) : physicalQ h (t, (s, 0)) = 1 - t := by
  apply (SimilarityCoordinates.eq_coordinateQ (by linarith) (by linarith)
    (p := (1 - t, 0)) (sub_pos.mpr ht) (sub_pos.mpr ht) ?_).symm
  simp [SimilarityCoordinates.forwardScalar]

theorem physicalEta_at_zero_z (h t s : ℝ) : physicalEta h (t, (s, 0)) = 0 := by
  simp [physicalEta, SimilarityCoordinates.coordinateEta]





























end NavierStokes.NaturalCore
