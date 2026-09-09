import NavierStokes.ProblemStatement
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.Topology.Algebra.Support

/-!
# Whole-space vocabulary for the R³ comparison

This module fixes the coordinates and finite-energy notions used by the
whole-space half of the development, independently of the periodic target.
The coordinates, Euclidean norm, differential operators, and the viscosity-one
residual `navierStokesResidual` are those of `NavierStokes.ProblemStatement`;
no periodicity assumption is made here. Time is the first coordinate of
spacetime.

Smoothness of velocity and pressure at time zero is relative to the physical
half-domain. The equation uses ordinary derivatives at positive times; zero
initial velocity is imposed separately. This avoids differentiating an arbitrary
extension to negative time at the boundary. `∞` in the `ContDiff` scope means
every finite differentiability order.

The whole-space theorem itself is stated and proved through the comparator
interface: `NavierStokes.Comparator.navier_stokes_breakdown_R3` in
`NavierStokes/ComparatorSolution.lean`, via
`NavierStokes.R3CompactCandidate.Properties`.
-/


noncomputable section

open Set MeasureTheory
open scoped ContDiff

namespace NavierStokesR3.ProblemStatement

/-- R³ with its ordinary Euclidean norm. -/
abbrev Space := NavierStokes.ProblemStatement.Space

/-- Spacetime, with time first. -/
abbrev SpaceTime := NavierStokes.ProblemStatement.SpaceTime

abbrev VelocityField := NavierStokes.ProblemStatement.VelocityField
abbrev PressureField := NavierStokes.ProblemStatement.PressureField

/-- Square integrability with respect to ordinary Lebesgue volume on R³.
This condition is explicit because the real Bochner integral is totalized. -/
def SquareIntegrableAtTime (u : VelocityField) (t : ℝ) : Prop :=
  Integrable (fun x : Space => ‖u (t, x)‖ ^ 2) (volume : Measure Space)

/-- Kinetic energy at a time. It is used below only together with the explicit
integrability condition `SquareIntegrableAtTime`. -/
def kineticEnergy (u : VelocityField) (t : ℝ) : ℝ :=
  (1 / 2 : ℝ) * ∫ x : Space, ‖u (t, x)‖ ^ 2 ∂(volume : Measure Space)

/-- One finite bound for the kinetic energy at every time in `times`, with
square integrability required at every such time. -/
def UniformFiniteEnergy (times : Set ℝ) (u : VelocityField) : Prop :=
  ∃ E : ℝ, 0 ≤ E ∧ ∀ t ∈ times,
    SquareIntegrableAtTime u t ∧ kineticEnergy u t ≤ E

end NavierStokesR3.ProblemStatement
