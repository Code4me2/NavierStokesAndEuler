import Euler.ParentEulerState
import Euler.SmoothEulerEvolution

/-! The actual physical velocity and pressure force in every Sobolev
order. Strong time evolution follows from their classical Euler equation
and continuous L² jets, including both endpoint derivatives. -/

noncomputable section

namespace EulerParentPacketFrames

open Set EulerSmoothLimit EulerLpTranslation EulerSmoothFieldSobolevTime
  EulerSmoothEulerEvolution EulerVolterraConvolution EulerTimeIntervalRestriction

structure SobolevData {A : Parent} (E : Evolution A) where
  velocity : Icc (0 : ℝ) A.T → SmoothL2Field Space
  force : Icc (0 : ℝ) A.T → SmoothL2Field Space
  velocity_match : ∀ (t : Icc (0 : ℝ) A.T) x, E.velocity (t,x)=(velocity t).field x
  force_match : ∀ (t : Icc (0 : ℝ) A.T) x, E.force t x=(force t).field x
  velocity_continuous : ∀ n, Continuous (fun t => (velocity t).jetLp n)
  force_continuous : ∀ n, Continuous (fun t => (force t).jetLp n)

namespace SobolevData

variable {A : Parent} {E : Evolution A} (S : SobolevData E)


def restrictTime (T : ℝ) (hT : 0 < T) (hTA : T ≤ A.T) :
    SobolevData (E.restrictTime T hT hTA) where
  velocity t := S.velocity (initialInclusion A.T T hTA t)
  force t := S.force (initialInclusion A.T T hTA t)
  velocity_match t x := S.velocity_match (initialInclusion A.T T hTA t) x
  force_match t x := S.force_match (initialInclusion A.T T hTA t) x
  velocity_continuous n := (S.velocity_continuous n).comp (initialInclusion A.T T hTA).continuous
  force_continuous n := (S.force_continuous n).comp (initialInclusion A.T T hTA).continuous

end SobolevData
end EulerParentPacketFrames
