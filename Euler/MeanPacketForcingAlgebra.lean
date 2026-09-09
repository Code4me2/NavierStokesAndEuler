import Euler.MeanPacketForcing
import Euler.LpSmoothFieldAlgebra

/-!
# Genuine algebraic closure of admissible mean forcing

Admissibility is preserved by finite sums, bounded linear maps, and actual
spatial directional derivatives. Every witness consists of literal smooth
fields and their continuous L² jets; no inverse or equation is assumed.
-/

noncomputable section

namespace EulerMeanPacketProvider

open Set MeasureTheory ContinuousLinearMap EulerSmoothLimit EulerMeanSolenoidal
  EulerLpTranslation EulerLpTranslation.SmoothL2Field EulerPacketPointJets
  EulerPacketProfileRecursion
open scoped ContDiff

namespace Forcing

variable {D : Data} {raw raw' : VectorField}

/-- The time path is constructed from the actual zeroth L² jet. -/
def ofSlices (A : ℝ → SmoothL2Field Space)
    (hA : ∀ n, Continuous (fun t : Icc (0 : ℝ) D.T => (A t).jetLp n))
    (heq : ∀ (t : Icc (0 : ℝ) D.T) x θ, raw (t,(x,θ)) = (A t).field x) : Forcing D raw where
  slices := A
  jets_continuous := hA
  path := ⟨fun t => (A t).toLp, continuous_toLp (fun t : Icc (0 : ℝ) D.T => A t) (hA 0)⟩
  path_eq _ := rfl
  raw_eq := heq



/-- Applying a genuine bounded linear map preserves every actual L² jet. -/
def map (G : Forcing D raw) (L : Space →L[ℝ] Space) : Forcing D (fun z => L (raw z)) :=
  ofSlices (fun t => mapField L (G.slices t))
    (continuous_jetLp_mapField L (fun t : Icc (0 : ℝ) D.T => G.slices t) G.jets_continuous)
    (fun t x θ => by simp only [G.raw_eq t x θ, mapField_field])

def smul (G : Forcing D raw) (c : ℝ) : Forcing D (c • raw) :=
  G.map (c • ContinuousLinearMap.id ℝ Space)



end Forcing


end EulerMeanPacketProvider
