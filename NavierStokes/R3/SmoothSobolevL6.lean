import NavierStokes.R3.ComparisonCutoffs
import Common.SobolevL6

/-!
# Homogeneous Sobolev bounds for smooth square-integrable functions

The support-free `H¹ → L⁶` inequality is proved once in `Common.SobolevL6`;
this module restates it on `Space` under the names the Riesz-test estimates use.
-/


noncomputable section

open MeasureTheory
open scoped ContDiff ENNReal

namespace NavierStokesR3.RieszTestOperators

open ProblemStatement

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The homogeneous `H¹ → L⁶` inequality without a support assumption.
Only the function itself must have finite `L²` norm for this extended-norm
inequality; the right side may be infinite. -/
theorem smooth_eLpNorm_six_le {f : Space → E} (hf : ContDiff ℝ 1 f)
    (h2 : MemLp f 2 volume) :
    eLpNorm f 6 volume ≤
      (eLpNormLESNormFDerivOfEqInnerConst (volume : Measure Space) 2 : ℝ≥0∞) *
        eLpNorm (fderiv ℝ f) 2 volume :=
  Common.SobolevL6.eLpNorm_six_le hf h2

/-- A smooth function with square-integrable value and derivative belongs to
`L⁶`, with no support hypothesis. -/
theorem smooth_memLp_six {f : Space → E} (hf : ContDiff ℝ 1 f)
    (h2 : MemLp f 2 volume) (hD2 : MemLp (fderiv ℝ f) 2 volume) :
    MemLp f 6 volume :=
  Common.SobolevL6.memLp_six hf h2 hD2

/-- The real-valued homogeneous Sobolev bound when both `L²` norms are finite. -/
theorem smooth_eLpNorm_six_toReal_le {f : Space → E} (hf : ContDiff ℝ 1 f)
    (h2 : MemLp f 2 volume) (hD2 : MemLp (fderiv ℝ f) 2 volume) :
    (eLpNorm f 6 volume).toReal ≤
      (eLpNormLESNormFDerivOfEqInnerConst (volume : Measure Space) 2 : ℝ) *
        (eLpNorm (fderiv ℝ f) 2 volume).toReal :=
  Common.SobolevL6.toReal_eLpNorm_six_le hf h2 hD2

end NavierStokesR3.RieszTestOperators
