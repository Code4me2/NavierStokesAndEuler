import NavierStokes.R3.WholeSpaceComparisonClosure
import NavierStokes.R3.PressureFlux
import NavierStokes.R3.CompactComparisonBounds

/-!
# Whole-space finite-energy comparison

The reference velocity has one compact spatial support throughout the closed
time interval. The competing velocity has only smoothness and a uniform
finite-energy bound. No growth, decay, support or derivative bound is assumed
for the competing pressure or velocity. The pressure flux estimate is derived
from the actual equation by the imported pressure recovery and commutator
theorems.
-/


noncomputable section

open Set MeasureTheory
open scoped ContDiff

namespace NavierStokesR3.WholeSpaceUniqueness

open ProblemStatement Comparison
open NavierStokes.ProblemStatement (spatialDivergence)
open NavierStokes.PeriodicUniqueness (spatial_smooth)

/-- Whole-space comparison on a positive closed time interval. Finite energy
of the reference velocity is a consequence of its compact spatial support. -/
theorem classical_uniqueness_on_Icc {T : ℝ} (hT : 0 < T)
    {u v : VelocityField} {p q : PressureField} {K : Set Space}
    (hu : ContDiffOn ℝ ∞ u (Comparison.slab 0 T))
    (hv : ContDiffOn ℝ ∞ v (Comparison.slab 0 T))
    (hp : ContDiffOn ℝ ∞ p (Comparison.slab 0 T))
    (hq : ContDiffOn ℝ ∞ q (Comparison.slab 0 T))
    (hK : IsCompact K)
    (hsupp : ∀ t ∈ Icc (0 : ℝ) T, tsupport (fun x => u (t, x)) ⊆ K)
    (hev : UniformFiniteEnergy (Icc (0 : ℝ) T) v)
    (hdu : ∀ t ∈ Ioo (0 : ℝ) T, ∀ x, spatialDivergence u t x = 0)
    (hdv : ∀ t ∈ Ioo (0 : ℝ) T, ∀ x, spatialDivergence v t x = 0)
    (hNS : ∀ t ∈ Ioo (0 : ℝ) T, ∀ x,
      navierStokesResidual 1 u p t x = navierStokesResidual 1 v q t x)
    (hzero : ∀ x, u (0, x) = v (0, x)) :
    ∀ t ∈ Icc (0 : ℝ) T, ∀ x, u (t, x) = v (t, x) := by
  have heu := CompactComparisonBounds.uniformFiniteEnergy_of_compact_slab hu hK hsupp
  let H : PressureRecovery.Hypotheses T u v p q :=
    ⟨hT, hu, hv, hp, hq, hdu, hdv, (fun t ht x => by simpa using hNS t ht x), heu, hev⟩
  have hum : ∀ t ∈ Icc (0 : ℝ) T,
      AEStronglyMeasurable (fun x => u (t, x)) volume :=
    fun t ht => (spatial_smooth hu ht).continuous.aestronglyMeasurable
  have hvm : ∀ t ∈ Icc (0 : ℝ) T,
      AEStronglyMeasurable (fun x => v (t, x)) volume :=
    fun t ht => (spatial_smooth hv ht).continuous.aestronglyMeasurable
  have hew := uniformFiniteEnergy_sub hum hvm heu hev
  obtain ⟨M, hM0, hM⟩ := uniformFiniteEnergy_lpNorm_two_bound
    (fun t ht => (hum t ht).sub (hvm t ht)) hew
  obtain ⟨U, hU0, hU⟩ := CompactComparisonBounds.exists_lpNorm_three_bound
    hu.continuousOn hK hsupp
  obtain ⟨G₀, hG₀, hTensor⟩ := uniformFiniteEnergy_tensorDiff_lpNorm_one_bound hum hvm heu hev
  obtain ⟨CP, hCP, hpressure⟩ := PressureFlux.exists_uniform_actual_pressure_flux_bound
    H M U G₀ hM0 hU0 hG₀ hM hU hTensor
  obtain ⟨G, hG0, hG⟩ := CompactComparisonBounds.exists_gradient_bound hT hu hK hsupp
  obtain ⟨R₀, _hR₀, hvanish⟩ := CompactComparisonBounds.exists_radius_weight_derivative_zero hK hsupp
  apply WholeSpaceComparisonClosure.eq_of_pressure_flux_bound
    hT.le hM0 hG0 hCP hu hv hp hq
    (fun t ht => (hM t ht).1) (fun t ht => (hM t ht).2) hG hdu hdv hNS hzero hvanish
  intro R hR t ht
  simpa only [WholeSpaceComparisonClosure.pressureEnvelope, neg_div] using hpressure R hR t ht

end NavierStokesR3.WholeSpaceUniqueness
