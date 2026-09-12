# Periodic finite-slab composition — UNVALIDATED implementation draft

Classification: research discussion / unelaborated draft, **not accepted Lean**. No theorem in this file has been compiled or axiom-audited in Round2. Kept in Markdown because the focused compile slot has not been allocated. No missing proof is to be replaced with an axiom or `sorry`.

## Exact proposed theorem

Fix one `0 < t0 < 1`, `H = 1-t0`, and `0 < S < H`. Keep the same reference `ur = shift t0 u`, comparator `v`, and datum `a : Space → Space` throughout restrictions to smaller slabs. For the raw-field theorem the origin of `ur` is immaterial; translation is a subsequent specialization, not an existence construction.

Inputs:

- `ContDiffOn ℝ ∞ ur (slab 0 S)`, similarly for `v`, `pr`, `q`;
- `ContinuousOn fr (slab 0 S)` (smooth forcing is stronger);
- `UnitSpatialPeriodsOn (Icc 0 S)` for both velocities and both pressures;
- divergence zero for both velocities on the closed slab;
- `ur (0,x) = a x` and `v (0,x) = a x` for arbitrary `a`;
- on `Ioo 0 S`, literal residuals `navierStokesResidual ur pr s x = fr (s,x)` and `navierStokesResidual v q s x = 0`, with viscosity one;
- if the theorem is packaged as a closed-slab solution contract, use the corresponding PDE with `derivWithin (fun r => field (r,x)) (Icc 0 S) s` at endpoints. No full two-sided derivative of an arbitrarily extended comparator at zero is assumed or inferred.

Conclusion: there exists `B > 0`, derived from `ur` smoothness on the compact slab/cube, with

```
∀ s ∈ Icc 0 S, ∀ y ∈ cube,
  ‖spatialDerivative ur s (toSpace y)‖ ≤ B
```

and for every `s ∈ Icc 0 S`, writing

```
L r = B
k r = 2 * L r + 1
A s = ∫ r in 0..s, k r
g s = cubeIntegral (fun x => ‖fr (s,x)‖ ^ 2)
```

one has the genuine integral estimate

```
energy ur v s ≤ Real.exp (A s) *
  ∫ r in 0..s, Real.exp (-A r) * g r.
```

The constant function `L = B` is a proved gradient majorant, not a hypothesized differential inequality. A continuous time-dependent `L` with a verified majorant property can be substituted into the same scalar adapter. No optimal time-dependent supremum is necessary for this target. `B = B_S` may diverge as `S ↑ H`.

## Short Lean drafts of the two PDE adapters

These use frozen round-one research imports. Do not copy round-one object outputs into a clean build. On later integration, resolve these imports from the appropriate newly elaborated output root.

```lean
import Research.UnforcedRestart.«energy-comparison».Main
import Research.UnforcedRestart.«gronwall-threshold».Main
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

noncomputable section
open Set
open scoped ContDiff
namespace UnforcedRestart.Round2.PeriodicSlab
open NavierStokes.ProblemStatement NavierStokes.SolutionDifference
open NavierStokes.PeriodicIntegration NavierStokes.PeriodicUniqueness

/-- The source is the actual cube squared norm, not a primitive assumption. -/
theorem force_energy_continuousOn {S : ℝ} {f : VelocityField}
    (hf : ContinuousOn f (slab 0 S)) :
    ContinuousOn (fun t => cubeIntegral (fun x => ‖f (t, x)‖ ^ 2)) (Icc 0 S) := by
  exact cubeIntegral_continuousOn_Icc (hf.norm.pow 2)

/-- Derivative and inequality are outputs of joint regularity and both PDEs. -/
theorem slab_energy_derivative_le {S t B : ℝ}
    {u v f : VelocityField} {p q : PressureField}
    (hu : ContDiffOn ℝ ∞ u (slab 0 S))
    (hv : ContDiffOn ℝ ∞ v (slab 0 S))
    (hp : ContDiffOn ℝ ∞ p (slab 0 S))
    (hq : ContDiffOn ℝ ∞ q (slab 0 S))
    (hf : ContinuousOn f (slab 0 S))
    (hpu : UnitSpatialPeriodsOn (Icc 0 S) u)
    (hpv : UnitSpatialPeriodsOn (Icc 0 S) v)
    (hpp : UnitSpatialPeriodsOn (Icc 0 S) p)
    (hpq : UnitSpatialPeriodsOn (Icc 0 S) q)
    (hdu : ∀ s ∈ Ioo 0 S, ∀ x, spatialDivergence u s x = 0)
    (hdv : ∀ s ∈ Ioo 0 S, ∀ x, spatialDivergence v s x = 0)
    (hNSu : ∀ s ∈ Ioo 0 S, ∀ x, navierStokesResidual u p s x = f (s, x))
    (hNSv : ∀ s ∈ Ioo 0 S, ∀ x, navierStokesResidual v q s x = 0)
    (hB : ∀ s ∈ Icc 0 S, ∀ y ∈ cube,
      ‖spatialDerivative u s (toSpace y)‖ ≤ B)
    (ht : t ∈ Ioo 0 S) :
    HasDerivAt (energy u v) (energyRate u v t) t ∧
      energyRate u v t ≤ (2 * B + 1) * energy u v t +
        cubeIntegral (fun x => ‖f (t, x)‖ ^ 2) := by
  have ht' : t ∈ Icc 0 S := ⟨ht.1.le, ht.2.le⟩
  have hft : Continuous (fun x : Space => f (t, x)) :=
    continuous_space_slice hf ht'
  have hres (x : Space) :
      navierStokesResidual u p t x - navierStokesResidual v q t x = f (t, x) := by
    rw [hNSu t ht x, hNSv t ht x, sub_zero]
  have hr := UnforcedRestart.EnergyComparison.forced_energy_rate_le
    (spatial_smooth hu ht') (spatial_smooth hv ht')
    (spatial_smooth hp ht') (spatial_smooth hq ht')
    (hpu t ht') (hpv t ht') (hpp t ht') (hpq t ht')
    (hdu t ht) (hdv t ht)
    (time_differentiable_at_interior hu ht)
    (time_differentiable_at_interior hv ht) hft hres (hB t ht')
  refine ⟨energy_hasDerivAt hu hv ht, ?_⟩
  have hd := dissipation_nonneg (u - v) t
  linarith

end UnforcedRestart.Round2.PeriodicSlab
```

The above lemma's gradient bound is an adapter parameter only. **Do not accept it alone as O5.** The final theorem must obtain its bound using

```
exists_gradient_bound hS hu isCompact_cubeImage
```

and map `y ∈ cube` to `toSpace y ∈ cubeImage` with `⟨y, hy, rfl⟩`. It must also assemble the following FTC and endpoint steps. The draft has no claimed successful syntax/API check.

## Minimal FTC adapter: exact mathematical proof and API obligations

For `c : ℝ → ℝ` continuous on `[0,S]`, define the literal interval integral `P(s) = ∫ r in 0..s, c r`. Prove the tuple

1. `ContinuousOn P (Icc 0 S)`;
2. `P 0 = 0`;
3. for each `t ∈ Ioo 0 S`, `HasDerivAt P (c t) t`;
4. for each `s ∈ Icc 0 S`, `IntervalIntegrable c volume 0 s`.

No behavior of `c` outside the closed slab is needed. The source APIs are:

- `ContinuousOn.intervalIntegrable` on `uIcc 0 s`, obtained by restriction and `uIcc_of_le hs.1`;
- `ContinuousOn.integrableOn_Icc`, followed by `continuousOn_primitive_interval` for item 1; the latter expects `IntegrableOn c (uIcc 0 S)`, **not just the syntactically different `IntervalIntegrable` premise**;
- `intervalIntegral.integral_same` for item 2;
- `intervalIntegral.integral_hasDerivAt_right` for item 3, with interval integrability on `[0,t]`, local strong measurability, and full continuity at interior `t`.

For the last two local conditions restrict closed-slab continuity to `Ioo 0 S`. Use `ContinuousOn.stronglyMeasurableAtFilter isOpen_Ioo` for measurability; use closed-slab `ContinuousWithinAt.continuousAt (Icc_mem_nhds ht.1 ht.2)` for continuity at `t`. Continuity **at a single point alone** is not a proof of local measurability; the open-neighborhood continuity supplies it. Do not silently assume global continuity of the raw fields.

Apply this adapter first to `k = 2*L+1`, obtaining the actual `A`, then to `c(r) = exp(-A(r))*g(r)`, obtaining the actual `P`. Its continuity follows from `A` and `g`; `g` continuity is proved by the cube-integral adapter above. Thus every primitive derivative and integrability premise is discharged from actual coefficients/forcing.

For `E = energy ur v`, take `energy_continuousOn hu hv`, `energy_initial_zero (fun x => (hu0 x).trans (hv0 x).symm)`, and the derivative/rate tuple. `weighted_budget` on `[0,S]` yields

```
exp(-A(s))*E(s) ≤ P(s)
```

since `E(0)=P(0)=0`. Multiply by `exp(A(s)) > 0`, using `exp(A(s))*exp(-A(s)) = 1`, to obtain the claimed integral estimate. This step never differentiates `sqrt(E)` at zeros.

## Closed-slab boundary obligations

The integrated estimate needs endpoint **continuity**, not endpoint full time derivatives. This is deliberate, not an omitted term in integration by parts in time: the scalar monotonicity theorem only differentiates on the open interval.

Joint `ContDiffOn` on the nondegenerate slab supplies a continuous joint within derivative, because `(uniqueDiffOn_Icc hS).prod uniqueDiffOn_univ` holds. At every `(s,x)` its restriction to spatial directions is the genuine full spatial derivative, by `spatialDerivative_eq_within_comp`. The time-direction evaluation gives `HasDerivWithinAt` on `[0,S]`. Repeating spatial differentiation yields continuous spatial second derivatives on the closed slab; the pressure gradient is likewise continuous. Hence interior residual identities extend to the closed slab for the within-time residual, by continuity and density of `(0,S)` in `[0,S]`. This is a **mathematical derivation**, not a Round2 checked endpoint lemma.

At zero, `[0,S]` and `[0,∞)` agree locally, so this within derivative agrees with `derivWithin (Ici 0)` when `S>0`. At `S`, there is no such agreement: a raw comparator defined only by a `[0,S]` contract may be arbitrary immediately to its right. Do not replace the left boundary derivative at `S` by `derivWithin (Ici 0)` or a full derivative. A comparator supplied on all `[0,H)` with `S<H` instead has `S` as an interior time.

For the translated reference the frozen `candidate_shift_within_equation` already gives the actual `Ici 0` equation at zero, from full differentiability at the OLD interior time `t0`. The translated force remains present. There is no corresponding automatic unforced comparator existence result.
