# Actual forcing budget — agent 11

> Classification notice (agent 18): task-local research labels below are historical and superseded by [MANIFEST.md](../../Research/UnforcedRestart/MANIFEST.md). Its four actual candidate-contract force-budget lemmas are class **A**, not B; this does not establish the weighted stability threshold. Research categories are unrelated to Clay problem alternatives A/B/C/D.

## Verdict and classification

**No verified force-removal/stability threshold for the actual candidate was found.** The actual force has bounded derivatives on whole future spacetime (compact case) or on a fundamental periodic cell, not merely finite jets on the axis. Consequently its time-integrated norms on shrinking terminal intervals become small against **fixed** tolerances. This does not compare them with the shrinking tolerances of a singular-reference stability theorem.

Fresh formal results: four checked lemmas in `Research/UnforcedRestart/actual-forcing-budget/Main.lean`, namespace `UnforcedRestart.ActualForcingBudget`. They concern the real `R3CompactCandidate.Properties`, actual Fréchet jets, and genuine Lebesgue time integrals. They do not assert an unforced solution exists, nor transfer singularity. Theorems are unconditional implications from the repository candidate properties, whose actual assembly is source-mapped below; the file does not import or freshly instantiate the enormous actual assembly.

Independently read the planner and both prior Astra `final-report.md` and `skeptical-review.md` at the artifact directory specified in `PLAN.md`. Their distinction between C/D and A/B survives this source inspection. No independent audit of every correction estimate, clean baseline kernel rebuild, or Comparator challenge execution is claimed.

## Exact fields and source route

All paths below are under `NavierStokes/`; viscosity is **one**. Space is `ProblemStatement.Space = EuclideanSpace ℝ (Fin 3)`, spacetime is `ℝ × Space`; fields take `(t,x)`.

1. `ActualCandidateAssembly.Witness`, lines 1016–1051, fixes one schedule and the actual sums `ASum`, `BSum`, `PSum`. `selected_witness`, lines 1070–1074, closes this construction at `ActualCandidateConstruction.selectedBudget` and `selectedThreshold`. Its final existential supplies compact force and `R3CompactCandidate.Properties` for the activated cut fields. Its earlier force is the **periodic** force, with full boundary jet identities; do not confuse these two existential fields.
2. `MixedPeriodicAssembly.exists_compact_candidate` constructs the compact force first. Put
   \[
   U=\operatorname{curl}(\eta A)+\eta B,
   \quad P=\eta P_{\infty},\qquad u=\theta U,\quad p=\theta P.
   \]
   This uses `cutVelocity`, `SpatialLocalization.cutPressure`, then `TimeLocalization.activatedVelocity/activatedPressure`. The spatial cutoff is genuinely smooth:
   `η(x)=SmoothCutoffs.cutoff(16(x₀²+x₁²))*SmoothCutoffs.cutoff(4x₂)`.
   Its fixed support cylinder is
   \[
   K=\{x:x_0^2+x_1^2\le1/16,\ |x_2|\le1/4\},
   \]
   compact and contained in the coordinate cube of half-width `1/4`. It is one on `radialSquare < 1/32`, `|x₂| < 1/8`. This is not a spatial cutoff shrinking to the axis.
3. `CandidateFromLimits.force` is `SpacetimeGluing.smoothExtension 1` of `tracedResidual`, with a Taylor–Borel future extension selected from actual residual limits. `force_eq_activated_residual` gives
   \[
   f(t,x)=R_1(u,p)(t,x),\quad \forall t\in[0,1),\ \forall x\in\mathbb R^3.
   \]
   This is an identity on **all** presingular spatial points, not only a germ. `force_smooth` gives global spacetime smoothness of this constructed force; `force_zero_outside` keeps the same spatial cylinder at every real time; `force_zero_from` is only for `t≥2`.
4. `MixedPeriodicAssembly.candidate_of_periodization`, `periodized_navier_stokes`, and `periodize_jets` use separated translates. Periodic forcing is the lattice periodization of the compact force. Locally it equals a single translate; nonlinearity is not being superposed across overlapping supports.

The explicit activation identity, by ordinary differentiation on `0<t<1`, is
\[
f=\theta R_1(U,P)+\theta' U+(\theta^2-\theta)DU(U).
\]
The switch is zero for `|t|≤3/8` and one for `t≥3/4`. Hence activation errors disappear on the late presingular interval, but the **cut residual** remains. Cutting a potential adds `∇η × A` to the velocity and creates derivative commutators in the residual. No source identity sets these annular terms to zero near time one.

### Terminal neighborhoods, not just terminal jets

`MixedPeriodicAssembly.cutResidual_vanishingJointJets` transfers the incoming joint residual flatness at `(1,0)` through the plateau. `JointResidualLimits.boundaryLimits` is zero at the origin, but for `x≠0` it is the Taylor series of an actual one-sided extension selected at `(1,x)`. `CandidateFromLimits.force_boundary_jets` identifies the force jets with that family. These exterior jets are **not asserted zero**. For periodic fields, the zero jet assertion repeats at lattice copies of the origin.

Thus:

* On a fixed compact spacetime slab including `t=1`, every force derivative is uniformly bounded, including the cutoff annulus and all exterior points.
* In a sufficiently small joint neighborhood of `(1,0)`, continuity and the zero jet imply smallness of any fixed jet. Smooth infinite flatness also implies arbitrary Taylor-order local bounds, with order-dependent constants and neighborhoods (ordinary deduction, not newly formalized).
* Neither claim implies `sup_x |D^m f(t,x)| → 0` as `t↑1`: the terminal trace can be nonzero away from the origin. We have **not proved** that this actual trace is nonzero either.
* Even flatness of a smooth function at every derivative order at one point does not force it to vanish on a neighborhood. No terminal force-free or periodic-gradient interval has been established.

## Norm estimates that really follow

Let `J_m(t,x)=iteratedFDerivWithin ℝ m f futureDomain (t,x)`. For `t>0` these are ordinary full jets; the within convention at zero is retained. `CompactSpatialForceDecay.jet_zero_outside` shows every jet is supported in the same closed `K`, using a relative-neighborhood argument, not an unjustified assertion about derivative supports. `jet_decay` proves, for each `m∈ℕ` and each real `N`, existence of `C_{m,N}>0` with
\[
 |J_m(t,x)|\le C_{m,N}(1+|x|+t)^{-N}\quad(t\ge0).
\]
This decay is obtained by compactness of weighted jets plus compact future time support. It is **not** a small parameter bound. At `N=0`, our checked lemma extracts `|J_m|≤C_m` uniformly on the entire future.

**Unformalized deductions from those formal inputs.** Write `V=volume(K)<∞`, with the usual Lebesgue normalization, and `I=[a,b]⊂[0,∞)`, length `ℓ=b-a`. For `1≤p<∞`,
\[
 \|J_m(t)\|_{L^p_x}\le C_m V^{1/p},\qquad
 \|J_m\|_{L^q_t(I;L^p_x)}\le C_m V^{1/p}\ell^{1/q}
 \quad(1\le q<\infty).
\]
For `p=∞`, omit the volume factor; for `q=∞`, omit the length factor. Continuity, compact support and finite-dimensional tensor targets supply measurability and integrability; these mixed-norm statements are not new accepted Lean declarations here. In particular
\[
 \int_a^b\|f(t)\|_2dt\le C_0\sqrt V\ell,\qquad
 \int_a^b\|f(t)\|_\infty dt\le C_0\ell.
\]
All spatial derivative orders have analogous bounds. Integer `H^k` bounds follow by bounding each spatial derivative using the full tensor and summing over finitely many coordinate directions; retain the corresponding finite dimension/order constants. Compact support persists for these derivatives. No fractional Sobolev, Besov, or Leray-projector estimate is silently included.

Periodic norms must use a **unit cell**, not the whole-space integral of a periodic function. `PeriodicForceDecay.futureJet_decay` supplies the same uniform bound by taking its real decay exponent zero. Unit-cell volume is one, so `L^p` bounds follow from the uniform bound; one can sharpen these by tracking the single translated compact support. Whole-space `L²` of a nonzero periodic force is not finite.

For a parabolically rescaled force at fixed viscosity, a spatial derivative mixed norm scales as
\[
 \|D_x^k f_r\|_{L^q_sL^p_y}
 =r^{3+k-2/q-3/p}\|D_x^k f\|_{L^q_tL^p_x}
\]
(on corresponding domains), so force-critical exponents satisfy `2/q+3/p=3+k`. Smooth compact forcing belongs to the usual finite-exponent norms on finite slabs, including, for instance, `L¹_t L³_x`. Finite membership and short-interval smallness alone are not a verified critical-space perturbation theorem for a singular reference. This scaling calculation is unformalized here; no limit solution is claimed.

## Why the threshold is still not checked

Fix `0<t₀<1`, `H=1-t₀`, and let `w=u-v` with equal data at `t₀`, where `v` would be an unforced solution at the same viscosity. If an independently justified energy comparison gives, for `g=||w||₂`,
\[
 g'(t)\le K(t)g(t)+F(t),\quad g(t₀)=0,
 \qquad F(t)=\|f(t)\|_2,
\]
then the scalar bound would be
\[
 g(T)\le\int_{t₀}^T
 e^{\int_s^T K(r)dr}F(s)ds
 \le C_0\sqrt V\,(T-t₀)e^{\int_{t₀}^T K(r)dr}.
\]
This is **explicitly conditional/unformalized**: the actual PDE-to-energy hypotheses (pressure flux, regularity, integrability) and the scalar differentiation at `g=0` must be justified. A reference-dependent coefficient can become unbounded as `T↑1`. The budget estimate is linear in remaining interval length; it does not bound the weighted integral by a specified vanishing tolerance. An upper bound that diverges also does not prove the actual error diverges.

Even a uniform `L²` error bound does not preserve the actual axis speed. Point evaluation requires a stronger comparison norm (e.g. a proved `H^k→C⁰` embedding with `k>3/2` in dimension three, and derivative evaluation needs `k>5/2`). A viscous stability estimate in that norm needs its own reference bounds, force norms and lifespan theorem. Those constants are not supplied by the force decay declarations.

For a modified force `χf`, the forcing discrepancy is `(1-χ)f`, not zero on the transition slab. If a transition width is `d`, its time derivatives contain terms `d^{-j}χ^{(j)}D_t^{m-j}f`. Spatial norm bounds may improve with the slab length, but full spacetime derivative budgets need not. Cutting the force does not make the old velocity solve the changed equation.

**Unknown inputs/constants:** actual `C_m` and weighted compactness maxima; schedule/Borel extension seminorms and neighborhoods; exterior terminal trace size; solenoidal projection bounds in the chosen norm (`L∞` boundedness of the Leray projection cannot be presumed); singular-reference amplification; Sobolev embedding constants; restart strong norms and local lifespan; pressure correction admissibility. No numerics or smallness in a freely tunable construction parameter have been extracted. The future Borel extension contributes to the global constants used here; a bound on `[t₀,1]` alone could be smaller but is still nonquantitative in the inspected declarations.

**Success criterion for force removal:** specify a genuine unforced local solution class and strong-norm comparison theorem, then prove the actual weighted solenoidal discrepancy is below its explicit tolerance throughout the required presingular horizons, with lifespan coverage and noncircular growth transfer. None of these last requirements is discharged here. An alternative success would be proving a smooth admissible pressure potential for the force on an entire terminal slab; origin jets and shutdown at two do not supply it.

## Accepted formal deliverables and validation

Only accepted Lean file: `Research/UnforcedRestart/actual-forcing-budget/Main.lean`. Imports: `NavierStokes.R3CompactCandidate`, `NavierStokes.PeriodicForceDecay`, `Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic` (all baseline).

Every theorem has the explicit premise `h : R3CompactCandidate.Properties u p f`, for real repository fields, and order `m : ℕ`:

| Declaration (namespace above) | Conclusion / additional hypotheses | Classification |
|---|---|---|
| `compact_jet_bound` | `∃ C>0, ∀t≥0, ∀x, ||J_m(t,x)||≤C` | B: actual-field uniform analytic bound |
| `compact_jet_intervalIntegrable` | for `0≤a≤b`, every fixed `x`, the norm jet is `IntervalIntegrable` w.r.t. `volume` | B: actual time-integral admissibility |
| `compact_time_integral_bound` | `∃ C>0, ∀0≤a≤b, ∀x, ∫_a^b ||J_m(t,x)||dt≤C(b-a)` | B: actual pointwise-in-space time budget, **not** integral of spatial supremum |
| `compact_short_budget` | for fixed `ε>0`, `∃δ>0`, the preceding integral is `<ε` whenever `b-a<δ` | B with elementary scalar step; δ is independent of a,b,x, not a stability tolerance |

There are no substantive new definitions or unlisted helper exports. Inline `#print axioms` covers all four declarations. The integral bounds do not rely on the totalized integral of a nonintegrable function: the separate interval-integrability theorem proves that obligation. No failed Lean attempts remain; both focused compilations succeeded, the second adding the integrability result.

Exact final command, exit **0**:

```sh
env LEAN_NUM_THREADS=1 lake env lean -j1 \
  -DautoImplicit=false -DwarningAsError=true \
  -o Research/UnforcedRestart/actual-forcing-budget/out/Main.olean \
  -i Research/UnforcedRestart/actual-forcing-budget/out/Main.ilean \
  Research/UnforcedRestart/actual-forcing-budget/Main.lean \
  > Research/UnforcedRestart/actual-forcing-budget/out/Main.log 2>&1
```

`out/Main.exit` records `0`. `out/Main.log` records all four closures, each exactly a subset of `{propext, Classical.choice, Quot.sound}` (each uses all three). No warnings, custom axioms, placeholders, unsafe mechanisms, native proof shortcuts, resource-limit overrides or challenge imports. No broad build, dependency modification, commit or push. Final `git diff --exit-code` for tracked sources returned zero.

Unproved bridges remain: mixed spatial-time norm packaging; quantitative actual seminorms; weighted strong-norm PDE comparison and thresholds; terminal pressure absorbability/zero force; applicable unforced local existence/continuation; growth transfer and coverage through all required horizons. These are obstructions/research obligations, not conjectures asserted as results.
