# Energy comparison — agent 8

## Result and scope

**Checked analytic result (B), explicitly conditional on classical field/PDE hypotheses:** periodic inhomogeneous relative energy balance and a dissipative Young inequality, at viscosity **one**. These use actual repository derivatives and cube Lebesgue integrals; the energy identity is a conclusion, not a hypothesis. No competitor existence, force smallness, or blowup transfer is proved. No new whole-space theorem is claimed.

Read independently: `PLAN.md`, the prior Astra `final-report.md` and `skeptical-review.md` in the specified artifact directory, and the source modules below. The prior warning is confirmed: equal-force uniqueness cannot compare a forced reference with an unforced competitor. The new theorem removes this equal-force restriction in the periodic energy calculation, not in local existence or strong-norm stability.

## Accepted Lean

Only `Research/UnforcedRestart/energy-comparison/Main.lean`; sole direct import `NavierStokes.PeriodicUniqueness`. Namespace `UnforcedRestart.EnergyComparison`. Inline axiom audit covers every exported declaration (no new definitions):

1. `forced_energy_balance` — actual-field differential and integrated analytic bridge (A/B).
2. `forcing_work_le` — actual cube-integral Young inequality (B).
3. `forced_energy_rate_le` — actual dissipative relative-energy estimate (B).

All three are universally quantified conditional lemmas, not assertions that a new NS solution exists. No conjecture is encoded as a hypothesis-free theorem.

### Exact mathematical hypotheses and conclusions

`Space = EuclideanSpace ℝ (Fin 3)`, velocity and force fields have type `ℝ × Space → Space`, pressure fields type `ℝ × Space → ℝ`. For arbitrary real `t`, take fields `u,v,p,q,f`. At that time assume:

* All four spatial slices `u,v,p,q` are `ContDiff ℝ ∞`.
* All four spatial slices have `UnitPeriods` (unit coordinate periods).
* `spatialDivergence u t x = spatialDivergence v t x = 0` for every `x`.
* Both velocity time slices at every `x` are fully differentiable at `t`.
* `x ↦ f(t,x)` is continuous.
* For every `x`, `navierStokesResidual u p t x - navierStokesResidual v q t x = f(t,x)`.

Here `f` means **force difference**. For forced reference and unforced competitor this is the reference force, with positive sign. Let

\[
w=u-v,\quad r=p-q,\quad E(t)=\int_Q|w|^2,\quad
D(t)=\sum_{i=1}^3\int_Q|\partial_iw|^2,
\]
\[
C(t)=\int_Q\langle w,Du(w)\rangle,\quad W(t)=\int_Q\langle w,f\rangle.
\]

`Q` is `[0,1]^3` in `Fin 3 → ℝ` coordinates, mapped by `PeriodicIntegration.toSpace`. `D` uses the sum of squared coordinate derivative norms (Hilbert–Schmidt convention), whereas the bound on `Du` below uses its operator norm.

The first theorem proves
\[
\operatorname{energyRate}(u,v,t)=-2D(t)-2C(t)+2W(t).
\]

The second theorem assumes only continuous slices `w,f` and proves
\[
2W\le \int_Q|w|^2+\int_Q|f|^2.
\]

The third retains all first-theorem hypotheses and assumes a real `B` with
`∀ y ∈ cube, ‖spatialDerivative u t (toSpace y)‖ ≤ B`. It proves
\[
\operatorname{energyRate}(u,v,t)+2D(t)
\le(2B+1)E(t)+\int_Q|f(t)|^2.
\]

No positivity premise on `B` is necessary for this pointwise estimate; its gradient-bound premise already forces nonnegativity on the nonempty cube. Force periodicity is unnecessary for the integral manipulations. In an actual periodic PDE application it follows from the residuals under the corresponding time-periodicity hypotheses. No energy bound field is added to the periodic Comparator class.

## Why the analytic cancellations are legitimate

The proof subtracts the actual residuals and uses the existing derivative subtraction and advection expansion to derive
\[
\partial_tw=\Delta w-Du(w)-Dw(v)-\nabla r+f.
\]

It does not invoke the equal-force `difference_equation` with an invalid premise. Smooth spatial slices ensure all displayed integrands are continuous and hence integrable on the compact cube. Each splitting of the Bochner integral supplies continuity hypotheses; there is no use of a nonintegrable integral's default value to obtain the result.

The baseline lemmas used for boundary cancellation are:

* `PeriodicUniqueness.cubeIntegral_laplacian_energy`: periodic derivative traces and integration by parts give `-D`.
* `cubeIntegral_transport_energy_zero`: periodicity of `w,v` and `div v=0` give zero transport work.
* `cubeIntegral_pressure_energy_zero`: periodicity of **pressure difference as well as velocity**, and `div w=0`, kill pressure work.
* `neg_coupling_le_energy`: pointwise operator norm estimate integrated on the cube.
* `PeriodicIntegration.cubeIntegral_mul_partial` and related box identities underlie these cancellations; the module imports mathlib's box divergence theorem.

Pressure is periodic here, not merely periodic up to an affine function. A time-only gauge is harmless; an affine spatial pressure is not licensed.

## Presingular slab and endpoint bridge

**Unformalized assembly of already checked baseline lemmas:** fix `0<t₀<1` and `0<S<1-t₀`, set `a=t₀`, `b=t₀+S`. Suppose `u,v,p,q` are jointly `ContDiffOn ℝ ∞` on `slab a b`, spatially periodic there, divergence-free and satisfy the force-difference PDE on `Ioo a b`. Suppose `f` is jointly continuous there (smooth force suffices).

For every `t∈Ioo a b`, `SolutionDifference.spatial_smooth` and `time_differentiable_at_interior` discharge the slice hypotheses. Crucially, `PeriodicUniqueness.energy_hasDerivAt hu hv ht` identifies `energyRate` with the derivative of the genuine integral. Consequently
\[
\frac12 E'(t)+D(t)=-C(t)+W(t)
\]
there. `energy_continuousOn` gives endpoint continuity, and `energy_initial_zero` gives `E(a)=0` if the restart data agree. No zero original datum is assumed. `Solution.mono` is not an arbitrary-data restart theorem.

Joint slab smoothness and compactness also give a uniform finite gradient bound via `SolutionDifference.exists_gradient_bound`, using `PeriodicUniqueness.cubeImage`. This supplies some `B_S`, not a bound uniform as `S↑1-t₀`. With appropriate continuity of the rate terms, the fundamental theorem of calculus gives the integrated balance on the closed slab. That last assembly/integration is not exported by this task.

After translating to `s=t-t₀`, the same identities hold on the **open** new time interior. We do not assert a full derivative at `s=0` from one-sided smoothness, or identify it with Comparator `derivWithin` without a boundary bridge. No smoothness at original time `1` is assumed.

**Unformalized general-viscosity deduction:** if both residuals are instead defined as `∂t u+Du(u)-νΔu+∇p` with the same `ν>0`, the same calculation replaces `D` by `νD`. The exported Lean theorems only concern the repository's viscosity-one residual.

## Whole space: explicit unresolved bridge

On R³, periodic cube cancellation cannot be reused. Compact support belongs to the constructed reference `u`, not to `v` or `w=u-v`. Smoothness and finite `L²` velocity alone do not justify pressure-flux removal or differentiation under an infinite-volume integral.

A sufficient analytic route, **not formalized here**, is localization with smooth compact cutoffs `χ_R→1`, `|∇χ_R|≲1/R`, `|Δχ_R|≲1/R²`. The localized identity contains
\[
\tfrac12 E_R'+\nu\int\chi_R|\nabla w|^2
=-\int\chi_R\langle w,Du(w)\rangle+\int\chi_R\langle w,f\rangle
+\tfrac\nu2\int |w|^2\Delta\chi_R
+\tfrac12\int |w|^2v\cdot\nabla\chi_R
+\int r\,w\cdot\nabla\chi_R.
\]

One must justify the limit, for example by assuming/proving on each slab:

* `w∈C_t L²_x ∩ L²_t H¹_x`, enough time regularity for the localized identity, and the required integrability of coupling and forcing work;
* `Du∈L¹_t L∞_x` and `f∈L²_t L²_x` (or a separately handled `L¹_t L²_x` budget);
* vanishing of the three displayed boundary terms after time integration (absolute spacetime integrability of `|w|²|v|` and `|r||w|` is a sufficient, stronger condition for the latter two);
* endpoint convergence and dominated/monotone convergence for the remaining terms.

These are sufficient analytic obligations, not claims about an arbitrary Comparator competitor. In particular no pressure decay is silently inserted. The actual existing `NavierStokesR3.WholeSpaceUniqueness.classical_uniqueness_on_Icc` takes smooth velocity and pressure, a common compact reference support, slab-uniform competitor finite energy, divergence freedom, **equal residuals**, and equal initial data. It obtains pressure recovery through `PressureRecovery.Hypotheses`, `PressureFlux.exists_uniform_actual_pressure_flux_bound`, then `WholeSpaceComparisonClosure`. Its equal-residual pressure recovery is not already a theorem for our force difference. That inhomogeneous recovery/flux closure remains unproved here.

## Actual candidate path and remaining success criteria

Source path: `ActualCandidateAssembly.selected_witness` bundles the periodic candidate and compact candidate; `selected_candidate` projects the periodic `candidateStatement`. `R3CompactCandidate.Properties` extends `Solution (Ico 0 1)` and supplies force smoothness, common compact velocity support, compact force support, and speed unboundedness. `R3CompactCandidate.of_limits` uses `CandidateFromLimits.force_eq_activated_residual` with `TimeLocalization.activatedVelocity/activatedPressure`. Compact-first periodization is described in `MixedPeriodicAssembly`. No selected-witness specialization or Comparator verification was compiled by this task.

To apply the new periodic estimate one still needs an actual unforced comparator of the appropriate nonzero restart datum, same viscosity, lifespan covering the desired slabs, and periodic pressure. To transfer singular axis speed one needs a norm controlling evaluation, not this `L²` estimate. Concentration can have small `L²` norm and large pointwise amplitude. For example, smooth rescaled bumps `ε^{-1}ψ(x/ε)` have squared `L²` norm proportional to `ε` in dimension three and value proportional to `ε^{-1}` at the origin. The phenomenon also admits divergence-free examples by rescaling a smooth compactly supported curl with nonzero origin value. Thus no positive `L²`-error threshold alone preserves pointwise blowup.

Success achieved: checked inhomogeneous periodic balance, exact dissipation sign, checked actual forcing-work bound. Missing: quantified candidate budget relative to deteriorating constants, strong-norm comparison, unforced local existence/lifespan, whole-space inhomogeneous pressure recovery, and candidate-specific application. Neither A/B failure nor terminal force removal follows.

## Validation and provenance

Successful final command (exit **0**, recorded in `out/Main.exit`):

```sh
env LEAN_NUM_THREADS=1 lake env lean -j1 \
  -DautoImplicit=false -DwarningAsError=true \
  -o Research/UnforcedRestart/energy-comparison/out/Main.olean \
  -i Research/UnforcedRestart/energy-comparison/out/Main.ilean \
  Research/UnforcedRestart/energy-comparison/Main.lean \
  > Research/UnforcedRestart/energy-comparison/out/Main.log 2>&1
```

Inline `#print axioms` output for **each** of the three exported theorems is exactly the allowed set `[propext, Classical.choice, Quot.sound]`. No additional definitions require auditing. `git diff --exit-code` returned 0 after compilation. New outputs remain within the owned task directory; no baseline/configuration edits or broad builds were performed.

Development failures were elaboration issues, not accepted proofs: an inner-product scalar needed an explicit `ℝ` annotation; equality negation required `congrArg Neg.neg`; integral rewriting needed explicit lambda-shaped continuity facts; pointwise function arithmetic needed `change`. Corrected source passed strict elaboration and complete inline closure checks. Only the final log is acceptance evidence.

This is fresh focused research elaboration against prepared baseline artifacts, not a clean kernel rebuild of dependencies, independent challenge run, or proof of equivalence with Clay prose.
