# Smooth force cutoff — bounded result and obstruction

## Status

**Unconditional formal result (force transformation):** a genuine C∞ shutdown preserves future smoothness, spatial support, and unit spatial periods. Applied to any `R3CompactCandidate.Properties u p f`, the modified force satisfies the actual `Comparator.ForceConditionDecay` predicate. This is not a solution construction.

**Explicitly conditional formal PDE bridge:** if the old residual equals `f` at a point, its defect for the modified force is exactly `(1-ρ) • f`. The original velocity and pressure satisfy the new equation if and only if this defect vanishes.

No unforced counterexample, stability estimate, or local-existence theorem is claimed.

## Types, cutoff, and endpoints

All fields use `Space = EuclideanSpace ℝ (Fin 3)`, `SpaceTime = ℝ × Space`, `VelocityField = SpaceTime → Space`, and `PressureField = SpaceTime → ℝ`. Fix real times `0 < t₀ < t₁ < 1`. Define

\[
  ρ(t)=1-\operatorname{smoothTransition}((t-t₀)/(t₁-t₀)),\qquad
  g(t,x)=ρ(t)f(t,x).
\]

This uses Mathlib's actual smooth transition (the same construction underlying the imported smooth bump), not an indicator or an assumed cutoff. `ρ` is smooth on all ℝ, `0≤ρ≤1`, equals one for **all** `t≤t₀`, and equals zero for **all** `t≥t₁`, including endpoints. Positive-order scalar derivative support is contained in `[t₀,t₁]`; the formal statement does not assert equality of supports or endpoint derivative values. Smoothness holds even for degenerate parameter choices, but plateau theorems require `t₀<t₁`; support-in-future additionally uses `0≤t₁`.

`cutForce_smoothOn` works on any subset `D` of spacetime, including the closed future domain. No time-zero full derivative PDE convention is inferred from this force smoothness theorem. `cutForce_support` is a spacetime nonzero-support inclusion. `cutForce_supportedIn` preserves the stronger single spatial set valid for every `t≥0`. With a compact spatial set, the imported all-order within-jet decay theorem proves the real-exponent Comparator force predicate, including its time-zero convention. This does not require the old velocity to be smooth at time one.

Periodicity is precisely `UnitSpatialPeriodsOn times f`, for an arbitrary set of real times. Multiplication by a scalar depending only on time preserves it. Periodic forces are not integrated over all of ℝ³. This file proves periodicity and smoothness, but does not package a separate `ForceConditionPeriodic` theorem.

## What equation changes?

The formal PDE operator is viscosity **one**:
\[
 R(u,p)=∂_t u+Du(u)-Δu+∇p.
\]
At any point where `R(u,p)=f`,
\[
 R(u,p)-g=(1-ρ)f.
\]
Thus the old pair still solves the new equation exactly when `(1-ρ)f=0`. For `t≥t₁` this requires `f=0`. The identity uses the actual repository residual; it does not abstract differential operators into assumed linear maps.

**Unformalized differential deduction:** if instead one cuts the velocity and pressure, `U=ρu`, `P=ρp`, under classical time differentiability and two spatial velocity derivatives (and a spatial pressure derivative), then at fixed viscosity ν,
\[
 R_ν(U,P)=ρf+ρ'u+(ρ²-ρ)Du(u).
\]
This includes *both* activation errors. If pressure is left unchanged, add `(1-ρ)∇p` to the right side. Divergence remains `ρ div u`. These product-rule identities are not newly formalized here; the formal development cuts only the force, never the velocity. A velocity shut off before one cannot retain the original terminal speed blowup.

For a new solution `v,q` of `R(v,q)=g`, let `w=u-v`, `r=p-q`. On a smooth presingular slab, the intended difference equation is
\[
 ∂_t w=Δw-Du(w)-Dw(v)-∇r+(1-ρ)f.
\]
This is an **unformalized deduction here**, not a comparison estimate. The sign is positive with this difference convention. The needed new solution does not follow from admissibility of `g`.

## Two distinct restart proposals

1. **Immediate unforced restart:** prescribe datum `a(x)=u(t₀,x)` and solve with force zero at new time `s=0`. Zero forcing is smooth and admissible in its own right. It need not match the old force at `t₀`, so gluing the entire forced history to zero need not be smooth. Even if an unforced solution exists, agreement with `u(t₀+s,x)` has not been proved; that old field still has force `f(t₀+s,x)`.
2. **Smooth switch-off:** prescribe `g=ρf`, retain the history before `t₀`, and seek a new solution with the same restart datum. The new equation is forced during `(t₀,t₁)` and unforced only afterward. A further restart at `t₁` uses the *new* datum `v(t₁,x)`, not the original `u(t₁,x)` unless agreement is proved. Neither the existence up to `t₁` nor preservation of growth up to one is a consequence of this file.

In either case the translated presingular horizon is `H=1-t₀>0`, not the whole future; endpoint `s=H` is not assumed regular. `ProblemStatement.Solution` hardcodes zero initial velocity and cannot simply be reused for arbitrary restart datum.

## Independently inspected source map

Read the planner and both prior Astra `final-report.md` and `skeptical-review.md` at the artifact path specified in `PLAN.md`. Their warning that terminal flatness and shutdown at two are not unforced restart theorems is confirmed by these source signatures:

- `NavierStokes/SmoothCutoffs.lean`: actual bump, `cutoff_contDiff`, plateau/support theorems, `timeSwitch_contDiff`; the existing activation switch is zero early and one late, not shutdown.
- Mathlib `Analysis/SpecialFunctions/SmoothTransition.lean`: `Real.smoothTransition`, its global smoothness, bounds and plateau theorems. This supplies our reverse transition.
- `NavierStokes/TimeLocalization.lean`: `activatedVelocity_eq_late` is equality for `t≥3/4`; it preserves rather than removes terminal velocity growth. Its divergence lemmas use actual spatial differentiability.
- `NavierStokes/CandidateFromLimits.lean`: `force` is a smooth extension of the traced activated residual; `force_eq_activated_residual` requires `0≤t<1`; `force_smooth` is global; `force_zero_from` requires `2≤t`.
- `NavierStokes/R3CompactCandidate.lean`: `Properties.force_smooth`, `.force_support`, `.force_time_support`; `of_limits` builds the activated compact candidate with that actual extended force.
- `NavierStokes/CompactSpatialForceDecay.lean`: `SupportedIn`, `jet_zero_outside`, `jet_decay` (every natural jet order and real decay exponent), `forceConditionDecay` to the actual Comparator predicate.
- `NavierStokes/MixedPeriodicAssembly.lean`: `exists_compact_candidate` constructs first via `R3CompactCandidate.of_limits`; the periodic assembly then uses the compact candidate. Spatial lattice translation commutes with a time-only scalar; interchange with the locally finite periodization is an elementary deduction, not newly checked here.
- `NavierStokes/ActualCandidateAssembly.lean:1025–1074`: the `Witness` conclusion includes `∃ compactForcing, R3CompactCandidate.Properties ... compactForcing`; `selected_witness` closes this source route. Our theorem consumes exactly this `Properties` type, but does not import or re-elaborate the heavy selected-witness construction.
- `NavierStokes/ProblemStatement.lean`: concrete operators, domains, unit periods, zero-datum trap. `NavierStokes/ResidualCalculus.lean` has constant-spatial-scalar derivative/divergence rules; no general activation residual theorem is asserted on their strength alone.

## Accepted Lean file and declaration ledger

Only `Research/UnforcedRestart/smooth-force-cutoff/Main.lean` is proposed for acceptance. Namespace prefix for every entry: `UnforcedRestart.SmoothForceCutoff.` Inline axiom prints cover **every** definition and theorem; no separate research import mapping is needed.

| Declarations | Exact premise summary | Classification |
|---|---|---|
| `shutdown`, `shutdown_smooth`, `shutdown_bounds` | Arbitrary real endpoints/time | C: scalar construction |
| `shutdown_early`, `shutdown_late` | `t₀<t₁`, respectively `t≤t₀`, `t₁≤t` | C |
| `shutdown_derivative_support` | `t₀<t₁`, natural `n`; derivative order `n+1` | C |
| `cutForce` | Real endpoints, actual `VelocityField` | A: field transformation |
| `cutForce_smoothOn` | `ContDiffOn ℝ ∞ f D`, arbitrary spacetime set `D` | A |
| `cutForce_early`, `cutForce_late` | Strict endpoint order and corresponding closed plateau inequality | A |
| `cutForce_support` | Arbitrary endpoints and force | A |
| `cutForce_periodic` | `UnitSpatialPeriodsOn times f` | A |
| `cutForce_time_support` | `t₀<t₁`, `0≤t₁` | A |
| `cutForce_supportedIn` | Existing `SupportedIn K f` | A |
| `compact_candidate_cut_admissible` | `t₀<t₁`, `0≤t₁`, `Properties u p f` | A: actual Comparator admissibility via imported decay estimate |
| `old_residual_defect`, `old_solves_cut_iff` | Actual pointwise `navierStokesResidual u p t x = f (t,x)` | A: explicitly conditional PDE algebra |

No new integral estimate (class B) is claimed. Ordinary assumptions in the transformation lemmas do not contain a desired new solution or desired blowup.

### Successful strict check and axiom audit

From worktree root, command executed serially with exit **0**:

```sh
env LEAN_NUM_THREADS=1 lake env lean -j1 \
  -DautoImplicit=false -DwarningAsError=true \
  -o Research/UnforcedRestart/smooth-force-cutoff/out/Main.olean \
  -i Research/UnforcedRestart/smooth-force-cutoff/out/Main.ilean \
  Research/UnforcedRestart/smooth-force-cutoff/Main.lean \
  > Research/UnforcedRestart/smooth-force-cutoff/out/Main.log 2>&1
```

The final serial rerun also exited **0**. `git diff --exit-code` exited **0**, recorded in `out/baseline-diff.exit` with empty `out/baseline-diff.log`; tracked baseline files remain unchanged. Only owned paths were written; no build/install/configuration/commit operation was performed.

`out/Main.exit` records `0`. `out/Main.log` contains the complete inline axiom output: each of the 17 exported declarations has exactly `{propext, Classical.choice, Quot.sound}`. No other trust primitive occurs in these closures. The check uses prepared cached baseline imports; it is not a clean rebuild, independent Comparator execution, or Clay-prose audit.

A first strict attempt failed because the periodicity proof left a definitional-equality goal and a binder triggered the unused-variable linter. Fixed with `rfl` and an anonymous binder; no options were weakened. Failed elaboration output included Lean's unresolved-goal `sorryAx`, so that attempt was not accepted. The corrected final source and successful fresh axiom log contain no such closure. No incomplete Lean scratch file is accepted.

## Unproved bridges and acceptance boundary

- Applicable nonzero-datum Navier–Stokes local existence, lifespan through `t₁`, continuation toward one, and uniqueness in the relevant class.
- Strong-norm comparison of the new and old solution, with pressure/boundary handling and constants on presingular slabs. L² closeness alone does not transfer pointwise growth.
- Sufficient smallness of `(1-ρ)f` in those precise norms relative to the deteriorating stability threshold. `0≤ρ≤1` gives no such quantitative threshold. Higher time derivatives of the cutoff typically cost powers of `(t₁-t₀)⁻¹`; no uniform-in-width higher-jet bound is claimed.
- Terminal literal zero force or admissible pressure-gradient absorbability is not proved. Pointwise flatness at `(1,0)` and shutdown at `2` cannot supply either on a terminal interval before one.
- A new solution after switch-off need not have fixed compact velocity support. Only the **force** support is preserved here.

**Success criterion met:** smooth admissible modified force, honest unchanged/zero regions, and the exact old-field defect are checked. **Failure criterion for an unforced conclusion remains:** no construction or stability control of the modified solution. Any claim that the old singular velocity automatically continues solving the cut equation is directly contradicted by the checked defect identity unless its extra vanishing condition is separately discharged.
