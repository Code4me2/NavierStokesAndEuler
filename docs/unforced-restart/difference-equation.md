# Difference equation — bounded checked result

Owner: agent 7; namespace `UnforcedRestart.DifferenceEquation`.

## Status and classification

**Unconditional formal result:** the actual repository differential operators obey unequal-residual subtraction under the explicit differentiability hypotheses below. These are class **A**, actual-field differential/PDE bridges, not energy estimates or existence theorems. `restart_difference_zero` is elementary class **C** data infrastructure. No unforced candidate or A/B failure is claimed.

**Explicitly conditional lemma:** applying the bridge to an unforced comparator assumes that comparator exists and satisfies the unforced PDE. Neither this premise nor any error bound is constructed here. Algebra alone uses any common real viscosity; the intended NS application fixes one common `ν > 0`. There is no varying-viscosity comparison.

Only accepted source: `Research/UnforcedRestart/difference-equation/Main.lean`, importing only `NavierStokes.SolutionDifference`. Inline axiom audits cover every exported declaration. No research imports or auxiliary Lean files.

## Equations and sign audit

Let `Space = EuclideanSpace ℝ (Fin 3)`, `SpaceTime = ℝ × Space`, `u,v,f,g : SpaceTime → Space`, `p,q : SpaceTime → ℝ`, and `ν,t : ℝ`, `x : Space`. All fields take `(t,x)`, not Comparator's `(x,t)` order. Define the actual-operator residual

\[
R_\nu(u,p)=\partial_tu+Du(u)-\nu\Delta u+\nabla p.
\]

`residual_one` checks equality with `ProblemStatement.navierStokesResidual` at viscosity one. This is an operator definition, not a new solution predicate.

For **plan convention** `w=u-v`, `r=p-q`, if `Rν(u,p)=f` and `Rν(v,q)=g`,

\[
Du(u)-Dv(v)=Du(w)+Dw(v),
\qquad
\partial_tw=\nu\Delta w-Du(w)-Dw(v)-\nabla r+f-g.
\]

The first identity is imported `SolutionDifference.advection_difference`; the second is new `difference_forces`. Thus forced-reference minus unforced-comparator has **plus** `f`. `forced_unforced` states precisely this specialization for the baseline viscosity-one residual.

For the **user-task convention** `z=v-u`, `ρ=q-p`, `unforced_forced` instead checks

\[
\partial_tz=\nu\Delta z-Dv(z)-Dz(u)-\nabla\rho-f.
\]

**Unformalized deduction (equivalent expansion):** because `v=u+z`, this is also

\[
\partial_tz=\nu\Delta z-Du(z)-Dz(u)-Dz(z)-\nabla\rho-f.
\]

Equivalently the two nonlinear terms can be written `-Du(z)-Dz(v)`. Do not swap only the force sign while retaining the old definition of pressure difference. Each checked equation uses its own explicitly displayed decomposition; no nonlinear term is discarded.

## Exact hypotheses and exported declarations

Names below have prefix `UnforcedRestart.DifferenceEquation.`.

| Declaration | Hypotheses / conclusion |
|---|---|
| `residual` | Definition for every real `ν`, built from actual temporal derivative, advection, Laplacian and pressure gradient. |
| `residual_one` | All `u,p,t,x`; equality to the baseline residual. |
| `difference_forces` | At a fixed `t,x`, both velocity spatial slices and both pressure spatial slices are `ContDiff ℝ ∞` on all of `Space`; both time curves at `x` are `DifferentiableAt ℝ` at `t`; the two pointwise residual equalities hold, with the **same** `ν`. Concludes the displayed `u-v` equation with `f-g`. |
| `forced_unforced` | Same regularity; baseline residual of `u,p` equals `f(t,x)`, baseline residual of `v,q` equals zero. Concludes the `+f` equation. |
| `unforced_forced` | Same regularity; `residual ν u p = f`, `residual ν v q = 0` at the point. Concludes the displayed `v-u`, `q-p`, `-f` equation for the same arbitrary real `ν`. |
| `forced_unforced_on_slab` | All four fields `ContDiffOn ℝ ∞` on `slab a b = Icc a b ×ˢ univ`; both viscosity-one PDEs at every `t ∈ Ioo a b` and every `x`. Concludes the difference PDE there. No assertion at `a` or `b`. If the interior is empty the assertion is correctly vacuous. |
| `divergence_free_difference` | Spatial velocity slices smooth at `t`, each divergence zero for every `x`; concludes divergence of `u-v` zero for every `x`. Force equality unnecessary. Exchange arguments to obtain the reversed convention. |
| `restart_difference_zero` | For arbitrary `t₀ : ℝ` and `a : Space → Space`, both fields equal `a` at every `(t₀,x)`; concludes `(u-v)(t₀,x)=0`. No zero-datum hypothesis on `a`. Exchange arguments for `v-u`. |

No divergence, support, periodicity, energy, or force smoothness hypothesis is required for the **pointwise subtraction** theorem. This does not mean those hypotheses can be dropped from integration or existence. Spatial smoothness is stronger than the minimal differentiability needed but is exactly reusable from existing slab lemmas. Full time differentiability is explicit so that arbitrary default values of `fderiv` outside differentiability do not justify invalid subtraction.

## Restart domains and boundary convention

For `0<t₀<1` and `0<S<1-t₀`, apply the slab theorem in original time with `a=t₀`, `b=t₀+S`. The difference PDE holds on `(t₀,t₀+S)`, the shared datum gives zero error at `t₀`, and spatial divergence subtraction also applies at endpoints when the slices are smooth. No presingular statement includes `t=1`.

Writing `s=t-t₀` is a mathematical change of coordinates, not an implemented derivative-translation theorem here. After a separately verified translation bridge, the corresponding interior is `0<s<S`. The source temporal derivative is an ordinary full Fréchet derivative evaluated at `1`. Comparator's `derivWithin` at zero requires a separate boundary identification; this file does not claim one. The source `ProblemStatement.Solution` hardcodes zero initial velocity at old time zero, and is deliberately not used as an arbitrary-datum restart structure.

## Independently inspected source map

- `NavierStokes/ProblemStatement.lean:32–87`: actual field types and differential operators; residual has viscosity **one**. `Solution` at lines 189ff includes `zero_initial_velocity` independently of its time set.
- `NavierStokes/SolutionDifference.lean`: complete file inspected. Imported `temporalDerivative_sub`, `spatialLaplacian_sub`, `pressureGradient_sub`, `spatialDivergence_sub`, `advection_difference` justify differential algebra; existing `difference_equation` assumes equal residuals and therefore cannot be applied to forced/unforced fields. `spatial_smooth` and `time_differentiable_at_interior` discharge slab regularity only with their actual time-domain hypotheses. `nonlinear_energy_bound` is pointwise, not integration by parts.
- `NavierStokes/R3CompactCandidate.lean`: `Properties` extends `Solution (Ico 0 1) f u p`; `of_limits` supplies its PDE using `CandidateFromLimits.force_eq_activated_residual` with the equality reversed. This is the precise forced-reference interface, not an unforced solution.
- `NavierStokes/ActualCandidateAssembly.lean:1016–1051,1070–1073`: `selected_witness : Witness ...`; expanding `Witness` gives common sums `ASum,BSum,PSum`, a periodic `CandidateProperties` witness and a compact force with `R3CompactCandidate.Properties` for `TimeLocalization.activatedVelocity (MixedPeriodicAssembly.cutVelocity ASum BSum)` and `TimeLocalization.activatedPressure (SpatialLocalization.cutPressure PSum)`. The periodic pair uses `periodicVelocity` and `periodicPressure` instead. These are the actual candidate paths. The new Lean file does not import/instantiate the enormous assembly, nor claim existence of its unforced comparator.

Prior `final-report.md` and `skeptical-review.md` in the specified Astra artifact directory were independently read. Their warning that forced exclusion is not unforced exclusion agrees with this audit. Their residual perturbation expansion is consistent with the signs above. Their pressure/integration arguments were not independently reproved here.

## Unproved bridges and success/failure criteria

1. Supply an actual admissible unforced comparator at the nonzero snapshot, with the same positive viscosity and a lifespan covering the desired slabs. This is **not** a premise equivalent to blowup, but is unproved here, especially if coverage up to the singular time is sought.
2. Verify snapshot admissibility, conversion from Comparator field order/derivatives, and shifted-time boundary regularity. No snapshot vanishing claim.
3. Obtain an inhomogeneous relative-energy identity using actual integrals. On the torus the pressure must be periodic and the divergence/periodic boundary terms justified. On R³ no compact support of the competitor or decay of its pressure may be inferred from reference support; flux, integrability and integration by parts remain required.
4. Obtain quantitative strong-norm estimates and check actual force budgets against them. Pointwise differential subtraction and zero initial error imply neither zero later error nor pointwise blowup transfer. `f-g` remains present.
5. No force-free terminal interval, terminal gradient-force representation, or local existence theorem is constructed.

Success for this task is strict compilation of the real-operator unequal-force identity with both sign conventions, nonzero shared datum and endpoint restrictions visible. This bounded success is achieved. Success for a forced-to-unforced blowup reduction would additionally require the above analytic/existence inputs; that remains blocked. No conjecture is asserted as a theorem.

## Validation and provenance

Final focused command from the prepared worktree root (also reruns all inline axiom checks):

```sh
env LEAN_NUM_THREADS=1 lake env lean -j1 \
  -DautoImplicit=false -DwarningAsError=true \
  -o Research/UnforcedRestart/difference-equation/out/Main.olean \
  -i Research/UnforcedRestart/difference-equation/out/Main.ilean \
  Research/UnforcedRestart/difference-equation/Main.lean \
  > Research/UnforcedRestart/difference-equation/out/Main.log 2>&1
```

**Exit 0**; recorded in `out/Main.exit`. Every one of the eight listed declarations prints exactly the allowed axiom set `{propext, Classical.choice, Quot.sound}` in `out/Main.log`. `git diff --exit-code` also returned **0** after final elaboration. No baseline source/config changes, builds, package operations, or commits performed.

An initial draft failed strict checking: an unnecessary `<;>` linter complaint and a missing `zero_add` normalization in the reversed-force specialization. The former was fixed by sequencing tactics; the latter by adding the actual simplification lemma. That failed invocation was not accepted (its failed theorem's axiom output included elaborator-generated `sorryAx`). The final source contains no incomplete proof and the successful final log contains no such axiom. No failed Lean file is retained as an accepted result.

Evidence is fresh research elaboration against prepared baseline imports, not a clean-from-source dependency rebuild, independent Comparator challenge execution, or Clay-prose equivalence audit.
