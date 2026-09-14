# Time translation: checked presingular PDE bridge

Owner: agent 4, `UnforcedRestart.TimeTranslation`. Only owned research/docs paths changed.

## Result and classification

**Unconditional formal results (class A, actual-field calculus):** time translation commutes with all spatial operators, preserves presingular/slab smoothness, and commutes with the full temporal derivative when the old time slice is differentiable. For an actual `CandidateProperties` witness, that differentiability follows from its stated smoothness, including at **new time zero**. Both the full-derivative and `derivWithin (Ici 0)` shifted equations are proved.

**Explicitly conditional formal lemma (class A):** `candidate_shift_unforced` requires literal force vanishing on the entire old interval `[t₀,1)`. This is not supplied by the construction. It is a conditional PDE reduction, not evidence that force removal is possible or that an unforced solution exists globally.

No analytic estimate (class B), local-existence theorem, growth-transfer theorem, or A/B counterexample is claimed.

## Types, intervals, equations

`Space = EuclideanSpace ℝ (Fin 3)`, `SpaceTime = ℝ × Space`. Fields are total functions on spacetime; regularity is asserted only on specified sets. For every real `t₀` with `0 < t₀ < 1`, set `H = 1-t₀ > 0`. For velocity `u : SpaceTime → Space`, pressure `p : SpaceTime → ℝ`, and force `f : SpaceTime → Space`, define

\[
 u_r(s,x)=u(t₀+s,x),\quad p_r(s,x)=p(t₀+s,x),\quad f_r(s,x)=f(t₀+s,x),\qquad a(x)=u(t₀,x).
\]

For every `s ∈ [0,H)` and every `x : Space`, `t₀+s ∈ (0,1)`. Thus the old equation is available even when `s=0`. The checked identity at viscosity **one** is

\[
 R_1(u_r,p_r)(s,x)=R_1(u,p)(t₀+s,x)=f_r(s,x),\qquad u_r(0,x)=a(x).
\]

The datum need not vanish. For every `0<S<H`, both shifted velocity and pressure are `ContDiffOn ℝ ∞` on `[0,S]×Space`; indeed the checked smoothness result covers `[0,H)×Space`. `shift_smooth_slab` does not require `S>0`, since its statement remains valid for an empty/degenerate slab. No equation or smoothness conclusion is made at `s=H`.

**Unformalized deduction:** since no amplitude, space, or viscosity change occurs, the identical calculation preserves any fixed `ν>0` in `∂ₛu_r+Du_r(u_r)-νΔu_r+∇p_r=f_r`. This file deliberately exports only the repository's viscosity-one residual theorem, not a silently viscosity-parametrized version.

## The boundary issue is discharged here, not ignored

The baseline `ComparatorBridge.temporalDerivative_eq` assumes strictly positive time. It cannot by itself identify the derivatives at new time zero. Our proof instead supplies

\[
 \operatorname{HasDerivAt}(s\mapsto u(t₀+s,x),\ \partial_tu(t₀+s,x),\ s).
\]

It uses differentiability of the old time slice and the affine chain rule. Unique differentiability of `Ici 0` at every nonnegative `s` then gives

\[
 \operatorname{derivWithin}_{[0,\infty)}u_r(s,x)=\partial_tu(t₀+s,x),\quad 0\le s<H.
\]

For candidate fields, old differentiability comes from `ProblemStatement.smooth_at_interior`, because `t₀+s∈(0,1)`. Accordingly `candidate_shift_within_equation` proves the actual within-time PDE at zero, with the repository's advection, Laplacian, and pressure gradient. This is not yet a packaged Comparator solution: its horizon remains finite, and Comparator spatial-operator/coordinate bridges and solution-class requirements remain separate.

For a generic field known only `ContDiffOn` on an old closed slab `[t₀,t₀+S]`, full old-time differentiability at its left endpoint does **not** follow without more information about its extension. Our generic derivative theorems expose that premise. The constructed reference has the needed larger old smooth domain. This does not automatically prove a corresponding full derivative statement for an arbitrary restarted competitor. At `t₀=0`, the above interior-old-time argument is unavailable. At `t₀=1`, it is also unavailable and the horizon is zero.

## Independently inspected source map

- `NavierStokes/ProblemStatement.lean`: actual `temporalDerivative`, `spatialDerivative`, `advection`, `spatialDivergence`, `pressureGradient`, `spatialLaplacian`, `navierStokesResidual`; `CandidateProperties`; `smooth_at_interior`; `Solution.mono`.
- `NavierStokes/SolutionDifference.lean`: `spatial_smooth`, `smooth_at_interior`, `time_differentiable_at_interior` explain the closed-slab/interior distinction. This task uses the original presingular-domain interior lemma to include the new boundary.
- `NavierStokes/ComparatorBridge.lean`: `temporalDerivative_eq` excludes zero; `rescale_temporalDerivative` is scaling, not translation; `toComparator/fromComparator` handle `(t,x)` versus `x,t`; `gradient_eq`, `laplacian_eq` identify spatial operators.
- `NavierStokes/ComparatorDefinitions.lean`: `NavierStokesExistenceAndSmoothness.navier_stokes` quantifies over every `t≥0` using `derivWithin`, with arbitrary initial datum. The periodic extension requires periodic **pressure and velocity**. The whole-space extension requires `MemLp` and global energy control.
- `NavierStokes/ActualCandidateAssembly.lean:1070–1078`: `selected_witness` yields the actual assembled witness; `selected_candidate` extracts `∃ u p f, CandidateProperties u p f`. The exported candidate lemmas accept exactly that proposition. No construction module is imported or rebuilt here merely to instantiate the existential witness.
- `NavierStokes/R3CompactCandidate.lean`: `Properties` extends `Solution (Ico 0 1) f u p`; `of_limits` constructs it from the compact-first fields. Our generic `shift_smooth`, `old_time_differentiable`, and `shift_residual` apply to its inherited fields without periodicity assumptions. Its equation field plus the translated interval supplies the same shifted equation; a separate R³ wrapper is not exported.

The prior Astra `final-report.md` and `skeptical-review.md` were read independently. Their conditional restart suggestion is consistent with these lemmas, but force extension/shutdown at time two and pointwise terminal flatness do not discharge the terminal-zero-force premise.

## Accepted Lean declarations and exact assumptions

Single accepted file: `Research/UnforcedRestart/time-translation/Main.lean`.
Imports: `NavierStokes.SolutionDifference`, `NavierStokes.ComparatorBridge` (which supplies the original problem definitions transitively). No cross-task or challenge imports.

All names below have prefix `UnforcedRestart.TimeTranslation.`. Every declaration has its own inline `#print axioms`.

| Declaration(s) | Assumptions / conclusion |
|---|---|
| `shift` | Definition for any type `V`, real shift and `SpaceTime → V`. |
| `shift_initial` | Arbitrary field, real shift, spatial point; snapshot identity. |
| `horizon_pos` | `t₀<1`; `0<1-t₀`. |
| `shifted_time_interior` | `0<t₀`, `s∈Ico 0 (1-t₀)`; old time in `(0,1)`. |
| `shift_smooth` | Normed real target, presingular `ContDiffOn ℝ ∞`, `0≤t₀`; shifted half-open smoothness. |
| `shift_smooth_slab` | Same, plus `S<1-t₀`; shifted closed-slab smoothness. |
| `shift_spatialDerivative`, `shift_divergence`, `shift_advection`, `shift_laplacian`, `shift_gradient` | Arbitrary fields and real times; definitional spatial translation identities. No differentiability premise is needed for these identities of the actual total operators. |
| `shift_hasDerivAt`, `shift_temporalDerivative` | Old time-slice `DifferentiableAt` at `t₀+s`; chain rule and temporal-operator identity. |
| `shift_derivWithin` | Same plus `0≤s`; within-derivative identity including zero. |
| `shift_residual` | Old velocity time differentiability; exact actual residual identity, arbitrary pressure. |
| `old_time_differentiable` | Velocity presingular smoothness, `0<t₀`, `s∈Ico 0 (1-t₀)`; required old differentiability. |
| `candidate_shift_equation`, `candidate_shift_within_equation` | `CandidateProperties u p f`, `0<t₀`, `s∈Ico 0 (1-t₀)`; respective full/within forced PDE. |
| `candidate_shift_unforced` | Previous candidate assumptions and `∀ t∈Ico t₀ 1, ∀ x, f(t,x)=0`; shifted zero residual. |

`shifted_time_interior` and `horizon_pos` are elementary domain infrastructure (class C); other theorem groups are class A. Smoothness results concern actual fields, not norms or energy. Candidate hypotheses are established by the source construction; only the additional terminal-zero-force hypothesis is unknown.

## Validation and provenance

Successful focused command, exit **0**:

```sh
env LEAN_NUM_THREADS=1 lake env lean -j1 \
  -DautoImplicit=false -DwarningAsError=true \
  -o Research/UnforcedRestart/time-translation/out/Main.olean \
  -i Research/UnforcedRestart/time-translation/out/Main.ilean \
  Research/UnforcedRestart/time-translation/Main.lean \
  > Research/UnforcedRestart/time-translation/out/Main.log 2>&1
```

Exit recorded in `out/Main.exit`. Full inline axiom output is `out/Main.log`: all **19 declarations** have exactly `[propext, Classical.choice, Quot.sound]`; no unexpected axiom. Fresh elaboration uses the prepared cached baseline dependencies, not a new baseline kernel rebuild or independent Comparator verification. `git diff --exit-code` returned **0** after the successful check. No builds, installs, baseline modifications, commits, or pushes.

One earlier invocation exited 1: the chain-rule proof's limited simplifier did not unfold `deriv` and `temporalDerivative`, leaving a type mismatch. Explicitly unfolding those definitions resolved it. The failed elaboration's downstream axiom prints were not accepted evidence; no incomplete source remains on the accepted list.

## Remaining bridges and acceptance criteria

1. **Force removal:** establish `f=0` on `[t₀,1)` or an admissible pressure potential there. Neither terminal jets nor post-singular shutdown suffice. Failure to establish this means the shifted equation remains forced.
2. **Data/class:** snapshot rapid decay/finite energy on R³, or unit periodicity on the torus; pressure convention and any required comparator energy/flux properties. Translation is not a replacement for those task-specific checks.
3. **Nonzero-data comparison/local theory:** `ProblemStatement.Solution` hardcodes `u(0,x)=0`, even after `Solution.mono`. We do **not** construct `Solution` for the restarted fields. An applicable arbitrary-datum uniqueness/existence framework remains necessary; no local theory is invented here.
4. **Horizon:** none of these results covers `s=H` or all future time. Smooth force there does not imply smooth velocity. An unforced global competitor, if hypothetically supplied, still needs comparison on every presingular slab and the independent blowup contradiction.
5. **Stability alternative:** changing the force rather than proving terminal vanishing changes the equation. Quantitative comparison and strong-norm growth transfer are wholly separate obligations.

Success for this task is the checked finite-horizon differential translation, including the boundary convention. A force-free restart construction or any A/B conclusion would require the unresolved bridges above. No conjecture is promoted to a theorem.
