# Strong-norm growth transfer — bounded result, agent 10

## Verdict and classification

Four freshly checked conditional norm/compactness lemmas (class C), and a source/analytic obstruction audit (class D). **No viscous stability, unforced existence, or A/B exclusion is proved.** No new unconditional statement that any unforced field blows up is asserted. The implications themselves are unconditional formal theorems; their comparison premises are explicitly conditional and unverified for unforced solutions.

Read independently: `Research/UnforcedRestart/PLAN.md`, and both `final-report.md` and `skeptical-review.md` in the planner-specified prior Astra artifact directory. Their forced/unforced distinction and H⁴-reference warning survive direct source inspection.

## Actual mechanism and exact source route

Types are `NavierStokes.ProblemStatement.Space = EuclideanSpace ℝ (Fin 3)`, `VelocityField = (ℝ × Space) → Space`. Fields below are internal time-first fields. The baseline residual has viscosity one. The norm lemmas are independent of viscosity; applying them to PDE solutions requires both velocities at the same fixed positive viscosity.

Directly inspected declarations:

* `NavierStokes/BaseResidual.lean`: `baseVelocity_at_origin`, `baseVelocity_norm_at_origin`, `baseVelocity_axis_tendsto_atTop`. Given smooth coefficients, strictly increasing scales, positive leading axial coefficient, positive-stage axial zeros, and fixed `0<h<1/2`, the norm at the origin is `j_* (1-t)^(-(1/2+h))`, `j_*>0`, for `t<1`.
* `NavierStokes/GermCandidateAssembly.lean`: `origin_eventually_base` and `origin_blowup`. These concern the **unlocalized mixed field** and require the stated axis-zero germs, angular data and diverging diagonal scales. Agreement is eventual in `𝓝[<] 1`, not throughout the evolution.
* Final transfer route: `MixedPeriodicAssembly.cutVelocity_origin`, `periodicVelocity_origin`, then `TimeLocalization.activatedVelocity_eq_late`. These are the localization/activation bridges identified in the source chain, not new checked wrappers here.
* `NavierStokes/ActualCandidateAssembly.lean:1070–1078`: `selected_witness` closes the concrete witness; `selected_candidate` extracts `CandidateProperties`, whose `speed_unbounded` field is the formal input usable below. The new file does not import this large assembly or freshly replay its construction.
* `ProblemStatement.SpeedUnboundedAtOne` quantifies arbitrary positive threshold and terminal radius, allowing spatial witnesses anywhere. Its `false_of_agree` uses compact reduction; speed unboundedness alone is not enough to contradict whole-space smoothness if witnesses escape spatially.
* `PeriodicUniqueness.periodic_bound_on_slab` bounds a continuous unit-periodic field on an entire closed slab using the compact cube. No pressure or PDE hypotheses are involved in this compactness lemma.

The actual axis is stronger than arbitrary moving spatial witnesses. It requires no transported invariant to transfer velocity growth: evaluation at `x=0` is enough. Preservation of the axis-zero correction germs by a different, unforced PDE is not supplied by construction identities.

## Precise comparison target

Fix `0<t₀<1`, `H=1-t₀`, and restart fields `uᵣ(s,x)=u(t₀+s,x)`, `vᵣ(s,x)`, with equal initial datum and the same viscosity. Write `w=uᵣ-vᵣ`. A sufficient estimate for all sufficiently late `0≤s<H` is

`‖w(s,0)‖ ≤ ρ ‖uᵣ(s,0)‖ + B`, with fixed `0≤ρ<1`, `0≤B<∞`.

The triangle inequality gives

`‖vᵣ(s,0)‖ ≥ (1-ρ) j_* (H-s)^(-(1/2+h)) - B`.

This is an **unformalized deduction** from the exact eventual axis formula and the checked evaluation lemma. It excludes continuity through `(H,0)` once the estimate is established. Bounded absolute error is sufficient (`ρ=0`); error `o((H-s)^(-(1/2+h)))` is sufficient; bounded error divided by reference growth with limsup strictly below one is sufficient. The coefficient must be strictly below one: `v=0` has error exactly `‖u‖` and does not inherit growth.

A useful analytic contract is

`‖w(s,0)‖ ≤ C_eval N(w(s)) ≤ ρ j_* (H-s)^(-(1/2+h)) + B`.

Here `N` must be a genuine norm with a proved evaluation inequality, not a symbolic name for desired growth. `evaluation_budget` keeps both premises visible using the scalar value `N`; it does not declare this scalar to be a Sobolev norm. The other transfer lemmas assume the resulting pointwise inequality explicitly.

## Which strong norm, which constants?

**Unformalized standard Sobolev deductions:** in dimension three, inhomogeneous `H^s` embeds into bounded continuous velocity for `s>3/2`; integer `H²` suffices for axis velocity. To control gradient point evaluation, `s>5/2`; integer `H³` suffices. The critical equalities `s=3/2` and `s=5/2` do not supply these embeddings. Specify full inhomogeneous norms, representative regularity, and actual L² derivatives; a homogeneous seminorm without low-frequency assumptions is not silently interchangeable.

On R³ define, for example, `‖w‖_{H^k}² = Σ_{|α|≤k} ∫ |∂^α w|² dx`. On the unit torus use one period cube (or equivalent Fourier-series norm), not whole-space integrals of periodic functions. Constants depend on this normalization, vector/tensor norms, derivative convention and domain. Once chosen, `C_eval` is fixed independently of time, but the PDE comparison constant need not be. No numerical Sobolev constant is estimated here.

Direct inspection of `Euler/EulerProof/Mollification.lean:280–282,428–435` finds a genuine R³ result `real_smooth_fderiv_le_H3` for smooth real vector fields with `MemLp (iteratedFDeriv ℝ j f) 2 volume` for every `j≤3`. Its coefficient is `9*smoothEmbeddingConstant`, with the latter defined using Fourier embedding and bump coefficients. This is a concrete potential gradient-evaluation bridge, not yet an identification of an NS error norm or a periodic embedding theorem.

Direct inspection of `Euler/OrdinaryEulerStability.lean` and `OrdinaryEulerVaryingHorizon.lean` shows:

* `referenceWordBound` controls order **4**, via `referenceSize`;
* `h3_stability` (in `OrdinaryH3Envelope.lean:115–120`) requires two Euler evolutions, order-four reference bounds, initial error ≤ε and `640 ε exp(3 stabilityConstant(M) T) ≤ 1/2`;
* `no_gradient_escape_varying` requires actual Euler stage solutions, horizons ≤ a fixed reference horizon, and errors tending to zero. It invokes the H³ gradient embedding and compact-trajectory contradiction.

These are not NS stability/existence theorems. The abstract `evaluation_budget` also applies to the normed space of continuous linear maps, so gradient values may replace velocities once a genuine derivative-difference bound is proved. No Euler invariant or support-transport claim is transferred to viscous evolution.

### Why L² comparison fails

**Unformalized counterexample:** choose a smooth compactly supported divergence-free `ψ` on R³ with `ψ(0)≠0` (take `A(x)=½ χ(x)(a×x)`, where `a≠0` and the smooth compactly supported scalar cutoff `χ` equals one near zero, and set `ψ=curl A`; then `ψ(0)=a`, since `curl(a×x)=2a`). A vector potential constant near zero would instead have zero curl there. Set `w_ε(x)=ε⁻¹ ψ(x/ε)`. Then `‖w_ε‖₂=ε^{1/2}‖ψ‖₂→0`, while `|w_ε(0)|=ε⁻¹|ψ(0)|→∞`. For sufficiently small ε the support fits strictly inside a period cell centered at zero; periodizing gives the same cell L² scaling and origin value on the unit torus. Thus even smooth divergence-free L²-small errors can cancel a large pointwise core. Energy/dissipation bounds alone do not control evaluation. These are functional counterexamples, not asserted pairs of NS solutions.

## Noncircularity and missing bridges

The norm implications do not hide a solution predicate, equation, existence theorem, or blowup in a custom definition. Reference growth is an explicit premise already supplied by the forced construction. **The relative-error premise, combined with this reference growth, already forces comparator blowup.** Calling this premise “stability” without independently deriving it would simply assume the decisive part of the desired unforced exclusion. In particular, for a comparator known continuous through the endpoint, our last theorem proves this premise is impossible; it does not construct such an estimate.

Needed new work:

1. Applicable local unforced NS existence and uniqueness for the nonzero snapshot; coverage of every `S<H`, or a separate justified continuation/exclusion argument. No existence beyond a local time is assumed as progress.
2. Actual inhomogeneous strong-norm estimate for `w`, with same viscosity, pressure/projection control, boundary conventions, integrability and derivative counts. An L² Gronwall bound cannot fill this slot.
3. Quantitative constants depending on the actual singular reference and an actual norm of the removed forcing. Constants can diverge as `S↑H`; slab-by-slab finiteness is insufficient.
4. Prove the resulting bound satisfies the displayed growth-relative threshold uniformly for one fixed restart. Choosing a new `t₀` separately for each `S` changes the datum and does not yield one counterexample.
5. Assemble the eventual axis identity for the selected compact or periodic candidate in a focused wrapper if using the sharper axis-only theorem; `CandidateProperties.speed_unbounded` alone feeds the all-space transfer theorem instead.

Success criterion: one independently derived error budget in a proved evaluation-controlling norm, for the same restarted datum on arbitrarily late slabs, with constants beating reference growth. Present result: this criterion is **not discharged**. No new conjecture of unforced singularity is claimed.

## Accepted Lean and reproducibility

Only accepted file: `Research/UnforcedRestart/strong-norm-growth-transfer/Main.lean`. Only import: `NavierStokes.PeriodicUniqueness` (transitively the actual problem statement). Namespace `UnforcedRestart.StrongNormGrowthTransfer`; every exported declaration:

1. `evaluation_budget`: arbitrary normed additive group, two explicit evaluation/budget inequalities; conclusion `(1-ρ)‖a‖-B≤‖b‖`. No sign assumptions needed for this algebraic implication.
2. `speed_transfer`: actual fields, `t₀<1`, `ρ<1`, `B≥0`, reference `SpeedUnboundedAtOne`, relative error at every spatial point for `0<t<1` and `t>t₀`; transfers that predicate. Positive `t₀` and nonnegative `ρ` are natural applications but unnecessary for the theorem. Its proof shrinks the terminal radius to `min δ (1-t₀)`.
3. `no_periodic_continuous_comparator`: previous hypotheses plus continuity and unit periods of **velocity** on `[0,1]×R³`; contradiction. Pressure periodicity remains required for any upstream PDE comparison, but is irrelevant to this purely velocity compactness step.
4. `no_continuous_axis_comparator`: arbitrary `t₀`, `ρ<1`, `B≥0`; reference norm arbitrarily large at origin on `(t₀,1)`, axis-relative error there, and competitor continuous on `[t₀,1]×{0}`; contradiction. No periodicity, compact support or competitor global spatial bound required.

Exact successful final command (exit **0**):

```sh
env LEAN_NUM_THREADS=1 lake env lean -j1 \
  -DautoImplicit=false -DwarningAsError=true \
  -o Research/UnforcedRestart/strong-norm-growth-transfer/out/Main.olean \
  -i Research/UnforcedRestart/strong-norm-growth-transfer/out/Main.ilean \
  Research/UnforcedRestart/strong-norm-growth-transfer/Main.lean \
  > Research/UnforcedRestart/strong-norm-growth-transfer/out/Main.log 2>&1
```

Inline `#print axioms` audits all four exports; entire output is in `out/Main.log`, status in `out/exit-code.txt`. Each closure is exactly `[propext, Classical.choice, Quot.sound]`. Both focused elaborations succeeded; no failed Lean attempts remain. No custom definitions, axioms, bypasses, resource overrides, challenge imports, or shared research imports. `git diff --exit-code` returned 0 for tracked sources. No broad build, dependency repair, commit or push. This is fresh research elaboration against cached baseline dependencies, not a clean kernel rebuild of the repository or independent Comparator verification.
