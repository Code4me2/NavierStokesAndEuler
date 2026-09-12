# Scaling and compactness — bounded result (agent 12)

## Verdict and classifications

**Unconditional formal results, with explicit ordinary hypotheses:** five small theorems and two definitions in `Research/UnforcedRestart/scaling-and-compactness/Main.lean`. They establish the force zoom bound/pointwise limit, scalar homogeneity, and the exact parabolically zoomed axis norm of the actual repository base. They do **not** establish a parabolic residual chain rule, an assembled-candidate limit, compactness, or unforced existence/nonexistence.

**Source audit / unformalized deductions:** the fixed-viscosity scaling equations, norm scaling, eventual transfer to the assembled candidate, and compactness obstruction below. No conjecture is asserted as a theorem. In particular A/B remains open in this investigation.

Read independently: `Research/UnforcedRestart/PLAN.md`; prior Astra `final-report.md` and `skeptical-review.md` under `/home/velvet/.pi/agent/thread-phase/artifacts/astra-textbook-proof-investigation-codex-2026-09-09T20-00-53-927Z-e2c30812/`; actual source declarations listed below. This is not an independent audit of the complete construction.

## Fixed-viscosity zoom (unformalized differential calculation)

Let `Space = EuclideanSpace ℝ (Fin 3)`, `SpaceTime = ℝ × Space`, and let real `ν>0`, `r>0`. For a classical solution of

\[
 R_ν(u,p)=∂_t u+Du(u)-νΔu+∇p=f,\qquad \operatorname{div}u=0,
\]

on an open domain, set, wherever `(1+r²s,ry)` lies in that domain,

\[
 U_r(s,y)=r u(1+r²s,ry),\quad P_r(s,y)=r²p(1+r²s,ry),\quad F_r(s,y)=r³f(1+r²s,ry).
\]

Each residual term has factor `r³`; divergence has factor `r²`. Consequently `R_ν(U_r,P_r)=F_r` at the **same** viscosity. This calculation requires one time derivative, two space derivatives of velocity, and one space derivative of pressure at the sampled points. Only its elementary viscosity coefficient identity is newly formalized, not the differential theorem.

The original presingular interval `0<t<1` becomes `-r⁻²<s<0`. A fixed compact negative-time slab is eventually covered as `r→0+`. No regularity at `s=0` is presumed. The total Lean field value at original time one is not a smooth terminal velocity.

Fixed spatial support `K` becomes `r⁻¹K`, so compactness of support is not uniform. Unit-periodic velocity **and pressure** acquire coordinate periods `1/r`, not generally period one. Thus this zoom of the torus is a growing-domain problem, not automatically another unit-torus comparator.

### Norm homogeneities (unformalized change of variables)

For finite `1≤p,q<∞`, spatial set `Ω` and time interval `I` in zoom coordinates, using Lebesgue measure and assuming the displayed norms are defined, put `I_r=1+r²I`, `Ω_r=rΩ`. Then

\[
 \|U_r\|_{L^q(I;L^p(Ω))}=r^{1-2/q-3/p}\|u\|_{L^q(I_r;L^p(Ω_r))},
\]
\[
 \|F_r\|_{L^q(I;L^p(Ω))}=r^{3-2/q-3/p}\|f\|_{L^q(I_r;L^p(Ω_r))}.
\]

The usual essential-supremum versions use `1/∞=0`. Velocity-critical exponents satisfy `2/q+3/p=1`; force-critical exponents satisfy `2/q+3/p=3`. The instantaneous whole-space squared energy and integrated squared gradient both scale with factor `r⁻¹` on corresponding domains. A bounded original energy/dissipation therefore does not itself give a uniform bound of those rescaled quantities.

For force, `L¹_t L²_x` has factor `r⁻¹/²`, and `L¹_t L∞_x` has factor `r`. The original shrinking time interval must be included: if the compact reference force has uniformly bounded whole-space `L²` norm near one, the former is at most `M |I| r^{3/2}`. This is not a velocity-stability threshold or a relative error estimate. No numerical constant is extracted here.

## Viscosity normalization is different (source-supported)

`NavierStokes/ComparatorBridge.lean:66–71` defines

\[
 \mathrm{rescale}(a,c,f)(t,x)=a f(ct,x),\quad
 f_ν(t,x)=ν²f(νt,x).
\]

The associated forward fields are `u_ν=νu(νt,x)` and `p_ν=ν²p(νt,x)`: viscosity changes from one to `ν`, singular time changes to `1/ν`, and spatial periods do not change. The checked existing `rescale_residual` at lines 219–230 is the **inverse** direction: for `ν>0`, `t>0` and velocity smooth on the future domain, its viscosity-one residual equals `ν⁻²` times the original viscosity-`ν` operator at `t/ν`. It does not assert spatial zoom covariance. `normalized_solution_core` additionally takes an actual Comparator solution with zero datum.

Letting `ν→0` can reduce the force amplitude but changes diffusion and horizon. It is not fixed-positive-viscosity force removal or a fixed-ν smallness theorem.

## Actual axis and failed classical compactness

Source path, with quantifiers retained:

1. `NavierStokes/BaseResidual.lean:59–98`: `baseVelocity_at_origin` and `baseVelocity_norm_at_origin` assume `StrictMono a`, `0<h<1/2`, smooth coefficients `d`, zero positive-order axial coefficients at `(0,0)`, and (for the norm) positive leading coefficient. For every `t<1`,
   `‖baseVelocity a h C d (t,0)‖ = (1-t)^(-(1/2+h)) d.axial 0 (0,0)`.
2. `NavierStokes/FinalSlowBase.lean:303–315`: `leading_origin` identifies this coefficient with `W.axis.j>0`; `axis_tendsto` instantiates the base with the constructed smooth coefficients and strictly increasing scales. The fixed profile has `0<h<1/2`.
3. `NavierStokes/GermCandidateAssembly.lean:124–174`: `origin_eventually_base` is eventual equality in `𝓝[<] 1` for the **unlocalized** mixed velocity. Inputs include the certificate/profile witnesses, positive `qbig`, axis-zero initial and positive stages on the specified local domain, actual angular data, and schedule tending to infinity. `origin_blowup` combines this equality with `axis_tendsto`.
4. `NavierStokes/MixedPeriodicAssembly.lean:131–137`: `periodicVelocity_origin` and `cutVelocity_origin` preserve that exact origin value; `NavierStokes/TimeLocalization.lean:68–70` removes activation for `t≥3/4`.
5. `NavierStokes/ActualCandidateAssembly.lean:1070–1074`: `selected_witness` supplies the closed selected construction; its assembly at lines 1060–1066 retains compact and periodic candidates from the same schedule. This selection is source-inspected, not imported as a new theorem in this task.

**New checked actual-base identity:** `base_zoom_axis` gives for every `r>0`

\[
 \|r u_b(1-r²,0)\|=r^{-2h}d.axial_0(0,0).
\]

**Unformalized assembled transfer:** composing steps 1–5 yields, for the fixed assembled candidate and all sufficiently small `r>0`, `‖U_r(-1,0)‖=j_*r^{-2h}→∞`. The eventual cutoff threshold depends on the fixed construction; no uniform statement as `h↓0` is available.

For every sequence `r_n→0+`, this diverges. Hence that sequence has no subsequence converging locally uniformly to a finite continuous velocity on a neighborhood of `(-1,0)`, nor is it locally uniformly bounded there. This rules out this direct classical compactness strategy, **not** every weak/distributional limit or every alternative choice of centers/scales. Point evaluation is not continuous in weak `L²`, so this argument neither precludes weak convergence nor proves that a weak limit is nonzero.

Merely dividing the zoom by its divergent amplitude also changes its equation. If `V_r=r^{2h}U_r`, `Q_r=r^{2h}P_r`, then

\[
 ∂_s V_r+r^{-2h}DV_r(V_r)-νΔV_r+∇Q_r=r^{2h}F_r.
\]

This is not standard fixed-viscosity NS with unit convection coefficient. Retiming to restore that coefficient changes the diffusion coefficient. Neither procedure supplies the requested unforced fixed-ν solution.

## Vanishing force is easy; a limit theorem is not

`CandidateFromLimits.force_smooth` (lines 83–88) gives genuine spacetime smoothness of the constructed force. `force_eq_activated_residual` (101–105) identifies it on `0≤t<1`. Therefore its continuity at `(1,0)` supplies the hypothesis of new `zoomForce_tendsto`: for every fixed real spacetime point `(s,y)`, `r³ f(1+r²s,ry)→0`. This uses no terminal flatness whatsoever, so cannot by itself distinguish this construction from arbitrary smooth forcing.

Unformalized strengthening: bounded force on an actual spacetime neighborhood yields `sup_K |F_r|≤Mr³` on each fixed compact zoom set `K` for small `r`. Smoothness similarly gives mixed derivative factors `r^{3+2a+|β|}` times bounded original derivatives. Point jets alone should not be substituted for these neighborhood bounds. Constants may depend on the derivative order and neighborhood. These force facts coexist with the explicit divergent axis velocity.

A successful unforced limit route must still provide:

* a fixed negative-time domain and a topology with uniform velocity and pressure bounds;
* compactness strong enough to pass `U_r⊗U_r` to the asserted product, or control and eliminate any defect stress;
* justified derivative/distributional passage and pressure gauge control;
* a nontriviality mechanism surviving the chosen topology (a diverging point value is insufficient in a weak topology);
* regularity/admissible restart data and the appropriate R³ energy or torus class;
* a singularity/nonextension conclusion for the limit, not just existence of an ancient unforced weak solution.

None is supplied by force convergence. Success would require new estimates and a genuine compactness theorem; the classical locally bounded topology is already obstructed in this normalization. No such theorem or an applicable NS local-existence result is invented here.

## Accepted Lean declarations and validation

Only accepted Lean file: `Research/UnforcedRestart/scaling-and-compactness/Main.lean`. Direct imports: `NavierStokes.ComparatorBridge`, `NavierStokes.BaseResidual`. Namespace for **all** declarations: `UnforcedRestart.ScalingAndCompactness`.

| Declaration | Classification and precise scope |
|---|---|
| `zoomVelocity` | Definition on actual `VelocityField`, arbitrary real `r,T` |
| `zoomForce` | Definition on actual `VelocityField`, arbitrary real `r,T` |
| `viscosity_coefficient` | C, scalar identity for all real `r,ν`; no PDE chain rule |
| `zoomForce_norm_le` | C, norm estimate for actual fields, `r≥0` and bound `‖f(T+r²s,ry)‖≤M`; no hidden sign assumption on `M` |
| `zoomForce_tendsto` | C, actual-field pointwise limit for each fixed `z`, assuming only `ContinuousAt f (T,0)`; two-sided `r→0` |
| `axis_power` | C, scalar real-power identity for `r>0`, any real `h` |
| `base_zoom_axis` | Actual constructed-base evaluation identity (not a PDE estimate); precisely the hypotheses in source-map item 1, `C:ℝ`, and `r>0` |

Final successful command (exit **0**), including inline axiom audit of every definition/theorem:

```sh
env LEAN_NUM_THREADS=1 lake env lean -j1 \
  -DautoImplicit=false -DwarningAsError=true \
  -o Research/UnforcedRestart/scaling-and-compactness/out/Main.olean \
  -i Research/UnforcedRestart/scaling-and-compactness/out/Main.ilean \
  Research/UnforcedRestart/scaling-and-compactness/Main.lean \
  > Research/UnforcedRestart/scaling-and-compactness/out/Main.log 2>&1
```

Final serial rerun again exited **0**. `git diff --exit-code` exited **0** (tracked baseline unchanged); both statuses are recorded in `out/Scope.log`. Writes were confined to this task's research directory and this report. No builds, dependency changes, commits or pushes were performed.

`out/Main.exit` contains `0`. `out/Main.log` contains seven complete axiom outputs: **each exactly `[propext, Classical.choice, Quot.sound]`**. No separate research import path or AxiomAudit file is needed: commands are inline. This is fresh focused elaboration against prepared cached baseline imports, not a clean baseline kernel rebuild, independent Comparator run, or Clay-prose equivalence audit.

Failed attempts, excluded from acceptance: an initial real-power rewrite rewrote every occurrence of `r` instead of only the leading factor and needed a natural-to-real cast normalization. A later continuity composition required its inner map specified explicitly; using `Filter.Tendsto.smul` avoided function-action elaboration ambiguity. These attempts exited 1; corrected proofs above exited 0. No incomplete Lean files remain on the accepted list, and failed logs' provisional `sorryAx` diagnostics are not accepted closures.

Unproved bridges are exactly the differential covariance, change-of-variable norm statements, assembled eventual identity wrapper and its divergence limit, compact-uniform force estimates, and all compactness/nontriviality/solution-class obligations above. None is hidden as an axiom or target-equivalent solution predicate.
