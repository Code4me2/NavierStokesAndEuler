# LocalizedForce — exterior jets certified; annular solenoidal residual unresolved

## Decision and classification

**Precisely unresolved annular terminal curl.** No conclusion here rules out exact pressure removal on any terminal slab, nor establishes it or controlled growth transfer. Numerical experiments on the actual selected candidate: **no-go without certified representations and derivative tails**. Symbolic reasoning uniform in the witness is viable.

New focused Lean acceptance: `Research/UnforcedRestart/Round3/LocalizedForce/Main.lean`, three universal source-connected support theorems for the literal `MixedPeriodicAssembly.cutResidual` and its terminal tensors. These are **checked conditional calculus/construction tools**, not a new closed theorem about `WitnessFeasibility.selected.forcing`. Their specialization below is an **unformalized actual-candidate deduction**. The product/curl calculations and bounds below are ordinary analysis, not Lean acceptance. No nonvanishing conjecture is promoted to evidence.

## Exact selected dependence

Use the single frozen `WitnessFeasibility.selected : Data`, source SHA-256 `7d77092a3da73faedebac0a052c6fd2ce6fc46d340f48f796dd5e45f926be8da`. Let `a=selected.schedule`, `A=potentialSum a`, `v=directSum a`, `p=pressureSum a`, and `f=selected.forcing`; use its `ea,eb,ep,jets`. There is no independent choice of schedule or force here. The wrapper has not been imported from a moving output.

B=0, N0=`ActualCandidateConstruction.selectedThreshold`=`ActualCarrierGeometry.startingThreshold 0`, its actual geometry proof, h=`CorrectionInitialization.ActualPrimary.h` with 0<h<1/2; viscosity=1, T=1, unit periods, restart=1/2. The sums use `(fun j => (a j : ℝ))`, `PhysicalWaveSum.physicalQ h`, and respectively `ActualCandidateAssembly.potentialStages/directStages/pressureStages B N0 geometry`. Preserve the upstream slow-base scale schedule as well as this diagonal schedule: they are not interchangeable.

Source map:

* `ActualCandidateAssembly.zerothPotential` includes `TailGaugePotential.finalPotential certificate modulation upper B`; `potentialStages_zero/succ` and the three stage definitions fix the entire mixed sequence. Positive-stage active-annulus germs do not identify the separate fixed spatial localization annulus.
* `TailGaugePotential.radialNormalize/gaugedSwirl/potential/finalPotential`, `finalPotential_sameCurl`, `central_oneSidedExtension`, `nonzeroAxialExtension`, `realized_awayExtensions`: actual anchored slow potential and its extension mechanism.
* `AxisymmetricFields.potential`: the axial component is +K e₂; `SpatialCurl` uses (∂₁u₂−∂₂u₁, ∂₂u₀−∂₀u₂, ∂₀u₁−∂₁u₀).
* `MixedPeriodicAssembly.cutVelocity`, `cutResidual`, `periodicVelocity_eventuallyEq_cut`, `representative`, `cutResidual_awayExtensions`, `boundaryLimits`; `SpatialLocalization.cutPressure`, support and plateau declarations; `TimeLocalization.activatedVelocity/Pressure` and their eventual late equalities.
* `JointResidualLimits.OneSidedExtension.jet_tendsto`, `boundaryLimits`, `past_filter_neBot` supply the terminal-limit argument. `selected.jets` identifies f, not an arbitrarily evaluated terminal velocity. The periodic and compact existential forces need not be identified.

No numerical values are extracted for h, nominal normalization, slow coefficients, modulation, cutoff choices, schedules, extension neighborhoods or derivative bounds. The source's heat primitive is a symbolic integral, not a certified numerical enclosure for the full selected sum.

## Complete localization and activation calculation (unformalized)

Assume smooth A,v,p on an open spacetime neighborhood before T, or use their smooth one-sided extensions away from the origin. Put χ=`spatialCutoff`, u=curl A+v, b=∇χ×A, U=χu+b, P=χp. χ is independent of time. Expanding each product gives

```
R₁(U,P) = χ R₁(u,p) + ∂t b − Δb − (Δχ)u
 − 2 Σ_i (∂iχ)∂i u + p∇χ
 + (χ²−χ)(u·∇)u + χ(u·∇χ)u + χ(u·∇)b
 + (b·∇χ)u + χ(b·∇)u + (b·∇)b.
```

This retains the direct angular field inside u. The pressure pieces cancel only together under curl:
`curl(χ∇p)=∇χ×∇p`, `curl(p∇χ)=∇p×∇χ`, hence `curl ∇(χp)=0` for C² pressure/cutoff. Dropping only the second piece gives the wrong curl. Viscous residual curl requires fourth spatial derivatives of A. Smoothness suffices locally, but does not give an effective selected bound near the singularity.

For ρ=`SmoothCutoffs.timeSwitch`, before T:

```
R₁(ρU,ρP)=ρR₁(U,P)+ρ' U+(ρ²−ρ)(U·∇)U,
curl R₁(ρU,ρP)=ρ curl R₁(U,P)+ρ' curl U
                  +(ρ²−ρ)curl((U·∇)U).
```

Activation defects disappear as germs for t>3/4, including the terminal limiting calculation. They cannot be discarded on the fixed restart interval [1/2,1). The smooth force extension is not required to equal the residual after T; `CandidateFromLimits` only guarantees shutdown at t≥2. Terminal flat activation is not force shutdown.

## Anchored gauge: one load-bearing product/curl calculation

The actual slow swirl uses K(t,s,z)−K(t,1,z), physical radial energy s=(x₀²+x₁²)/2. Write k(t,z)=K(t,1,z), G=−k e₂. This is the difference of gauged and ungauged **slow-base** potentials, not a claimed replacement of the entire A. Source `partialS_radialNormalize` and `finalPotential_sameCurl` justify uncut curl invariance for t<1. G is curl-free because it depends only on t,z; its localized curl need not vanish.

With x=x₀,y=x₁,z=x₂ and derivatives indicated by subscripts, assuming χ,k smooth,

```
g = curl(χG) = ∇χ×G = (−k χ_y, k χ_x, 0),
η = curl g = (−k_z χ_x−k χ_xz,
              −k_z χ_y−k χ_yz,
               k(χ_xx+χ_yy)).
```

The calculation uses ∂xk=∂yk=0, mixed-partial commutation, and div g=0. Pure axial cutoff variation alone produces no g; radial transition, and radial/axial overlap, can. This is an exact relative contribution, **not a nonzero certificate**: k or the total residual may cancel it. It is also not legitimate to evaluate an ungauged divergent terminal primitive and subtract infinities; use anchored one-sided extension germs for terminal quantities.

For any smooth comparison localized velocity W, keeping pressure unchanged, the exact residual difference caused by this velocity addition is

`D=R₁(W+g,P)−R₁(W,P)=∂t g−Δg+(W·∇)g+(g·∇)W+(g·∇)g`.

For ε the Levi-Civita symbol with ε₀₁₂=1, its complete component curl is

```
(curl D)_i = ∂t η_i − Δη_i
 + Σ_{j,k,l} ε_{ijk} [
     (∂j W_l)(∂l g_k) + W_l ∂j∂l g_k
   + (∂j g_l)(∂l W_k) + g_l ∂j∂l W_k
   + (∂j g_l)(∂l g_k) + g_l ∂j∂l g_k ].
```

All indices range over 0,1,2. This includes every nonlinear cross term; a gauge-only curl calculation is not the curl of the total force. Joint smoothness (or sufficient mixed time derivatives and four spatial derivatives of potentials) justifies the commuting derivatives. In a terminal argument these hypotheses belong to local extensions, not the singular original field at (1,0).

The anchored central-plane extension uses `heatPrimitive E h = −∫₁ˢ F(t,r)dr` and `heatPotential`, valid on the source's exterior segment neighborhood with s>0. This improves symbolic endpoint regularity. It does not identify all annular/cap jets with that heat field without checking the actual stage germs and exterior hypotheses at the same point.

## Checked support result and whole-cell coverage

New declarations in namespace `UnforcedRestart.Round3.LocalizedForce`:

1. `cutResidual_zero_outside A v p t hx`: no smoothness assumption; the literal residual is zero outside the closed support cylinder because velocity and pressure vanish on a full spacetime neighborhood.
2. `cutResidual_eventually_zero_outside`: strengthens this to a germ, hence every derivative of the residual agrees with zero there.
3. `terminal_boundary_jets_zero_outside A v p ea ev ep x hx n`: with the actual AwayExtensions hypotheses and representative(x) outside the closed cylinder, every order-n periodic terminal tensor is zero. Proof: the cut-residual jet is eventually zero, the chosen smooth extension has that jet limit, and uniqueness holds in the nontrivial open-past filter. No VanishingJointJets-at-origin hypothesis or terminal velocity regularity is needed for this exterior conclusion.

Exact actual specialization of (3): substitute A,v,p,selected.ea/eb/ep above and rewrite by `selected.jets n x`. It yields all terminal jets of f zero at these exterior representatives, independently of noncomputable extension selection. This specialization is documented, not newly Lean-checked as a closed selected theorem.

Coverage:

* Plateau r²<1/32, |z|<1/8: cutoff defects vanish as germs; residual agrees with the **original mixed residual**, not automatically zero. Only the lattice origin has the already checked full terminal flatness.
* Fixed localization annulus/caps: support cylinder r²≤1/16, |z|≤1/4 minus plateau. All product terms above must be retained. Its nonzero interior terminal curl remains unresolved.
* Strict exterior: newly checked terminal tensors zero. For the actual force the presingular exterior vanishing follows from candidate residual equality and activated local germs (ordinary specialization).
* Support boundary: not covered by the strict `hx` in the new theorem. For actual smooth f, approximate from exterior representatives in the central no-overlap cube; continuity of each force jet extends zero to the cylinder boundary. This is an unformalized deduction, not a claim that an arbitrary nonsmooth A has zero residual on the boundary.
* Lattice translates: use a fixed integer translation germ. Cell seams have a neighborhood outside every support copy; representative discontinuities must not be differentiated. The representative is only a pointwise selector of terminal tensors.

Thus the surviving possible obstruction is supported in the localization cylinder; neither the whole plateau nor the entire annulus is proved terminal-force-free. No arbitrary postterminal support statement follows from these terminal jets.

## Analytic certificates and nonlocal influence

For a smooth periodic force on the unit torus, let P_sol denote the orthogonal L² projection onto divergence-free fields (including constants). This is ordinary Hodge analysis, not a new Lean construction. Then
`‖P_sol f‖₂≤‖f‖₂`, and for a smooth periodic velocity/pressure before T,
`‖P_sol f‖₂≤‖∂t(ρU_per)−Δ(ρU_per)+(ρU_per·∇)(ρU_per)‖₂`.
Here U_per is the separated periodization, not a nonlinear superposition assertion. These inequalities require finite norms and provide no smallness automatically.

For the gauge residual difference above on a compact smooth region or periodic cell, a directly usable bound is

`‖P_sol D‖₂ ≤ ‖∂t g‖₂+‖Δg‖₂+‖W‖∞‖∇g‖₂+‖g‖∞‖∇W‖₂+‖g‖∞‖∇g‖₂`,

using Euclidean vector and Frobenius gradient norms. For localized pieces not individually periodic, periodize within separated supports first. This bound is conditional; no selected norm enclosures have been supplied. Higher Sobolev product bounds additionally need explicit multiplication constants and higher selected derivatives. An enclosure excluding zero for one total curl component, or a nonzero transverse Fourier coefficient with a rigorous full-cell integration/tail bound, would be an effective certificate. Isolated gauge or base contributions do not suffice.

Pressure and diffusion defeat spatial-independence reasoning. Incompressibility gives
`Δp=div f−div((u·∇)u)` on each smooth presingular slice; the periodic inverse Laplacian is nonlocal. Projecting an annular force need not leave annular support. Heat propagation also reaches the core at positive times. Even positive support distance supplies at most kernel-dependent estimates, not independence, and the singular core has no uniform distance from every possible original-residual contribution. No fixed-restart growth-relative stability constants or projected-force budgets are established here.

A nonzero terminal curl component would, by smooth force continuity, obstruct absorption on a neighborhood of T and hence arbitrarily late slabs. A nonzero value only at t<1 excludes only slabs containing that time. The zero exterior jets proved here exclude neither possibility. Whole-terminal-cell zero curl/mean at T alone would still not establish any terminal interval identity. Mean zero does not mean P_sol f=0.

## Acceptance and command manifest

Only the owned source/output subtree and this report were changed; no baseline/config/dependency edits, commits, pushes, builds or frozen validators. Read-only source input and hash inventory: `LocalizedForce/evidence.json`. This includes the exact accepted source hash and evidence for every attempt. All output is in unique `LocalizedForce/out/strict-*` directories.

Command (three serial invocations, exits 1,1,0):

```
python3 Research/UnforcedRestart/Round3/Integration/focused.py LocalizedForce
```

The existing coordinator script was read/reused, not edited. Successful run: `out/strict-_w9_cwc3/{command.json,result.json,compile.log}`. Each command record contains the full systemd scope/env/compiler/paths and SHA-256 manifest. Direct pinned Lean 4.34.0-rc2, `-j1 -DautoImplicit=false -DwarningAsError=true`; LEAN_NUM_THREADS=1, LEAN_SRC_PATH absent, unique output first, then frozen external source-built resolver; 1 CPU, 6 GiB, no swap, 32 tasks, 600 seconds. No lake or worktree cache fallback.

Accepted `Main.lean` SHA-256: `77570f73bccf5aa00987dacaabed688ddd2867b9137bab83d0ff913af033ebd7`. `python3 Research/UnforcedRestart/Round3/LocalizedForce/manifest.py` exited 0 (hash/freeze/triage PASS); `git diff --exit-code` and `git diff --cached --exit-code` both exited 0. New research files are untracked, not committed.

All three successful printed axiom closures are exactly within propext/Classical.choice/Quot.sound. Failed logs retain elaboration errors and their diagnostic sorryAx; neither failed output nor those diagnostic closures is accepted. Source triage rejects forbidden proof constructs. Focused named-export checking is not a generated-helper/imported-closure aggregate audit. No new axioms, sorry/admit, unsafe, native shortcuts or proof-setting suppression were introduced. No external numerical computation was performed.
