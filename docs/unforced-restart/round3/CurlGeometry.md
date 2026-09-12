# CurlGeometry — checked actual curl adapters; annular obstruction unresolved

## Decision and ownership

**Precisely unresolved annular terminal curl.** No certified nonzero actual terminal curl component, whole-cell zero-curl identity, or whole-terminal-interval pressure absorption was obtained. No conclusion here rules out exact removal for the selected candidate on any terminal interval. Conversely, no interval of removal is established. No numerical experiment was performed; **no-go for actual-candidate numerics** without certified representations and jet errors. A negative search is not vanishing.

This receiving pass acts explicitly as CurlGeometry. Writes are confined to `Research/UnforcedRestart/Round3/CurlGeometry/` and this report. PLAN, initial REPORT, other owners, published proof, prior research and frozen validators remain read-only. Read the round-one FINAL-REPORT and Round2 REPORT/VALIDATION-LEDGER together with CLEAN-RECOVERY: old cached/blocked statuses are historical; clean source-built dependencies already exist and were reused, not rebuilt.

## One actual witness and source specialization

Use **only** `UnforcedRestart.Round3.WitnessFeasibility.selected`, the frozen complete-record choice from `ActualCandidateAssembly.selected_witness`. No fresh choice of force, schedule, h, or compact candidate is made here.

* Wrapper: `Research/UnforcedRestart/Round3/WitnessFeasibility/Main.lean`, SHA-256 `7d77092a3da73faedebac0a052c6fd2ce6fc46d340f48f796dd5e45f926be8da` (verified before every check).
* `ActualCandidateConstruction.selectedBudget = 0`; `selectedThreshold = ActualCarrierGeometry.startingThreshold 0`, with its actual geometry proof. `h = CorrectionInitialization.ActualPrimary.h`, unchanged, with upstream `0<h<1/2`. No numerical threshold/h is substituted. ν=1, T=1, unit spatial periods; the fixed subsequent restart remains t0=H=1/2.
* `a = selected.schedule`. Write A=`potentialSum a`, v=`directSum a`, p=`pressureSum a`. Each is exactly `SolenoidalDiagonal.potentialSum (fun j => (a j : ℝ)) (PhysicalWaveSum.physicalQ h)` applied to its actual sequence. `ActualCandidateAssembly.lean:509–546,1016–1074` identifies these sequences and the common witness.
* The zeroth potential includes **all** `TailGaugePotential.finalPotential` and `initialPotential`, not just a scalar base velocity (`ActualCandidateAssembly.lean:198–213`). The direct sequence is the actual angular mean sequence, not zero by convention.
* `ea,eb,ep = selected.ea,selected.eb,selected.ep` are the same away-extension proofs. `JointResidualLimits.OneSidedExtension` has an open neighborhood of `(1,x)`, smooth value, and agreement with the incoming field on that neighborhood's open past. `MixedPeriodicAssembly.cutResidualExtension` constructs the cut residual of three such values; its agreement proof uses germs. `boundaryLimits` chooses a residual extension at a nonzero representative; this choice is not an evaluator.
* Actual periodic velocity is `activatedVelocity (periodicVelocity A v)`; actual periodic pressure is `activatedPressure (periodicPressure p)`; force is **selected.forcing**. Its PDE equality is `selected.candidate.navier_stokes` on `0<t<1`; global smoothness is `selected.smooth`; terminal tensors are `selected.jets`.
* We do **not** identify the separate existential compact force with this periodic force. All finite-time identifications below use the actual PDE and separated-copy germs. All terminal identifications use the selected force's given jets. Neither requires equality of those existential components or a regular terminal reference velocity.

The source-backed smooth shutdown is only for t≥2 (`CandidateFromLimits`), not on a presingular slab. The future extension cannot alter the selected presingular curl or its terminal limit, although its postterminal values are not determined by the PDE.

## New strictly checked statements

Source: `Research/UnforcedRestart/Round3/CurlGeometry/Main.lean`.
Namespace: `UnforcedRestart.Round3.CurlGeometry`. Exactly one definition and seven theorems; no generic lemma collection.

| Declaration | Classification and exact scope |
|---|---|
| `terminalEntry` | Actual-candidate definition: J₁(x)(constant direction (0,eᵢ)) evaluated in component j, with the selected sums and ea/eb/ep. |
| `spatial_slice_derivative` | **Conditional calculus tool:** joint `DifferentiableAt ℝ f (t,x)` implies `D_x f(t,·)(x)[v]=Df(t,x)[(0,v)]`. No unsupported endpoint differentiation. |
| `terminalEntry_eq` | **Checked actual-candidate theorem**, all x,i,j: the actual selected force's spatial Jacobian entry at t=1 equals `terminalEntry x i j`. Uses smooth force, chain rule and `iteratedFDeriv_one_apply`. |
| `terminal_curl_component` | **Checked actual-candidate theorem**, all x and i∈Fin 3: `(curl f)(1,x)ᵢ = terminalEntry x (i+1) (i+2) − terminalEntry x (i+2) (i+1)`, cyclic Fin-3 indices. |
| `terminal_curl_origin` | **Checked actual-candidate theorem:** `(curl f)(1,0)=0`. This is only origin flatness, not a whole-cell theorem. |
| `terminal_curl_ne_zero` | **Conditional actual-candidate certificate interface:** unequal specified antisymmetric tensor entries imply a nonzero terminal curl vector. The unequal-entry hypothesis remains unproved; this theorem is not itself a nonvanishing result. |
| `selected_curl_continuous` | **Checked actual-candidate theorem:** joint continuity of `SpatialCurl.spatialCurl selected.forcing` on all spacetime. No velocity smoothness at T is used. |
| `late_inner_curl` | **Checked actual-candidate residual identity:** if `3/4<t<1` and `x∈PeriodicLocalization.innerCube (1/4)`, then `(curl f)(t,x) = curl (MixedPeriodicAssembly.cutResidual A v p)(t,x)`. Uses activation's eventual-one germs, spatial separated-copy germs, residual locality, and the actual PDE on a whole spatial slice. Not differentiation of point equality. |

`SpatialCurl.curlLinear_apply_zero/one/two` fixes the convention as `(∂₁f₂−∂₂f₁, ∂₂f₀−∂₀f₂, ∂₀f₁−∂₁f₀)`. The terminal component theorem now closes the previously unformalized order-one tensor-to-spatial-curl adapter. It supplies no sign estimate on the tensor.

## Actual residual and vorticity calculation

**The calculations in this section are source-grounded, unformalized deductions**, not additional checked Lean theorems. Assume joint smoothness on an open neighborhood at a presingular point (or use the actual smooth one-sided extension at a nonzero terminal representative). Smoothness ensures all product rules and commuting mixed derivatives below. More economically the calculation needs the displayed mixed time/spatial derivatives, spatial order four of A, order three of v and order two of p; no uniform terminal velocity bounds are assumed.

Put χ=`SpatialLocalization.spatialCutoff`, g=∇χ, u=curl A+v, b=g×A. The definitions in `MixedPeriodicAssembly.lean:43–61` and `SpatialLocalization` give

```
U = cutVelocity A v = curl(χ A)+χ v = χ u+b,
P = cutPressure p = χ p,
R₁(U,P) = ∂t U+(U·∇)U−ΔU+∇P.
```

This is viscosity exactly one. Let ω=curl u and Ω=curl U. Complete spatial localization of the vorticity is

```
Ω = χ ω + g×u + curl b,
curl b = g div A − A Δχ + (A·∇)g − (g·∇)A.
```

In particular neither the direct v nor the cutoff-potential b may be discarded. Before invoking incompressibility,

```
curl R₁(U,P) = ∂t Ω − ΔΩ
             + (U·∇)Ω − (Ω·∇)U + Ω div U.
```

Derivation: `curl ∇P=0` by symmetry of the spatial Hessian; `curl ∂t U=∂t Ω` and `curl ΔU=ΔΩ` by mixed-derivative commutation. Write `(U·∇)U=∇(|U|²/2)−U×Ω` and use `div Ω=0` to obtain the last three terms. The selected late-time local U is divergence-free by the candidate equation and the same separated-copy/activation germs, so its `Ω div U` term vanishes. This is the forced vorticity equation, **not** an inference from axis velocity growth.

For ρ=`SmoothCutoffs.timeSwitch`, the actual local activated pair is (ρU,ρP), hence

```
R₁(ρU,ρP) = ρ R₁(U,P)+ρ' U+(ρ²−ρ)(U·∇)U,
curl R₁(ρU,ρP) = ρ(∂t Ω−ΔΩ)+ρ' Ω
               + ρ²[(U·∇)Ω−(Ω·∇)U+Ω div U].
```

This retains the activation derivative, viscosity, and nonlinear coefficient. Equivalently, for the actual activated velocity V and W=curl V, its force satisfies `curl f = ∂t W−ΔW+(V·∇)W−(W·∇)V`, with div V=0. Activation defects disappear by a **joint eventual-one germ** only when t>3/4 (`TimeLocalization.lean:77–93`), not throughout the fixed restart [1/2,1). Terminal force jets can use that late regime, but are not defined by evaluating R₁ of the singular global velocity at t=1.

### Full localization residual, and a load-bearing curl product calculation

Let R=R₁(u,p). Expanding every cutoff term gives

```
R₁(U,P) = χR + ∂t b − Δb − (Δχ)u − 2 Σᵢ (∂ᵢχ)∂ᵢu + p g + N,
N = (χ²−χ)(u·∇)u + χ(u·∇χ)u + χ(u·∇)b
  + (b·∇χ)u + χ(b·∇)u + (b·∇)b.
```

For the full **viscous localization commutator** K=−Δb−(Δχ)u−2Σᵢ(∂ᵢχ)∂ᵢu, the complete curl calculation is

```
curl K = −Δ(curl b) − ∇(Δχ)×u − (Δχ)ω
         −2 Σᵢ [∇(∂ᵢχ)×∂ᵢu + (∂ᵢχ)∂ᵢω].
```

Indeed each scalar-vector term uses `curl(q a)=∇q×a+q curl a`, and `curl(∂ᵢu)=∂ᵢω`; the b term uses commuting Laplacian/curl. This includes the Hessian and third derivatives of χ, derivatives of every mixed incoming field, and fourth derivatives of A inside Δ curl b. Dropping χ derivatives loses precisely the potential annular obstruction.

Combining this with `curl(χR)=g×R+χ curl R`, `curl(∂t b)=∂t curl b`, `curl(p g)=∇p×g`, and the explicitly specified N gives the full residual curl. The preceding Ω equation also expands the complete nonlinear curl without leaving any presumed zero commutator. Pressure cancellation must be performed on the pair: the g×∇p inside g×R cancels ∇p×g; χ curl ∇p is zero. Thus cutoff pressure creates no curl **in total**, although p∇χ individually generally does. No pressure term is silently omitted.

Anchored gauge is already part of A. `TailGaugePotential.radialNormalize` subtracts the swirl primitive at physical radial coordinate s=1; `potential`, `spatialCurl_potential`, and `finalPotential` retain all slow orders and prove the incoming curl is unchanged. An unlocalized curl-free change G would nevertheless change `curl(χA)` by `g×G`. This explains why substituting an ungauged potential in the annulus is invalid. We make no claim that the actual summed gauge contribution vanishes after localization; b contains it exactly.

## Terminal tensors, whole-cell coverage and scope

Let Jₙ(x)=`MixedPeriodicAssembly.boundaryLimits A v p ea eb ep x n`. For y=`representative x`, the boundary definition is the Taylor tensor of a smooth local cut-residual extension when y≠0, and zero when y=0. `cutResidualExtension` provides the requisite extension from the three actual field extensions. The terminal value of its curl is fixed by its order-one tensor; choosing another agreeing smooth extension cannot change that past limit. This uniqueness observation is ordinary analysis here, not a new effective representation theorem.

The checked `terminal_curl_component` holds **for all x**, including seams and the annulus. Its right side is still symbolic:

* **Origin / lattice copies:** origin curl zero is checked. Extension to integer translates follows from the existing spatial-curl periodicity theorem and actual force periodicity (source-connected deduction, not a new named theorem here).
* **Plateau:** χ=1 on `r²<1/32, |x₂|<1/8`; germ identities reduce the cut residual to the original mixed residual. At nonzero points that still requires the actual original residual jet. Flatness at the origin alone says nothing about them.
* **Localization annulus:** `supportCylinder \ plateau`, including radial transition, axial caps, plateau edges and support boundary. All displayed b, χ-derivative, direct-field and nonlinear terms must be included. This is not the iteration's active annulus. No certified cancellation or sign in its interior is supplied.
* **Exterior and outer support boundary:** outside the closed cylinder `r²≤1/16, |x₂|≤1/4`, cut velocity and pressure have zero germs, so the presingular residual and its spatial curl are zero there. Smooth selected-force continuity then gives zero terminal curl there. At the outer boundary, approach from the exterior and use spatial continuity. These last exterior/boundary conclusions are unformalized deductions in this pass, not inferred from merely zero point values. They do not cover interior transition points.
* **Translates and seams:** the cylinder lies in the separated inner cube; curl periodicity and local single-copy germs handle translates. Never differentiate `round`, `nearestIndex`, or the discontinuous representative function. `late_inner_curl` checks the finite-time copy calculation; the terminal tensor theorem has all-space scope independently.

No zero-curl assertion is inferred by sampling any part of this coverage. Spatial separation does not imply that annular forcing cannot influence the core: viscosity diffuses and incompressible pressure is nonlocal.

## What a certificate would and would not prove

**Conditional calculus consequence, not a certified nonvanishing result:** if actual entries in `terminal_curl_ne_zero` are unequal, the checked component identity gives cᵢ(1,x*)=b≠0. Checked joint force-curl continuity then supplies δ>0 with `|cᵢ(t,x*)−b|<|b|/2` for `|t−1|<δ`. Thus every sufficiently late time has a nonzero curl at x*. This rules out an everywhere-gradient force on any presingular terminal slab ending at 1, and on all nonempty slabs inside that late neighborhood. The quantitative δ and the interval-exclusion composition have not been newly formalized.

A nonzero value only at some t₁<1 excludes slabs containing t₁ (and a local neighborhood by continuity), not all later slabs. Whole-cell terminal zero curl, even together with zero mean, proves no whole-interval identity: `(1−t)g(x)` is a diagnostic counterexample to that logical inference when curl g≠0, **not** the selected force. On the torus zero curl alone also leaves the harmonic mean obstruction. An admissible periodic potential on an entire fixed slab, with suitable joint time regularity, is required; pressure correction is p−φ. Literal f=0 preserves both old fields and is a different claim.

**Smallest missing actual analytic certificate:** prove an unequal pair of the selected J₁ spatial entries at one actual nonzero annular representative, with all localization/direct-field terms, or prove equality of all antisymmetric entries throughout the cell and then throughout a fixed terminal slab. There is no proposed numerical value of h, N0, schedule, tail constant, cutoff jet, or extension value. A numerical certificate would require enclosures of these exact entries whose difference excludes zero, including error from derivatives of the entire selected diagonal sum. Mere finite smooth bounds or locally finite formulas without an effective active-index/tail certificate do not provide this.

The formal identities use no evaluator: analogous arguments work uniformly for any complete record satisfying the same selected-data contract. Thus universal-in-witness symbolic analysis can bypass noncomputable selection. Whether such analysis forces annular nonvanishing or vanishing is **unresolved**, not a conjecture promoted to a result. No conjecture is accepted as mathematics here.

## Accepted source / declaration / axiom / command manifest

Final source SHA-256: **`4fe5a5fda25cd5a2e70fec1d0a40c0b79bbadec12f23bca9bed4883e5c15c81d`**.

Final focused evidence: `Research/UnforcedRestart/Round3/CurlGeometry/out/strict-0m49nclb/`:

* `manifest.json`: exact commands, private environment, source/compiler hashes, logs and all output hashes for the unchanged frozen wrapper replay and final CurlGeometry source; both **exit 0**.
* `CurlGeometry.log`: `#print axioms` for all eight named declarations above. Every closure is exactly a subset of `{propext, Classical.choice, Quot.sound}`; no rejected axiom appears in the accepted log.
* `source-manifest.json`: cited baseline sources and hashes, byte equality with their CLEAN checkout sources, wrapper/source/tool hashes, and git preservation check commands/exits.
* Imported wrapper was strictly recompiled **read-only from its frozen source** into this run's unique module-path output. No moving cross-role objects were imported.

Reproduction from the authorized worktree:

```sh
python3 Research/UnforcedRestart/Round3/CurlGeometry/check.py
```

Driver SHA-256 `4339046be70191b8856ff2a859ee3f92baea9a77ac79b220a46e2724519d6a8b`. Each run has unique outputs and private HOME; direct pinned Lean uses `-j1 -DautoImplicit=false -DwarningAsError=true`, `LEAN_NUM_THREADS=1`, and clean `env -i` (so LEAN_SRC_PATH is unset). LEAN_PATH is unique run lib followed only by the explicit external roots in `snapshot/external-evidence.json`. Installed compiler hash is checked. Serialized systemd scope limits: CPUQuota=100%, MemoryMax=6G, MemorySwapMax=0, TasksMax=32, timeout 600s. No Lake invocation, shared build, cache fallback, dependency operation or external computation occurred.

Source triage rejects forbidden proof placeholders, axioms, unsafe/native shortcuts and option overrides in the two compiled sources. Direct import is solely the frozen wrapper, whose import is `NavierStokes.ActualCandidateAssembly`. All eight new substantive exports are axiom-printed. This is **focused export acceptance**, not new aggregate enumeration of generated helpers/all imported modules; the inherited clean audit remains the evidence for its frozen closure only. Installed Lean/core/compiler/runtime and host are trusted, not bootstrapped anew.

Attempt history is preserved: `strict-jf09_d3t` and `strict-hid7abje` each failed (exit 1) on the spatial chain-rule helper, first from reversed `hasFDerivAt_const` arguments and then an unresolved scalar type. Their `sorryAx` prints are compiler-generated **rejected diagnostics**, not accepted source axioms. `strict-fsczq36f` passed the first seven exports; `strict-0m49nclb` passed the final eight, including `late_inner_curl`. No failed draft is imported.

At final recorded checks, `git diff --exit-code` and `git diff --cached --exit-code` both returned 0; HEAD remained `597692fa5d55e07d810b2d96ead1a67972585425`. No commit, push, ref, baseline, dependency or build-configuration changes. The new role artifacts are not claimed to be part of preservation snapshot e970490cf8f0cfb41fca101c62702fab7347c17c.
