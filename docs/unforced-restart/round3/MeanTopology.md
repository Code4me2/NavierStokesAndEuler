# MeanTopology — compact momentum checked; force-mean composition still open

## Verdict and scope

**Precisely unresolved annular terminal curl.** This pass supplies a nontrivial **checked actual-candidate theorem**: the compact velocity belonging to the single frozen selection has zero total momentum for every `0<t<1`. Its nonlinear transport also has zero component integral. The selected periodic force's vector cell mean is checked continuous on every closed finite time interval, including at `T=1`.

**Not newly checked:** zero cell mean of that force, or a periodic potential from mean plus curl. The source-backed ordinary-analysis argument still gives zero force mean on `(0,1)`, and by continuity on `[0,1]`; the remaining Lean composition is identified below. No result here rules out exact removal on any time interval. No slab gradient identity, nonzero terminal obstruction, or perturbative growth transfer is proved.

Ownership: only `Research/UnforcedRestart/Round3/MeanTopology/` and this report were written. PLAN, REPORT, other roles, baseline sources, earlier research and frozen validators are read-only. No commit, push, configuration edit, dependency build, cache fallback, or numerical sampling.

## One actual witness and specialization map

Read PLAN, round3 REPORT, round-one FINAL-REPORT, Round2 REPORT, VALIDATION-LEDGER and CLEAN-RECOVERY. The recovery supersedes historical cached/blocked validation statuses, not mathematical limitations.

The cross-role dependency is the explicitly frozen source
`Research/UnforcedRestart/Round3/WitnessFeasibility/Main.lean`, SHA-256
`7d77092a3da73faedebac0a052c6fd2ce6fc46d340f48f796dd5e45f926be8da`.
It is read-only recompiled into each new **MeanTopology-owned** output root; no moving worker object is imported.

Let `d = WitnessFeasibility.selected`, chosen once by `Classical.choice data_nonempty` from `ActualCandidateAssembly.selected_witness`:

| Quantity | Exact specialization |
|---|---|
| B, N0 | `ActualCandidateConstruction.selectedBudget = 0`; `selectedThreshold = ActualCarrierGeometry.startingThreshold 0`, with `selectedThreshold_geometry` |
| h | `CorrectionInitialization.ActualPrimary.h`, the actual primary exponent; `0<h<1/2`, not assigned a numerical replacement |
| schedule | `d.schedule`; its `d.selectedSchedule` covers all three stage sequences together |
| A, v, p_raw | `WitnessFeasibility.potentialSum d.schedule`, `directSum d.schedule`, `pressureSum d.schedule`; these unfold to `SolenoidalDiagonal.potentialSum (fun j => (a j : ℝ)) (PhysicalWaveSum.physicalQ h)` on the respective actual stages |
| compact U | new `MeanTopology.compactVelocity = activatedVelocity (MixedPeriodicAssembly.cutVelocity A v)` |
| compact P | `activatedPressure (SpatialLocalization.cutPressure p_raw)`; used in the analytic argument, not a new Lean definition |
| periodic u,p | `WitnessFeasibility.velocity d.schedule`, `WitnessFeasibility.pressure d.schedule` |
| periodic f | `d.forcing`, with `d.candidate`, `d.smooth`, and full terminal `d.jets` |
| away extensions | `d.ea`, `d.eb`, `d.ep`; retained by the same record but not used in the compact-momentum proof |

Viscosity `ν=1`, terminal time `T=1`, unit periods, fixed restart `t0=1/2`, horizon `H=1/2`. The proof does not alter any parameter, schedule, cutoff, gauge, or existential choice. The compact forcing quantified separately in `selected_witness` is **never identified** with `d.forcing`.

Source evidence: `ActualCandidateAssembly.Witness/witness/selected_witness` (around 1016–1074), `MixedPeriodicAssembly.cutVelocity`, `activated_periodicVelocity_eventuallyEq_cut`, `activated_periodicPressure_eventuallyEq_cut`, `activated_cutVelocity_zero_outside`, `spatialDivergence_congr`, `periodized_navier_stokes`, `candidate_of_periodization`; `SpatialLocalization.supportCylinder_coordinate_bound`, `isClosed_supportCylinder`, `isCompact_supportCylinder`. The accepted manifest hashes these source files and verifies their bytes equal the clean checkout.

The proofs use only the chosen record's equations/regularity and the actual cut/periodic field formulas. They would work uniformly for any coherent `Data` record with those formulas; no evaluation of `Classical.choice` is needed. They are not consequences of incompressibility for an arbitrary periodic velocity: a constant periodic velocity is the obvious counterexample to zero momentum without the compact-first geometry.

## Checked Lean results

Source: `Research/UnforcedRestart/Round3/MeanTopology/Main.lean`.
Namespace: `UnforcedRestart.Round3.MeanTopology`.

| Declaration(s) | Classification and exact scope |
|---|---|
| `compact_component_integral_zero` | **Conditional calculus tool.** For `v : Space → Space`, `ContDiff ℝ ∞ v`, `HasCompactSupport v`, and actual divergence `Σj spatialPartial j v x j = 0` everywhere, proves `∫R³ v_i = 0`. Uses `NavierStokesR3.CompactEnergy.integral_fderiv_apply` with the coordinate function; no assumed momentum identity. |
| `compactVelocity` | **Actual-candidate definition**, from the frozen selected schedule. |
| `compactVelocity_zero_outside`, `compactVelocity_zero_germ`, `compactVelocity_agreement` | **Checked actual-candidate identities.** Zero off the closed support cylinder, zero spacetime germ there, and agreement with the periodic selected velocity in the inner cube. |
| `compactVelocity_smooth_slice` | **Checked actual-candidate theorem**, smooth compact velocity slice for `0<t<1`; transfers `candidate.velocity_smooth` by germs. |
| `compactVelocity_divergence_free` | **Checked actual-candidate theorem**, divergence zero for `0≤t<1`, including support boundaries. |
| `compactVelocity_compact_support` | **Checked actual-candidate theorem**, compact spatial support for every real t; this support statement does not assert terminal smoothness. |
| `selected_compact_momentum_zero` | **Checked actual-candidate theorem**, `∫R³ U_i(t,x) dx = 0`, every `0<t<1`, every component i. |
| `selected_compact_transport_zero` | **Checked actual-candidate theorem**, `∫R³ D(U_i)(U) = 0`, every `0<t<1`, every i. This is the actual nonlinear transport, not an assumed flux cancellation. |
| `selected_force_mean_continuousOn` | **Checked actual-candidate theorem**, continuity of `t ↦ cubeIntegral (f(t,·))` on every `[a,b]`, a vector Bochner integral. Uses only `d.smooth`, not terminal velocity regularity. |
| `periodic_potential_component_mean_zero` | **Conditional calculus tool**, necessary mean test for a `C¹` unit-periodic scalar potential, directly specializing the existing proved `cubeIntegral_partial_eq_zero`. Does not prove sufficiency. |

There are 11 theorems and one definition, all with printed axiom closures. Support/germ helpers are actual-field interfaces needed by the momentum proof, not separate force-removal claims.

### Whole-domain coverage of the checked momentum proof

`χ(x)=cutoff(16(x₀²+x₁²)) cutoff(4x₂)` has closed support cylinder
`K={r²≤1/16, |x₂|≤1/4}`. Every coordinate of a point in K has absolute value at most `1/4`, hence K is strictly inside `innerCube (1/4)` (whose defining bound is `|x_i|<3/4`). On **all of K**, including radial transition, axial caps and boundaries, the activated periodic velocity and U agree as spacetime germs. Candidate divergence freedom therefore transfers to U. Outside K, a zero germ supplies both smoothness and zero divergence. Compactness of K supplies actual compact support.

The integration-by-parts identity is

`∫ D(x_i)(U) = -∫ x_i div U = 0`.

Thus `∫U_i=0` without asserting that `χv` is divergence-free by naive cutoff calculus or that it has a compact potential. Testing instead with `U_i` gives the checked transport cancellation. Lattice translates and seams enter the later cell adapter, not this whole-space integral; no local plateau argument substitutes for annular coverage.

## Mean normalization and integrated momentum — unformalized composition

Use `PeriodicIntegration.cubeIntegral`: product Lebesgue measure on `Coords = Fin 3 → ℝ`, restricted to `Icc 0 1`, pulled to `Space` by `toSpace`. The cube has volume one, as proved in frozen `Round2.ActualForce.cubeIntegral_constant`. Thus the cell **integral equals its normalized average**, componentwise and for the vector mean. There is no missing factor `(2π)³` or division by an unspecified volume. On periods L_i the average would instead be the integral divided by `L₀L₁L₂`.

For any sufficiently jointly smooth periodic incompressible solution at interior times,

`m_i(t) = ∫Q f_i = d/dt ∫Q u_i = M_i'(t)`.

Indeed `R₁(u,p)=∂t u + Du(u) - Δu + ∇p`; incompressibility writes convection as `Σj ∂j(u_i u_j)`, and periodic velocity/pressure cancel all spatial derivative integrals. Pressure periodicity is essential. This equation alone does **not** force `m=0`; neither zero initial momentum nor incompressibility alone makes momentum constant under forcing.

For this compact-first candidate the stronger cancellation follows in ordinary analysis:

1. The newly checked theorem gives `∫R³ U_i(t)=0` for all `0<t<1`.
2. Local joint smoothness and one fixed compact support K allow differentiation under the whole-space integral on any closed time neighborhood strictly inside `(0,1)`. Consequently `∫ ∂t U_i=0`. No uniform presingular bound as `t↑1` is needed.
3. The nonlinear integral is now checked zero. Compact derivative integration also gives `∫ ΔU_i=0`, `∫ ∂iP=0`. Therefore the actual compact **residual** R₁(U,P) has integral zero.
4. Periodicity plus the separated-copy velocity and pressure **germs** identifies the periodic residual locally with one translate of the compact residual. The nonlinear term has only one nonzero local copy; no nonlinear superposition identity is used. `d.candidate.navier_stokes` identifies f with that residual on `0<t<1`.
5. Integrating the periodized compact residual on any unit cell gives its whole-space integral. Translating the centered cell to `[0,1]³` does not change the periodic integral. Hence `m(t)=0` on `(0,1)`.
6. The newly checked closed-slab continuity of the selected force mean extends this identity to **both endpoints 0 and 1**. This step uses no velocity trace at 1.

**Status: steps 2–6 are not a newly checked Lean composition.** The analytic conclusion is zero mean on `[0,1]`, not just a zero derivative of an unidentified momentum. Activation causes no exception: U already contains the time activation, so the compact-momentum identity is identically zero even while activation varies. Equivalently `∫(a'U₀+a∂tU₀)=0`; the nonlinear activation factor `a²` does not spoil zero transport integral. One must not discard activation terms on the restart interval beginning at `1/2`; activation is eventually one only after `3/4`.

No mean identity for `1<t<2` follows from this proof. `CandidateFromLimits.force_eq_activated_residual` and `force_zero_from` describe the construction's extension and cutoff, but the selected wrapper does not export equality with a particular compact extension, or a particular shutdown threshold. Its exported `force_time_support` supplies only some finite future endpoint. Do not unfold an existential proof to assign extra global properties to the selected record.

### Smallest outstanding Lean adapters

* Whole-space differentiation of the actual compact momentum using the fixed support and joint local smoothness. Relevant proved interfaces include `R3.CompactTimeIntegral` and `SmoothParameterIntegral`; this pass did not compose them.
* Laplacian/pressure component cancellation via `R3.CompactEnergy.integral_partial_eq_zero` and the actual cut-pressure smoothness/support. These are short derivative/support adapters, not unknown physical constants.
* **Cell integral of the separated periodized compact residual equals its whole-space integral**, including Euclidean/product-coordinate measure transport, cell translation and seams of measure zero. A bounded search of `PeriodicLocalization.lean` found no integral adapter. This is a search result, not a claim none exists anywhere in Mathlib.
* Use those equalities and `d.candidate.navier_stokes`, then take limits of the already checked continuous mean. The terminal velocity must not be differentiated.

## Torus topology and an explicit smooth-potential certificate

The following is **unformalized deduction / conditional analytic tool**, not an actual-witness curl theorem or a conjectural assumption relabeled as proof.

For a smooth unit-periodic real vector field f on R³, a periodic scalar potential exists **iff** spatial curl is zero everywhere and `∫Q f=0`. Curl uses `(∂₁f₂−∂₂f₁, ∂₂f₀−∂₀f₂, ∂₀f₁−∂₁f₀)`, matching `NavierStokes/SpatialCurl.lean:30–52` (`curlLinear`, `curl`, `spatialCurl`); zero curl is symmetry of all spatial first partials. A nonzero constant vector is curl-free but fails the mean/cycle test. Conversely mean zero alone leaves nonconstant solenoidal modes; it is not `P f=0`.

Here is a feasible analytic certificate avoiding Fourier convergence machinery. For joint smooth f on an **open time domain J × R³**, define a fixed-gauge potential

`φ(t,x) = ∫₀¹ Σi x_i f_i(t,sx) ds`.

Differentiation under this compact parameter integral is justified locally uniformly in `(t,x)`. At every t where curl f vanishes everywhere,

`∂j φ = ∫₀¹ [f_j(t,sx) + s Σi x_i ∂j f_i(t,sx)] ds`
`       = ∫₀¹ d/ds [s f_j(t,sx)] ds = f_j(t,x)`.

The increment `φ(t,x+e_i)−φ(t,x)` then has zero spatial gradient by periodicity of f, so is independent of x. It equals the integral of f_i around the i-th unit cycle. Averaging this cycle over transverse coordinates, and using periodicity in its own coordinate, identifies it with `m_i(t)` (unit-volume normalization). Thus zero mean makes φ periodic. Subtracting its cell mean fixes a zero-average gauge if desired; the radial formula already fixes `φ(t,0)=0` and is jointly smooth.

For a closed time slab I inside J the same formula is ambient smooth even if curl and mean vanish only on I; the gradient and periodicity conclusions hold on I, including endpoints. For a terminal slab `[a,1)` the residual equation is asserted only before 1. Smooth f permits a potential with terminal regularity if the spatial criterion holds there, but does not make u or the old pressure regular at 1. A corrected pressure must satisfy the requisite joint/relative regularity and periodicity on its actual domain; its sign is **p−φ**. A purely spatial existence statement at each time without a coherent gauge does not itself supply that regularity.

Formal library gaps for sufficiency: implement the compact-parameter formula, commute its spatial derivative with the integral, prove the curl-symmetry calculation, constant increment from zero gradient on connected R³, and cycle/cell identification with correct measures. Existing `PeriodicIntegration` proves necessity (partial integrals vanish), not this whole sufficiency package. No new axiom or notation for a solenoidal projection fills these gaps.

## Certificates, numerical recommendation and interval consequences

**Go:** symbolic, universal-in-selection integration and periodization adapters. They require no computable schedule or numerical h/N0. The mean route has exact cancellations, not an unresolved floating-point constant. Continue the annular curl analysis separately.

**No-go now:** actual-force numerical mean/curl experiments presented as certified evidence. The frozen selection supplies existence and smoothness, not finite evaluators and certified derivative tails for h, threshold, schedule, profiles, away extensions or forcing. No parameter values or surrogate samples were used here. A floating-point nonzero mean would conflict with the analytic cancellation or expose discretization error; it would not certify a harmonic obstruction without certified actual-field error bounds.

A certified nonzero terminal curl or mean plus force/curl continuity would exclude arbitrarily late exact pressure-absorption slabs. No such nonzero certificate is obtained. A nonzero value only at an earlier time would exclude slabs containing that time, not all later slabs. Zero terminal mean (even if fully formalized) neither proves zero terminal curl nor a whole-terminal-interval identity. Literal force zero preserves p; an absorbable nonzero gradient requires replacing p by p−φ. No conclusion here chooses either exact removal or controlled perturbation.

## Accepted source / declaration / axiom / command manifest

Canonical role manifest: `Research/UnforcedRestart/Round3/MeanTopology/MANIFEST.json`.
It records all 12 printed exports and their axiom lists, exact accepted source, driver and source-map hashes, source equality to the clean checkout, the cross-role freeze, and evidence hashes. It is **focused named-export validation**, not a new aggregate enumeration of generated helpers or imported project closures. The historical clean-replay aggregate remains frozen and is not rerun.

Accepted `Main.lean` SHA-256:
`0c106afc75bcfed595457f9a7f77fe1c9bd0699ba5e33caf694d86cc40cdb963`.
Driver SHA-256:
`49e6ee24bfa2b8119d03a1f878ee25670fdc68c94f1c519ceed69b00247f4170`.
Manifest SHA-256:
`cde039301ccd98fd95acbedb607e8222efec98bb9e67c6637da37f1cc07fc2a7`.

Run from the authorized worktree:

```sh
python3 Research/UnforcedRestart/Round3/MeanTopology/check.py
```

Final accepted run: `MeanTopology/out/strict-mb_z5gut/`. Both frozen-wrapper and new-source compiler exits **0**, driver **0**. Exact argv/environment/cwd/source/compiler/output/log hashes are in each `*.command.json` and `*.result.json`; source copies and full logs are preserved there.

Each invocation uses direct pinned Lean 4.34.0-rc2 with `-j1 -DautoImplicit=false -DwarningAsError=true`, `LEAN_NUM_THREADS=1`, environment cleared (`LEAN_SRC_PATH` unset), unique output root first, then only the external resolver in snapshot `external-evidence.json`. Dependency outputs from `/home/velvet/research-builds/unforced-round2-clean-20260909T221339Z` are read-only. `systemd-run` enforces one CPU, 6 GiB, zero swap, 32 tasks; `timeout 600`. No Lake invocation. Source triage rejects placeholders, custom axioms, unsafe/native proof shortcuts, option overrides and challenge imports in the new source/frozen wrapper. All printed axiom closures are contained in `{propext, Classical.choice, Quot.sound}`. Installed Lean/core/compiler/runtime and host are trust roots.

Rejected attempts are retained, not accepted: `strict-e9y08ksr` compiled the wrapper successfully but the driver's original single-line axiom parser rejected a wrapped axiom list; the parser was corrected without changing any proof setting. `strict-x212rf_b`, `strict-68zv82m7`, `strict-1i2tl027`, `strict-10tzrj_u` have Lean elaboration failures (projection typing/simplification and initial germ/support syntax); their diagnostic `sorryAx` is compiler error recovery, not accepted source/proof. `strict-f853krkn` is an earlier narrower pass. Every attempt has unique owned outputs; failed drafts are preserved as source copies under out/.

Read-only final git checks: HEAD remains `597692fa5d55e07d810b2d96ead1a67972585425`; tracked diff and index diff empty. These checks are not a fresh 2,878-file snapshot audit. All newly written files remain isolated and uncommitted; no frozen validator or snapshot script was run.
