# WitnessFeasibility — fixed selection, effective-data audit and certificates

## Decision and scope

**NO-GO for numerical experiments advertised as evaluating the selected whole-cell force, terminal curl, or nonzero Fourier modes. GO for symbolic, selection-uniform germ certificates.** No actual parameter values, sampled surrogate, numerical sign certificate, whole-terminal-slab identity, or perturbative growth transfer was produced. This is an effective-data gap, not a computability-impossibility theorem or a proof that removal is impossible.

Ownership: only `Research/UnforcedRestart/Round3/WitnessFeasibility/` and this report. The frozen `Main.lean` is unchanged (SHA-256 `7d77092a3da73faedebac0a052c6fd2ce6fc46d340f48f796dd5e45f926be8da`). New mathematics is `Certificates.lean`; new tooling is `check.py`. Read PLAN, REPORT and the four historical reports specified in PLAN together: the completed CLEAN-RECOVERY supersedes historical dependency-build blockers, not mathematical limitations. No old validators were run.

## 1. Exact specialization map

In this section source paths start `NavierStokes/`; all fields below use **the same** `d := UnforcedRestart.Round3.WitnessFeasibility.selected`.

| Object | Literal source / declaration and dependence | Evaluation status |
|---|---|---|
| ν, T, periods, restart | `ProblemStatement.navierStokesResidual` (84): viscosity 1. Terminal 1, unit periods. PLAN fixes t0=1/2, H=1/2; every S<H restricts these same data. | Exact constants, not adjustable. |
| B, N0 | `ActualCandidateConstruction.selectedBudget` (110)=0; `selectedThreshold` (112)=`ActualCarrierGeometry.startingThreshold 0`. `startingThreshold requested` (34)=max requested geometricThreshold. | B is explicit. `geometricThreshold` (26) is `.choose` from `PositiveRepresentatives.exists_positive_reference_charts`, dependent on the fixed nominal profile. No numeral extracted. |
| Profile and h | `FinalSlowBase.ProfileData` (451), `profileData_nonempty`, `actualProfile` (469); `CorrectionInitialization.ActualPrimary.profile/outgoing/nominal/h/certificate/modulation` (2967ff). | One `Classical.choice` of outgoing profile, nominal witness, cone certificate, loop, modulation and full true-cone proof. h is its `outgoing.data.h`, with 0<h<1/2. Neither h=1/4 nor a freely chosen nominal profile is licensed. |
| Upper, primary geometry | `ActualPrimary.upper` (2984)=2*activeRight nominal; `Choice` (2988), `choice_nonempty`, `choice` (3010), `slots`, `phases`, `covariance`. | Geometry includes prepared.N, detGap>0, entryBound≥1, inverseLower>0, covariance inequalities. `.choice` selects the full prepared object and constants; proof of bounds is not an evaluator. |
| Inner/base Borel scales | `FinalSlowBase.scales` (202) uses `EntranceAlignedBase.scales`; latter (880) chooses from `exists_admissibleScales`; `EntranceAlignedBase.trueWidth` (30) uses `H.initial.choose`. | Distinct from the outer diagonal schedule a. Finite modulation/coefficient functions and scale choices remain upstream dependencies. |
| Cycle and physical band | `ActualCandidateConstruction.parameters`, `parameterSequence`, `cycle` (34–43); `ActualCycleParameters.fixedParameters` (191), `bandFloor` (95)=prepared.N; `firstBand` (75)=max 4 bandFloor; `qbig` (83)=ChartScales.Q firstBand. | Cycle is an iteration with constant parameter sequence, not an independently sampled correction each step. Its input fields, solves, means and geometry are noncomputable real/function data. qbig is a fixed positive dyadic scale, not a supplied number. |
| Potential stages A_j | `ActualCandidateAssembly.potentialStages` (509); zeroth stage (200)=`TailGaugePotential.finalPotential certificate modulation upper B + initialPotential B N0`. Positive stages (493)=particularPotential + signedPotential + streamMeanStages (j+1). `initialPotential` (35)=initial physical potential + streamMeanStages 0. | Anchored potential, current-state particular/signed solves and stream means all retained. Not the base alone. |
| Direct stages B_j | `directStages` (514)=`LocalAngularDiagonal.rawSeries (directData ...)`; directData (503) uses the same meanCycleInput; initial direct field (41)=angularMeanStages 0. | A direct angular contribution exists **outside the curl operation**. It cannot be dropped. |
| Pressure stages P_j | `pressureStages` (518); zeroth pressure (203)=FinalSlowBase.pressure + initialPressure; initialPressure (38)=physical pressure + pressureMeanStages 0; positivePressure (498)=particularPressure + signedPressure + pressureMeanStages (j+1). | Same cycle, geometry and base; no independent pressure choice. |
| Outer schedule a | `ActualCandidateAssembly.witness` (1054) obtains a `GermCandidateAssembly.WitnessData`; `exists_candidate_witness_of_finite_stages` (180, obtain at 211) selects through `StageEstimates.exists_schedule`. `MixedDiagonalSchedule.exists_three_component_local_schedule` (208) uses common losses and `CutStageEstimates.exists_physical_local_diagonal_cut_bounds`. | `MixedCandidateWitness.SelectedSchedule` (25) exposes a0≥1, positivity, doubling, StrictMono, divergence to infinity, 1/a_j<qbig, three smooth sums and vanishing original-residual joint jets. It does **not** expose executable a_j, the underlying raw numerical loss tables, or an error oracle. |
| ASum, BSum, PSum | `Main.potentialSum/directSum/pressureSum`: `SolenoidalDiagonal.potentialSum (fun j => (a j : ℝ)) (PhysicalWaveSum.physicalQ h)` on the respective sequences; `cutStage` and `potentialSum` (32–38). | Exactly Σ′_j cutoff(a_j q(z)) stage_j(z). physicalQ (361) is the actual similarity coordinate, positive/smooth for t<1. No replacement q is permitted. |
| Local and periodic fields | `MixedPeriodicAssembly.cutVelocity` (48), `periodicVelocity` (52), `SpatialLocalization.cutPressure/periodicPressure`; `TimeLocalization.activatedVelocity/activatedPressure` (26–30). | With χ(x)=cutoff(16(x0²+x1²))cutoff(4x2), U=curl(χ ASum)+χ BSum, P=χ PSum. Periodize the localized fields, then activate **both** velocity and pressure by β=timeSwitch. u=Main.velocity a; p=Main.pressure a. |
| Cutoff profiles | `SmoothCutoffs.cutoffBump/cutoff` (27–34), `scaledCutoff` (135), timeSwitch in same file. | Fixed Mathlib ContDiffBump, inner radius 1/2, outer 1, not an arbitrarily selected smooth cutoff. Real-valued/library noncomputability alone does not show it intrinsically lacks a computable representation; no certified derivative evaluator was extracted here. |
| Away extensions ea,eb,ep | `JointResidualLimits.AwayExtensions/OneSidedExtension` (73–82), `GermCandidateAssembly` (211ff), `MixedPeriodicAssembly.cutResidualExtension/cutResidual_awayExtensions` (300–331). | AwayExtensions is a **Prop** giving Nonempty local smooth extensions, not a table of functions. Away from zero, actual extension functions are classically selected. Their open neighborhoods and agreement on t<1 are essential. |
| Terminal tensor | `d.jets`, `MixedPeriodicAssembly.boundaryLimits` (345), `JointResidualLimits.boundaryLimits` (123). | At y=representative x=0 it is zero. At y≠0 it is `ftaylorSeries ℝ e.value (1,y)`, where e is a chosen one-sided extension of the **cut residual**. Symbolic exact tensor, not evaluated numbers. |

This is a dependency-interface audit, **not** an exhaustive extraction of every transitive choice in the thousands of imported declarations. In particular the outgoing/nominal/modulation construction and all subordinate pulse, inverse, primitive, compact-bound and local-solve producers have not been converted to effective representations. The map identifies the fixed producers and the earliest opaque inputs; it does not claim that the named list exhausts their internal choices. Source hashes for this audit are in `source-manifest.json` in the owned subtree.

## 2. Which force extension is actually retained?

`ActualCandidateAssembly.Witness` (1019) existentially retains a, ea/eb/ep, periodic forcing, CandidateProperties, global force smoothness, consequences, growth, derivative decay, terminal jets, and a separate compactForcing witness. `selected_witness` specializes B and N0 but remains a proposition, not a reducible data-valued record.

The **constructor route** in `MixedPeriodicAssembly.exists_candidate_force` (539) obtains a compact candidate, then supplies `PeriodicLocalization.periodize F`. For that compact construction, `CandidateFromLimits.force` (85) is `SpacetimeGluing.smoothExtension 1 (tracedResidual ...)`; `force_eq_activated_residual` covers 0≤t<1, `force_boundary_jets` fixes terminal derivatives, and `force_zero_from` gives zero for t≥2. `SpacetimeGluing.smoothExtension` (334) glues to `SpatialBorelExtension.rightExtension`; that module's `templateBound` (127), `localScale` (185), `scale` (192), and `extension` (275) involve compact-bound and scale choices and a Taylor–Borel sum. Future values are not determined just by incoming jets.

**Important retained-contract limitation:** frozen `Main.Data` is a projection/weakened contract of Witness, and `selected := Classical.choice data_nonempty` selects one whole **Data**. It does not retain the compactForcing, the equation identifying a periodic force with its periodization, the literal `CandidateFromLimits.force` definition, or a shutdown-at-2 field. Therefore do not rewrite `d.forcing` as that constructor formula or claim `d.forcing(t,x)=0` for t≥2 merely by unfolding Data. Data gives an existential finite future support endpoint via CandidateProperties, not the numeral 2. Nor does the original Witness proposition itself identify its two existential force components with one another.

The prescribed frozen selection is kept unchanged, rather than silently replacing it with a strengthened wrapper. What **is** enough for this task: on 0<t<1, CandidateProperties fixes `d.forcing=R₁(u,p)` exactly; global smoothness and `d.jets` give the actual terminal values and derivatives. For a fixed schedule, changing a permissible smooth force cannot change its incoming residual. The new checked theorem proves equality on (0,1); endpoint/all-jet equality of such forces also follows by smoothness and uniqueness of incoming limits, but that further composition is not a new theorem here. No equality for t>1 follows.

Thus extension selection is **not** a knob for cancelling terminal annular curl. It is also not the main numerical obstacle at T: replace its representation by any genuine local extension using the new certificate below. The substantial unresolved dependence is the retained schedule and upstream fields.

## 3. New checked certificates and precise hypotheses

Namespace: `UnforcedRestart.Round3.WitnessFeasibility`. Import: frozen `Main.lean` only; Main imports `NavierStokes.ActualCandidateAssembly`.

| Declaration in `Certificates.lean` | Classification and exact scope |
|---|---|
| `selected_force_eq_residual` | **Checked actual-candidate theorem.** For t∈(0,1), every x, the selected forcing equals the residual of Main.velocity/pressure of its own schedule. No endpoint PDE assertion. |
| `same_schedule_force_eq` | **Checked uniform actual-record consequence.** d,e:Data and d.schedule=e.schedule imply their forces agree at every (t,x), 0<t<1. Does not compare different schedules or arbitrary candidate fields. |
| `extension_jet_unique` | **Conditional calculus tool.** e,g:OneSidedExtension f x, f:VelocityField, any n. Their full n-jets at (1,x) agree. Proof uses `OneSidedExtension.jet_tendsto`, `past_filter_neBot`, Hausdorff limit uniqueness. Does not assume f smooth at 1 or that its jets vanish. |
| `boundaryLimits_choice_independent` | **Conditional constructor/proof-irrelevance tool**, not analytic progress: changing proofs of AwayExtensions leaves boundaryLimits unchanged (`rfl`). The preceding theorem, not this proof-irrelevance fact, permits genuinely different extension functions. |
| `selected_terminal_jet_eq_extension` | **Checked actual-candidate specialization with explicit extension hypothesis.** For x with representative y≠0 and **any** e:OneSidedExtension of the actual cutResidual ASum BSum PSum at y, the selected n-jet at (1,x) equals the n-jet of e.value at (1,y). No assumed equality with the desired terminal tensor is an input. This removes dependence on the classically chosen extension *representation*, not on the selected fields. |

The existing `Main.terminal_origin_jets` remains the narrow checked unconditional terminal vanishing result. New work proves no nonzero terminal component and no whole-cell vanishing identity. No conjecture is promoted to a theorem.

## 4. Feasible analytic/evaluation certificates

### Preterminal finite-prefix reduction — source theorem plus unformalized specialization

`SolenoidalDiagonal.potentialSum_eventuallyEq_partial` (59) is an existing **germ**, valid for any component sequence when a→∞, q is continuous at z and q(z)>0. `PhysicalWaveSum.physicalQ_pos/smoothAt` and SelectedSchedule supply these for every selected preterminal point. Hence each outer sum agrees locally with a finite prefix, simultaneously for all derivative orders; `iteratedFDeriv_eventuallyEq` (112) licenses derivatives. This is stronger than an uncontrolled truncation experiment.

Moreover doubling and a0≥1 give a_j≥2^j by induction (ordinary deduction, not newly formalized). On a neighborhood with q≥q_min>0, any N with 2^N q_min>1 kills **all** j≥N there via `SmoothCutoffs.scaledCutoff_zero_of_one_le`. This gives a schedule-uniform tail cutoff once an effective positive q_min is supplied. On a compact slab strictly below 1 such a minimum exists by positivity/continuity; an existential minimum is not a numerical lower bound. This applies only to the **outer** diagonal sum: the retained finite stages themselves contain non-effective profiles, inverses, integrals and inner Borel schedules. Their actual first N schedule integers and input-function jets are still not certified numerical data. No fixed positive-q cutoff across the singular endpoint is inferred.

### Terminal local-extension certificate — now checked as an interface

For y≠0, supply an explicit smooth local expression E for the actual cut residual, an open neighborhood of (1,y), and proof of equality on its t<1 portion. `selected_terminal_jet_eq_extension` then identifies its jets with the selected force. This works even if the selected extension was opaque. The still-missing task is to **derive E from actual ASum/BSum/PSum germs**, with every localization term, and evaluate or bound its first spatial jet. Assuming the sign of that jet would merely restate the goal.

For U=curl(χA)+χB and P=χPSum, R₁(U,P)=U_t+DU(U)−ΔU+∇P. A straightforward full-jet evaluator for its spatial curl would require, conservatively, A derivatives through order 4, B through order 3, P through order 2, plus χ through order 4 and mixed time/spatial derivatives. One can reduce pressure requirements after proving curl∇P=0 on the smooth extension. These are derivative-count diagnostics (unformalized), not supplied bounds. Activation before the eventual-one regime also requires β′U and (β²−β)DU(U); β is one for t≥3/4, with a one-germ for t>3/4. Restart t0=1/2 is not wholly in that regime.

### Curl and Fourier certificate contracts — conditional ordinary analysis

Write J₁(x)=the selected first full force jet at (1,x). For spatial directions v_i=(0,e_i), the repository curl convention gives components

`(J₁(v₁)₂−J₁(v₂)₁, J₁(v₂)₀−J₁(v₀)₂, J₁(v₀)₁−J₁(v₁)₀)`.

This matches `SpatialCurl.curlLinear` and `curlLinear_apply_zero/one/two` (29–44). The restriction/coordinate adapter is ordinary calculus here, not a new Lean curl theorem. If each of the two derivative components in one difference is enclosed with error ε, its curl error is at most 2ε. A rational interval excluding zero is a usable nonvanishing certificate; a floating-point negative search is not a zero identity.

Normalize on Q=[0,1]³, volume 1: `f̂(k)=∫Q f(1,x) exp(−2π i k·x) dx`, k∈ℤ³. If a certified approximant g satisfies ∫Q|f−g|≤ε, then |f̂(k)−ĝ(k)|≤ε, plus the certified quadrature error for ĝ. For k≠0, periodic gradients have coefficients parallel to k; certify a nonzero component of k×f̂(k) (error ≤|k|ε in Euclidean norm), or a nonzero divergence-free test pairing. At k=0 the coefficient is the mean, with this normalization. Integration by parts and periodicity give `curl(f)^∧(k)=2π i k×f̂(k)` under spatial smoothness. These are **conditional calculus tools stated in ordinary analysis**, not formalized adapters or evaluated coefficients. Smoothness alone yields finite norms, not an effective quadrature modulus/error bound.

No certified nonconstant coefficient, derivative bound, or selected annular sign enclosure exists in this pass. The mean-zero argument in MeanTopology remains a separately documented **unformalized deduction**, not a newly checked Fourier value. Mean-zero is not vanishing solenoidal projection.

## 5. Whole-cell coverage and universal reasoning

Use y=x−integerShift(round x), not derivatives of the discontinuous representative map. `MixedPeriodicAssembly` supplies local separated-copy germs and jet transport; these—not nonlinear superposition—justify evaluation at representatives.

* y=0: selected terminal jets vanish by the frozen theorem (lattice-translate coverage follows from the representative formula and d.jets).
* Plateau r²<1/32, |y2|<1/8: χ has the one-germ, so cut residual has the original-residual germ. Only the origin has the supplied vanishing-joint-jet conclusion; do not make the whole plateau terminal-flat.
* Localization annulus/caps: support cylinder r²≤1/16, |y2|≤1/4 minus plateau. This includes radial transitions, axial caps and their intersections. No actual first-jet sign/zero certificate derived. It is not the correction iteration's shrinking active annulus.
* Support exterior and boundary: χ vanishes on the open exterior. Residual zero germs there, then smooth-extension continuity to boundaries, offer exact zero certificates independent of a. Carrying this through d.jets, all derivatives and seams has not been newly formalized here; the future all-time support claim of a particular constructor must not be assigned to Data without a bridge.
* Lattice translations/cell seams: use separated copies; seams do not authorize differentiating round. No uncovered transition region can be dismissed by an axis formula.

Universal-in-witness reasoning is possible and preferable: compact divergence identities, pressure-gradient curl cancellation, localization product identities, exterior zero germs, and one-sided limit uniqueness can hold for every permitted record. The new extension certificate is one such usable bridge. However no proof here makes **different outer schedules or different upstream profiles** have identical annular residuals. The fixed actualProfile is shared by all Data, while a is selected per Data. Universal nonvanishing would need structural signs/identities independent of those allowed a-values, not arbitrary replacement parameters.

## 6. Exact-removal scope and next decision gate

**None of the new conclusions rules out exact removal on any terminal slab.** They isolate the invariant target, not its sign. A certified nonzero terminal curl at one x, using smooth force continuity (not endpoint velocity regularity), would exclude every sufficiently late terminal absorption slab and hence any exact absorption interval ending at 1. A nonzero preterminal value only excludes slabs containing that time. Even whole-cell zero curl and mean at t=1 do not establish a gradient identity throughout a terminal interval. Literal f=0 and absorbable f=∇φ are different: the latter needs periodic, suitably jointly smooth φ and pressure p−φ.

Smallest useful next gate: produce an actual one-sided cut-residual extension formula at a nonzero localization representative and a rigorously bounded antisymmetric spatial first jet. Alternatively prove a whole-slab identity uniform over the allowed witnesses. The new theorem permits using a convenient explicit extension rather than evaluating Classical.choice. Without that identity or certified input representations, **do not spend numerical effort sampling an invented h, threshold, profile or schedule as the actual candidate**. Symbolic computation or interval code tested on separately labeled toy inputs may be useful tooling, but no such experiment was performed here.

## 7. Accepted source/declaration/axiom/command manifest

Focused run (both compiler exits 0):

```sh
python3 Research/UnforcedRestart/Round3/WitnessFeasibility/check.py
```

Evidence: `Research/UnforcedRestart/Round3/WitnessFeasibility/out/certificates-v6ayi6z_/` with `Main-command.json`, `Certificates-command.json`, `Main.log`, `Certificates.log`, `result.json`. The result records source, tool, pinned compiler, resolver, log and all generated output hashes and exact commands/environment. `Certificates.lean` SHA-256: `89f21ae88123d46f07eedaaf8c09216f98bbeb1111c73ae660c29dfc291a9d85`. Sources: frozen Main plus Certificates. Mathematical declarations: Main's eight previously printed definitions/theorems, and exactly the five Certificates declarations listed above. All printed closures are contained in `{propext, Classical.choice, Quot.sound}`.

The runner compiles the frozen Main first into a **new role-local module path**, then Certificates; it imports no mutable worker output. Direct installed Lean 4.34.0-rc2 with `-j1 -DautoImplicit=false -DwarningAsError=true`; env -i, LEAN_NUM_THREADS=1, LEAN_SRC_PATH absent. Resolver starts at this run's new lib, then the source-built external roots from `snapshot/external-evidence.json`; no worktree .lake or cache fallback. Each compiler has one CPU, 6 GiB, zero swap, 32 tasks, 600 seconds. No Lake invocation, dependency rebuild, baseline/config edit, commit or push.

**Retained failed attempt:** `out/certificates-vcevkh_s/`: Main exit 0, Certificates exit 1. Strict checking caught the letI style warning, deprecated dif_neg, and an unnecessary tactic after simplification closed a proof-irrelevance goal. That failed log's compiler-generated sorryAx output is rejected, not accepted mathematics. The source was repaired without option suppression; the next unique run passed. No failed objects are imported in acceptance.

This is **focused named-export checking**, not a fresh generated-helper/imported-environment aggregate audit. Frozen Round1/2 clean acceptance is unchanged; no broader Round3 acceptance is claimed. `source-manifest.json` supplements the compile result with accepted-source hashes and audited source/declaration locations. All 24 audited project-source hashes matched their source-built external checkout counterparts. Read-only `git rev-parse HEAD`, `git diff --exit-code 597692fa5d55e07d810b2d96ead1a67972585425 --`, and `git diff --cached --exit-code` exited 0; HEAD remains the baseline and tracked/index diffs are empty. These are not a rerun of the frozen 2,878-file preservation audit. The installed compiler/core/runtime and host remain trusted inputs.
