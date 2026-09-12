# Round5 — actual selected-force curl discrimination

Status: source-grounded plan and three read-only investigation assignments. No new curl decision is claimed; integration follows investigation reports. This session has no subagent-dispatch tool: the assignments below are ready for dispatch, not claims that independent agents have run.

## Preservation and inherited result

Authorization covers only new `Research/UnforcedRestart/Round5/` and `docs/unforced-restart/round5/` work, plus unique external validation outputs. Original Lean, configuration, dependencies, Round1–4 sources, documentation and receipts remain read-only. No commits, refs, index writes, pushes, dependency operations, blanket builds, or filesystem immutability changes. The supervisor's verified archive is `/home/velvet/research-snapshots/research-and-companion-20260912T192848Z/research-manifest.json`; do not recreate it or rerun historical receipt writers.

Initial HEAD is `597692fa5d55e07d810b2d96ead1a67972585425`. The concurrent documentation ref described in Round4's SUPERVISOR-REF-ADDENDUM already exists; preserve the current refs, not an obsolete pre-addition list. Repository README and repository instruction-file search were read (no AGENTS.md found). Round3 FINAL-REPORT, STATUS-ADDENDUM, CurlGeometry report, Round4 FINAL-REPORT and SUPERVISOR-REF-ADDENDUM were read. Round3's missing-mean status is historical: the literal source `Round4/Integration/Assembly.lean` proves selected force cell mean zero for all `t ∈ [0,1]` and all components, under ordinary coordinate-cube Lebesgue volume. No Round4 STATUS-ADDENDUM exists in the directory listing.

## Literal binding (mandatory for every report and theorem)

Use `d := UnforcedRestart.Round3.WitnessFeasibility.selected` and `f := d.forcing`. This is the *record* selected by `Classical.choice data_nonempty`, not a newly chosen witness of ActualCandidateAssembly.selected_witness.

Set `a := d.schedule`, `A := WitnessFeasibility.potentialSum a`, `v := WitnessFeasibility.directSum a`, `p := WitnessFeasibility.pressureSum a`. Keep `d.ea`, `d.eb`, `d.ep`, `d.selectedSchedule`, `d.candidate`, `d.smooth`, `d.jets`. Viscosity is one, terminal time one, spatial periods one. Budget is selectedBudget (definitionally zero); threshold is selectedThreshold, with selectedThreshold_geometry; h is CorrectionInitialization.ActualPrimary.h. Do not supply numerical h, threshold, profile or schedule values.

Source chain:

* `Round3/WitnessFeasibility/{Main,Certificates}.lean`: bindings; actual PDE residual equality on `(0,1)`; same-schedule force equality; extension-jet uniqueness.
* `ActualCandidateAssembly.lean`: selected_witness → witness → GermCandidateAssembly.exists_candidate_witness_of_finite_stages → `E.exists_schedule ... 1`. The same three stage sequences and schedule are retained.
* `MixedCandidateWitness.SelectedSchedule`: positive natural scales, doubling, strict monotonicity, divergence to infinity, `1/a_j < qbig`, ThreeSmoothSums, VanishingJointJets. These are not exact residual vanishing on an open slab, nor an effective evaluator.
* `SolenoidalDiagonal.{cutStage,potentialSum}`: actual tsum of `scaledCutoff (a_j) (physicalQ h) • stage_j`. `potentialSum_eventuallyEq_partial` supplies an existential common-neighborhood finite prefix at positive q. Retain derivatives of these q-dependent cutoffs, including those of the zeroth stage.
* Zeroth A is TailGaugePotential.finalPotential + initialPotential; initialPotential includes initial waves and stream means. Positive A includes particular + signed + stream means. Direct v consists of actual angular mean stages. Zeroth p is FinalSlowBase.pressure + initialPressure; positive p includes particular + signed + pressure means. `ActualCandidateAssembly.exteriorStages`, `positive_stage`, `stageRealizations`, `physicalData` describe the literal sequences, not a substitute base.
* TailGaugePotential.radialNormalize anchors the swirl primitive at physical s=1. Curl-free gauge changes before cutting need not be harmless after cutting; retain the actual anchored potential and all slow orders.

## Coordinates and target propositions

Space is repository Euclidean `Space`, coordinates indexed by `Fin 3`. Set

`D_i f_j(t,x) := (fderiv ℝ (fun y => f (t,y)) x (coordinateVector i)) j`.

Use `C(t,x) := NavierStokes.SpatialCurl.spatialCurl f (t,x)`, exactly

`(D_1 f_2 − D_2 f_1, D_2 f_0 − D_0 f_2, D_0 f_1 − D_1 f_0)`.

These are physical Cartesian derivatives, not cylindrical partials or derivatives in coordinate-measure variables. Cylindrical reductions must prove their frame/Jacobian conversion. Never differentiate round/nearestIndex/representative.

Strong zero target Z:

`∃ τ : ℝ, 0 ≤ τ ∧ τ < 1 ∧ ∀ t, τ < t → t < 1 → ∀ x : Space, C(t,x)=0`.

Prefer an explicit fixed τ if the proof supplies one. A τ depending only on the already fixed selected record is acceptable if certified existentially. An all-space terminal value at t=1 alone is not Z.

Strong obstruction target N:

`∀ t0 : ℝ, t0 < 1 → ∃ t : ℝ, max 0 t0 < t ∧ t < 1 ∧ ∃ x : Space, C(t,x) ≠ 0`.

Proof routes: (i) genuine selected unequal terminal entries at some x plus selected_curl_continuous gives nonzero curl at every sufficiently late time at that x, hence N; (ii) a selected time/space sequence tending to 1 with proved total nonzero curl; (iii) analytic contradiction from an assumed all-space zero terminal slab, provided the source-specific PDE/uniqueness hypotheses are all established. Classical negation of Z can give N but is not itself a producer of that negation.

Weaker W: `∃ t ∈ (0,1), ∃ x, C(t,x) ≠ 0`. W obstructs absorption only on intervals containing such a time (and a neighborhood by continuity). It does not exclude later terminal slabs. Conditional unequal-entry lemmas or generic curl identities are supporting infrastructure, not main success.

Z plus Round4 mean zero removes the curl and constant-mode obstructions. Actual pressure absorption still needs a smooth periodic potential φ with f=∇φ on that same slab, including joint time regularity; pressure becomes p−φ. Do not label curl zero alone a completed pressure construction. No comparator lifespan, restart at 1/2, or growth-transfer conclusion follows automatically.

## Complete geometry and contribution map

Let r²=x₀²+x₁², z=x₂, χ(x)=cutoff(16r²) cutoff(4z), as in SpatialLocalization. Let ρ=timeSwitch. On a separated copy,

`U = curl(χ A) + χ v = χ(curl A+v) + ∇χ × A`, `P=χp`.

The actual local activated velocity and pressure are ρU and ρP. The force residual is `∂t(ρU) + ((ρU)·∇)(ρU) − Δ(ρU) + ∇(ρP)`. Its curl must retain ρ′ curl U and the nonlinear coefficient ρ². For t>3/4, joint eventual-one activation germs eliminate the switch defects; never do this on the entire restart interval [1/2,1).

| Region | Source reduction and remaining work |
|---|---|
| Plateau r²<1/32, |z|<1/8 | χ=1 as a germ. MixedPeriodicAssembly.cutResidual_eventuallyEq_original reduces to the original *full mixed* residual; no source theorem says its curl is zero there. |
| Radial transition 1/32<r²<1/16, |z|<1/8 | Include ∇χ×A, temporal/viscous derivatives and all nonlinear cross terms. Potentially exploit actual heat-exterior identities, not arbitrary heat profiles. |
| Axial caps r²<1/32, 1/8<|z|<1/4 | Include axial χ derivatives and endpoint physicalQ effects. Do not infer the cap is active: schedule cutoffs can kill fields; prove the regime for this a. |
| Radial/cap overlap 1/32<r²<1/16, 1/8<|z|<1/4 | Both factors vary; mixed derivatives cannot be discarded. |
| Interfaces and outer boundary | Inner interfaces require coverage/continuity from adjacent regions, not extrapolation from the plateau alone. Outer boundary can be approached from strict exterior using selected-force smoothness. |
| Strict exterior r²>1/16 or |z|>1/4 | Round3 LocalizedForce has generic zero germs of cutResidual and terminal_boundary_jets_zero_outside. Selected specialization/periodic transport remains a possible auxiliary task, not main success. |
| Origin and lattice copies | terminal_origin_jets and terminal_curl_origin are checked at origin. Periodicity transports to lattice copies; this does not cover plateau or transitions. |
| Other copies/seams | supportCylinder lies in the cube of half-width 1/4; `innerCube (1/4)` actually means every |x_i|<3/4. representative is nearest-lattice translation with coordinates of absolute value ≤1/2. Use periodicity and local single-copy germs. |

Distinguish this fixed localization annulus from the iteration's shrinking `ActualPolarCoverage.active`, determined by profileRadius / physicalQ. ActualCandidateAssembly PhysicalStage.exterior and exteriorStages eliminate correction germs only under their precise physical-domain and non-active hypotheses. The base potential/pressure survive in the exterior and the diagonal cutoff still acts on stage zero. Prove all inequalities before invoking an exterior formula.

Pressure: curl ∇(χp)=0 by C² regularity. In a split residual χR + p∇χ + other terms, ∇χ×∇p from curl(χR) cancels ∇p×∇χ from curl(p∇χ). A sign of either term alone is meaningless. Source pressure still matters when using source PDE/exterior identities to simplify temporal, viscous and nonlinear contributions.

At t=1 use d.jets or genuine OneSidedExtension germs and Round3 Certificates, not pointwise evaluation of a possibly singular terminal velocity. Round3 CurlGeometry.terminalEntry has derivative-direction index first, output-component index second; unequal cyclic entries must be *proved*, not assumed.

## Three assigned read-only investigations

Assignments are in [INVESTIGATIONS.md](INVESTIGATIONS.md). Each investigator reads original sources only; no Lean/source/config/dependency edits and no builds. Return a report in the orchestration response; the integrator alone may save it under Round5. No new global witness selection. Each report must distinguish established theorem, complete unformalized analytic proof, conditional route and unresolved gap, and state exact quantifiers and source hypotheses.

1. **A — terminal radial/exterior analytic producer:** seek actual nonzero terminal curl via anchored heat-exterior reduction, or identify exact failure of that route.
2. **B — caps, active annulus and selected schedule:** seek arbitrarily-late nonvanishing via same-schedule scale regimes, or a genuine all-region zero slab.
3. **C — global analytic discrimination:** test PDE/compactness/unique-continuation routes to N or Z; independently audit total pressure/activation cancellation and the logical strength of A/B proposals.

## Integration and validation

Integrator compares complete returned proofs and chooses the strongest genuine route: N or Z first, W second with exact time scope. Do not choose a route just because its generic calculus is easy. Before Lean implementation write a short DECISION identifying the actual producer, all remaining adapters and its quantified conclusion. If none has a producer, report unresolved explicitly; auxiliary support/continuity identities do not change that decision.

All new Lean belongs under Research/UnforcedRestart/Round5. Reuse `/home/velvet/research-builds/unforced-round2-clean-20260909T221339Z` read-only and the exact frozen research objects resolved by existing provenance receipts. Consult Round3 ValidationRepair README and Round4 repair manifests for resolver/compiler pins and strict workflow, without invoking historical writers. No blanket rebuild. Focused new module compilation uses unique output roots, pinned Lean, `-j1 -DautoImplicit=false -DwarningAsError=true`, one thread, existing 600-second / 6-GiB-no-swap limits. Preserve diagnostic failures as failures. Record commands, direct-import provenance, hashes and printed axiom closures; reject sorry/admit, new axioms, unsafe/native shortcuts and weakened checks. Standard inherited closures propext/Classical.choice/Quot.sound are not new axioms. Report the bounded validation trust scope accurately.

This planning pass runs no Lean compiler and asserts no new theorem. No redundant archive or full filesystem freeze is needed.
