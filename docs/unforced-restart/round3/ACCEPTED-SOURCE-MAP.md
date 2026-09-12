# Accepted proof/source map — completed Round3 integration

Companion: [DECISION](DECISION.md), [machine validation manifest](VALIDATION-MANIFEST.json). Paths below are repository-relative. Declaration names are under `UnforcedRestart.Round3.<Role>` unless stated otherwise. The manifest enumerates every printed export, source line, axiom list, source hash, accepted log and output hash.

**Acceptance means the exact statement in the source, with its hypotheses**, not every prose deduction in its role report. There are five accepted modules, 36 distinct named exports, of which 28 belong to the four completed additions. No new mathematical declarations are introduced by this integration.

## A. Actual-selected interfaces and theorems

| Source | Exports / exact scope | Accepted evidence directory |
|---|---|---|
| `Research/UnforcedRestart/Round3/WitnessFeasibility/Main.lean:14–56` | `potentialSum`, `directSum`, `pressureSum`, `velocity`, `pressure`; `data_nonempty`, `selected`, `terminal_origin_jets`. Frozen coherent Data selection, all-order origin flatness. Data definition at line 29 inspected; its discarded Witness conjuncts are not retained facts. | `WitnessFeasibility/out/certificates-v6ayi6z_` (wrapper replay) |
| `Research/UnforcedRestart/Round3/WitnessFeasibility/Certificates.lean:10–49` | `selected_force_eq_residual`: all x, t∈(0,1). `same_schedule_force_eq`: any two Data with equal schedule, same time range. `selected_terminal_jet_eq_extension`: nonzero representative, supplied genuine extension of the actual cut residual, any n. No sign/zero premise discharged. | `WitnessFeasibility/out/certificates-v6ayi6z_` |
| `Research/UnforcedRestart/Round3/CurlGeometry/Main.lean:11–92` | `terminalEntry` definition; `terminalEntry_eq`, `terminal_curl_component`: all x and spatial indices. `terminal_curl_origin`. `terminal_curl_ne_zero`: **conditional on unequal entries**. `selected_curl_continuous`: all spacetime. `late_inner_curl`: 3/4<t<1, x in innerCube(1/4). | `CurlGeometry/out/strict-0m49nclb` |
| `Research/UnforcedRestart/Round3/MeanTopology/Main.lean:27–118` | `compactVelocity`; `compactVelocity_zero_outside`, `compactVelocity_zero_germ`, `compactVelocity_agreement`; `compactVelocity_smooth_slice` for (0,1); `compactVelocity_divergence_free` for [0,1); `compactVelocity_compact_support` for every t; `selected_compact_momentum_zero`, `selected_compact_transport_zero` for (0,1); `selected_force_mean_continuousOn` for every finite [a,b]. | `MeanTopology/out/strict-mb_z5gut` |

All evidence directory prefixes above are `Research/UnforcedRestart/Round3/`. Full compiler commands and exact source hashes are in the JSON manifest, not inferred from directory names. Wrapper replays are dependencies, not additional distinct exports.

## B. Generic/conditional tools — not closed force-removal claims

| Source | Accepted tool | Why not a decision certificate |
|---|---|---|
| `WitnessFeasibility/Certificates.lean:23–35` | `extension_jet_unique`, `boundaryLimits_choice_independent` | The former proves uniqueness from genuine agreeing germs. The latter is proof irrelevance (`rfl`), not an effective evaluator or independence of different schedules. |
| `CurlGeometry/Main.lean:19–24` | `spatial_slice_derivative` | Requires joint differentiability; the actual specialization is separately checked. |
| `MeanTopology/Main.lean:14–23` | `compact_component_integral_zero` | Compact smooth divergence-free whole-space field; does not apply to arbitrary periodic constant fields. |
| `MeanTopology/Main.lean:122–125` | `periodic_potential_component_mean_zero` | Necessity for C¹ unit-periodic potentials only, not sufficiency. |
| `LocalizedForce/Main.lean:10–59` | `cutResidual_zero_outside`, `cutResidual_eventually_zero_outside`, `terminal_boundary_jets_zero_outside` | Universal literal cut-residual construction. Last theorem requires away extensions and representative strictly outside closed supportCylinder. All n; not spatial-boundary vanishing. Closed selected-force specialization is not a named export. |

The shortened source paths in this table start `Research/UnforcedRestart/Round3/`. LocalizedForce accepted evidence is `LocalizedForce/out/strict-_w9_cwc3/`.

## C. Directly cross-checked upstream definitions and producers

These are baseline **read-only source anchors**, not new Round3 declarations or a new imported-closure audit. Their hashes and byte equality to the external source-built checkout are recorded in the integration manifest.

| Baseline source | Anchor and use |
|---|---|
| `NavierStokes/ProblemStatement.lean:84–118` | Viscosity-one residual; existential finite future force support; SpeedUnboundedAtOne; CandidateProperties (periodicity, interior PDE, divergence, speed growth). |
| `NavierStokes/ActualCandidateAssembly.lean:200–204,493–521,1016–1074` | Anchored full zeroth potential; positive particular/signed/mean terms; direct angular sequence; three shared sums in Witness; explicit H³/decay/compact conjuncts discarded by Data. |
| `NavierStokes/ActualCandidateConstruction.lean:110–115`; `NavierStokes/ActualCarrierGeometry.lean:26–34` | Budget zero; threshold is startingThreshold 0, a max with a selected geometric threshold, not a supplied numeral. |
| `NavierStokes/MixedCandidateWitness.lean:25–33` | SelectedSchedule positivity, doubling, divergence to infinity, three smooth sums and original residual joint limits. Not an evaluator. |
| `NavierStokes/SolenoidalDiagonal.lean:32–69` | Literal tsum, partialPotential, common-neighborhood zero tail and finite-prefix germ. Positive q needed; no endpoint truncation inferred. |
| `NavierStokes/JointResidualLimits.lean:73–155` | OneSidedExtension domain/smoothness/past agreement; AwayExtensions is a Prop; all-jet limit; boundaryLimits zero at origin or chosen Taylor tensor; nontrivial past filter. |
| `NavierStokes/MixedPeriodicAssembly.lean:43–61,281–358` | Cut velocity includes χB outside curl; residual locality; cutResidualExtension from three field germs; periodic boundary tensors at representatives. No arbitrary terminal velocity evaluation. |
| `NavierStokes/SpatialLocalization.lean:39–111` | χ=cutoff(16r²)cutoff(4x₂), closed K and open plateau, compactness and coordinate bounds. |
| `NavierStokes/TimeLocalization.lean:26–30,69–93` | Both fields activated, strict late eventual-one germs. |
| `NavierStokes/TailGaugePotential.lean:25–29,371–391` | Physical radial anchor, normalized primitive, all slow orders, same uncut curl, away extensions. Not gauge invariance after localization. |
| `NavierStokes/CandidateFromLimits.lean:83–117` | Particular smooth extension force, preterminal activated-residual equality and shutdown at 2. Not definitionally the force exported by Data. |
| `NavierStokes/PeriodicIntegration.lean:26–48` | Product-coordinate unit cube, measure and Bochner integral; coordinate directional partials. |
| `NavierStokes/SpatialCurl.lean:29–52` | Curl convention used in antisymmetric first-jet formula. |
| `NavierStokes/R3/CompactTimeIntegral.lean:60–165` | Interior differentiation under a common compact spatial support; C¹ slab specialization and time derivative adapters. Source-checked mechanism for the next bridge, not its completed specialization. |
| `NavierStokes/SmoothParameterIntegral.lean:28–119` | Genuine integrated jets with local integrable majorants; supplementary generic interface, no effective majorants extracted. |

The longer choice/provenance chain is documented by [WitnessFeasibility](WitnessFeasibility.md) and its `source-manifest.json`. This integration does not claim exhaustive evaluation or inspection of every transitive choice.

## D. Analytical deductions and missing producers (not formal acceptance)

| Deduction / target | Actual prerequisites | Missing formal or mathematical step |
|---|---|---|
| Selected exterior jets zero | d.jets + LocalizedForce terminal tensor theorem | Closed selected specialization; boundary continuity composition separately. |
| Selected force mean zero on [0,1] | Checked compact momentum/transport, common support, joint local smoothness, actual residual and periodic germs, checked mean continuity | Time differentiation, Laplacian/pressure integrals, periodization integral and coordinate-measure transport, endpoint composition. |
| Periodic potential on slab | All-space curl zero and zero mean at **every time of one slab**, global smooth f | Actual slab curl producer; formal smooth potential/cycle argument; pressure correction and comparison. |
| Obstruction to any terminal absorption slab | Actual nonzero terminal antisymmetric entry + checked curl continuity | Actual nonzero jet producer; interval-exclusion composition. |
| Localization/vorticity/gauge formulas | Actual full A/B/P, smooth local germs, χ and β | Product/commuting-derivative formalization and actual total jet evaluation/sign or cancellation. Individual contributions do not certify total curl. |
| Perturbative route | Actual g=Πf and u coefficients; fixed datum and restart; projected viscous response plus nonlinear remainder | Nonzero effective-force certificate if claiming persistence, evolution estimates, growth-relative budget, existence/lifespan/admissibility. |

## E. Earlier generic infrastructure and validation tooling remain separate

`Research/UnforcedRestart/strong-norm-growth-transfer/Main.lean` was source-read: `speed_transfer` needs a pointwise relative error estimate; its generic evaluation budget is not PDE stability. Its axis version has an explicit axis-growth premise. None is newly specialized/accepted here. Earlier Round1/2 acceptance remains at its frozen scope.

Role `check.py`, `LocalizedForce/manifest.py`, `Integration/focused.py`, and new `Integration/reconcile.py` are **tools, not mathematics**. Existing accepted logs retain strict compiler commands and failed attempts separately. The new reconciliation tool verifies current source/log/output hashes, printed export coverage and axiom whitelist, source-built checkout equality, and read-only preservation. It does not compile, build dependencies, run numerical experiments, or claim aggregate semantic validation.
