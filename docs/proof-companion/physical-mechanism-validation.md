# Physical mechanism — v2 claim ledger and bounded dependency map

**Qualified handoff; documentation/source inspection only.** Companion chapter [07](07-physical-mechanism.md) adds corrected physical exposition and the optional bounded approximation/pressure mapping. No port, merge, build, installation, network access, commit, ref/worktree mutation or B successor was undertaken. Follow-up preservation checks used read-only Git queries. This is not fresh elaboration, an axiom audit, kernel validation, reviewer approval or a complete human proof.

## 1. Authority, revisions and evidence

The current user authorized both exposition and dependency mapping, overriding the review plan's earlier proposal-only/P0 sequencing for these documentation deliverables. There is no separate preservation-only approval project. Existing `INPUTS.json`, source export and earlier evidence snapshots are the preservation anchors. The original authoring pass reported 16/16 companion hashes before its edits. At this follow-up's entry, 14/16 matched: only the already authorized README/SOURCE-MAP reading-link additions differed. Those two files need no further edits; their existing links resolve.

Only `07-physical-mechanism.md`, this ledger, and minimal reading links in companion `README.md`/`SOURCE-MAP.md` are in scope. Chapters 01–06, native/primitive plans and ledgers, historical research strategy, upstream export, all Lean/config files and Git state remain outside write authority.

| Revision | Role, not interchangeable witness identity |
|---|---|
| `597692fa5d55e07d810b2d96ead1a67972585425` | Historical chapters 01–04/source-map baseline; no recertification |
| `26e896edbdbe1215c0d50ddba24b2b6453646f5f` | Original refactored source at `/home/velvet/Desktop/NavierStokesAndEuler`; retained architecture for mapping and chapters 05–06 |
| `6da0731071d900b7a1cf3fb9c009aa7cf6bc6c7f` | Companion worktree anchor at `/home/velvet/worktrees/proof-native-control-20260912T185404Z` |
| `1d16509bec4609ae418e64842e81b8b0ac07dcc7` | Research selection/evidence anchor at `/home/velvet/worktrees/unforced-restart-20260909T202951Z` |
| `f9e8bc5b38b6e212696e8a30e3e91517af887bbd` | Newly inspected upstream export under `/home/velvet/upstream-strategy-f9e8bc5-9d96jtuy/upstream`; all upstream links here are commit-pinned |

Read review inputs: [FINAL-OVERVIEW](/home/velvet/upstream-strategy-f9e8bc5-9d96jtuy/FINAL-OVERVIEW.md), [PLAN](/home/velvet/upstream-strategy-f9e8bc5-9d96jtuy/PLAN.md), [REVIEW-DISPOSITIONS](/home/velvet/upstream-strategy-f9e8bc5-9d96jtuy/REVIEW-DISPOSITIONS.md). Their adoption gates are not satisfied by this draft.

Paper P: [new PDF](/home/velvet/upstream-strategy-f9e8bc5-9d96jtuy/papers/navier-stokes.pdf), [extracted text](/home/velvet/upstream-strategy-f9e8bc5-9d96jtuy/papers/navier-stokes.txt). The local PDF has 166 pages, metadata creation date 2026-09-08. Its inspected bytes have SHA-256 `0e779481c4da40bd28d1e642e1d8ca57447d129610df28dfa5a11e9af8ae228f` (recomputed in this follow-up). This checksum identifies bytes, not independently authenticated publication provenance; the metadata date is not an immutable revision identifier. Existing manifests associate the export with `f9e8bc5…`; this inspection does not authenticate that association against Git objects. Printed page 81 was independently extracted from the PDF and agrees with the text's energy identity. Decisive text inspected: §§2.2–3.3, pp.5–12; §6.1–6.2, pp.62–65; §7.1–7.4, pp.76–87, including (7.13), (7.16)–(7.22), (7.23)–(7.34), (7.39)–(7.42). Other final-theorem/localization references in the chapter are paper locators, not a fresh full proof audit.

The current [PDE adversarial verdict](/home/velvet/worktrees/unforced-restart-20260909T202951Z/docs/unforced-restart/strategy/timing-response/pde-adversarial-verdict.md) and decisive portions of the [source/strategy verdict](/home/velvet/worktrees/unforced-restart-20260909T202951Z/docs/unforced-restart/strategy/timing-response/source-and-strategy-adversarial-verdict.md) were also read: their qualified acceptance of finite-slab algebra does not establish selected excitation or persistence. This supplement changes no such disposition.

**Numbering distinction:** source comments in `PulseGrowth` cite older Lemma 8.5/Proposition A.4, and `TangentProjection`/`PrimaryODE` cite older equation (27). The new paper's corresponding pulse discussion is §7, notably (7.13), (7.22). This ledger maps formulas by their bodies, not by assuming old section numbers refer to the new PDF. The historical temporal viscosity rescaling in chapter 03 is also not silently replaced by the new paper's spatial rescaling with unchanged singular time.

## 2. Claim/source/imported-assumption register

“S” means inspected statement and decisive proof/definition body; “H” means human reconstruction; “P” means paper explanation. None means fresh Lean validation. All records carry their complete enclosing parameters and fields, not just the shorthand below.

| Claim | Support | Imported assumptions / open scope |
|---|---|---|
| PM-01: annular stress plus flat background error | P §3.2 pp.9–11, Prop.5.5; S `FinalSlowBase.residual_identity`, `error_jetRate` | Actual aligned profiles, Borel scales, finite identities, physical approach and radius bound. Identity alone defines an error; flatness needs the separate producer. No general background solver claimed. |
| PM-02: different radial/axial contraction; non-negligible viscosity | P §3.1 pp.7–8, §6 pp.62–65; H substitution of powers | Compact similarity regions away from endpoint coordinates; fixed h. Amplitude/wavelength powers suppress logs and edge weights. Slot time is a frozen-model coordinate, not a full physical clock symmetry. |
| PM-03: principal pressure-constrained ODE | S `TangentProjection.projected_balance`, `pressure_cancellation`, `normal_projectedRhs`; `PrimaryODE.ambientSolution_hasDerivAt` | Nonzero normal, continuous modal coefficients/source, frame `Kinematics`, closed slot membership. Residual source is not the final external force; exact ODE reconstruction is not full NS evolution. |
| PM-04: shear-energy identity | H dot product in chapter §3; P (7.22) p.81; S `MovingFrameODE.baseAction`, tangency and reconstructed derivative | Real homogeneous amplitude, correct cylindrical basis/matrix, nonzero normal. Normal term has zero work; rotation cancels algebraically. No separately located Lean theorem of the complete displayed identity, and no claim all tangent directions grow. |
| PM-05: growth then damping | S `PulseGrowth.netGrowth_sign`, slot sign proofs; `PulseCovariance.reference_envelope_gaussian_bounds`; P Lemma 7.4 pp.80–81 | Positive reference rate, threshold and slot length. Actual frame-error/kinematics and growing-mode estimates are additional inputs; reference midpoint sign is not an exact turning-time theorem for every actual component. |
| PM-06: tiny seeds and cutoff tails | P §2.2 p.6, §7.2 pp.77–81, (7.40) p.87; H Gaussian/exponential comparison | Nonzero homogeneous seed, chosen cutoff, fixed stage/order losses. Product rule leaves `(1−ψ)b+ψ′a`; these are flat tail terms, not a proof the complete external force is exponentially small. |
| PM-07: actual covariance and positive weights | S `PulseCovariance.PulseBounds.mass_lower`, `mass_upper`, `actualColumn_factorization`, `compact_actual_positive_inverse`; `ActualPrimaryCovariance.viewSum_covariance_factor`; P §7.3 pp.81–84 | Pointwise Gaussian bounds, compact cutoffs, tangent-direction estimates, strict cone, common-torus averaging, active labels and native strip. Source factorization explicitly retains `partitionFactor`; paper squared partition/coverage is not automatically transferred to every selected enlarged cell. |
| PM-08: correction/curl/localization leave smooth force | P §7.4 pp.85–87, §9 pp.100–115, §10 pp.116–125; S `CandidateFromLimits.tracedResidual_smooth`, `force`, `force_smooth` | Actual jointly smooth presingular fields and locally uniform limits of all residual derivatives. Correction iteration, exterior germs, localization and schedule producers remain imported construction debt. Only force extends, not singular velocity. |
| PM-09: “installed growth” clarification | P §§2–3; H PM-03–07; preserved research [central obstacle](/home/velvet/worktrees/unforced-restart-20260909T202951Z/docs/unforced-restart/strategy/CENTRAL-OBSTACLE.md) | Versioned correction of physical interpretation only. Does not retract valid selection/residual statements or rewrite historical evidence. |
| PM-10: no autonomous/deletion leverage supplied | H exact subtraction and `L_U U_t=F_t`; preserved [force report](/home/velvet/worktrees/unforced-restart-20260909T202951Z/docs/unforced-restart/strategy/force-response/FINAL-REPORT.md), [timing overview](/home/velvet/worktrees/unforced-restart-20260909T202951Z/docs/unforced-restart/strategy/timing-response/OVERVIEW.md) | One selected force/datum, physical unit torus, Leray retaining constants. Full selected propagator response, nonlinear feedback and lifespan bridge missing. Historical direct-source control is not total response; timing overview is explicitly provisional. No inference from raw point jets to projected signs. |
| PM-11: independent approximation/pressure value | S five complete new module bodies listed below | Completion-style class, not density equivalence with all distributional H³ fields. Whole-space cancellation, not a torus zero-mode theorem, selected-force deletion or arbitrary-data existence. |

Source bodies for PM-01–08 are linked beside the chapter formulas. Their source proofs have actual suppliers, but this targeted inspection does not audit the entire profile/correction dependency tree. In particular chapter 06's literal selected enlarged-label ranges and normalized numerical arrays remain **unproved, not disproved**. A new whole-domain finite-prefix estimate cannot retrospectively fill those numerical inputs or make constants uniform in stage/order.

## 3. Optional bounded mapping: approximation/pressure only

### Roots and mathematical contracts

Requested public roots:

1. `NavierStokesR3.H3Comparison.H3Approximation` in [H3Approximation][A]. It extends H¹ with ordered second/third L² jets and convergence of **one common compact-smooth sequence** through order three. No pointwise differentiability of the limit is imposed. `partial_toH1` keeps order `ddf j i`; `of_contDiff_compact` uses the constant sequence. This does not construct approximations for every externally defined H³ field.
2. `NavierStokesR3.H3PressureOrthogonality.pressure_pairing_zero` in [H3PressureOrthogonality][O]. Inputs: `H1Approximation w dw`, a.e. `Σ_i dw i x i=0`, scalar pressure `ContDiff ℝ 1 p`, and each `spatialPartial i p` in whole-space L². Output: `∫ Σ_i w_i ∂_i p=0`. No pressure integrability/normalization or compact limiting velocity is assumed.

Body chain: map the H¹ field to complex components → pass approximation derivatives through continuous tempered-distribution differentiation → establish curl-free pressure gradient using compact-test integration by parts and Schwartz approximation → Fourier divergence/curl relations → pointwise orthogonality off frequency zero → Plancherel → real representative integral. The singleton zero frequency is null in R³ L²; this is **not** permission to discard a constant torus mode.

### Exact direct project imports of the five proposed new modules

| Module (all under `NavierStokes/R3/`) | Direct project imports |
|---|---|
| [H3Approximation][A] | `R3.CompactEnergy` |
| [H3Comparison][C] | `R3.H3Approximation` |
| [H3PressureDistribution][D] | `R3.H3Comparison`, `R3.SchwartzCompactApproximation` |
| [H3DivCurlFourier][F] | `R3.WeakFourierUniqueness` |
| [H3PressureOrthogonality][O] | `R3.H3PressureDistribution`, `R3.H3DivCurlFourier` |

Direct Mathlib imports, exactly as inspected: A: `MeasureTheory.Function.L2Space`, `MeasureTheory.Function.LpSpace.Indicator`; C: none; D: `Analysis.Distribution.TemperedDistribution`, `Analysis.Calculus.LineDeriv.IntegrationByParts`, `Analysis.Calculus.FDeriv.Symmetric`; F: `Analysis.Fourier.LpSpace`; O: none. Prefix each with `Mathlib.`. Transitive Mathlib/compiler closure has not been validated or costed as a build.

### Retained dependency closure and adapters

A recursive lexical import traversal finds **19 project modules** in the literal upstream closure: five new roots/helpers, the eleven same-named retained dependencies below, plus upstream `PeriodicUniqueness`, `R3.ScalarEnergyBound`, `R3.CompactForceBound`. Only `R3.WeakFourierUniqueness` and `R3.ComparisonFourierSetup` are byte-identical between the two revisions in that closure. “Retain” below therefore means retain the refactor implementation, **not** claim unchanged upstream bytes.

For the proposed mixed closure, retain these project edges verbatim from refactor (all `R3.*` names have prefix `NavierStokes.`):

| Retained module | Direct project imports |
|---|---|
| `NavierStokes.ProblemStatement` | none |
| `NavierStokes.PeriodicIntegration` | `NavierStokes.ProblemStatement` |
| `R3.ProblemStatement` | `NavierStokes.ProblemStatement` |
| `R3.CompactEnergy` | `NavierStokes.SolutionDifference`, `NavierStokes.PeriodicIntegration`, `R3.CompactTimeIntegral`, `NavierStokes.ProblemStatement`, `NavierStokes.WithTopLemmas` |
| `R3.CompactTimeIntegral` | `R3.ProblemStatement` |
| `R3.CompactSchwartz` | `R3.ProblemStatement` |
| `R3.ComparisonSetup` | `R3.ProblemStatement`, `NavierStokes.SolutionDifference`, `NavierStokes.PeriodicIntegration` |
| `R3.ComparisonCutoffs` | `R3.ComparisonSetup`, `Common.Cutoffs` |
| `R3.ComparisonFourierSetup` | `R3.ComparisonSetup` |
| `R3.SchwartzCompactApproximation` | `R3.CompactSchwartz`, `R3.ComparisonCutoffs` |
| `R3.WeakFourierUniqueness` | `R3.CompactSchwartz`, `R3.ComparisonFourierSetup` |
| `NavierStokes.SolutionDifference` | `NavierStokes.ProblemStatement`, `NavierStokes.WithTopLemmas` |
| `NavierStokes.WithTopLemmas` | none |
| `Common.Cutoffs` | none |

Thus the candidate project closure is also 19 modules: five additions plus fourteen retained dependencies. This is a file/import map, not a proof that this mixture elaborates.

**Three necessary namespace adapters, confined to new files:** A, C and D each open `NavierStokes.PeriodicUniqueness (spatial_partial_contDiff)`. Refactor supplies that declaration in [SolutionDifference](../../NavierStokes/SolutionDifference.lean), imported by retained [CompactEnergy](../../NavierStokes/R3/CompactEnergy.lean). A future port would open `NavierStokes.SolutionDifference` instead; no old compatibility alias or wrapper edit is needed in the proposed design.

`H3Comparison` proves its own compact bilinear integration by parts using Mathlib; it does not call removed upstream compact-energy lemmas. `H3PressureDistribution` uses retained `SchwartzCompactApproximation.continuous_zero_of_compactSupport`; the inspected diff removes other convenience declarations but retains this producer. Retained `ComparisonCutoffs` delegates to `Common.Cutoffs`; no need to restore upstream bump implementation. The two byte-identical Fourier files retain their refactor dependencies, which are not thereby certified identical as a closure.

Upstream `ScalarEnergyBound` and `CompactForceBound` are absent at refactor and their architecture is consolidated in retained CompactEnergy. Do **not** add them just to recover upstream imports. No `H3Energy` or `ComparisonGronwall` call enters the five-module body/import closure; the separate energy migration to `GronwallInterior` is deferred, not repaired here.

### Public declaration inventory for the bounded family

Names below are source declarations, not elaborated `#check` results. Generated structure constructors/projections are part of each record's contract but not individually enumerated. Private helpers are excluded from public API, not from the source closure.

- **A / namespace `NavierStokesR3.H3Comparison`:** `smooth_compact_memLp`, `H1Approximation`, `toLp_comp`, `H1Approximation.map`, `H3Approximation`, `H3Approximation.partial_toH1`, `H3Approximation.of_contDiff_compact`.
- **C / same namespace:** `inner_toLp`, `integrable_inner_of_memLp`, `tendsto_integral_inner`, `H1Approximation.integral_inner_derivative`, `H3Approximation.integral_inner_laplacian`, `pressure_orthogonality`. The last theorem requires H¹ approximation of pressure itself; it is not the less restrictive requested O target.
- **D / namespace `NavierStokesR3.H3PressureDistribution`:** `ComplexTest`, `ComplexL2`, `ComplexDistribution`, `distribution`, `partial_continuous`, `compact_integration_by_parts`, `partial_partial_eq`, `partial_commute`, `gradient_compact_test_commute`, `derivative_toLp_apply`, `derivative_toLp_of_compact`, `H1Approximation.derivative_distribution`, `gradient_curl_free`.
- **F / namespace `NavierStokesR3.H3DivCurlFourier`:** `ComplexL2`, `ComplexDistribution`, `coordinate`, `coordinate_eq_inner`, `coordinate_temperate`, `coordinate_continuous`, `multiplier`, `multiplier_apply`, `integrable_coordinate_test`, `locallyIntegrable_coordinate`, `ae_sum_coordinate_eq_zero`, `ae_coordinate_eq`, `coordinate_conj`, `inner_eq_zero_of_coordinate_relations`, `fourier_coordinate_derivative`, `fourier_constant_ne_zero`, `fourier_divergence`, `fourier_curl`, `sum_inner_eq_integral`, `fourier_inner_ae_zero`, `inner_eq_zero_of_divergence_eq_zero_curl_eq_zero`.
- **O / namespace `NavierStokesR3.H3PressureOrthogonality`:** `complexComponent`, `complexComponent_apply`, `spatialPartial_ofReal`, `sum_distribution_eq_zero`, `component_divergence_eq_zero`, `integral_representatives`, `pressure_pairing_zero`.

### Consumer/witness disposition and ceiling

Upstream direct import consumers outside this five-file family are `H3Operations` and `H3WeakEmbedding` (A), `H3Products` (C), and `H3CandidateUniqueness` (O). They are **deferred—not imported or modified**. Their downstream energy, weak/strong, candidate and lifespan families are not required to expose the requested independent roots. No existing refactor consumer needs rerouting to a newly added module; leave umbrella roots and both Comparator wrappers unchanged.

A future separately approved pilot can therefore start with **five named new source files, three local namespace adaptations, zero retained-file modifications**, below the proposed 12-file STOP ceiling. This is a source-level candidate, not F2 approval or a guaranteed complete compiler repair list. Stop if compatibility requires unlisted files, changed contracts, new dependencies or witness routing; reference-only remains acceptable. Build cost is unmeasured. Full transitive toolchain/artifact correspondence and fresh checks remain future gates.

These modules construct approximation records and prove integral identities; they do not select a new singular fluid. Public statement equality, producer equality and proved field identity are different. Keeping old imports/producers untouched preserves the intended research lineage; changing a wrapper's producer later would require an identity/replay map for datum, force, pressure, support, viscosity, schedule and domains. Research `WitnessFeasibility.selected` is a separate classical choice. `AllResidualJetRates` must be supplied for consumers that ask for it, such as upstream `LocalPaper.properties_of_schedule`, not imposed universally on wrapper routing and not discharged here.

Current chapter/ledger links describe this reference-only increment. Historical strategy documents retain their original evidence class. No selected projected-force pairing, autonomous seed, endpoint propagator, nonlinear tracking remainder or arbitrary-data continuation theorem is supplied. Same-force zero-datum lifespan improvements, if later considered, are not force deletion. B stays paused.

## 4. Validation and remaining review

Checks performed: manifest hashes before edits; recursive project-import enumeration and source-byte comparisons for the named closure; full five-module body inspection; targeted physical source bodies; paper text and page-81 PDF extraction; human sign, power and dot-product calculations. No builds/probes used existing `.olean` files, and no existing artifact is treated as current validation.

Final document checks are limited to word ceilings, link targets, allowed-file content changes and preservation of the other manifest-pinned companion files. Remote immutable URLs are checked structurally and against local export paths, not fetched. No claim of host-wide bitwise preservation or historical receipt recertification is made. The old validator's 30 NSC/NSA/EUL IDs do not cover PM-01–11 or this dependency map.

Document-check outcome: PASS. Chapter and executive overview are below 2,500 and 300 whitespace-delimited words respectively. All local links resolve; all 13 upstream URLs are commit-pinned and their paths exist in the export (no network verification). The 14 manifest-pinned companion files outside the authorized README/SOURCE-MAP edits remain byte-identical. That describes the original pass. The v2 follow-up adds a before/after file-hash and Git-metadata comparison, plus read-only HEAD/ref queries; results and scope follow below.

Independent review still needed: selected physical supplier/domain transfer, all-order construction input derivations, exact complete-force decomposition, and future compiler/axiom/kernel acceptance for any implementation. The chapter's energy calculation is expanded, but its coefficient geometry is imported, not a standalone human proof of the full paper.

## 5. Supplied QUALIFY reviews — dispositions and follow-up checks

Both supplied reviews are accepted **with their scope restrictions**, not converted into unqualified mathematical approval. Their reported independent checks remain reviewer evidence, not a fresh kernel audit here.

| Review request | v2 disposition |
|---|---|
| Energy/extraction sign and normalization (both reviews) | Addressed in §3: representative-point negative-N calculation, extraction criterion, cosine energy/flux factors. §4 gives the two positive-weight equations and strict transverse cone. No sign reversal was needed. |
| Full versus leading stress (second review) | Addressed in §§1, 4: full summed `T_phys`, leading `T`, and chart order-zero `T_0,*` distinguished. No claim of entire nonlinear residual cancellation. |
| Surviving means and pressure (both reviews) | Addressed in overview and §§4–5: zero angular means of cylindrical wave components; auxiliary-dependent means survive; double averaging precedes evaluation; localized pressure includes `−div f` and every cutoff derivative. |
| Graduate terminology and geometry (both reviews) | Addressed: chart `F=V/R`, axial `G`, covariance `C`, cutoff pulses `b_sigma`, target, and projected operator defined. Rotational feedback is an illustration for the chosen geometry, not a universal necessity. |
| Projected deletion operator (second review) | Addressed in §5: pressure-inclusive and projected operators separated; presingular common classical slab, periodic zero-mean pressure and constant-retaining Leray convention explicit. Both displayed signs retained. |
| Immutable paper identifier (both reviews) | Addressed in §1 with recomputed SHA-256 and authentication limit. |
| Library map and selected-domain boundary | Retained reference-only: reviewer-reproduced 19-module closures and three adapters do not certify compiler compatibility. Common-sequence approximation and conditional whole-space orthogonality do not supply arbitrary-field density or torus mode removal. |

Follow-up directly inspected the paper's angular-mean discussion on p.12, chart coefficients, representative energy transfer and covariance formulas on pp.81–83, and localized force/pressure formula (10.5), plus the source bodies of `baseAction`, `viewSum_covariance_factor`, and `force`/`force_smooth`. Other v1 supplier inspections and the reviewers' broader checks are inherited evidence, not claimed as repeated complete audits.

**Unresolved scope: BLOCKED for complete reconstruction, selected-witness certification, implementation approval, and B.** No newly identified sign error remains in the displayed elementary algebra. The selected enlarged-domain bridge and native partition factor remain explicit; source-trusted profile, correction and all-order suppliers are not independently derived here. One fixed selected witness still lacks complete-force deletion/autonomous future seeding, projected response, nonlinear tracking/concentration persistence and comparison lifespan. B remains paused.

Follow-up mechanical checks: unchanged companion validator; narrow local/reference link and full-commit source-path checks against the supplied export/tar; PDF checksum; chapter/overview word ceilings; changed-file whitespace; all 16 input hashes compared with only README/SOURCE-MAP exceptions; repository file inventory and Git metadata compared against the follow-up entry snapshot. These are documentary checks, not Lean elaboration, kernel validation or a full mathematical proof. Results: PASS. The unchanged validator reports 17 Markdown files, 606 relative links, 30 human IDs, 30 mapped lemmas and 174 lexical source targets. Chapter/overview: 1,876/222 whitespace-delimited words (limits 2,500/300). All 13 unique full-commit upstream links match export and tar bytes; all 14 local links in chapter/ledger resolve; PDF checksum and whitespace checks pass. All 16 input hashes were compared: the 14 protected companions are identical, with only the two pre-existing authorized README/SOURCE-MAP exceptions. The follow-up changed only chapter 07 and this ledger; README/SOURCE-MAP were not edited again. Before/after repository inventory and Git-metadata hashes are unchanged outside those two documents: all Lean/config files, HEAD, index and refs preserved; HEAD and ref listings also match INPUTS. Read-only queries, no commits or pushes. The snapshot bounds this preservation claim to this worktree's files and its Git metadata, not host-wide state.

[A]: https://github.com/openai/NavierStokesAndEuler/blob/f9e8bc5b38b6e212696e8a30e3e91517af887bbd/NavierStokes/R3/H3Approximation.lean
[C]: https://github.com/openai/NavierStokesAndEuler/blob/f9e8bc5b38b6e212696e8a30e3e91517af887bbd/NavierStokes/R3/H3Comparison.lean
[D]: https://github.com/openai/NavierStokesAndEuler/blob/f9e8bc5b38b6e212696e8a30e3e91517af887bbd/NavierStokes/R3/H3PressureDistribution.lean
[F]: https://github.com/openai/NavierStokesAndEuler/blob/f9e8bc5b38b6e212696e8a30e3e91517af887bbd/NavierStokes/R3/H3DivCurlFourier.lean
[O]: https://github.com/openai/NavierStokesAndEuler/blob/f9e8bc5b38b6e212696e8a30e3e91517af887bbd/NavierStokes/R3/H3PressureOrthogonality.lean
