# Native-control validation and remaining obligations

## Provenance and coverage

Supplement to [chapter 05](05-native-weighted-control.md), at source baseline `26e896edbdbe1215c0d50ddba24b2b6453646f5f` (HEAD verified before edits). The supplied N1, N2 and clock/joint-ODE reports are derivation evidence, not certification. The author also read the [native plan](native-control-plan.md) and both prior reports named there in full, and cross-checked selected actual source bodies. This is author-level reconstruction, not independent mathematical review or fresh formal validation.

The eight `native-control-*` anchors below are deliberately **not** NSC/NSA/EUL IDs. `validate.py` still covers the historical 30 IDs only; it additionally checks relative Markdown links across the directory and lexical targets in the source map. It does not become an eight-claim mathematical checker by seeing these files. No test was weakened or reclassified. [VALIDATION.md](VALIDATION.md) is unchanged and remains historical.

Evidence labels:

- **Expanded:** a displayed calculation from explicitly stated inputs, checked against selected source bodies and/or the supplied derivations; not a dependency-closure audit.
- **Source identity:** actual field/reindexing identity checked in the cited implementation.
- **Source-only input:** mathematical supplier identified but its complete human derivation or numerical constants not recovered. Dependent claims retain this qualification.

## Claim → source → obligation ledger

All source paths below are at the new baseline. Chapter sections give fully qualified declarations alongside the calculations; short names in this table are navigation labels in the linked file, not new theorem names.

| Explicit chapter anchor and mathematical claim | Principal source bodies | Evidence and outstanding obligation |
|---|---|---|
| [native-control-identity](05-native-weighted-control.md#native-control-identity): same initializer, active pair, arbitrary copy, current source and frame | [ActualParticularStageControls](../../NavierStokes/ActualParticularStageControls.lean), `selectedControl`, `selected_tangent_eq`, `selectedActualControl`; [ActualParticularCycleData](../../NavierStokes/ActualParticularCycleData.lean), `native_residual` | Source identity. Incoming frequency coherence and residual invariant remain inputs. The particular-state binding is not the later signed-correction state. Independent review of all enclosing initialization hypotheses remains open. |
| [native-control-normal](05-native-weighted-control.md#native-control-normal): signed eigenpair and mesh/rounding normal comparison (2.1)–(2.5) | [PrimaryRepresentatives](../../NavierStokes/PrimaryRepresentatives.lean), `ReferenceCone`; [PhaseEstimates](../../NavierStokes/PhaseEstimates.lean), `explicit_normal_estimate`, `rounded_normal_estimates`; [BasePhaseGeometry](../../NavierStokes/BasePhaseGeometry.lean), `phase_errors_on_mesh`, `FamilyData.phase_estimates` | Expanded from prepared normalized base and cone inputs. **NC-D1:** deriving those primitive inputs from the summed profile is not done. Expand `PrimaryGeometryAssembly.exists_prepared` suppliers, notably actual chart estimates and the modulated positive cone, to complete that upstream production. |
| [native-control-energy](05-native-weighted-control.md#native-control-energy): tail denominators, moving-frame errors, two-sided damping and all-harmonic upper energy bound (3.1)–(3.6) | [BasePhaseGeometry](../../NavierStokes/BasePhaseGeometry.lean), `FamilyData.coordinate_errors`, `FamilyData.modal_errors`, `FamilyData.damping_error`, `FamilyData.construction`; [MovingFrameODE](../../NavierStokes/MovingFrameODE.lean), `modal_equations_iff`, `modal_energy_le` | Expanded order-zero producer conditional on NC-D1's permitted primitive outputs. No assumed `UniformModalControl.energy` or `PhaseConstruction.modal_errors`/`damping_error`. Does not prove all-order coefficient jets or negative definiteness. |
| [native-control-clock](05-native-weighted-control.md#native-control-clock): literal matrix transport, closed-time membership, exact exponential cancellation (4.1)–(4.4) | [ActualParticularControl](../../NavierStokes/ActualParticularControl.lean), `transported_errors`, `transported_coefficient`, `scaled_selected_copy_energy`; [ScaledActualParticularControl](../../NavierStokes/ScaledActualParticularControl.lean), `scaledControl` | Source identities and expanded calculation. Normal scaling remains in normal and motion fields. Only the exponential, not duration or geometry, is free of inverse-clock losses. |
| [native-control-source](05-native-weighted-control.md#native-control-source): actual separation, full-path exact envelope, affine all-jet transfer (5.1)–(5.4) | [ActualSignedGeometry](../../NavierStokes/ActualSignedGeometry.lean), `clock_outer_in_slot`, `slotGeometry_separated`; [WaveEnvelopeTransport](../../NavierStokes/WaveEnvelopeTransport.lean), `copyEnvelope_path`; [ActualParticularControl](../../NavierStokes/ActualParticularControl.lean), `source_path_bounds` | Expanded from fixed slot-system injectivity and incoming all-jet invariant. **NC-D2:** previous-cycle production of that invariant is outside scope. No weight differentiation or assumed projected-source class. Closed rectangle equality does not prove radial extension beyond the open class domain. |
| [native-control-projection](05-native-weighted-control.md#native-control-projection): actual projection columns and exact affine/Leibniz constants (6.1)–(6.2) | [PhaseJetBounds](../../NavierStokes/PhaseJetBounds.lean), `normalGeometry_jets`, `FrameJets.forcing`, `PhaseFamily.frameData_jets_of_phase_comparison`; [ActualParticularControl](../../NavierStokes/ActualParticularControl.lean), `frame_forcingLinear_jets`, `frame_input_jets` | Projection/Leibniz mechanism expanded; **NC-D3:** primitive all-order phase/base jet witnesses and compact derivative constants remain source-only. Order-zero closeness is insufficient to infer them. At this algebraic stage, order-`N` normal/motion/shear/frame jets consume base `F,G` jets through `N+1` via `PolynomialJets.directional`; residual, joint solution and synthesis need jets through `N`. Normal motion uses its explicit formula, not a differentiated comparison bound. This order ledger does not recover the missing numerical witnesses. Expand their actual suppliers and quantitative composition bounds to finish this central higher-order input. |
| [native-control-joint](05-native-weighted-control.md#native-control-joint): exact numerical joint Fréchet bound (7.1), including endpoint parameter | [WeightedODEJets](../../NavierStokes/WeightedODEJets.lean), `jet_solution_eq_solution`, `norm_iteratedFDeriv_odeFamily_le_polynomial`; [ParticularWaveBounds](../../NavierStokes/ParticularWaveBounds.lean), `forced_joint_jet_bound`; [JointODE](../../NavierStokes/JointODE.lean), `reparamSolution_eq_actualSolution` | Expanded consumer after the preceding producers; inherits NC-D2–D3. Exact `rescaleConstant = 2^N K^2+K+1` and exponent `(m+2)(d+1)` recovered. Endpoint bounds concern the smooth reparameterized representative, not arbitrary extensions of the closed-interval solution. |
| [native-control-output](05-native-weighted-control.md#native-control-output): affine endpoint synthesis, real/imaginary norms, pressure sign and class gain | [ParticularWaveBounds](../../NavierStokes/ParticularWaveBounds.lean), `copySolve_jet_bound_from_modal`, `pressure_class`; [TangentProjection](../../NavierStokes/TangentProjection.lean), `pressure_cancellation`; [ActualParticularStageControls](../../NavierStokes/ActualParticularStageControls.lean), `selected_inverse_frequency`, `selected_raw_jets` | Modal/ambient numerical majorant and cancellation algebra expanded. **NC-D4:** inverse-normal and inverse-carrier numerical producers unexpanded; pressure conclusion is class-level, with exponent `1+σ`. Expand `CurlClassBounds.normalInverse_unweighted` and `UniformPrimaryWeights.harmonic_inverse_bandBound` for a fully numerical pressure ledger. **NC-D5:** radial boundary extension, cutoff defects and physical localization are separate work. |

## What the new chapter changes

It supplies a real order-zero producer inequality, not solely a conditional Volterra argument: reference cone → mesh/rounding → moving-frame modal errors and normalized damping → (4.2). It also supplies separation → exact weight along every sampled time → affine and projected source jets, while displaying rather than hiding the primitive higher-order jet input.

The exact modal numerical bound and ambient endpoint loss are recovered in terms of those input witnesses. The pressure numerical constants are not. Thus the particular-wave portion of **OBL-NSC-004 is narrowed, not closed**. OBL-NSC-005–006, signed/mean inverses, finite-head matching, cutoff/Gaussian defects, physical realization, whole-space pressure recovery and the complete singularity argument are unchanged. No source defect, new singularity theorem, external Clay equivalence or formal certification is asserted.

## Checks and their limits

Documentation checks are run from the repository root:

```text
python3 docs/proof-companion/validate.py
git diff --check
git rev-parse HEAD
git status --short
```

An additional read-only lexical/link inspection of the new chapter checks that its eight explicit anchors occur once and have a ledger row, and that backticked fully qualified declaration names have a lexical declaration suffix somewhere among the chapter-linked Lean files. This is an author check, not a new installed validator and not namespace resolution. The existing validator and historical ledger are not edited.

Executed results:

- Existing validator: **PASS (mechanical scope only)** — 12 Markdown files, 493 relative links, the unchanged 30 human IDs/30 mapped lemmas, and 174 lexical source targets. The extra source targets are supplemental navigation, not extra historical claim coverage.
- Native author check: **PASS** — eight unique explicit chapter anchors, each with one ledger row; 70 declaration suffixes located among 26 chapter-linked Lean files. This union-of-files spelling check does not verify which namespace exports a declaration or all its hypotheses.
- `git diff --check`: no diagnostics; new chapter trailing-whitespace check also passed.
- HEAD remains the frozen baseline. Status is documentation-only: chapter, new ledger, three integration files, and the already-untracked plan. Historical `VALIDATION.md` and `validate.py` are unchanged.

The first documentation check caught a displayed algebraic bracket/product parsed as a Markdown link, and the first lexical check caught missing direct source-file links for primitive suppliers. The prose/link notation was corrected; no checker was changed to suppress failures.

No Lean builds, probes, configuration changes, external symbolic computations, commits or pushes were performed. Only documentation in this worktree was edited; the pre-existing untracked plan is retained. The two subsequently supplied independent reviews corroborate the selected downstream chain, not NC-D1 or NC-D3–D5. Those producer and boundary obligations still require independent reconstruction.

## Independent-review revision and rerun

Both supplied reviews found no high-severity defect in the selected downstream calculations. Their verdicts are review evidence, not fresh kernel validation. This revision changes only chapter 05 and this ledger; the three integration files and untracked plan were already present at entry.

| Review finding | Disposition and source-body check |
|---|---|
| Medium, both reviews: missing initial-data and forcing jet premises | **Repaired, not waived.** §7 now states bounds on every initial, forcing and coefficient jet through `N`, with nonnegative constants and positive weight. `WeightedODEJets.lean:460–490`, `norm_jet_solution_le`, explicitly supplies `hxj` and `hfj` at every order. The reviewers' zero-coefficient counterexamples invalidate the old general explanation; the revised premises exclude them. The actual initial family is identically zero, including after rescaling, so (7.1) and its constants are unchanged. |
| Low, both reviews: primitive derivative-order shift | **Clarified.** §6's finite-order table and NC-D3 now record base orders through `N+1`, versus normal/motion/frame, residual, joint solution and synthesis through `N`. `PhaseJetBounds.lean:166–175` requests `hf.bound (N + 1)`; `polynomial_jets` at 540 onward uses the first directional base derivatives at 569–572. Motion uses its explicit formula. Numerical supplier debt remains open. |
| Low, second review: complete point-domain conjunction | **Clarified.** §1 displays strip membership, selected reference-carrier membership, transverse closed-copy membership and sampled closed-time membership together; current-copy jets add interior current time. Checked against `ActualParticularControl.frame_input_jets` (264–294), `scaled_selected_copy_energy` (770 onward), and `ScaledActualParticularControl.neighborhood`/`patch` (74–86). The energy theorem needs only the carrier/time subset of this conjunction; the chapter does not claim every conjunct is necessary for energy alone. |
| Motivation, second review: midpoint peak | **Added.** §4 substitutes the damping normalization into the reference rate: since `m` increases through `u` at `L/2`, the rate changes from positive to negative there. This explains the envelope peak without claiming an exact Gaussian. `GaussianEnvelope.referenceRate` uses the same slot magnitude. |

No serious unresolved exposition error was identified in these reviewed chains after the repairs. This is not a pass for the outstanding analytic producer obligations.

### Actual revision commands and results

Run from the repository root (the temporary script was an ad hoc standard-library check, not a repository/config change):

```text
python3 docs/proof-companion/validate.py
python3 /tmp/native-review-check.py
git diff --check
git rev-parse HEAD
git status --short
```

The temporary script ran `git ls-tree -r --name-only` and `git archive` at the full baseline hash, `git diff --name-only` against that baseline, and `git ls-files --others --exclude-standard`. It extracted the archive into a fresh temporary directory and compared worktree bytes against **all 2,342 baseline tracked files outside the six explicitly declared overlay paths**. All matched, including every Lean and configuration file, the historical validator and historical validation ledger. HEAD remained `26e896edbdbe1215c0d50ddba24b2b6453646f5f`.

The only permitted overlay was these six paths under `docs/proof-companion/`: `02-ns-construction.md`, `README.md`, `SOURCE-MAP.md`, `05-native-weighted-control.md`, `native-control-plan.md`, and `native-control-validation.md`. Changed and nonignored untracked paths were checked to be a subset of that list. The archive received exactly those six documentation files, not a worktree copy, `.lake`, build artifacts or other untracked material. It then ran the baseline `validate.py` directly in that export. Temporary export cleanup was automatic.

Results (superseding the earlier author-check counts for the revised chapter):

- Worktree **and isolated export** validator: **PASS (mechanical scope only)**; 12 Markdown files, 493 relative links, unchanged 30 IDs/30 mapped lemmas, 174 lexical source targets.
- Export narrow check: **PASS**; eight distinct native anchors, exactly one ledger row each; 72 fully qualified backtick-name occurrences with a lexical suffix among the 26 directly linked Lean files. Relative links and anchors were also covered by the export validator.
- Additional exact-file source checks: **PASS** for the reviewed ODE declaration and `hxj`/`hfj`, the base `N+1`/directional supplier, both control declarations, and neighborhood/patch domain and interior-time clauses in the four source files listed in the disposition table. These spelling checks supplement the manual body reading above; they do not resolve namespaces or certify hypotheses or mathematics.
- Baseline byte comparison: **PASS**. Overlay trailing-whitespace check and `git diff --check`: **PASS**, no diagnostics. No undeclared untracked input was needed by the export checks.

No kernels, Lean builds, probes, installs, source/config edits, commits, pushes or publication were performed. Markdown/link/byte checks do **not** certify the human mathematics.

### Remaining opacity and possible small follow-up

The human derivation now available is the selected signed cone/mesh/rounding → normal/frame/damping → all-nonzero-harmonic energy chain, exact clock cancellation, separated full-path source transfer, projection/Leibniz bounds, correctly hypothesized joint-jet induction and endpoint synthesis, and complex pressure cancellation. NC-D1–D5 remain: summed-profile preparation, prior-cycle residual production, quantitative all-order primitive suppliers, numerical inverse-normal/frequency witnesses, and boundary/localization work. The full correction cycle and physical singularity conclusion do not follow.

A possible small future code consolidation, **not executed**, is a finite-order corollary exposing the `N+1` base-to-`N` frame dependency already implemented by `PolynomialJets.fderiv`/`directional` and `PhaseFamily.polynomial_jets`. The inspected bodies support that dependency; they do not supply a newly reconstructed numerical producer. No replacement ODE framework or source repair is justified by these reviews.
