# Unforced restart synthesis — integrated, bounded results

## Verdict

**Accepted: 12 research theorem files, 82 theorems and 6 definitions. No unforced existence, terminal force removal, quantitative strong-norm stability, or A/B conclusion.**

This integration follows the user's integration authorization (superseding PLAN's earlier read-only agent-14 role). PLAN, task sources/reports, setup, original Lean/configuration, and the original checkout were not changed. The coordinator README's setup-only status is historical; this document records the integrated acceptance status.

All twelve reports and `Research/UnforcedRestart/PLAN.md` were read, all twelve Lean files inspected, and the central solution/operator/energy signatures checked. Distinct `UnforcedRestart.*` namespaces coexist without modification. The combined import uses quoted hyphenated module segments and a separate research output root; there are no cross-task dependencies or weakened hypotheses.

## Agent 18 review disposition

The integration-history statements above describe the original integration run. Subsequent documentation repairs and fresh checks are recorded in [VALIDATION.md](VALIDATION.md). No accepted Lean statement is changed. Throughout **all task reports**, task-local A–D classifications are historical and superseded by the per-declaration integrated manifest; these research categories are not Clay alternatives A/B/C/D. In particular, pressure absorption is B and actual force budgets are A. The independent reviews accept only bounded research and leave O1–O10 open.

## What has actually been established?

Classification used here and in the manifest:

* **A — actual candidate-to-PDE/admissibility result:** conclusions apply under precisely the repository candidate contract, or explicitly consume its constructed witness. Admissibility alone is not a PDE existence theorem.
* **B — conditional PDE reduction/estimate:** real operators or integrals, with field regularity/PDE/comparison hypotheses still explicit. This includes generic field transformations; it does not assert an applicable comparator exists.
* **C — generic scalar/abstract tool:** no independently derived NS stability estimate. Analytic helpers and logical diagnostics are marked as such, not mislabeled as candidate PDEs.
* **D — unproved research/source-supported discussion:** not an accepted Lean theorem.

| Task | Accepted progress | Boundary of acceptance |
|---|---|---|
| R³ restart data | A: closed `actual_candidate_restart_data` consumes `ActualCandidateAssembly.selected_witness`; all interior snapshots satisfy the actual decay predicate and squared-speed Lebesgue integrability. One compact set supports all spatial jets. C: weighted compactness helper. | Constants depend on slice/order/real exponent; no terminal uniform datum bound, pressure decay, or restart existence. This is the new **closed construction specialization**, unlike the merely source-mapped specializations in most other reports. |
| Periodic restart data | A: candidate snapshot admissibility and smooth periodic pressure slice. C: actual lattice-sum snapshot identity and gauge periodicity. | No whole-space energy of a periodic field, convergence from formal summation, or separately compiled selected-witness specialization. |
| Time translation | A: candidate forced equation on `0≤s<1−t₀`, including actual `derivWithin (Ici 0)` at new zero. B/C: generic translation calculus/domain facts. | `candidate_shift_unforced` is B: assumes `f=0` on **all** `[t₀,1)×R³`. That assumption is not established. No global Comparator solution is packaged. |
| Smooth force cutoff | B: genuine smooth shutdown, support/periodicity preservation, exact old-field residual defect. A: actual compact-candidate modified-force admissibility. C: scalar cutoff construction. | Modifying force constructs no modified solution. On the late plateau the old pair solves the new equation only if its old force vanishes. No periodic force-decay predicate wrapper or velocity-cutoff product-rule theorem was added. |
| Pressure absorption | B: `R(u,p−φ)=R(u,p)−∇φ`, remaining force and exact gradient criterion; smooth/periodic pressure contracts. | No terminal potential, Helmholtz projection, or pressure-flux theorem. A time-only gauge changes no spatial gradient. |
| Difference equation | B: actual unequal-force subtraction, both conventions, interior slab and divergence statements. C: arbitrary shared datum gives initial zero error. | No equal-force uniqueness substitution, integration, existence or error estimate follows from the algebra. |
| Periodic energy | B: genuine cube-integral forced `energyRate` balance and Young/dissipative rate bound. | The exports are **rate identities**, not a newly assembled time-integrated energy theorem. Joint slab smoothness plus baseline `energy_hasDerivAt` is a further adapter. Whole-space inhomogeneous pressure recovery remains open. |
| Gronwall threshold | C: weighted primitive budget, general and zero-initial-error thresholds. | The primitives' derivative identities are premises. FTC instantiation, actual PDE inputs and force-to-threshold comparison are not new theorems. |
| Strong-norm growth transfer | C: norm/evaluation inequalities, relative-error growth transfer and compact-continuity contradictions. | The decisive relative-error estimate is assumed, not derived. `N` is a scalar, **not a defined Sobolev norm**. H²/H³ embeddings and NS strong-norm estimates are discussion only. |
| Actual forcing budget | A: uniform actual compact-force jet bound, interval integrability and fixed-tolerance short-time budget. | Checked integrals are `∀x, ∫‖J_m(t,x)‖dt`, **not** `∫sup_x‖J_m‖dt`, mixed spatial-time norms or a weighted strong-norm budget. Bounds uniform in x help future packaging, but do not perform it. |
| Scaling/compactness | C: force zoom definition, norm/pointwise limit and scalar homogeneity; B: exact actual-base axis identity under its full coefficient hypotheses. | No parabolic PDE covariance theorem, assembled-candidate eventual wrapper, compactness or limit solution. The locally uniform compactness obstruction is a source-supported deduction for this normalization, not a checked no-compactness theorem or a refutation of all weak-limit strategies. |
| Local theory obstruction | C: nonzero snapshot cannot use the zero-datum `Solution` structure. B: force rigidity and zero-datum periodic unforced uniqueness specialization. D: bounded source search. | No applicable general NS local-existence/continuation theorem was located. This is not a theorem that none could exist under another name. |

Exact per-declaration classifications, direct imports and frozen source hashes are in [MANIFEST.json](../../Research/UnforcedRestart/MANIFEST.json) and [MANIFEST.md](../../Research/UnforcedRestart/MANIFEST.md). Full hypotheses remain in the accepted Lean statements and task reports; classifications do not erase them.

## Compatibility audit

1. **Fields and classes.** Internal fields are `(ℝ × EuclideanSpace ℝ (Fin 3)) → V`; Comparator is curried space-first. The datum divergence bridge is checked, but a finite-horizon restart is not the global Comparator class. `Solution I f u p` always requires `u(0,x)=0`, even when `0∉I`; `mono` does not change datum/time origin. Raw periodic uniqueness already permits arbitrary common data on `[a,b]`. Raw R³ uniqueness permits arbitrary common data at zero, but must be translated and supplied slab-uniform competitor energy.
2. **Time.** Fix one `0<t₀<1`, `H=1−t₀`, and `0<S<H`. Reference fields are smooth on `[0,S]` after translation, not at `H`. Full derivatives for a generic closed-slab competitor are justified only in its time interior. The reference's new-zero within derivative is checked because its old time lies in `(0,1)`; this does not grant the same extension to a generic one-sided competitor. A pressure-absorption hypothesis only on `(t₀,1)` needs an additional boundary argument if a within PDE at zero is claimed.
3. **Force and pressure signs.** For `w=u−v`, `r=p−q`, common viscosity one gives `∂t w=Δw−Du(w)−Dw(v)−∇r+f−g`. Swapping fields also swaps pressure and transport decomposition. Cutting force to `g=ρf` leaves discrepancy `+(1−ρ)f`. Absorbing `f=∇φ` uses `p−φ`, never `p+φ`. `f−∇φ` is not automatically divergence-free.
4. **Viscosity.** The internal residual, translation, energy and absorption results use exactly one. `DifferenceEquation.residual ν` explicitly extends the operator and proves its value at one; subtraction itself permits any real common ν. Dissipative applications need ν>0. Scaling's coefficient identity is not a spatial chain rule. Comparator viscosity normalization changes time/amplitude/force and must not be confused with fixed-viscosity parabolic zoom.
5. **Energy/norms.** `E=∫_Q|w|²` has no half; `D=Σ_i∫_Q|∂_iw|²` uses coordinate/Hilbert–Schmidt squares. The coupling majorant `B` bounds the operator norm of `Du`. The checked periodic rate is `energyRate=−2D−2C+2W`, and `energyRate+2D≤(2B+1)E+∫_Q|f|²`. Here `f` is the residual difference. No extra periodic Comparator energy field is required. Whole-space finite reference energy is not an infinite-volume error/pressure-flux estimate.
6. **Periodicity/support.** Periodic velocity **and pressure** are necessary for energy cancellation; an affine pressure is not an admissible periodic gauge. The pressure need not be part of the initial datum. Compact velocity support belongs to the reference, not a new viscous comparator. Compact-first periodization uses separated copies and local pressure equality, not general nonlinear superposition; independently evolved viscous copies can overlap.
7. **Growth.** L² closeness alone cannot preserve point evaluation. An actual H² velocity/H³ gradient evaluation route requires proved norms/embeddings and strong PDE stability. All-space `SpeedUnboundedAtOne` also needs spatial compact reduction to contradict whole-space smoothness; arbitrary moving witnesses could escape. The axis-only criterion avoids that issue, but needs actual eventual axis growth and the unproved error premise.

## The actual-force gap

The compact and periodic forces are different components of the selected witness. The former is the smooth extension of the activated compact residual; the latter is its separated periodization. Force equality with the residual is presingular and spatially global. Shutdown at time **2** occurs after the singular time **1**. Flat boundary jets at the origin do not set the exterior terminal trace to zero, imply a terminal force-free interval, or supply a periodic potential. Neither nonzero exterior terminal trace nor terminal absorbability has been proved here.

Consequently there are two still incomplete paths:

* **Exact restart:** data + translated PDE + an actual terminal zero/gradient-force identity + admissible pressure correction + nonzero-data class conversion/uniqueness. Only the first two and conditional algebra are supplied.
* **Perturbative restart:** an actual comparator + unequal-force PDE + justified energy/strong-norm estimate + actual quantitative weighted forcing budget + evaluation control uniform toward H. The periodic energy step is now substantive progress; the scalar and norm tools do not establish the subsequent PDE estimates or smallness.

The alternative zoom route has small force but uncontrolled velocity. For the actual base the checked axis norm is `r^(−2h) d.axial 0 (0,0)` at zoom point `(-1,0)`, `0<h<1/2`. Transferring that formula eventually to the assembled field obstructs locally uniform classical compactness in this normalization. It does not exclude every weak/distributional approach, supply a nontrivial limit, or pass the nonlinear product.

**Logical qualification:** local theory is needed to construct a restarted evolution, but not as an extra axiom in a reductio against global A/B: a hypothetical global solution would already provide existence and horizon coverage. Even that legitimate reductio still lacks force removal or sufficiently strong quantitative comparison. Local existence by itself does not fix those gaps.

## Fresh evidence and trust boundary

Run from this isolated worktree:

```sh
python3 Research/UnforcedRestart/integration/validate.py
```

Final run: **exit 0**, recorded in [run.exit](../../Research/UnforcedRestart/integration/run.exit). Every mathematical file and the combined audit used `lake env lean -j1 -DautoImplicit=false -DwarningAsError=true`, with `LEAN_NUM_THREADS=1`. Outputs are solely under `Research/UnforcedRestart/integration/validation/lib/`; no build or dependency repair was necessary.

* [SUCCESS.json](../../Research/UnforcedRestart/integration/validation/SUCCESS.json): exact 13 compiler commands, exit codes, log paths, inline research closures, pinned baseline/toolchain and counts.
* [run.log](../../Research/UnforcedRestart/integration/run.log): final serial run summary.
* [declarations.tsv](../../Research/UnforcedRestart/integration/validation/declarations.tsv): **42,929** project/research constants and complete axiom closures, including generated helpers and all imported project dependency exports, not merely selected probes.
* [dependencies.json](../../Research/UnforcedRestart/integration/validation/dependencies.json): **11,108** imported modules in loader order, exact source/olean paths and SHA-256 hashes, direct source imports and inherited project options. There are **526** imported project/research modules (including modules with no constants); no inherited project option overrides were found.
* All 42,929 closures are permitted: 38,280 use all three axioms; 3,664 use only `propext`; 320 use `propext, Quot.sound`; 665 use none. All 88 named research exports use the permitted three. Project/research dependency sources also passed the forbidden-construct scan; the semantic audit rejects unsafe project constants and any unexpected closure.
* Baseline `597692fa5d55e07d810b2d96ead1a67972585425`, tracked working/index diffs and all eleven package revisions/working diffs passed checks before and after. No original files/configs changed; no commits, pushes, broad builds or original-checkout commands/writes.

This is fresh research elaboration plus broad **cached dependency** source inventory/axiom auditing, not a clean kernel rebuild of every dependency, independent Comparator execution, or Clay-prose equivalence proof. External Mathlib/Lean metaprogramming is library infrastructure, not a claim that every unused external declaration is a safe mathematical theorem. All external axioms used by covered project results are included transitively. No `ComparatorChallenges.*` module is imported. Historical challenge-placeholder warnings in the unrelated baseline build are not accepted evidence.

The initial integration audit counter needed a `Nat` annotation; its compiler exit 1 is preserved in `integration/rejected-audit-elaboration.log`. Later inventory runs failed nonzero on Lake-source and quoted research-path resolution; those tooling failures produced no success marker and were corrected without changing theorem sources or strictness. Task-local failed drafts and unproved proposals are explicitly excluded in the manifest. See [OBLIGATIONS](OBLIGATIONS.md) for the remaining work.
