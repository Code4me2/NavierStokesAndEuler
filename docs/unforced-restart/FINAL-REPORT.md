# Final report — validated bounded research; unforced restart OPEN

**Technical validation: PASS with cached dependencies. Mathematical scope labeling: PASS. Unforced restart and Clay alternatives A/B: NOT RESOLVED.** Safe to retain as isolated research, not as a completed proof or publication.

Agent 20 inspected all twelve accepted Lean sources, the manifest, scope/review documents and Agent 19's external independent report, and reran the frozen validator successfully. No proof/code changes were made. This report is authorized by the final reporting request; earlier read-only role descriptions in PLAN are historical.

## 1. Exact location and preservation

- Worktree: `/home/velvet/worktrees/unforced-restart-20260909T202951Z`
- Branch: `research/unforced-restart-20260909T202951Z`
- HEAD/baseline: `597692fa5d55e07d810b2d96ead1a67972585425`
- Report: `docs/unforced-restart/FINAL-REPORT.md`
- Accepted sources: `Research/UnforcedRestart/<slug>/Main.lean`; aggregate tooling: `Research/UnforcedRestart/integration/Audit.lean`.

The original companion/proof checkout `/home/velvet/Desktop/NavierStokesAndEuler` remains untouched by this work. Agent 20 performed no commands against it. Baseline Lean, challenge files, dependency configuration and toolchain were not edited. No publication, commit, push, merge, clean dependency build or Comparator rerun occurred. Writes in this reporting pass consist only of this document, isolated run logs/status, and designated regenerated validation artifacts.

## 2. What turning the forcing off actually means

Use the repository's viscosity-one residual

\[
R_1(u,p)=\partial_tu+Du(u)-\Delta u+\nabla p=f.
\]

Fix **one** interior time \(0<t_0<1\), datum \(a(x)=u(t_0,x)\), and horizon \(H=1-t_0\). Translation gives \(u_r(s,x)=u(t_0+s,x)\), with the **same translated force**, for \(0\le s<H\). Translation does not turn forcing off.

Turning it off prescribes a **new initial-value problem**:

\[
R_1(v,q)=0,\qquad \operatorname{div}v=0,\qquad v(0,x)=a(x).
\]

If an applicable existence theorem supplies it, this is a new evolution. Its pressure must satisfy the new equation and the relevant admissibility conditions; it is not automatically the old pressure. Equal initial data do not imply equal later velocities for different forces. **Neither the old trajectory nor its singular growth is inherited without exact force removal or a sufficiently strong, quantitative stability argument.** This research supplies neither an applicable restarted solution through the required horizon nor that argument. It also does not prove that a restarted evolution must stay regular or must blow up.

There are precise exceptions/conditions, not an automatic inheritance rule:

- Keeping **both** old fields fixes their residual and hence their force. The old pair is unforced only where its old force is zero. `candidate_shift_unforced` explicitly assumes \(f(t,x)=0\) for **every** \(t\in[t_0,1)\) and every \(x\).
- Keeping the velocity but correcting pressure works if an actual admissible potential satisfies \(f=\nabla\phi\): then **\(R_1(u,p-\phi)=0\)**. Spatial smoothness is needed for the identity; joint smoothness and, on the torus, periodicity of the corrected pressure must also be supplied. A potential only on the open slab does not settle the new-zero boundary convention.
- Replacing force by \(\rho(t)f\), where a smooth switch is eventually zero, produces a smooth modified **force**, not a solution. The old-pair defect is \((1-\rho)f\). After the switch this is the full old force.

The actual construction shuts its extended force down only at **time 2**, after the reference singular time **1**. Terminal origin flatness and force decay do not prove a globally force-free terminal interval. No admissible terminal potential has been constructed either. The actual exterior terminal trace has been proved neither zero nor nonzero here.

## 3. Accepted mathematics and source/declaration map

There are **82 theorems and 6 definitions in 12 accepted files**. These research labels are unrelated to Clay alternatives:

| Research category | Theorems | Definitions |
|---|---:|---:|
| A: candidate-contract/admissibility or closed construction specialization | 17 | 0 |
| B: conditional PDE results and field calculus | 41 | 3 |
| C: generic scalar/abstract tools and diagnostics | 24 | 3 |
| **Total** | **82** | **6** |

Candidate-contract implications are not all closed specializations. In particular, `R3RestartData.actual_candidate_restart_data` actually consumes `NavierStokes.ActualCandidateAssembly.selected_witness`; most other candidate results assume the repository's candidate properties. Those properties already include the **forced** equation and reference growth, not unforced existence.

In the map below, each source is `Research/UnforcedRestart/<slug>/Main.lean`, and each namespace has prefix `UnforcedRestart.`. Representative declarations identify the substantive results; the exhaustive **88-name map, source lines, direct imports, classifications and frozen hashes** are in [MANIFEST.md](../../Research/UnforcedRestart/MANIFEST.md) and [MANIFEST.json](../../Research/UnforcedRestart/MANIFEST.json). Task reports are linked through [SYNTHESIS.md](SYNTHESIS.md).

| Source slug / namespace | Declaration map and accepted scope; essential boundary |
|---|---|
| `r3-restart-data` / `R3RestartData` | `actual_candidate_restart_data`, `snapshot_admissible`, `fixed_jet_support`, `snapshot_energy_integrable`: actual compact-candidate snapshots are smooth, divergence-free, rapidly decaying in the real Comparator predicate, and have finite squared-speed integral. Candidate properties and presingular time are essential; one compact set supports all spatial jets, but decay constants depend on slice/order/exponent. No terminal uniform datum estimate or evolution. `compact_smooth_decay` is a generic compactness helper. |
| `periodic-restart-data` / `PeriodicRestartData` | `candidate_snapshot`, `candidate_pressure_snapshot`: under `CandidateProperties` and \(0<t_0<1\), admissible periodic velocity datum and smooth periodic pressure slice. `snapshot_admissible` exposes smoothness, divergence and periodicity directly. `periodize_snapshot` is a lattice-sum identity, not convergence or nonlinear superposition; `pressure_gauge_periodic` is generic. |
| `time-translation` / `TimeTranslation` | `candidate_shift_equation`, `candidate_shift_within_equation`: actual forced equation, including `derivWithin (Ici 0)` at new zero because the old time is interior. `shift_residual` requires old-time differentiability; `shift_smooth_slab` stays strictly below \(H\). `candidate_shift_unforced` requires full terminal vanishing. No global Comparator package. |
| `smooth-force-cutoff` / `SmoothForceCutoff` | `compact_candidate_cut_admissible`, `cutForce_smoothOn`, `cutForce_periodic`, `old_residual_defect`, `old_solves_cut_iff`: smooth/support-preserving cutoff and exact old-field defect. Early/late claims need ordered switch times; future-time support/admissibility also requires nonnegative final switch time. Smoothness/support/periodicity of input force remain explicit. No modified evolution. |
| `pressure-absorption` / `PressureAbsorption` | `residual_sub_pressure`, `unforced_iff_gradient`, `absorb_on`: exact minus-sign correction under smooth pressure/potential slices and actual residual/gradient identities. `corrected_pressure_smooth` and `corrected_pressure_periodic` require the respective contracts for both terms. `time_gauge_gradient` is zero; it removes no force. |
| `difference-equation` / `DifferenceEquation` | `difference_forces`, `forced_unforced`, `unforced_forced`, `forced_unforced_on_slab`: real unequal-force subtraction with explicit smooth velocity/pressure slices, temporal differentiability and both PDEs; closed-slab smoothness yields full derivatives only in the interior. `divergence_free_difference` additionally assumes divergence freedom. `restart_difference_zero` only assumes shared data. Common arbitrary real viscosity is allowed in subtraction algebra, not in a dissipativity claim. |
| `energy-comparison` / `EnergyComparison` | `forced_energy_balance`, `forcing_work_le`, `forced_energy_rate_le`: genuine periodic cube-integral rate identities/inequality, viscosity one, under the full assumptions detailed below. Not an assembled time-integrated stability theorem. |
| `actual-forcing-budget` / `ActualForcingBudget` | `compact_jet_bound`, `compact_jet_intervalIntegrable`, `compact_time_integral_bound`, `compact_short_budget`: under actual `R3CompactCandidate.Properties`, uniform jet bounds and genuine fixed-spatial-point time integrals on \(0\le a\le b\). Fixed positive tolerance only; no weighted strong-norm threshold. |
| `gronwall-threshold` / `GronwallThreshold` | **Generic scalar tools:** `weighted_budget`, `threshold`, `zero_initial_threshold`. Require closed-interval continuity of energy and primitives, interior derivative identities \(A'=k\), \(B'=e^{-A}g\), and \(E'\le kE+g\). Threshold is a further premise; zero-initial version assumes \(E(a)=B(a)=0\). No PDE identification or FTC adapter. |
| `strong-norm-growth-transfer` / `StrongNormGrowthTransfer` | **Generic tools:** `evaluation_budget`, `speed_transfer`, `no_periodic_continuous_comparator`, `no_continuous_axis_comparator`. Require evaluation/error bounds, reference growth, relative factor \(\rho<1\) and nonnegative additive constant for growth transfer. Contradictions additionally need endpoint continuity and periodic compact reduction, or explicit axis growth/axis comparison. `N` is a scalar, not a Sobolev norm; decisive `herr` is assumed, not derived. |
| `scaling-and-compactness` / `ScalingAndCompactness` | Generic `zoomForce_norm_le`, `zoomForce_tendsto`, `axis_power`, `viscosity_coefficient`; force convergence assumes continuity at the center. Actual-base `base_zoom_axis` requires strictly increasing schedule, \(0<h<1/2\), smooth coefficients, vanishing higher axial coefficients and positive zeroth coefficient. Gives \(r^{-2h}d_0\), not an assembled-candidate compactness/limit theorem. |
| `local-theory-obstruction` / `LocalTheoryObstruction` | `nonzero_snapshot_not_solution`: a nonzero snapshot cannot fit the zero-datum `Solution` wrapper, whatever its time set. `unchanged_fields_force_rigidity`: both residual identities fix the same force. `zero_datum_unforced_periodic_is_zero`: actual periodic `ClassicalSolution` with zero force and zero datum is zero on its lifespan; no implication for nonzero restart data. |

The six definitions are `residual`, `shift`, `shutdown`, `cutForce`, `zoomVelocity`, `zoomForce`. None defines a hidden existence or stability assumption. The separately classified setup `ImportProbe.lean` and aggregate audit are tooling, not extra mathematical results.

### Worked result: what the periodic comparison really proves

Let \((u,p)\), \((v,q)\) be viscosity-one fields at a fixed time. Assume:

1. all four spatial slices are smooth and **both velocities and both pressures are unit-periodic**;
2. both velocities are divergence-free and pointwise differentiable in time;
3. the residual discrepancy \(F=R_1(u,p)-R_1(v,q)\) is spatially continuous;
4. \(\|Du\|_{\mathrm{op}}\le L\) on the unit cube \(Q\).

Set \(w=u-v\), \(r=p-q\), and

\[
E=\int_Q|w|^2,\quad D=\sum_i\int_Q|\partial_iw|^2,\quad
C=\int_Q\langle w,Du(w)\rangle,\quad W=\int_Q\langle w,F\rangle.
\]

Unequal-force subtraction gives

\[
\partial_tw=\Delta w-Du(w)-Dw(v)-\nabla r+F.
\]

Periodic integration cancels transport and pressure work; the Laplacian gives \(-D\). The accepted Lean result is exactly

\[
\operatorname{energyRate}=-2D-2C+2W,
\qquad
\operatorname{energyRate}+2D\le(2L+1)E+\int_Q|F|^2.
\]

Indeed, \(-C\le LE\) and Young's inequality gives \(2W\le E+\int_Q|F|^2\). This is a genuine differing-force PDE estimate, not merely scalar algebra. With an unforced comparator, \(F\) is the old force; with force cutoff, it is \((1-\rho)f\).

**Not yet assembled:** identifying `energyRate` with \(E'\) on a slab requires joint slab regularity and the baseline `PeriodicUniqueness.energy_hasDerivAt` adapter, plus endpoint continuity. FTC and the scalar primitives must then be instantiated. If these bridges yield \(E'\le kE+g\) with zero initial energy, the conditional scalar mechanism gives

\[
E(s)\le e^{A(s)}\int_0^s e^{-A(r)}g(r)\,dr,
\qquad A(s)=\int_0^s k(r)\,dr.
\]

The integral version here is explanatory mathematics, not a new accepted Lean composition. To certify tolerance \(\delta(s)^2\), the weighted integral must be at most \(e^{-A(s)}\delta(s)^2\). Neither this actual threshold nor pointwise growth preservation follows from the rate theorem. Whole-space pressure-flux cancellation is also not supplied by periodic cancellation.

## 4. Actual force-budget applicability

The source route is `ActualCandidateAssembly.selected_witness` → compact candidate construction in `MixedPeriodicAssembly` → `CandidateFromLimits.force`, the smooth extension of the activated compact residual. The witness's compact and periodic forces are distinct components; the latter is separated periodization, not arbitrary nonlinear superposition.

For full future-domain jet \(J_m(t,x)\), the accepted compact-candidate lemmas give an existential \(C_m>0\), uniform in future time and space, and

\[
\forall x,\quad \int_a^b\|J_m(t,x)\|\,dt\le C_m(b-a)
\quad(0\le a\le b).
\]

The integrability obligation is proved. For fixed \(\varepsilon>0\), choosing \(b-a<\varepsilon/C_m\) makes every such integral smaller than \(\varepsilon\). This is useful actual-force information, but the checked quantity is **not** \(\int\sup_x\|J_m\|\), a mixed spatial-time norm, a Sobolev norm, or the weighted solenoidal discrepancy required for strong stability.

Ordinary finite-volume/support arguments suggest mixed-norm bounds, but those adapters and quantitative constants have not been formalized here. Periodic integrals must use a cell, not all of R³. The construction's force constants, singular-reference amplification, evaluation embedding constants and lifespan must be compared together. Moving \(t_0\) changes the datum and all those requirements. One cannot choose a different restart on every later slab and claim a single evolution reaches \(H\).

**Actual force-to-stability applicability: OPEN.** Smoothness and bounded derivatives supply fixed-tolerance short budgets, not the requisite weighted, horizon-wide strong-norm smallness.

## 5. Review findings and obstructions

Agent 19 independently checked the AR18-01–08 dispositions and found no new high/medium documentation blocker within that scope. The retained conclusions are:

- **AR18-01, exact removal:** correct sign is \(p-\phi\). Origin-flat forcing need not vanish away from the origin or on any terminal slab. Even curl-free torus force need not be a periodic gradient: a nonzero constant vector has nonzero circulation around some fundamental cycle.
- **AR18-02, evaluation:** the repaired explanatory concentration example uses \(A(x)=\tfrac12\chi(x)(a\times x)\), with \(\chi=1\) near zero and compact support. Then \(\psi=\operatorname{curl}A\) is divergence-free and \(\psi(0)=a\ne0\). For \(w_\varepsilon(x)=\varepsilon^{-1}\psi(x/\varepsilon)\), \(\|w_\varepsilon\|_2^2=\varepsilon\|\psi\|_2^2\to0\), while \(|w_\varepsilon(0)|=\varepsilon^{-1}|a|\to\infty\). Small separated supports can be periodized inside a cell. Thus **L² closeness cannot control pointwise growth**. This is a mathematical stress test, not a newly formalized PDE counterexample.
- **AR18-03, amplification:** for \(H>0\), \(E(s)=(Hs-s^2/2)/(H-s)\) satisfies \(E(0)=0\), \(E'=E/(H-s)+1\) on \([0,H)\), and diverges despite source integral \(s\le H\). This refutes a generic unweighted-budget inference, not actual PDE stability. Failure of a sufficient upper-bound test does not prove actual error divergence.
- **AR18-04, local theory:** `Solution` hardcodes zero datum even when zero is outside its time set; restriction is not restart. No applicable arbitrary-data NS local existence/continuation theorem was located by the bounded source search. This is not a proof that no such theorem exists elsewhere. ODE Picard–Lindelöf is not NS local theory. In a reductio against hypothetical global A/B existence, that hypothesis could supply the comparator and horizon coverage, but not force removal or strong comparison.
- **AR18-05, energy:** signs, factor two, operator-norm majorant and viscosity-one normalization agree with Lean. Periodic pressure is essential. No slab FTC/Gronwall assembly, R³ pressure-flux closure or strong stability is implied. Reference compact support must not be assigned to a viscous comparator.
- **AR18-06, cutoff/zoom:** explanatory product calculus gives \(R_\nu(\rho u,\rho p)=\rho R_\nu(u,p)+\rho'u+(\rho^2-\rho)Du(u)\). Width-\(d\) switch derivatives cost \(d^{-k}\). Pointwise small zoom force does not give compact velocity. The actual-base \(r^{-2h}d_0\) identity obstructs locally uniform compactness only after an assembled-field transfer; no general weak-limit impossibility is proved. Covariance, pressure bounds, nonlinear convergence and nontriviality are still missing; changing amplitude normalization changes the equation.
- **AR18-07–08, provenance/labels:** cached-dependency warnings and superseded task-local classifications are explicit. Pressure absorption is research B; actual force budgets are research A. Relabeling discharges no mathematics.

## 6. Remaining research questions and next experiment

All [O1–O10](OBLIGATIONS.md) remain open:

1. Arbitrary-data internal/Comparator adapters, endpoint derivatives and domain/pressure/energy contracts.
2. Applicable fixed-positive-viscosity existence, uniqueness, persistence and continuation with adequate horizon coverage (or clearly stated hypothetical comparator existence in a reductio).
3. Actual terminal force vanishing or an admissible gradient potential.
4. Corrected pressure/class, exact-route uniqueness and terminal contradiction assembly.
5. Periodic slab energy differentiation, endpoint continuity, initial energy, FTC and Gronwall integration.
6. Whole-space error integrability and actual pressure/convection boundary-flux closure.
7. Genuine evaluation-controlling strong norm and fixed-viscosity NS stability, including nonlinear/pressure control and derivative counts. H² velocity/H³ gradient embeddings are proposed routes, not accepted stability results.
8. Actual removed-force mixed/strong norms and weighted threshold for **one fixed restart** throughout all needed presingular horizons.
9. Derived relative-error estimate, evaluation embedding, and actual axis-growth specialization or justified spatial compact reduction. All-space unbounded witnesses may escape spatially.
10. Residual scaling covariance, assembled transfer, compactness topology, nonlinear convergence, nontrivial limit, regularity/class and nonextension conclusion.

**Next narrowly scoped experiment (not performed):** close only the periodic finite-slab adapter in O5. Fix one \(t_0\) and \(0<S<H\); retain explicit smooth periodic arbitrary-common-datum fields and unequal-force PDE hypotheses. Combine `energy_hasDerivAt`, `forced_energy_rate_le` and continuous coefficient/source primitives to prove a single genuine cube-energy integral estimate with zero initial error on \([0,S]\). Acceptance requires explicit endpoint continuity, force integrability, pressure periodicity, viscosity one, strict compilation and axiom audit. It must introduce no existence or strong-norm premise disguised as an achieved result. A failure should retain its diagnostics. Success would close one integration bridge only—not O7–O9, horizon coverage or A/B.

## 7. Validation, reproducibility and trust boundary

### Final Agent 20 execution

The unchanged frozen validator completed with **exit 0**: all **13 strict compilations** passed (12 accepted files plus aggregate audit). Logs: [agent20-run.log](../../Research/UnforcedRestart/integration/agent20-run.log), [agent20-run.exit](../../Research/UnforcedRestart/integration/agent20-run.exit). No final validation failure is hidden.

Run from the exact isolated worktree:

```sh
cd /home/velvet/worktrees/unforced-restart-20260909T202951Z
python3 Research/UnforcedRestart/integration/validate.py
git diff --exit-code 597692fa5d55e07d810b2d96ead1a67972585425 --
git diff --cached --exit-code
git branch --show-current
git rev-parse HEAD
git status --short
```

Each compiler invocation uses `LEAN_NUM_THREADS=1`, isolated `LEAN_PATH`, and `lake env lean -j1 -DautoImplicit=false -DwarningAsError=true`. No build/install is invoked. Exact expanded commands, fresh exit codes and log paths are in [SUCCESS.json](../../Research/UnforcedRestart/integration/validation/SUCCESS.json); objects are confined to `integration/validation/lib/`.

Final evidence records:

- Lean **4.34.0-rc2**, aarch64, commit `6a10ac8c22beadecabdbb0919c2b50214762f91d`.
- **88 named exports**; **42,929 distinct project/research axiom closures** in [declarations.tsv](../../Research/UnforcedRestart/integration/validation/declarations.tsv).
- Closure distribution: 38,280 use all three permitted axioms, 3,664 only `propext`, 320 `propext, Quot.sound`, 665 none. Every named research export uses only `propext`, `Classical.choice`, `Quot.sound`; no custom axioms, `sorryAx`, unsafe project constants or challenge imports were accepted.
- **11,108 imported modules**, including **526 project/research modules**, with source/olean inventories in [dependencies.json](../../Research/UnforcedRestart/integration/validation/dependencies.json).
- Frozen accepted-source/audit/validator hashes, comprehensive Lean-file classification, eleven package pins, path isolation and before/after baseline checks passed.

### Independent Agent 19 evidence — distinct from this rerun

Inspected external report: `/tmp/agent19-validation.JEWFbX/REPORT.md`. It records all commands below exiting zero, independent source and actual Lean-environment enumeration (**88 named exports + 14 generated helpers**, all covered), fresh-log/inventory hash checks, and byte comparison of **all 2,335 baseline files**, including the five challenge files. HEAD/index/tracked worktree and full before/after status were unchanged in that pass. Its scripts and logs are external temporary artifacts, not committed or durable report dependencies.

To repeat those independent checks while that directory remains available:

```sh
python3 /tmp/agent19-validation.JEWFbX/independent.py
env LEAN_NUM_THREADS=1 \
  LEAN_PATH="$PWD/Research/UnforcedRestart/integration/validation/lib" \
  lake env lean -j1 -DautoImplicit=false -DwarningAsError=true \
  /tmp/agent19-validation.JEWFbX/Probe.lean
python3 /tmp/agent19-validation.JEWFbX/check-results.py
```

The last script includes comparison against Agent 19's saved status snapshot: this reporting pass intentionally adds this report/run logs, so reproducing that historical status-equality test unchanged will require accounting for those authorized additions. The repository validator is the self-contained reproduction route for current acceptance. Agent 20 did not rerun Agent 19's independent scripts or claim a second independent baseline byte audit.

**Trust boundary:** this is fresh research/audit elaboration against cached dependencies, with broad source/artifact inventory and transitive axiom checks. Separate source and object hashes do not establish clean build correspondence. It is not a clean dependency kernel rebuild, independent Comparator certification, full independent audit of the baseline candidate construction, Clay-prose equivalence proof, or certification of baseline C/D claims.

Historical rejected compiler/tooling diagnostics remain retained, including `integration/rejected-audit-elaboration.log`; failed drafts and initial resolver failures are excluded by the manifest. They are not accepted theorem evidence.

**Final disposition:** retain the isolated lemmas and honest obligation map. Do not publish or promote this package as an unforced restart, an A/B resolution, or a Millennium solution.
