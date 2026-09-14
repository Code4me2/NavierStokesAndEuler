# R³ restart data — checked bounded result

Owner: agent 2 / `r3-restart-data`. Namespace: `UnforcedRestart.R3RestartData`.

## Result and classification

**Unconditional formal result (actual-candidate analytic admissibility, class B):**
`actual_candidate_restart_data` proves existence of the actual assembled compact candidate `(u,p,f)` with `R3CompactCandidate.Properties u p f`, such that **every** real `t₀` satisfying `0 < t₀ < 1` gives

\[
a:\mathrm{EuclideanSpace}\ \mathbb R\ (\mathrm{Fin}\ 3)\to
\mathrm{EuclideanSpace}\ \mathbb R\ (\mathrm{Fin}\ 3),\qquad a(x)=u(t_0,x),
\]

with the delivered `Comparator.InitialVelocityConditionDecay a` and Lebesgue integrability of `x ↦ ‖a x‖ * ‖a x‖`. Thus the finite kinetic-energy requirement is proved independently of merely interpreting the decay predicate.

This is **not** an unforced existence, stability, or blowup theorem. The candidate still solves its original forced viscosity-one equation. Admissibility does not imply that the force disappears when restarting.

**Explicitly conditional formal lemmas:** the snapshot lemmas take precisely an existing `R3CompactCandidate.Properties u p f` proof and `t ∈ Ico 0 1`. Their hypotheses are discharged in the closed theorem above by `ActualCandidateAssembly.selected_witness`, not by a new solution predicate.

## Statements and proof details

The same compact set works for every presingular time and every spatial derivative:

\[
\exists K\text{ compact},\quad
\forall t\in[0,1),\ \forall m\in\mathbb N,
\quad\operatorname{tsupport}(D^m[x\mapsto u(t,x)])\subseteq K.
\]

`fixed_jet_support` proves this stronger topological-support statement. It first closes the ordinary velocity support inside the original closed compact set and then applies mathlib's `tsupport_iteratedFDeriv_subset`. Consequently every spatial jet is zero outside that set. No unsupported inference about derivative support at the boundary is needed: the boundary is retained in `K`.

`compact_smooth_decay` proves, for a smooth `a : Space → Space` with all jet topological supports contained in compact `S`,

\[
\forall m\in\mathbb N,\ \forall k\in\mathbb R,\quad
\exists C>0,\ \forall x,\quad
\|D^m a(x)\|\le C/(1+\|x\|)^k.
\]

The proof bounds the continuous weighted jet `‖D^m a(x)‖ (1+‖x‖)^k` on `S`, takes `C = max M 1`, and uses zero jets off `S`. The positive base makes arbitrary real exponents legitimate, including negative exponents. Constants depend on the slice, order and exponent; there is **no** uniform bound as `t₀ ↑ 1`.

`TimeLocalization.spatial_smooth_including_initial` supplies full spatial smoothness even at original time zero. `ComparatorBridge.divergence_eq` identifies the actual internal divergence with the delivered Comparator divergence. Compact support and continuity of the squared norm give actual whole-space Lebesgue integrability by `Continuous.integrable_of_hasCompactSupport`.

## Exact Lean source map

- `NavierStokes/ProblemStatement.lean:189–195`: `Solution` smoothness, divergence and viscosity-one residual. It **hardcodes zero original datum**, even under time restriction.
- `NavierStokes/R3CompactCandidate.lean:34–43`: `Properties`, especially `velocity_support`. `of_limits` constructs it from activated compact fields and extended residual force.
- `NavierStokes/TimeLocalization.lean:91`: `spatial_smooth_including_initial` restricts relative spacetime smoothness along a spatial slice.
- `NavierStokes/ComparatorBridge.lean:34`: `divergence_eq` (no argument-order ambiguity remains for a fixed slice).
- `NavierStokes/ComparatorDefinitions.lean:108–129`: actual smooth/divergence-free/real-exponent full-Fréchet-jet initial-data predicate.
- `.lake/packages/mathlib/Mathlib/Analysis/Calculus/ContDiff/FTaylorSeries.lean:857`: derivative topological-support inclusion.
- `.lake/packages/mathlib/Mathlib/MeasureTheory/Function/LocallyIntegrable.lean:622`: continuous compactly supported functions are integrable.
- `NavierStokes/CompactSpatialForceDecay.lean`: `jet_decay` was inspected; it concerns **spacetime force jets on the future domain** with time support. We did not misuse it as a spatial initial-data theorem; the spatial proof is separate.

**Actual construction connection (formally consumed):**
`NavierStokes/ActualCandidateAssembly.lean:1016–1051`, `Witness`, uses one selected schedule for `ASum`, `BSum`, `PSum`. Its final existential component is

```
∃ compactForcing,
  R3CompactCandidate.Properties
    (TimeLocalization.activatedVelocity
      (MixedPeriodicAssembly.cutVelocity ASum BSum))
    (TimeLocalization.activatedPressure
      (SpatialLocalization.cutPressure PSum))
    compactForcing
```

`witness` obtains that component from `GermCandidateAssembly.exists_candidate_witness_of_finite_stages` and `w.compact_candidate`. `selected_witness` at line 1070 closes the budget/threshold choice. Our closed theorem destructures this exact theorem and uses its **compact** component, not the periodic component or an arbitrary hypothetical candidate.

The prior Astra `final-report.md` and `skeptical-review.md` were independently read; source inspection here confirms their compact-first route and preserves their distinction between forced C/D and unforced A/B.

## Accepted Lean file and all exports

Only `Research/UnforcedRestart/r3-restart-data/Main.lean` is accepted. Imports: `NavierStokes.R3CompactCandidate`, `NavierStokes.TimeLocalization`, `NavierStokes.ActualCandidateAssembly`. No challenge/reference-placeholder import was added.

All names below have prefix `UnforcedRestart.R3RestartData.`:

| Declaration | Explicit inputs / output | Classification |
|---|---|---|
| `snapshot_smooth` | `Properties`, `t∈[0,1)` → full spatial smoothness | actual-field admissibility |
| `snapshot_divergence` | same → Comparator divergence zero at every `x` | actual-field operator bridge |
| `fixed_jet_support` | `Properties` → one compact set for every slice and jet | actual-field analytic support |
| `compact_smooth_decay` | smooth `a`, compact `S`, every jet supported in `S`, `m:ℕ`, `k:ℝ` → positive weighted bound | abstract analytic helper, not PDE stability |
| `snapshot_admissible` | `Properties`, `t∈[0,1)` → actual Comparator decay predicate | actual-field admissibility |
| `snapshot_compactSupport` | same → `HasCompactSupport` of slice | actual-field support |
| `snapshot_energy_integrable` | same → squared norm Lebesgue integrable | actual integral, class B |
| `actual_candidate_restart_data` | no hypotheses → assembled candidate with admissible, finite-energy snapshots for every `0<t<1` | unconditional actual-candidate result |

Inline `#print axioms` audits **all eight** exports; there are no new substantive definitions. Every closure is exactly `[propext, Classical.choice, Quot.sound]`, including the closed theorem's construction dependencies.

### Successful focused validation

Run from `/home/velvet/worktrees/unforced-restart-20260909T202951Z`:

```sh
env LEAN_NUM_THREADS=1 lake env lean -j1 \
  -DautoImplicit=false -DwarningAsError=true \
  -o Research/UnforcedRestart/r3-restart-data/out/Main.olean \
  -i Research/UnforcedRestart/r3-restart-data/out/Main.ilean \
  Research/UnforcedRestart/r3-restart-data/Main.lean \
  > Research/UnforcedRestart/r3-restart-data/out/Main.log 2>&1
```

**Exit 0**, recorded in `out/Main.exit`; complete inline axiom output in `out/Main.log`. This checks fresh research elaboration against prepared worktree-local baseline artifacts, not an independent clean baseline rebuild or Clay-prose equivalence audit. No broad build, installation, configuration edit, commit or push. `git diff --exit-code` returned 0 for tracked sources.

A first attempt failed because `positivity` did not unfold the function expression in the real-power continuity side condition. Explicitly changing that goal to `1 + ‖x‖ ≠ 0` fixed it. That failed run was not accepted; the final strict compile and all closures pass. No incomplete `.lean` attempts remain.

## Endpoint, quantifier and obstruction audit

- **Original time zero:** slice lemmas remain valid there, but the closed restart theorem uses the requested strict `0<t₀<1`.
- **Singular endpoint:** `t₀=1` is excluded. No classical endpoint trace is inferred from a total Lean function value.
- **New initial datum:** need not be zero; nor do we assert it is nonzero for every positive time (activation is initially zero). `Solution.mono` does not supply a restarted nonzero-datum solution.
- **Viscosity:** the imported internal candidate is viscosity one. Snapshot admissibility itself is viscosity independent, but no other-viscosity PDE is claimed.
- **Whole space:** finite energy uses R³ Lebesgue volume. No whole-space integral of a periodic field is used.
- **Pressure:** spatial velocity support does not assert compact pressure support from the abstract `Properties` fields. Snapshot initial-data admissibility does not require pressure data, so no pressure decay premise was smuggled in.

**Unproved bridges / failure criteria for an unforced reduction:** applicable positive-viscosity local existence and uniqueness for this nonzero datum; a correctly translated closed-half-line or presingular PDE class; terminal force vanishing or admissible gradient absorption; quantitative strong-norm control of any unforced competitor up to the candidate's growth regime. None follows from these data lemmas. Success here means admissibility of the actual snapshot, which is achieved; claiming an unforced solution follows would fail the task's mathematical acceptance gate.

No conjecture or unformalized analytic deduction is needed for the snapshot conclusions above. The possible unforced restart program remains an explicitly unproved program.
