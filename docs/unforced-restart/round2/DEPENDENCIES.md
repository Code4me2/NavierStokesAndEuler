# Round2 proof dependency / obligation graph

Status key: **K1** frozen checked research; **K2** newly strictly elaborated and audited, cached dependencies only; **A** ordinary-analysis derivation, not newly Lean-checked; **U** unproved bridge; **H** heuristic diagnostic. Every PDE theorem is conditional on its stated field contracts. Neither K1 nor K2 supplies comparator existence. Machine-readable counterpart: `DEPENDENCIES.json`.

## Accepted-source dependency DAG

```text
baseline SolutionDifference + PeriodicIntegration + PeriodicUniqueness
  ├─ K1 difference-equation (literal unequal-force residual subtraction)
  ├─ K1 energy-comparison (actual cube rate inequality)
  └─ K1 gronwall-threshold ← baseline GronwallInterior
          │
          └─ K2 PeriodicSlab/Main.lean ← Mathlib FTC
                ├─ force_energy_continuousOn
                ├─ slab_energy_derivative_le ← energy-comparison
                ├─ primitive_on_slab (generic FTC; literal integrals)
                └─ periodic_slab_comparison ← all three + weighted_budget
                      [derived B_S, zero common-datum error, closed endpoints]

K2 ActualForce/Main.lean ← K2 PeriodicSlab/Main.lean
  ├─ cubeIntegral_constant (unit cell volume checked)
  ├─ cell_energy_le ← cubeIntegral_constant + cube integral monotonicity
  ├─ candidate_shift_force_continuous ← CandidateProperties.force_smooth
  └─ candidate_cell_budget
       ← periodic compact-slab bound + candidate force periodicity
       ← cell_energy_le + candidate_shift_force_continuous + primitive_on_slab
       [∃C>0 uniform on fixed [0,H]; ∫₀ˢ∫Q |f(t0+r)|² ≤ C²s]
```

The implementation dependency ActualForce → PeriodicSlab is not a mathematical circle: ActualForce uses only the continuity/FTC tools, **not** the final PDE comparison to prove its budget. Application then supplies ActualForce's continuity output to PeriodicSlab's PDE theorem. The latter never requires the numerical budget bound as a hypothesis.

All twelve inherited sources remain accepted with their exact frozen hashes and 88 exports. No inherited research source imports Round2. Compile order: the original twelve in manifest order, PeriodicSlab, ActualForce, the unchanged frozen audit, then the new audit. The new aggregate audit imports all fourteen sources and enumerates all imported project/research constants and generated helpers, not just the 96 named exports.

## Application graph (AND means every predecessor is required)

```text
selected candidate [baseline construction; not independently recertified]
  → K1 datum admissibility + K1 forced translation
  → U O1 complete arbitrary-data Comparator adapter
       AND U O2 comparator existence / one comparator covering every S<H
       AND K2 finite-slab comparison
  → finite-slab L² control only; NO edge from L² to point evaluation

candidate global future jets [K1/source contracts]
  → K2 candidate-contract squared L² time/cell budget
  → A ordered spatial derivative restrictions + cell/support volume + Parseval
  → A L¹_t H³_B / L²_t H²_B projected-force budgets

baseline PeriodicSobolev evaluation theorem
  AND A multiindex/Bessel/derivative norm comparisons
  AND U O7 checked viscous H³ commutator/strong stability theorem
  AND U O8 actual weighted smallness, constants and nonlinear bootstrap
  AND U O9 selected-axis value wrapper + derived relative error
  AND U O1/O2 coverage and endpoint-continuous comparator
  → unproved growth-transfer contradiction

A presingular actual mean(f)=0
  AND U O3 actual curl(f)=0 on one WHOLE terminal slab
  → A smooth periodic potential f=∇φ
  AND K1 minus-sign pressure correction
  AND U O4 admissibility/endpoints/equal-force uniqueness assembly
  AND U O1/O2
  AND U axis_value_wrapper (selected reference-axis growth specialization)
  → alternative unproved exact-removal contradiction
```

`axis_value_wrapper` is the reference-growth specialization alone, not O9's derived relative-error transfer. The exact-removal route does not require O7/O8 or perturbative relative-error machinery.

O2 may be an explicitly hypothetical global existence assumption in a reductio, not a newly proved local-existence theorem. That conditional choice does not discharge O7–O9. O1's full boundary adapter is not needed for the raw interior-PDE L² theorem, but is needed before claiming the Comparator supplies those hypotheses. O6 (whole-space boundary flux/energy) and O10 (scaling/compactness) remain separate open branches; periodic proofs provide neither.

## Obligation dispositions

| ID | Round2 disposition |
|---|---|
| O1 | OPEN: reference translation checked historically; no new complete arbitrary-datum Comparator/endpoints adapter. |
| O2 | OPEN or explicit hypothetical input; no construction/existence/continuation theorem. |
| O3 | OPEN: mean compatibility is an ordinary-analysis deduction for the actual presingular periodic construction; selected whole-slab curl vanishing remains unknown. |
| O4 | OPEN: pressure sign checked, actual potential and final admissibility/uniqueness assembly missing. |
| O5 | **Raw periodic finite-slab composition CLOSED at K2/cached level.** Clean provenance and actual Comparator specialization remain separate. No uniform gradient bound as S→H. |
| O6 | OPEN: no R³ pressure/convection flux closure inferred from reference support. |
| O7 | PARTIAL: concrete baseline evaluation norm located; viscous strong comparison remains unformalized conditional analysis. |
| O8 | PARTIAL: actual candidate-contract L² mixed budget now K2; strong norms A; actual weighted threshold OPEN. |
| O9 | OPEN: no derived relative error; selected-axis germ/jet assembly not supplied. |
| O10 | OPEN: no compactness/nonlinear-limit bridge. |

## Negative evidence has no implication arrow to impossibility

H: base saddle strain suggests that a coarse positive global-norm amplification coefficient overwhelms the reference speed exponent. A: the scalar model calculation proves failure of that sufficient envelope **if its stated coefficient/forcing premises hold**. U: transfer of the base strain to the selected candidate's jets and any sharp comparator propagator estimate. There is no arrow from the failure of an upper bound to a lower bound on actual error, regularization after force removal, or impossibility of all force-removal mechanisms.
