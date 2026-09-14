# Round4 final report — selected-force mean theorem proved

**The bounded mathematical target is complete. CURL remains unresolved.**
The original exact-ref preservation condition still fails; the separate
concurrent-ref-aware check accepts only the exact addition documented in
[SUPERVISOR-REF-ADDENDUM.md](SUPERVISOR-REF-ADDENDUM.md). No Git ref is changed
by this repair. These preservation results are not mathematical hypotheses.

## Exact theorem and sources

`UnforcedRestart.Round4.Integration.selected_force_cell_mean_zero` in
`Research/UnforcedRestart/Round4/Integration/Assembly.lean` states:

```lean
(t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) (i : Fin 3) :
  (∫ y : NavierStokes.PeriodicIntegration.Coords,
    UnforcedRestart.Round3.WitnessFeasibility.selected.forcing
      (t, NavierStokes.PeriodicIntegration.toSpace y) i
    ∂(MeasureTheory.volume.restrict (Set.Icc 0 1))) = 0
```

The domain is the ordinary coordinate cube `[0,1]³`, with product Lebesgue
volume (`Coords = Fin 3 → ℝ`). `toSpace` is the explicit coordinate equivalence
to Euclidean `Space`. The force is the unchanged `WitnessFeasibility.selected.forcing`,
not an existentially chosen compact-force witness. There are no additional
hypotheses: only time membership and a component index. `Integration/Acceptance.lean`
checks the literal universally quantified target.

All source paths below are relative to `Research/UnforcedRestart/`:

- `Round3/WitnessFeasibility/Certificates.lean`:
  `WitnessFeasibility.selected_force_eq_residual` connects the actual force to
  its viscosity-one Navier–Stokes equation on `0 < t < 1`.
- `Round3/MeanTopology/Main.lean`: `MeanTopology.compactVelocity`,
  `selected_compact_momentum_zero`, `selected_compact_transport_zero`.
- `Round3/SelectedBridge/Main.lean`:
  `SelectedBridge.compact_component_integral_hasDerivAt` and
  `selected_compact_temporal_integral_zero` justify time differentiation and cancellation.
- `Round4/PressureIntegral/Main.lean`: `PressureIntegral.compactPressure` and
  `selected_compact_pressure_integral_zero`; `Components.lean` supplies
  `gradient_component_integrable`.
- `Round4/LaplacianIntegral/Main.lean`:
  `LaplacianIntegral.selected_compact_laplacian_integral_zero`;
  `Regularity.lean` supplies `laplacian_component_integrable`.
- `Round4/Integration/Main.lean`:
  `Integration.temporal_component_integrable`, `advection_component_integrable`,
  `advection_component_integral_zero`, `selected_compact_residual_integrable`,
  `selected_compact_residual_integral_zero`.
- `Round4/PeriodizationTransport/{Main,Residual,Cell}.lean`:
  `PeriodizationTransport.compactResidual`, `selectedCellMean`,
  `selected_cell_integral_transport`, `selectedCellMean_continuousOn`.
  Velocity and pressure use the same `selected.schedule`; actual PDE and germ
  agreement connect the selected force to the periodized compact residual.

## Human-readable calculation and endpoint bridge

For `0 < t < 1`, let `v` and `q` be those complete activated, localized compact
velocity and pressure fields. Every residual component is integrable before
linearity is used. For each component `i`,

```text
∫_[0,1]³ f_i(t,y) dy
 = ∫_ℝ³ [∂t v_i + (v·∇)v_i − Δv_i + ∂i q] dx
 = d/dt ∫_ℝ³ v_i dx + 0 − 0 + 0
 = 0.
```

Zero compact momentum follows from incompressibility and compact-support
integration by parts. Differentiation under the integral uses fixed compact
support, joint interior regularity and a local dominating bound. Advection
cancels using proved divergence freedom; pressure and Laplacian cancel by
compact derivative integration. Derivatives retain activation and cutoff
contributions. Cell transport uses measure-preserving coordinates, lattice
reindexing, justified sum/integral interchange, half-open tiling and null
closed-cell faces—not a replacement measure or totalized nonintegrable integral.

`Integration.selected_force_cell_mean_zero_interior` supplies interior zero.
`PeriodizationTransport.selectedCellMean_continuousOn` gives continuity of the
**actual force mean** on `[0,1]`. In `Assembly.lean`,
`ContinuousWithinAt.eq_const_of_mem_closure` and `closure_Ioo` extend the value
zero from `(0,1)` to both endpoints. Thus the initial and terminal force means
are zero without terminal velocity regularity or equality of future extensions.
New strict specializations in `Round4/Integration/RepairEndpoints.lean` are:

- `UnforcedRestart.Round4.Integration.selected_force_initial_mean_zero`;
- `UnforcedRestart.Round4.Integration.selected_force_terminal_mean_zero`.

Neither asserts pointwise force zero.

## Review and fresh repair validation

The two supplied independent reviews found no mathematical or Lean defect.
Their external evidence directories are `/tmp/round4-independent-LbkTWpdi/`
and `/tmp/round4-independent-VYXz7CEm/`. Both reported 11 successful strict
replays, 55 export closures, 42,982 imported project/helper constants across
11,113 modules, and fresh source/object correspondence. The second additionally
reported byte-identical objects, 69 Round4 declarations/helpers checked after
importing `FinalAudit`, and supplemental volume/integrability/endpoint checks.
These are attributed review results, not a claim that this repair is a third
independent review.

Fresh repair evidence lives in `Research/UnforcedRestart/Round4/Integration/`:

- `repair-replay.log`, `chain-7hszmr9h/receipt.json`: all 11 accepted sources
  rebuilt unchanged, topologically, with `-j1 -DautoImplicit=false
  -DwarningAsError=true`; all exits 0.
- `repair-endpoints.log`, `strict-txfa5ys7/receipt.json`: endpoint specializations,
  exit 0, same strict flags (12 strict compilations total).
- `REPAIR-MANIFEST.json`: versioned freeze, preserving the original manifest
  and recording old/new hashes of only PLAN and this report among old entries.
- `verify_repair.py`, `repair-verification.json`: original verification checks
  reused with the new manifest, plus fresh/frozen object equality, every direct
  import's provenance, source scans, and supplemental endpoint closure checks.
  The 55 accepted exports and two endpoint exports use only `propext`,
  `Classical.choice`, `Quot.sound`; imported project coverage remains 42,982
  constants / 11,113 modules. No forbidden axioms, unsafe project declarations,
  challenge imports or compiler diagnostics are accepted.

Historical dependencies are hash-verified and reused read-only, not rebuilt.
Compiler/core/runtime/host remain trust roots; no independent kernel checker ran.
Focused compiles retain one thread, CPU quota 100%, 6 GiB/no swap and 600 s limits.

Recheck the versioned package read-only:

```sh
python3 -B Research/UnforcedRestart/Round4/Integration/verify_repair.py
```

The original `verify_final.py` deliberately remains unchanged: it still rejects
the historical documentation hash drift. Historical failure receipts and
`FINAL-MANIFEST.json` are not overwritten. The PLAN hash transition is
`8ba501b6843db28cfc4c2cf37f39651e7035000bf0cbc38231ebf2adb21d82f6` →
`74264ca504f87f65691bc8ec172d11e8cf585e46a6b240d2f7e4c78feb7d25b9`.
This repair does not retroactively certify the old freeze.

All 3,234 preserved files, read-only snapshot sources, HEAD, index and tracked
diffs are checked unchanged; additions are restricted to the two Round4 trees.
The original ref status remains `FAIL_SHARED_REFS_CHANGED`. The separate
`PASS_EXACT_DOCUMENTED_ADDITION` requires every old ref unchanged, no deletion,
and exactly this added name/value:

```text
refs/heads/docs/native-weighted-control-20260912T185404Z
26e896edbdbe1215c0d50ddba24b2b6453646f5f
```

It relies explicitly on the supervisor provenance addendum, not on an inference
that any extra branch is harmless. No earlier accepted/source/config files,
historical artifacts or manifests were edited; no commits, pushes or ref writes.

## Remaining CURL problem

Mean zero eliminates only the constant spatial mode. The curl of this actual
selected force is still undecided. Pressure absorbability would require further
proved structure (in particular curl information), not just its integral.
This result does not prove force zero, gradient forcing, unforced restart,
unforced growth, or further A/B/comparator progress. See [ASSEMBLY.md](ASSEMBLY.md)
for the original assembly account; [PRIOR-PARTIAL-REPORT.md](PRIOR-PARTIAL-REPORT.md)
is retained as historical partial-stage evidence.
