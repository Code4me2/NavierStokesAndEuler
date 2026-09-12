# Round4 — partial failure of the end-to-end goal

**The requested selected-force zero cell mean on [0,1] is NOT proved.**
The exact acceptance test was run and failed (exit 1):
`Research/UnforcedRestart/Round4/Integration/AcceptanceTest.lean`, receipt
`Integration/strict-7b4qdio7/receipt.json` under the same Round4 source root.
Its final producer `Integration.selected_force_cell_mean_zero` does not exist.
This is a fail-closed test, not an accepted theorem source.

## Completed mathematics, same witness throughout

Five strictly compiled new mathematical sources, 37 printed export closures:

| Source relative to Research/UnforcedRestart/Round4 | Completed contract | Strict receipt under Integration |
|---|---|---|
| PressureIntegral/Main.lean | Selected activated compact pressure smoothness/support, actual gradient component integrability and cancellation | strict-pu_v_ph4/receipt.json |
| LaplacianIntegral/Main.lean | Same activated compact velocity; second-partial support, actual Laplacian component integrability and cancellation | strict-kq0n58kt/receipt.json |
| PeriodizationTransport/Main.lean | Correct coordinate volume transport, selected force residual/representative equality, genuine cell functional and force-mean continuity | strict-7pvbwp0j/receipt.json |
| PeriodizationTransport/Residual.lean | Uniform compact residual support and actual selected forcing = literal lattice periodization | strict-u8436kce/receipt.json |
| Integration/Main.lean | Temporal/advection integrability; actual advection cancellation; complete compact residual splitting and zero component integral | strict-vdtgmok2/receipt.json |

The assembled theorem is precisely `Integration.selected_compact_residual_integral_zero`:
for every `t ∈ (0,1)` and `i : Fin 3`,

`∫ x : Space, PeriodizationTransport.compactResidual (t,x) i = 0`.

All four residual terms have integrability producers. This does not exploit a totalized nonintegrable integral. `compactResidual` uses the selected schedule and both activations, with viscosity exactly one. `WitnessFeasibility.selected` and `selected.forcing` are unchanged; `selected.candidate` discharges existing witness obligations. There is no arbitrary-candidate implication or force-mean cancellation premise.

## Missing composition

The exact remaining mathematical adapter is the unit-cell integral of this residual's literal periodization = its whole-space integral. See [PeriodizationTransport.md](PeriodizationTransport.md) for its explicit statement. The support is separated, but the cell meets multiple translated pieces; pointwise representative equality alone is not integral transport. This adapter was not implemented. After it, the actual force-mean continuity must still be composed with interior zero to reach both endpoints. That endpoint composition is also not claimed complete.

Spatial convention is explicit: `Space = EuclideanSpace ℝ (Fin 3)` for the PDE and whole-space integral; `Coords = Fin 3 → ℝ` for the cell. `PeriodicIntegration.toSpace` is the coordinatewise identity continuous linear equivalence, now proved measure-preserving. The cell uses `volume.restrict (Icc 0 1)` on Coords, genuine product Lebesgue measure. No fake cell integral or replacement measure. No velocity regularity at t=1. The checked endpoint continuity concerns the smooth actual force only.

## Validation and freeze

* Read the six accepted Round3 sources and FINAL-REPORT; reverified the fresh six-source replay and aggregate receipts read-only before work. Logs: Integration/prior-replay-verification.log and prior-aggregate-verification.log (both exit 0).
* FREEZE-1.json freezes the three initial workstream outputs before Integration imports; FREEZE-2.json freezes all five accepted new mathematical sources/objects. Ownership is nonoverlapping and sequential, not claimed parallel agents. Earlier sources/objects are hash-pinned.
* Every focused attempt uses a unique output path, `autoImplicit=false`, `warningAsError=true`, one thread, CPU quota 100%, 6 GiB/no swap, 600-second timeout. No weakened checks or heartbeat increases. Failed exploratory compilations remain recorded, never accepted as proof.
* New imported-project/helper audit: Integration/strict-s8judypi/receipt.json, exit 0; **42,952 constants, 11,108 modules**. Export closures are exactly reconciled with all 37 source print commands; only propext, Classical.choice, Quot.sound. Unsafe imported project declarations are rejected.
* Integration/verify.py checks all imported module source/object correspondence against the previous aggregate/source-build records or the new frozen strict receipts. It checks the current accepted sources, outputs, logs, inherited research inputs and preservation. `--record` creates a unique verification directory; ordinary invocation is read-only. The verification receipt records the end-to-end failure, not success.
* Source-built dependency tree `/home/velvet/research-builds/unforced-round2-clean-20260909T221339Z` was reused read-only. No full build, dependency rebuild, Lake/cache command or duplicate build. Installed compiler/core/runtime and host remain trust roots. No new independent Comparator/Nanoda check.

## Preservation, including an explicit shared-ref failure

Before Round4 writes, an external manifest inventoried **3,234** preexisting files:
`/home/velvet/research-builds/unforced-round4-preserved-sf3yoys5/manifest.json`,
SHA256 `d1087cfeda45b6cf8d62e5ad8e89e2230cbcd84038c6fabfcf831a27cdee026a`.
Its adjacent `source/` snapshot includes the current Round3 sources, reports and structured receipts as ordinary read-only copies. No WORM/sudo/approval gate.

Earlier validated Git snapshot `e970490cf8f0cfb41fca101c62702fab7347c17c` preserves rounds1/2, **not Round3**.

All 3,234 preexisting inventoried files and external source copies verify unchanged. Worktree HEAD and index are unchanged; tracked/index diffs are empty. Worktree additions are only in the two authorized Round4 subtrees. This session ran no commit/push/merge/ref-writing command and did not touch the original checkout/published proof or prior evidence.

**However, global refs do not compare equal to the initial snapshot:**
`refs/heads/docs/native-weighted-control-20260912T185404Z` appeared, pointing to `26e896edbdbe1215c0d50ddba24b2b6453646f5f`. It was not created by this session; its provenance is not certified here. It was left untouched. The final verifier reports `FAIL_SHARED_REFS_CHANGED` and exits 1 rather than weakening the preservation test or claiming unchanged refs.

The final status therefore has two explicit failures: incomplete mathematical target and changed shared-ref inventory. Neither is an obstruction theorem. No curl, absorption, A/B or comparator-growth conclusion follows.

## Contracts

* [PressureIntegral](PressureIntegral.md): discharged on (0,1).
* [LaplacianIntegral](LaplacianIntegral.md): discharged on (0,1).
* [PeriodizationTransport](PeriodizationTransport.md): pointwise/coordinate producers checked; cell-integral contract unfulfilled.
* [PLAN](PLAN.md): exact target, source map, domains, ownership and acceptance rules.
