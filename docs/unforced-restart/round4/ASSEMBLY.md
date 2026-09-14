# Selected-force mean: complete assembly

## Result and exact type

`Research/UnforcedRestart/Round4/Integration/Assembly.lean` exports
`UnforcedRestart.Round4.Integration.selected_force_cell_mean_zero`:

```lean
∀ (t : ℝ), t ∈ Set.Icc 0 1 → ∀ (i : Fin 3),
  (∫ y : PeriodicIntegration.Coords,
    WitnessFeasibility.selected.forcing (t, PeriodicIntegration.toSpace y) i
    ∂(volume.restrict (Set.Icc 0 1))) = 0
```

This is the unchanged selected force, with genuine coordinate product Lebesgue cell measure. There are no cancellation, integrability, arbitrary-candidate, or terminal-velocity hypotheses. `Acceptance.lean` restates this literal integral, applies the producer, and prints both actual theorem types and the acceptance axiom closure.

## Proof composition

1. Frozen `Integration/Main.lean` establishes smoothness/support and integrability of the selected compact temporal and advection components. It uses the earlier selected temporal zero integral and divergence-free convective cancellation.
2. Frozen `PressureIntegral/Main.lean` and `LaplacianIntegral/Main.lean` provide actual integrability and cancellation of the gradient and Laplacian. All four components are integrable before `integral_add`/`integral_sub` split the residual (viscosity exactly one). Thus `selected_compact_residual_integral_zero` is not a totalized nonintegrable-integral shortcut.
3. Worker `PressureIntegral/Components.lean` and `LaplacianIntegral/Regularity.lean` are imported and replayed unchanged; their explicit regularity contracts remain available. No worker repair or ownership handoff was needed.
4. Worker `PeriodizationTransport/Cell.lean` identifies the actual selected periodic force cell mean with the compact residual whole-space integral, without extra premises. Its proof includes coordinate volume transport, lattice summability/reindexing, half-open fundamental-domain tiling, and null closed-cell faces.
5. `selected_force_cell_mean_zero_interior` composes that transport with compact cancellation for `0<t<1`.
6. For each component, `selectedCellMean_continuousOn` supplies continuity on `[0,1]` of the actual smooth force mean. Restrict its continuity within the interval to `(0,1)` and use `ContinuousWithinAt.eq_const_of_mem_closure` and `closure_Ioo`. This proves both endpoints without using terminal velocity regularity.

## Fresh strict chain

All paths below are relative to `Research/UnforcedRestart/Round4/Integration/`.
Chain receipt: `chain-p01zsnon/receipt.json` (all **11 exits 0**).

| Source relative to Round4 | Fresh receipt directory | Printed closures |
|---|---|---:|
| PressureIntegral/Main.lean | strict-9_6fs6u8 | 10 |
| PressureIntegral/Components.lean | strict-g1ou24v5 | 4 |
| LaplacianIntegral/Main.lean | strict-vbtzde0t | 8 |
| LaplacianIntegral/Regularity.lean | strict-tbhi0iyz | 6 |
| PeriodizationTransport/Main.lean | strict-rmeiy0dw | 8 |
| PeriodizationTransport/Residual.lean | strict-5zcu1dhj | 3 |
| PeriodizationTransport/Cell.lean | strict-ymgmxe52 | 5 |
| Integration/Main.lean | strict-0q4jhlgx | 8 |
| Integration/Assembly.lean | strict-cq82w9r4 | 2 |
| Integration/Acceptance.lean | strict-f2z0lpmk | 1 |
| Integration/FinalAudit.lean | strict-t0s23j3d | aggregate |

All **55** printed closures contain only `propext`, `Classical.choice`, `Quot.sound`. Aggregate audit checks **42,982** imported project/helper constants across **11,113** imported modules, rejecting unsafe declarations, forbidden axioms and challenge imports. Imported module source/object correspondence is reconstructed and hash-checked by the final verifier.

Each compilation has its own output library and receipt, `autoImplicit=false`, `warningAsError=true`, one thread, 600-second timeout, CPU quota 100%, 6 GiB memory/no swap. Fresh Round4 sources were compiled in topological order using only earlier fresh outputs and the pinned Round3 replay/clean source-built dependencies. No dependency build, Lake/cache command, baseline change, commit or push. Compiler/core/runtime/host are trust roots; no independent kernel checker is claimed.

## Freeze and reproduction

`Integration/FINAL-MANIFEST.json` is the final hash freeze of accepted sources, strict receipts/logs/objects, verifier/build scripts, and assembly documentation. This is a hash freeze, not WORM storage. Historical freezes and the old failed acceptance remain intact as evidence of the earlier incomplete attempt. The new successful acceptance is `Acceptance.lean`, not `AcceptanceTest.lean`.

From the repository root, read-only verification:

```sh
python3 -B Research/UnforcedRestart/Round4/Integration/verify_final.py
```

Separate receipt generation (writes only a fresh verification directory):

```sh
python3 -B Research/UnforcedRestart/Round4/Integration/record_final.py
```

Optional strict rebuild (writes fresh chain/build directories, does not replace the accepted freeze):

```sh
python3 -B Research/UnforcedRestart/Round4/Integration/replay.py
```

The verifier hashes the actual imported objects and their sources, rather than trusting an import name or a cached object alone. It validates the 3,234-file external historical preservation manifest and snapshot, HEAD/index and tracked diffs, and authorized addition paths. It checks global refs independently; a mathematical PASS does not override a preservation failure. Absolute paths make this reproduction specific to this checkout and its pinned external dependency tree.

## Scope limitation

**The mean-zero target on `[0,1]` is discharged. Zero mean does not decide curl and does not imply gradient forcing.** No pressure absorption, unforced restart, A/B, or comparator-growth conclusion follows merely from this theorem.
