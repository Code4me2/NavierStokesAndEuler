# LaplacianIntegral — contract discharged

Exclusive source: `Research/UnforcedRestart/Round4/LaplacianIntegral/Main.lean`.
Imports only frozen Round3 SelectedBridge, not a Round4 sibling. Frozen in Integration/FREEZE-1.json and FREEZE-2.json.

Velocity is exactly `Round3.MeanTopology.compactVelocity`, with the selected schedule and activation unchanged.
For `0 < t < 1`, every component and coordinate direction:

* `secondPartial_smooth`, `secondPartial_compact`, `secondPartial_integrable` provide actual second-partial regularity, support and integrability.
* `secondPartial_integral_zero` uses compact first-derivative support and integration by parts.
* `laplacian_component` identifies the PDE's actual vector Laplacian component with the finite sum of these second partials.
* `laplacian_component_integrable` justifies summation/splitting.
* `selected_compact_laplacian_integral_zero` proves
  `∫ x : Space, spatialLaplacian compactVelocity t x i = 0`.

Measure: Euclidean Lebesgue volume, not a finite substitute.
Strict compile exit 0: `Research/UnforcedRestart/Round4/Integration/strict-kq0n58kt/receipt.json`.
Eight exact printed export closures; only propext, Classical.choice, Quot.sound.
The earlier failed attempt is retained as diagnostics, not accepted evidence.
No velocity regularity at time one is used or asserted.

## Follow-up: explicit support/regularity and integrability interface

Read PLAN and FINAL-REPORT; the end-to-end partial failure remains unchanged.
The frozen `Main.lean` above is unchanged. New accepted source:
`Research/UnforcedRestart/Round4/LaplacianIntegral/Regularity.lean`.
It imports only the owned frozen `Main`, not any sibling workstream.
All exports below are in `UnforcedRestart.Round4.LaplacianIntegral`:

* `laplacian_zero_outside`: actual vector `spatialLaplacian compactVelocity t x = 0` outside `SpatialLocalization.supportCylinder`, for every time. The proof transports the full space-time zero germ through `ResidualRegularity.spatialLaplacian_congr`; no endpoint regularity is involved.
* `laplacian_support`: the operator's `tsupport` lies in that same closed cylinder.
* `laplacian_compact`: vector operator has compact support.
* `laplacian_component_smooth`: every component is `ContDiff ℝ ∞` for `t ∈ Ioo 0 1`, via the actual finite-sum operator identity in Main.
* `velocity_integrable`, `velocity_component_integrable`: vector and component Lebesgue integrability of the actual selected compact velocity on interior slices.

The existing `secondPartial_compact` obtains compact second-partial support by applying `compact_partial`, `compact_component`, then `compact_partial` to the very same velocity. `secondPartial_smooth` and `secondPartial_integrable` justify the summation used by `laplacian_component_integrable` and `selected_compact_laplacian_integral_zero`. No desired cancellation is an input hypothesis.

### Exact source bridges (read-only; no duplicate sibling implementation)

`Round3.MeanTopology.compactVelocity_smooth_slice` and `compactVelocity_compact_support` directly supply the new velocity-integrability proof. That module's `selected_compact_transport_zero` is the checked scalar-derivative transport cancellation. `Round4.Integration.advection_component_integral_zero` converts it to the PDE's actual `advection` using `SolutionDifference.fderiv_component`.

`Round3.SelectedBridge.selected_compact_temporal_integral_zero` is cancellation for the actual `temporalDerivative`. Its source obtains differentiation under the integral on a closed interior slab using `compactVelocity_contDiffOn_slab`, `compactVelocity_uniform_support` and `compact_component_integral_hasDerivAt`.

Existing read-only `Round4.Integration.temporal_component_integrable` and `advection_component_integrable` supply the two remaining residual-splitting integrability facts. They derive temporal smoothness from `SelectedBridge.compactVelocity_smoothAt` and `ResidualRegularity.contDiffOn_temporalDerivative`, temporal support from the zero germ, and advection smoothness/support from the same velocity. They are already composed with this owner's Laplacian exports in `Integration.selected_compact_residual_integrable` and `Integration.selected_compact_residual_integral_zero`. This follow-up does not import or modify Integration.

### Fresh strict evidence

Reproduction from the worktree root:

```sh
python3 Research/UnforcedRestart/Round4/LaplacianIntegral/check.py \
  Research/UnforcedRestart/Round4/LaplacianIntegral/Regularity.lean \
  Research/UnforcedRestart/Round4/Integration/strict-kq0n58kt/receipt.json
```

`check.py` is an unchanged copy of the existing focused checker, located in this owner's subtree so every new output stays owned. It verifies the previous replay pins/artifacts and imported Main source/objects before compilation. Dependency objects are reused read-only; private research copies and fresh outputs are in a unique directory.

Fresh receipt: `Research/UnforcedRestart/Round4/LaplacianIntegral/strict-ie2nck_p/receipt.json`, **exit 0**. Exact command/environment and input/output hashes are recorded there. Flags: `-j1 -DautoImplicit=false -DwarningAsError=true`; systemd scope CPUQuota=100%, MemoryMax=6G, MemorySwapMax=0, TasksMax=32; timeout 600 seconds. No dependency build, Lake/cache command, or heartbeat increase. All six printed export closures contain exactly `propext`, `Classical.choice`, `Quot.sound`; no holes or added axioms.

SHA256:

| File | Hash |
|---|---|
| Owned `Main.lean` (unchanged) | `144115d91bca4a94f75cf9bc5647f6a58c1c76589c31e831c8628534008d6c71` |
| Owned `Regularity.lean` | `0e7cfabb0c9788386d4f57caccb83d33cd09696fd7d78863e5d04117082f4d6a` |
| Fresh `Regularity.olean` | `d97aa74f2f63e2aa80597208456adc463f2c40c5cc8836f86e1716d27bb6b980` |
| Fresh `compile.log` | `d01fba7c71d1afaf10abe283fc33d6209ce894de516277a4c0849603a1bd8409` |
| Round3 `MeanTopology/Main.lean` | `0c106afc75bcfed595457f9a7f77fe1c9bd0699ba5e33caf694d86cc40cdb963` |
| Round3 `SelectedBridge/Main.lean` | `1db715d10a38f74df0bc294bbabd49c7b200b56388a9bb93a5c09b9c472603c5` |
| Round4 `Integration/Main.lean` (bridge reference only) | `0e755abb90fe5cd7b2a277f255da9081cdfe808ab0e2e60d7e245959c0462eda` |

Integration may retain its existing Main import, or import Regularity for these additional exports after freezing this receipt. The previous Integration freeze/audit does not automatically cover the new module.

### Remaining gap / scope

No Laplacian cancellation gap remains on `(0,1)`. The cell-integral transport and endpoint composition identified in FINAL-REPORT are not discharged here; no `[0,1]` acceptance is claimed. The previously reported shared-ref preservation flag is neither repaired nor dismissed. This follow-up writes only the owned source subtree and this report; no commit/push/merge or modification of frozen Main, prior research, baseline, or sibling files.
