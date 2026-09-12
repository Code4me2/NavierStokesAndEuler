# PressureIntegral — contract discharged

Exclusive source: `Research/UnforcedRestart/Round4/PressureIntegral/Main.lean`.
No Round4 sibling imports. Frozen in Integration/FREEZE-1.json and FREEZE-2.json.

`compactPressure` is exactly
`activatedPressure (SpatialLocalization.cutPressure (WitnessFeasibility.pressureSum WitnessFeasibility.selected.schedule))`.
It is not the pressure of a separately chosen compact-force witness.

Proved for every `t ∈ (0,1)` and `i : Fin 3`:

* Joint smoothness at every spatial point, including the support boundary, from the actual selected periodic pressure germ on the support cylinder and the zero germ outside.
* Slice smoothness and compact support (the latter for every real time).
* Exact identification of the actual `pressureGradient` component with the coordinate partial.
* Component integrability with Euclidean Lebesgue `volume : Measure Space`, using compact derivative support.
* `selected_compact_pressure_integral_zero`:
  `∫ x : Space, pressureGradient compactPressure t x i = 0`.

Strict compile exit 0: `Research/UnforcedRestart/Round4/Integration/strict-pu_v_ph4/receipt.json`.
Ten exact printed export closures; only propext, Classical.choice, Quot.sound.
No terminal pressure/velocity regularity is asserted. This contract alone is not a cell-mean theorem.

## PressureIntegral follow-up: explicit component interface

Added `Research/UnforcedRestart/Round4/PressureIntegral/Components.lean`; the frozen `Main.lean` is unchanged. Import `Components` for these exports in namespace `UnforcedRestart.Round4.PressureIntegral`:

* `compact_scalar_partial_contract`: exposes precisely smooth scalar slice and compact-support assumptions, and returns derivative smoothness, compact support, integrability and cancellation together.
* `pressure_integrable`: integrability of the actual selected activated compact pressure for `0<t<1`.
* `selected_gradient_component_contract`: discharges both generic assumptions using the same selected fields; returns smoothness, compact support, integrability and zero integral for each actual gradient component. Its integrability conjunct is the pressure term needed for residual splitting.
* `gradient_full_cutoff`: identifies the component as the partial derivative of `timeSwitch t * (spatialCutoff y * pressureSum selected.schedule (t,y))`. The entire product stays inside the derivative. In particular, the `p ∇cutoff` contribution is included, not set to zero or omitted. No separate smoothness of an uncut factor is assumed to obtain cancellation.

Existing `Main.smoothAt` (unqualified declaration `smoothAt` in this namespace) supplies joint smoothness across the support boundary; its sole time hypothesis is membership in `(0,1)`, and its witness input is `selected.candidate.pressure_smooth`. Support is available at all times, but smoothness/integrability/cancellation here are claimed only at interior times.

### Fresh strict evidence

Accepted receipt: `Research/UnforcedRestart/Round4/PressureIntegral/strict-yzagpnrc/receipt.json`; adjacent `compile.log`; exit **0**. Four printed closures contain only `propext`, `Classical.choice`, `Quot.sound`. No holes or added axioms. Earlier failed attempts are diagnostic only, not accepted objects.

`check.py` in the owned source directory rechecks the frozen Main source/object hashes and inherited research input hashes from the original pressure receipt, then runs the pinned compiler with `-j1 -DautoImplicit=false -DwarningAsError=true`, 600-second timeout, CPUQuota=100%, MemoryMax=6G, MemorySwapMax=0. Each attempt has unique outputs and HOME. Clean-source-built baseline dependencies and frozen research objects are used read-only; no dependency build or sibling-source import was added. The original aggregate dependency audit is inherited, not independently rerun here.

SHA256:

* unchanged `Main.lean`: `22cf707edd11b9d47f63ab7f9b3a6156095417749d92b075a3549caad98c6587`
* accepted `Components.lean`: `d97d9a17459dfeea998137ee648ca9feeb8fecff74c7b59fbf91e234c20a9e3a`
* accepted `Components.olean`: `7030450cc750b44ad8478ede585c608645903115cd672578a1ab7b704113c3d2`

No pressure-owned mathematical gap remains for componentwise compact residual splitting on `(0,1)`. The cell-integral transport and closed-interval assembly are outside this role; this follow-up does not claim those gaps resolved or re-certify the shared-ref inventory. Writes were confined to the owned pressure subtree and this report; no commit/push/merge or dependency build.
