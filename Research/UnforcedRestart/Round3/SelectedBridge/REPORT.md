# Selected bridge — accepted

Decision remains **(3): neither absorption nor obstruction decided**.

## Exact substantive result

`UnforcedRestart.Round3.SelectedBridge.selected_compact_temporal_integral_zero`
in `Main.lean` proves, for every `t ∈ Ioo (0 : ℝ) 1` and `i : Fin 3`,

```lean
(∫ x : Space, (temporalDerivative MeanTopology.compactVelocity t x) i) = 0
```

This is the ordinary whole-R³ volume integral of the PDE's time derivative.
The only explicit hypotheses are the interior time and the component index.
There is no zero-integral, interchange, force-removal, or sign hypothesis.

The velocity is **exactly** the frozen `MeanTopology.compactVelocity`:
`β [curl(χ A) + χ B]`, with A/B from `WitnessFeasibility.selected.schedule`.
The original noncomputable `Classical.choice data_nonempty` and its full
upstream choice dependence remain intact. No new witness, numerical profile,
truncated stage sum, strengthened Data, or chosen force constructor appears.

## Source/proof map (all hypotheses discharged)

| New theorem | Proof and source anchors |
|---|---|
| `compactVelocity_smoothAt` | Joint smoothness at every interior spacetime point. On the **closed** K=`SpatialLocalization.supportCylinder`, coordinate bounds put x in `innerCube (1/4)`, giving the actual compact/periodic spacetime germ. Transfer `selected.candidate.velocity_smooth` using `ProblemStatement.smooth_at_interior`. Off K use the checked zero germ. This includes K's spatial boundary and does not differentiate a representative map. |
| `compactVelocity_contDiffOn_slab` | For `0<a`, `b<1`, joint C¹ on `[a,b]×R³` by restriction of the preceding ordinary pointwise smoothness. |
| `compactVelocity_uniform_support` | The same fixed K works for **all real times**, using `MeanTopology.compactVelocity_zero_outside`. K is compact by `SpatialLocalization.isCompact_supportCylinder`. This helper restates an existing fact; it is not the substantive bridge. |
| `compact_component_integral_hasDerivAt` | For `0<a<t<b<1`, project joint C¹ to component i and specialize `NavierStokesR3.CompactTimeIntegral.hasDerivAt_integral_of_contDiffOn` (baseline lines 139–150). Its common-support hypothesis is explicitly supplied. Use `hasDerivAt_time_of_contDiffOn` (lines 100–113), differentiability, and the coordinate continuous linear map to identify the ordinary scalar derivative with the component of `ProblemStatement.temporalDerivative`. |
| `selected_compact_temporal_integral_zero` | Choose `[a,b]=[t/2,(t+1)/2]`, wholly inside `(0,1)`. Differentiate the existing `MeanTopology.selected_compact_momentum_zero` identity on an open time neighborhood and use derivative uniqueness. |

The baseline integral theorem is not an interchange axiom: its proof restricts
to K, obtains a bounded derivative on a compact time-neighborhood times K,
applies dominated local differentiation, and proves the derivative zero outside
K. Continuous compactly supported slices supply genuine integrability; the
argument does not obtain cancellation from a nonintegrable totalized integral.
No bound uniform as t approaches 1 and no velocity trace at 1 is used.

Inspected actual source anchors: the two imported Round3 modules in full;
`NavierStokes/R3/CompactTimeIntegral.lean` in full; `ProblemStatement` definitions,
CandidateProperties and smoothness adapter; R3 Space/measure vocabulary;
`SpatialLocalization` cutoff, compact K and coordinate bound;
`MixedPeriodicAssembly` cut velocity, activated agreement and support;
`TimeLocalization` activated velocity definition. The accepted integration's
three decision/source/validation files were read, not modified.

## Validation and preservation

Run `python3 Research/UnforcedRestart/Round3/SelectedBridge/check.py` for a fresh
unique-output strict check. The accepted run is `out/strict-bx6aiy6v/`.
Pinned Lean 4.34.0-rc2: `-j1 -DautoImplicit=false -DwarningAsError=true`, sanitized
environment, resource limits. No Lake invocation, dependency rebuild, or
baseline/earlier-module compilation occurred. Already accepted WitnessFeasibility
and MeanTopology objects were hash-checked and copied into the phase-owned
resolver; remaining imports resolve only through the frozen external clean
source-built roots plus installed Lean core, not the worktree `.lake`.

All **five** new named theorems have printed transitive axiom closures exactly
within `propext`, `Classical.choice`, `Quot.sound`. The final source has no holes,
new axioms, proof suppression, or unsafe/native proof mechanism. This is a
named-theorem closure audit, not a fresh aggregate imported-helper audit or an
independent certification of Lean/compiler/runtime/OS/hardware.

`VALIDATION-MANIFEST.json` records exact commands, source/log/output hashes,
inputs and trust roots; `validate.py` verifies the accepted run and preservation.
The prior 36 exports and prior validation manifest retain their original scope
and bytes. New preservation checks cover 3,041 preexisting source/research/docs/
root files, HEAD, refs and index, in addition to the old read-only verifier.

Attempt history is retained, not hidden: `strict-2giy3tju` failed import-root
resolution; `strict-rmmpxk96` failed elaboration (field-notation layout, projection
type inference, unspecified time argument). Their source snapshots are explicitly
`QUARANTINED.md`; failed target objects were removed. Their diagnostic `sorryAx`
closures are rejected. `strict-gohyv7l2` succeeded; the final replay above also
succeeded after improving source-snapshot/checker provenance recording. Only the
final run is designated accepted by the new manifest.

## Why it matters / what is still open

This closes precisely the time-differentiation gap in compact residual harmonic
cancellation. It does **not** prove the selected force's periodic mean zero.
Pressure-gradient and Laplacian integral adapters, separated-periodization and
coordinate-measure cell transport, and endpoint mean-continuity composition remain.

No slab curl cancellation, actual nonzero annular/plateau jet, coherent periodic
potential, absorption, obstruction, comparator lifespan, or perturbative growth
transfer has been proved here. No forced-to-unforced shortcut or A/B claim.

Actual-candidate numerics remain **no-go**: the noncomputable selected inputs have
no supplied concrete evaluable representations with certified finite-stage,
cutoff-jet, inner-Borel and integration/derivative error controls. No fictitious
computation was attempted. The chosen smaller analytic bridge is now proved.
No baseline/earlier research/config edits, commit, push, or ref/index write.
