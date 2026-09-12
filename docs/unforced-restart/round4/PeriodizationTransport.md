# PeriodizationTransport — cell transport discharged on (0,1)

Owned sources: `Research/UnforcedRestart/Round4/PeriodizationTransport/{Main,Residual,Cell}.lean`.
Main and Residual are unchanged. New Cell imports only the frozen owned Residual and Mathlib; no sibling workstream import.

## Accepted declarations

Existing Main/Residual declarations establish the exact coordinate measure map, compact residual support, selected presingular force identity, and force-mean continuity. Their historical receipts remain Integration/strict-7pvbwp0j and Integration/strict-u8436kce.

New Cell exports:

* `integral_coordinate_periodization`: integrable scalar lattice sum over the closed coordinate unit cell equals its whole-space integral.
* `integral_periodize_component`: bounded-support actual vector periodization has that equality componentwise, given component integrability.
* `selectedCellMean_eq_compact_integral`: selected-force integration interface with explicit component integrability.
* `compactResidual_component_integrable`: discharges that input for the actual selected residual, every interior time and component.
* **`selected_cell_integral_transport`**: unconditional selected specialization (apart from `t ∈ Ioo 0 1` and component index):

```lean
selectedCellMean t i = ∫ x : Space, compactResidual (t, x) i
```

`selectedCellMean` unfolds to precisely the requested coordinate integral of `WitnessFeasibility.selected.forcing` against `volume.restrict (Icc 0 1)`.

## Proof bridges

The additive lattice action on Coords is integer coordinate translation. A half-open product cell is proved an additive fundamental domain by coordinate floors and uniqueness. `Measure.univ_pi_Ico_ae_eq_Icc` handles all cell faces a.e. Fundamental-domain lintegral transport proves the finite norm-integral sum needed by `integral_tsum`; no unjustified interchange. Negation reindexes the plus-translation sum to the baseline minus-lattice convention. Bounded support supplies finite active translates and summability, permitting projection through the vector tsum. `toSpace_measurePreserving` transports whole-space integrability and integrals between the different coordinate and Euclidean types.

Actual residual component integrability is independent of sibling calculus: it equals the indicator of the closed compact support cylinder times the smooth actual selected force component. On the cylinder, the coordinate bound places every point in the inner cube, where `selected_force_inner` applies. Off it, `compactResidual_zero_outside` applies. Thus integrability is not a cancellation assumption and is not inferred from a totalized integral.

The selected force equality remains the previously checked `selected_force_eq_periodize`, using interior presingular PDE identities and separated-copy germs. No postterminal extension equality or terminal velocity regularity is asserted.

## Strict evidence and hashes

Final successful new compilation: `PeriodizationTransport/strict-t7gcxbu3/receipt.json` (paths relative to the Round4 source root). Exit 0; five printed closures, each exactly `[propext, Classical.choice, Quot.sound]`. No holes in accepted sources. Earlier failed exploratory receipts are not accepted objects.

Command and inherited dependency hashes are recorded in the receipt. One thread, `-DautoImplicit=false -DwarningAsError=true`, systemd CPU quota 100%, memory 6G/no swap, timeout 600; unique output directory each attempt. Clean-source-built dependency objects were reused read-only, without Lake/cache/dependency builds. `check.py` verifies inherited input hashes before compilation.

SHA256:

| Artifact | Hash |
|---|---|
| Main.lean | `96bc286bd7f70c954f9e01a9fc1cf78c19b636da0b1503f93b803ed9381a93a1` |
| Residual.lean | `4f6c809757e3f770990e589e19af12641a79595ee76142752f9c3e9d8b688a92` |
| Cell.lean | `0189024dec8e2420825c7c5af602b963d419e61c285f70d05232ba15b17d85c8` |
| strict-t7gcxbu3/Cell.olean | `76028becb6d91a880ff52c668f22ff2dcbca924fcfb4c80a46a9069b4fa6277e` |
| strict-t7gcxbu3/compile.log | `c0734ba29cfba81953fe5437490e4a0e1f7c31c884614af2b4fc90cd0ca2fb16` |

## Integration handoff / remaining status

Import Cell after freezing its source/object. Compose `selected_cell_integral_transport ht i` with the existing `Integration.selected_compact_residual_integral_zero ht i`. Then use `selectedCellMean_continuousOn` for endpoint closure. Those sibling/end-to-end edits were deliberately not made under this ownership restriction. The exact closed-interval acceptance test has not been rerun here and is not claimed passed; historical FINAL-REPORT predates this new transport proof.

No remaining mathematical gap in this owner's interior selected-field transport contract. Aggregate audit/freeze and closed-interval assembly remain the integrator's obligations. No new full preservation/ref certification is claimed; the previously reported shared-ref discrepancy is not repaired or hidden. No commit/push/merge performed; only owned paths written.
