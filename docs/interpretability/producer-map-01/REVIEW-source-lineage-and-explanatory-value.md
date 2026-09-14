# Independent review — source lineage and explanatory value

## Decision and scope

**The finite post-viscous-family reconstruction is a genuine explanatory advance and is acceptable as a conditional local argument.** It is not just a renamed inventory or a proof whose desired comparison inequality is hidden in an input record. The maps merit qualification, principally for an abbreviated residual hypothesis and for historical task/debt statements that must not be read as the current reconstruction status.

I read the final reconstruction, contract, atlas Markdown, both Euler map Markdown files and both Euler-target proposals, inspected their machine-readable node/edge/source/status material, and independently read the relevant literal source bodies. The comparison with existing exposition uses `docs/proof-companion/04-euler.md`, including its obligation ledger. This review is Euler-only: the NS-only maps and NS analytic claims in the atlas are not adjudicated.

Source pin: `5fdcfe346d399f68f19a820526b59b5326f28939`; observed HEAD agrees. Independent read-only checks found the Euler atlas anchors' current bytes equal to the pinned objects, with matching range hashes across 76 distinct files; additional inspected analytic helpers were also compared to the pin. These are provenance checks, **not mathematical or kernel verification**. I did not run the producer's checker, build, execute Lean, change sources, or write Git state. This review is my only intentional file output. No complete imported-closure audit is implied by the source inspections below.

## Per-artifact verdicts

Paths are relative to this output directory.

| Artifact | Verdict | Reason / required qualification |
|---|---|---|
| `RECONSTRUCTION.md` | **ACCEPT** | Conditional C06-output → global Cauchy limit → surviving energies → same signed-pressure law → C02 conclusion is explained rather than assumed. Acceptance excludes viscous production and the explicitly imported foundations. Interpret its L²-defect and discarded-top-order statements as limits of the displayed route, not impossibility theorems. |
| `RECONSTRUCTION-CONTRACT.md` | **QUALIFY** | Coherent, bounded boundary; no circular comparison premise. Correct §4C's phrase “only proved to vanish in L² by these inputs” to “the cited defect interface exports L² convergence; the selected passage uses only that interface.” See §4 below. |
| `Euler/MAP.md` | **QUALIFY** | Strong supplier/consumer expansion, with a real tangency and scalar-budget explanation. M2's residual implication omits two explicit hypotheses; B5 and the debt list are pre-reconstruction status, not the final status of the post-family subproblem. |
| `Euler/MAP.json` | **QUALIFY** | Same M2 hypothesis abbreviation is repeated in `macrograph.nodes`; inherited finite-solver debt needs an explicitly versioned link to RC-EU-FINITE-01. Its typed graph is useful navigation, not a complete dependency certificate. |
| `Euler/NEXT-TARGET.md` | **NEEDS-REVISION** as an active target | Acceptance item 4 prescribes spatial-tail control/time equicontinuity and invites stronger RHS passage than the actual argument needs. The later contract explicitly supersedes this checklist and excludes its full viscous-production demand. Preserve it only as a marked historical proposal with a supersession pointer. |
| `NavierStokes/Euler/MAP.md` | **QUALIFY** | Valid earlier Euler mapping; the sharper one-sided curvature distinction is valuable. Its “next/unexpanded” wording is historical relative to the root Euler expansion and reconstruction. Do not present its smaller expansion as the final analytic progress ledger. |
| `NavierStokes/Euler/MAP.json` | **QUALIFY** | Same historical status; local producer/consumer relations are explicitly allowed to pass through intermediates and should not be interpreted as direct calls. |
| `NavierStokes/NEXT-TARGET.md` | **ACCEPT** as a deferred proposal | Names a concrete physical-transfer obligation and respects the selected-Q barrier. It is not the selected or completed RC-EU-FINITE-01 task. |
| `MECHANISM-ATLAS.md` | **QUALIFY**, Euler portion | Correctly distinguishes finite-viscosity convergence from all-order uniqueness, and explicitly retracts the old tail/extraction checklist. Add a final-status link distinguishing the completed conditional reconstruction from remaining viscous and physical debt. |
| `MECHANISM-ATLAS.json` | **QUALIFY**, Euler portion | `selected_contract.completed=false` and `verification.human_reconstruction="contract only; not completed"` are intelligible as a pre-reconstruction snapshot, but stale as a final directory index. Version that snapshot or add the later reconstruction status without upgrading kernel/closure claims. |

The external checker script/log are provenance support, not separate mathematical deliverables. Their PASS vocabulary cannot raise these verdicts. I make no NS verdict by inheritance from the atlas.

## 1. Actual lineage: where the identity checks succeed

### Initialized inputs are not hypothetical matching records

The following bindings occur in the bodies, not merely in imports:

- `Euler/PacketInitializedBounds.lean:69–79` applies the normal estimate to the actual `joinedTerminalPrimary`, its regularity witness, its budget and its tangent theorem. `PacketJoinedApproximationBounds.lean:51–75` uses the zero first mean and the adjoint identity on the actual inverse frame. This justifies cancellation of the leading normal component, not smallness of the whole normalized velocity.
- `PacketInitializedCorrectionData.lean:23–38` defines the field by normalization and time change, and the residual by the joined inverse coefficient applied to the **actual initialized residual**, followed by the same normalization/time change. `correctionDataOfFields` receives those two fields.
- `PacketInitializedUniformBudget.lean:39–61` constructs the common-radius budgets and takes `Kc := L.correctionCoefficients NB period`, then passes the five cost bounds into `initializedAllOrderBudget`. `PacketInitializedSpatialBudget.lean:57–122` displays the literal order-independent background, derivative, residual and drift envelopes; its growth identity really is `rfl`.
- `AllOrderCorrectionData.lean:85–130` takes finite realizations of common towers and copies every inverse-metric field. The lowering equality is equality of Data, supported by value/derivative uniqueness, not agreement of a few scalar fields.

Thus the map's new point is substantive: a single initialized frequency and scalar budget can feed every correction order, while finite realization and cutoff indices vary. This does **not** make the later comparison constant uniform in that order, parent, or packet stage.

### Family, limit and equation belong to the same construction

`DriftViscousCorrectionFamily.lean:45–53` chooses the paths from `exists_global_gevrey_correction` together with each path's trace, divergence, mild identity, energy and norm bound. It does not independently choose a low-energy path and a different PDE path.

`DriftGevreyInviscidEnergyCompactness.lean:60–92` extracts those same fields, explicitly clears the exported defect convergence, constructs stability through the lower budget, and retains energies on the returned limit. That clearing is particularly useful evidence against confusing vanishing defect with nonlinear compactness.

`DriftGlobalInviscidGevrey.lean:54–67` obtains `u,e,hu,hconv,hi,hd,hM,hE`, immediately returns the same `e,hi,hd,hM,hE`, and supplies **that** `u,e,hconv` and its mild/norm fields to the equation passage. `AllOrderDriftFinite.lean:32–47` lowers the same A twice, discards the norm certificate in its destructuring, and composes the stronger derivative with the value operator. This confirms the report's consumer-specific warning: the `finite_exists` specification does not export the displayed M bound.

### Two different choice barriers are correctly respected

1. `AllOrderDriftFinite.lean:50–68` defines `Budget.solution` using `Classical.choose` and uses only `choose_spec` for the finite family. The reconstruction proves an admissible existential witness, not definitional equality of that witness with an internal exhibit. Later `CorrectionAssemblyCompatibility.lean:18–40` proves compatibility from equations, common Data and zero trace; compatibility is not a `FiniteFamily` field.
2. `PacketInitializedUniformFlow.lean:143–254` defines Q once, forms its weighted field/pressure bounds, constructs G through `Q.physicalFlowData`, and applies the physical error estimate to Q. `ParentUniformJoinedChild.lean:91–110` uses the same output at q=6 to get exponent 80. `ParentGeometryJoinedChoice.lean:26–70` retains Q, flow/coefficient/graph identity, labels, displacement and errors, but not canonical numerical formulas for Q's radius and target. `PacketJoinedSuccessor.lean:33–110` uses one selected F for state, bounds, low budget and renewal.

The selected record's errors are about its own Q. Nothing in the inspected consumer needs equality of that Q with the internal initialized exhibit. Calling the absent extra formula an unresolved attribution is appropriate; calling it a formal flaw would not be.

Finally, `ParentInitializedState.lean:75–96` separately supplies `initializedApproximationResidual` to `packetChild`. A correction Budget with an arbitrary prescribed residual is not silently promoted to physical Euler. This separation is an important successful field-use check.

## 2. Is the mathematical producer actually reconstructed?

**Yes, within the declared boundary.** C07 remains a substantial accepted theorem, but its output contains no cross-viscosity estimate or inviscid limit. `DriftGlobalGevreyCorrection.lean:51–80` visibly routes through partial bootstrap, energy-to-path norm and continuation. The report does not falsely claim to have reconstructed those proofs.

The comparison input is not circular either. `GevreyStabilityBudget.lean:21–79` extracts A₀ and A₂ from nonnegative weighted coefficient sums and copies the inverse metric; it does not store the desired two-solution inequality. The report then supplies the missing analysis:

- With signed `p=-P_G F`, `EulerCorrectionEquation.lean:27–56` gives source `-F-Gp`. Subtraction with `νΔu−μΔv=νΔ(u−v)+(ν−μ)Δv` gives the stated difference law and signs.
- Pressure cancels by symmetry of K, `KG=I`, and gradient/divergence orthogonality. It is the same G and lifted gradient space at both orders and viscosities. No pressure-difference estimate is inserted as an assumption.
- Top transport uses divergence of the actual approximation plus u, not a claimed L² Lipschitz estimate for transport. The remaining four terms put one differentiated background/solution factor in L∞ and the difference in L².
- `SobolevDifferenceEnergy.lean:26–79` and `MetricHeatEnergy.lean:70–162` match the factors: four directions each cost `Kx²/(2c²)`, giving `2Kx²/c²`; differentiation of squared energy doubles this. Multiplication by `ν≤1`, not division by ν, yields `4Kx²/c²` in the numerator of a.
- Young's inequality on `2(4KbM)|ν−μ|‖d‖₂` gives the `+1` in a and `b=(4KbM)²`. With zero trace, the displayed integrating-factor estimate gives `E_d≤b|ν−μ|² t exp(at)` and hence the claimed global path comparison.

The native norm issue is handled correctly. `CylinderSobolevOperators.lean:16–50` distinguishes the inherited finite-array maximum norm from `sumNorm`; one cannot silently substitute the latter while retaining these constants. The report keeps the four cylinder directions distinct from the three vector components and from physical R³ viscosity.

`SobolevPathInterpolation.lean:23–140` proves the actual word-square estimate by translation pairing. Prepending the same direction twice uses exactly the available higher word; no derivative commutation assumption is needed for this interpolation. Finite-coordinate path norms and completeness yield whole-sequence convergence, not a subsequence on expanding compact sets. The argument therefore needs no independent spatial-tail or equicontinuity hypothesis.

`GevreyEnergyLimit.lean:29–57` supports finite-energy continuity and exact restriction of surviving coordinates. For this invocation, `N=q−4` and `P+6≤q+1` reduce retention to `P≤q−5`. No top energy is exported by this passage. This is a source/output limitation, not a theorem that a different weak-jet argument could never retain more.

For the equation, `SobolevNonlinearCompatibility.lean:55–79` identifies pressure lifts by their common L² inverse/value. `CorrectionTime.lean:47–79` constructs the continuous projected source from the actual residual and full linearization, and `SobolevPressureTime.lean:27–46` obtains continuity from the resolvent. The report correctly does not replace the norm of that full linearization by A₀.

Finally, `CorrectionLimitEquation.lean:53–72` passes bounded time integrals in L². `InviscidSobolevEvolution.lean:24–71` and `InjectivePathDerivative.lean:23–40` recover the strong integral equation through an injective bounded map and a continuous stronger RHS. Injectivity alone would not lift differentiability. The report explains the missing ingredient rather than hiding it in the adapter name.

## 3. Concrete map correction: the residual domain is abbreviated too far

`Euler/MAP.md`, M2, and its JSON counterpart say that after the listed tail-base guard, “if N≥X−1” the residual amplitude is `exp(-0.7 X log k)`. The literal theorem `PacketInitializedCorrectionData.lean:73–82` additionally requires

- `BC.multiplierCost ≤ k^(1/100)`, and
- `6 ≤ X`.

These are separate premises, not consequences of `N≥X−1` and the stated tail-base guard. Add them to the node's input/output statement; for weighted conversion also retain the realization/cutoff and positive small-radius conditions displayed in `PacketInitializedCorrectionNorms.lean:80–92`.

The actual initialized caller supplies the missing guards (`PacketInitializedAllOrderBudget.lean:83–109`), and the detailed map's later scalar/field ledgers expose them. This is a local **map quantifier defect**, not a discovered failure of the actual producer or the final reconstruction.

## 4. Source-route limitation is not intrinsic mathematical necessity

The most important wording qualification concerns the viscosity defect. The displayed theorem and passage export/use L² convergence. But the accepted H^(q+2) bound does not intrinsically restrict the defect to L².

There is a concrete deduction from the existing operators. `CylinderSobolevDerivatives.lean:33–71` supplies contractive maps `D_i:H^(s+1)→H^s`. Define, as a human operator construction,

`L_q = Σ_(i<4) D_i^(q) ∘ D_i^(q+1) : H^(q+2) → H^q`.

Then `‖L_q u‖_(H^q)≤4‖u‖_(H^(q+2))`, and its value is exactly the four second words defining `laplacianEvaluation` in `SobolevHeatGenerator.lean:17–28`. Thus the same accepted family permits

`‖ν_n L_q u_n‖_(C_t H^q) ≤ 4ν_n M → 0`.

This is not a claim that the source's `viscousDefect` term already has that stronger type, nor a fresh formal theorem. It shows precisely why “only L² **by these inputs**” overstates the limitation. The valid statement is: **the cited interface and the chosen reconstruction pass in L², then use the stronger integral equation.** A stronger typed defect realization would be extra explanatory/operator work, not an extra tail or higher-state-regularity hypothesis.

Likewise, order thresholds, constants 4 and 5461, and the selected cutoff loss are sufficient/source-specific values. No minimal regularity, optimal constants, shortest proof, or empirical complexity lower bound follows. The report's reusable-comparison and integral-compression suggestions are reasonable exposition candidates, not demonstrated code eliminations.

## 5. Graph types, historical debt, and improvement over the companion

The atlas's C06→C03→C01→C02 spine and its equation-side edges are supported by actual calls in the inspected bodies. C08→C33 is an actual constructor binding; C31/C16→C32 and C32→C33 feed the same family. The maps' macro arrows are explicitly mathematical-use/navigation arrows, not direct-call or import-DAG claims. They must also not be read as chronological solution evolution: the all-order index and the auxiliary viscosity index have different jobs.

For field usage, the best new distinction is between:

- low-order coefficient, inverse, symmetry, divergence and path-bound inputs actually used after family production;
- Gevrey inverse/base/commutator/residual/drift budgets used to produce that family; and
- stronger numerical identities lost at selection boundaries.

Passing the whole budget does not prove minimal dependence on every field. The reconstruction's ledger correctly avoids that inference, and its explicit residual cancellation does not erase residual identity from restriction or residual size from energy retention.

The companion chapter already explains one scale hierarchy, different exact stages versus a common initial datum, H4-reference/H3 stability, the exceptional forward prefix, horizon directions, and the compact-curl class bridge. Those should **not** be counted as new mathematical discoveries of these maps. It also already says uniqueness identifies finite-order corrections and that one choice must supply both velocity and pressure.

What is concretely new is the literal supplier chain behind the abstract all-order budget, the leading-normal cancellation tied to that initialized primary, the detailed selected-Q export boundary, and especially the worked **viscosity-independent global comparison → word interpolation → finite-block retention → same projected law** argument. Chapter 04 explicitly leaves that finite solver unexpanded. The reconstruction advances precisely that boundary without claiming to close all of OBL-EUL-003.

The atlas correctly distinguishes the companion's historical `597692fa…` baseline from the present pin; I found no substitution of historical/upstream source for the inspected finite correction producers. Prior kernel reports remain prior evidence. However, final directory navigation should not leave “contract only; not completed” as an unversioned current claim. Preserve historical reports, but state which part is now conditionally reconstructed and which remains open. The physical-transfer proposal is deferred, not disproved or discharged.

## Strongest valid inference and one justified next task

**Strongest valid inference:** for fixed coherent A, actual B and fixed q≥6, accepting the matched viscous-family and foundational contracts, the same reciprocal-viscosity family has a whole-sequence global C_tH^(q+1) limit, with zero trace, lifted divergence freedom, the stated norm bound and every permitted finite energy. That limit satisfies the actual signed-pressure H^q equation in the interior and supplies exactly the existential specification used by C02. Neither a physical all-order Euler reconstruction nor extra numerical properties of an arbitrary selected Q follow from this result alone.

**One justified next technical task, not a launch:** reconstruct the drift-aware partial energy/bootstrap estimate used at `DriftGlobalGevreyCorrection.lean:65–80`, keeping local existence and continuation as named inputs. Derive how full background enters growth while the actual small drift enters radius loss, and recover the viscosity-uniform retained energy for the same mild path. This targets the largest remaining input to the accepted local proof rather than repeating its now-explained compactness inventory. No source changes, new campaign, or verification run is proposed here.
