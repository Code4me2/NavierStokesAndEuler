# Independent mathematical, quantifier and source-lineage audit

## Verdict and evidence boundary

**QUALIFY the finite Euler reconstruction: the conditional proof works; its advertised regularity limitation needs narrowing.** This is genuine post-family analytic reconstruction, not circular acceptance of a record containing the desired limit. The current package also needs a clearer historical/current status distinction.

I read the final reconstruction, contract, atlas, all three branch-map Markdown files, both actual NEXT-TARGET files, and inspected the JSON structures, quantitative prose, field ledgers and graph relations. I independently read the relevant producer/consumer bodies at baseline `5fdcfe346d399f68f19a820526b59b5326f28939`, including the comparison, interpolation, equation passage, initialized suppliers and selected-child interfaces. I compared 96 cited/helper source paths with literal pinned Git objects: no byte differences. The atlas's eight recorded input-artifact hashes match the actual files. These are provenance checks, **not kernel or mathematical verification**.

The mathematical review below is Euler-local. NS inspection was limited to the atlas's identity/rate boundary and its actual assembly; it is not an NS reconstruction or complete dependency audit. No builds, Lean probes, source/producer edits or Git writes were performed. This review is the only authored output. Imported foundational analysis and viscous production remain conditional inputs, not independently re-certified theorem closures.

## Per-artifact decisions

Paths are relative to this output directory. ACCEPT means acceptance for the artifact's stated, bounded purpose—not certification of Euler singularity formation.

| Artifact | Decision | Scope / correction |
|---|---|---|
| `RECONSTRUCTION.md` | **QUALIFY** | Accept the C06-to-C02 conditional derivation. Narrow the “only L²”/“requires integral upgrade” language as explained in finding 1. Distinguish interface loss from mathematical impossibility. |
| `RECONSTRUCTION-CONTRACT.md` | **QUALIFY** | Sound noncircular local boundary. Section 4C overstates what the inputs cannot prove; replace that assertion by a statement about the actual exported defect operator and chosen proof route. |
| `MECHANISM-ATLAS.md` | **QUALIFY** | Useful separation of strategies and indices. Retain the historical evidence labels but add a current disposition pointing to the completed conditional reconstruction and this qualification. |
| `MECHANISM-ATLAS.json` | **NEEDS-REVISION** as a current index | `selected_contract.completed=false` and `verification.human_reconstruction="contract only; not completed"` do not describe the final package. Preserve them as versioned historical fields or add a separate reconstruction status/link; do not upgrade kernel status. |
| `Euler/MAP.md` | **QUALIFY** | Materially useful supplier expansion. Its still-unexpanded finite compactness entry is now historical, not the whole current debt. Distinguish metric type binding from computational field dependence (finding 3). |
| `Euler/MAP.json` | **QUALIFY** | Eight nodes and typed relations are useful. Its finite-limit debt and active `next_target_kind` need a supersession/current-disposition link. Same metric-dependence qualification as Markdown. |
| `Euler/NEXT-TARGET.md` | **NEEDS-REVISION** as an active target | Its gate 4 prescribes spatial-tail/equicontinuity work not needed by the actual route; gates 2–3 also demand viscous energy production excluded by the later contract. Acceptable only as an explicitly superseded historical proposal. |
| `NavierStokes/Euler/MAP.md` | **QUALIFY** | Sound bounded predecessor map on the inspected Euler interfaces; not an additional independent reconstruction. Keep its sharper one-sided pressure distinction and mark finite-limit debt historically. |
| `NavierStokes/Euler/MAP.json` | **QUALIFY** | Same status and ceiling as its Markdown companion; macro mathematical use is not a direct-call assertion. |
| `NavierStokes/NEXT-TARGET.md` | **QUALIFY** | Precise deferred physical-error obligation. It is not the target completed by `RECONSTRUCTION.md`, nor a second active authorization. |
| `NavierStokes/MAP.md` | **QUALIFY**, limited inspection | Five-field identity boundary and same-prefix binding check out. No acceptance of all eight NS analytic mechanisms is implied. |
| `NavierStokes/MAP.json` | **QUALIFY**, limited inspection | Consistent sampled identity/rate ledger; no full NS edge or necessity audit. |
| `exact-check.py`, `exact-check.log` | **ACCEPT**, provenance only | The script checks bytes, blobs, ranges and anchors. Its explicit ceiling is appropriate; its log supplies no mathematical or kernel inference. |

The two NEEDS-REVISION navigation decisions do **not** overturn the conditional mathematical result. The atlas already explains supersession in prose; the defect is that standalone/machine consumers still receive an obsolete active status.

## 1. Concrete correction: L² is the exported defect target, not an intrinsic ceiling

The reconstruction correctly proves

\[
\|\nu_n\Delta_{cyl}u_n\|_{C_tL^2}\le4\nu_n M\to0
\]

and correctly follows `CorrectionLimitEquation.lean:34–72` through an L² integral equation. Its final stronger integral argument is valid. But the contract's assertion that the defect is “only proved to vanish in L² by these inputs,” and any reading that H^q passage is impossible from these inputs, is too strong.

**Countercheck using actual native operators, not a different Sobolev convention:** `Euler/CylinderSobolevDerivatives.lean:33–46,68–74` constructs contractive maps

\[
D_i^{(s)}:H^{s+1}\longrightarrow H^s.
\]

Therefore the bounded map

\[
\mathscr L_q=\sum_{i<4}D_i^{(q)}\circ D_i^{(q+1)}:
H^{q+2}\longrightarrow H^q
\]

has norm at most 4. Its value is exactly the four second-word coordinates defining `laplacianEvaluation` in `SobolevHeatGenerator.lean:18–40`. The derivative-array definition appends the two identical directions; no unproved interchange of derivative words is needed for this value identification. Consequently the **same supplied family bound** gives

\[
\|\nu_n\mathscr L_q u_n\|_{C_tH^q}\le4\nu_n M\to0.
\]

Together with the reconstruction's genuine H^q source convergence, this gives an H^q-valued lift of the entire RHS converging strongly. This is a human deduction from inspected operators, not a claim that the pinned source already defines or uses this exact packaged Laplacian map. Lifting the viscous derivative equations still needs an argument—e.g. the same commuting-integral/injectivity theorem applied before passage.

**Required wording correction:** “C21/C22 export and the selected source route uses only an L² defect estimate. We do not use the stronger H^q lift available by composing native derivative operators. The stronger derivative conclusion in this route is obtained by the continuous-RHS integral upgrade.” Do not say the integral upgrade is the uniquely necessary analytic strategy, or that the input regularity prevents H^q defect convergence.

Similarly, “top energy is not retained” is correct **as an exported C01/C02 conclusion and as a limitation of the demonstrated strong-continuity argument**. It is not a theorem excluding a separate weak top-order retention argument. No such stronger result is needed or attributed here.

## 2. The selected proof is mathematically substantive and noncircular

### Comparison and constants

`GevreyStabilityBudget.lean:21–79` constructs comparison inputs from coefficient bounds: it extracts the nonnegative zeroth weighted block and copies the inverse-metric data. It does not assume a solution comparison inequality. `DriftViscousCorrectionFamily.lean:45–53` chooses actual positive-viscosity mild solutions from the global viscous theorem. Its output contains norm/energy bounds and the mild law, not convergence. In `DriftGevreyInviscidEnergyCompactness.lean:60–92`, the exported defect is explicitly discarded before constructing the Cauchy limit. Thus there is no illicit replacement of nonlinear convergence by a vanishing defect.

I checked the subtraction against `CorrectionDifference.lean:18–43`: the residual cancels and the remainder has exactly transport `(d,Z+v)`, linear `d`, and the two algebraic terms `(Z+u,d)` and `(d,Z+v)`. No symmetry of the algebraic bilinear map is assumed.

The pressure convention agrees with `EulerCorrectionEquation.lean:27–61`:

\[
p=-P_GF,\qquad S=-F-Gp.
\]

Symmetry of K and **KG=I**, not an unexplained orthogonal projection in the K metric, give

\[
\langle Kd,G\delta p\rangle=\langle d,KG\delta p\rangle
=\langle d,\delta p\rangle=0.
\]

Here the pressure difference belongs to the same closed lifted gradient space and d to its orthogonal complement. Forward pressure coercivity and inverse-metric `c²` are properly distinguished.

The constants match `CorrectionStabilityConstants.lean:14–29`, `SobolevDifferenceEnergy.lean:26–79`, and the actual calls in `CorrectionDifferenceMetric.lean:25–121`:

- top transport costs `Kx V`, using `(1/2)(|κ|+‖m‖)≤1` and divergence of **both** Z and u;
- four heat directions contribute `2Kx²/c²` before energy differentiation; multiplying by `2ν` and using `ν≤1` gives `4Kx²/c²`;
- four reverse-transport products and two algebraic terms give `Lrem=A0+(4+2A2)Cemb(Zb+M)`;
- the viscosity mismatch costs `4M|ν−μ|`; Young contributes `+1` and `b=(4KbM)²`.

Hence `E′≤aE+b|ν−μ|²` with the stated a is justified. The closed-interval Gronwall argument requires no endpoint derivative and yields the stated global Lipschitz-in-viscosity L² path estimate. There is no inverse-viscosity loss in this comparison. This does not assert that upstream heat/local-existence constants individually avoid inverse viscosity.

The metric transport foundation is substantive but properly exposed: `SobolevMetricTransport.lean:75–107` mollifies the energy field and passes a representative metric bound through actual continuous operators. It is not a hidden assumption of the two-solution estimate. Accepting its density/weak-divergence theory under the contract is legitimate conditional exposition, not a formal flaw.

### Strong limit and retained blocks

`SobolevPathInterpolation.lean:23–43,100–140` proves the one-parent/two-derivative inequality by translation pairing. The reconstruction correctly prepends a direction in that argument; it does not silently identify all ordered words. Iteration reaches q+1 from a q+2 bound, not the top q+2 level. `SobolevCauchyInterpolation.lean:46–94` uses the **finite-array maximum norm** and completeness, not Rellich or spatial tightness.

The resulting convergence is whole-sequence and global on the noncompact cylinder. Trace and divergence pass at every closed-interval time. Retaining energy by finite-coordinate continuity of the same K(t) is valid, including at zero energy. The cutoff is precisely

\[
P\le q-4,\quad P+6\le q+1,
\quad\text{hence }P\le q-5.
\]

At q=6 this permits P≤1, not P=2. The weight is applied to each external-word base-block root, not to one overall root or an ordinary physical H^P norm. This agrees with `FiniteMetricEnergy` and `GevreyEnergyLimit.lean:30–45`.

### Equation passage

Restriction of pressure in `SobolevNonlinearCompatibility.lean:55–79` is proved by equality of the underlying coercive L² solve followed by value injectivity. This is stronger identity evidence than matching pressure bounds. The continuous projected quadratic source has the correct ball constant; its linear coefficient includes the background linearization and is not merely A0.

`IntegralPathLimit.lean:16–74` justifies continuous-path integration, endpoint traces and passage to the limit. `InjectivePathDerivative.lean:23–40` identifies the stronger **integral equation**, not differentiability from injectivity alone. `InviscidSobolevEvolution.lean:24–71` then recovers the literal signed-pressure H^q law. This remains sound despite finding 1: the proof follows a valid route, though that route is not forced by lack of input regularity.

## 3. Actual identity and field dependence

### Finite producer to its consumer

`DriftGlobalInviscidGevrey.lean:54–67` obtains one `u,e` from the energy-limit theorem, immediately exports that e, and supplies **that u,e,hconv** to equation passage. `AllOrderDriftFinite.lean:32–47` calls it at input q+2, rewrites `A.lower_twice`, discards the norm certificate, and composes the H^q derivative with `valueOperator`. The reconstruction tracks this exactly.

`Budget.solution` and `Budget.family` at lines 49–68 use `Classical.choose` and its exported specification. An internal exhibit is not definitionally the selected witness. The reconstruction respects this and does not smuggle the discarded norm or the hidden approximation family into the selected finite specification. Its separate same-viscosity uniqueness deduction is legitimate for the stated admissible mild class and common bound; it does not identify every selected inviscid witness with an internal family.

`AllOrderCorrectionData.lean:85–130` and `AllOrderCorrectionCoherence.lean:14–25` preserve the actual approximation/residual paths as well as the coefficients. Later `CorrectionAssemblyCompatibility.lean:18–40` uses inviscid uniqueness on the selected finite equations; compatibility is not assumed in `FiniteFamily`. `CorrectionAssemblyPressure.lean:29–60` then transports the same raw source to the same signed pressure. These are distinct steps from viscosity Cauchy convergence.

### Initialized scalar supply and selected child

`PacketJoinedApproximationBounds.lean:51–75` explicitly transfers primary tangency by the adjoint inverse-frame identity and removes the first normal term. `PacketInitializedCorrectionNorms.lean:63–78` uses a **word** normal bound, not just order-zero smallness, to obtain drift `2(3Cv+Cn)/k`. `PacketInitializedSpatialBudget.lean:57–122` supplies B0, B1, residual and drift independently of correction order. The all-order constructor fixes k/truncation and scalar radius/target first. The displayed residual and physical-error arithmetic is correct under its guards; it does not prove the recursive profile or pressure inverse estimates producing those guards.

`PacketInitializedUniformFlow.lean:143–254` defines Q once, forms `G=Q.physicalFlowData`, and uses Q's own field and pressure for the errors. `ParentGeometryJoinedChoice.lean:26–70` retains Q, coefficient identity and both errors. `PacketJoinedSuccessor.lean:33–110` uses one selected F for the state, physical bounds, low bounds and renewal. It does not export canonical Q.delta or Q.initialRadius formulas. The maps correctly refuse that stronger attribution. The separate ApproximationResidual obligation cannot be replaced by mere solvability of arbitrary correction Data.

**Additional explanatory fact the field ledger should expose:** metric supply is not computationally dependent on the two packet fields merely because they are arguments. In `PacketCorrectionMetricBudget.lean:93–119`, `sourceMetricBudget` fills every metric/derivative/coercivity/bound field from D and P; Z, G, κ and q bind the destination correction-data type. In `PacketCorrectionSourceData.lean:17–35`, the fields are genuinely copied into approximation/residual, whereas the metric comes from `metricTower D P`. The initialized call therefore proves *correct type/object association*, not sensitivity of the metric constants to the normalized residual. This is a concrete narrower dependency statement, not a claim that residual or approximation is globally dispensable. Add that distinction to the maps/reconstruction ledger rather than treating every argument edge as analytic dependence.

## 4. Quantifiers, graph semantics and necessity

The essential order of choices is preserved:

1. Fix the parent/initialized frequency and all-order A,B; then fix finite q≥6.
2. Fix M, Zb and comparison constants for that q **before** viscosity indices n,m. They may depend on L,T,A,B,q. Neither the native embedding cardinality nor `weight(...,q−4)⁻¹` is q-uniform.
3. After whole-sequence convergence, fix a surviving P and any closed-interval t. Derivatives are only interior.
4. Physical error constants have parent/frame/radius/frequency guards. They are not uniform over arbitrary selected budgets or parents.
5. Initial-data majorants permit dependence on fixed derivative m, not stage index. Reference-stability constants belong to the fixed reference, not a uniform stage H4 assumption. Those outer analytic producers were not reconstructed here.

The atlas's C06→C03→C01→C02 direct-instantiation spine agrees with the inspected bodies, as do C08→C33, C31/C16→C32, C22/C23/C25→C04 and C24→C05. Grouped source IDs identify declaration ranges, not one theorem per node. Macro arrows appropriately describe mathematical use rather than import or direct-call graphs. They should not be read as exhaustive dependency edges or standalone sufficiency claims.

The NS sample reinforces this distinction: `ActualPhysicalPrefixFields.lean:438–474` supplies five regularity/germ/exterior fields; `ActualCandidateAssembly.lean:974–994` binds the same raw sequences and iterate to both physical data and estimates. The residual estimate additionally calls `cartesianPull_jet_bound` and closure transfer at `ActualCycleResidualBounds.lean:909–949`. The extra-band identity `2Q_(N+1)=Q_N` is literal at `ActualCandidateConstruction.lean:94–102`. None of these identity facts alone supplies quantitative residual decay. This is the extent of the NS check.

Complexity classifications are acceptable only as **roles in this route**. Four heat directions, six base derivatives, q≥6, label exponent 80 and chosen scalar margins are source sufficient budgets, not optimal lower bounds. “Adapter” does not mean dispensable: truncation, pressure restriction and representative identification carry real equality obligations. No empirical minimality, benchmark improvement or theorem of irreducibility follows from these maps. Finding 1 shows why even a plausible “required order loss” needs this care.

## 5. Improvement over the companion and current debt

I compared with `docs/proof-companion/04-euler.md`, especially EUL-004 and its OBL-EUL-003 ledger. The companion already explains common-radius correction, uniqueness across orders, one-child identity, H4 reference stability, initial summability and the outer contradiction. Those cannot be counted as newly reconstructed merely because eight nodes now organize them.

There is nevertheless genuine added value:

- the maps connect actual tangency to the inverse-frequency drift and actual five-cost scalar suppliers to a single all-order budget;
- the reconstruction derives the pressure-cancelled, viscosity-independent comparison constant instead of citing a compactness record;
- derivative-word interpolation identifies a global whole-sequence route and eliminates the proposed tail/Rellich obligation;
- the exact retained cutoff and same-pressure restriction/integral mechanism narrow OBL-EUL-003 to a precise remaining upstream boundary.

Thus **this is not merely an old inventory reformatted**. Conversely, the repeated finite-solver “unexpanded” entries in historical maps must not remain the undifferentiated current debt. A correct current disposition is: *post-family comparison, lower-order convergence, retained blocks and equation passage conditionally reconstructed and reviewed; viscous Gevrey production, foundational inverse/heat/density analysis, all-order physical transfer and renewal not closed*. The present work does not close all of RI-05 or OBL-EUL-003.

The companion's `597692fa…` baseline, supplement pins `26e896e…`, and upstream/paper comparisons are historical evidence classes, not interchangeable witnesses for `5fdcfe3`. I found no substitution of upstream functions for the retained local source in the reviewed Euler chain. I did not re-audit the historical NS numerical-domain claims; preserving their unresolved selected-witness qualification is appropriate, not evidence of a current formal flaw.

## Strongest valid inference and one justified next task

**Strongest accepted result:** conditional on C06's actual uniformly bounded zero-data viscous mild family, the matched coefficient/inverse-metric data and the stated foundational contracts, the same family converges globally and wholly in `C([0,T],H^(q+1))`; its limit has the stated surviving metric energies, zero trace, lifted divergence constraint and the literal signed-pressure H^q interior equation, yielding exactly C02's exported L² derivative law. No extra family-tail hypothesis or selected-child numerical identity is needed. This is not a proof of viscous production, physical Euler reconstruction or a kernel result.

**One next technical task, if separately authorized:** reconstruct the shrinking-radius nonlinear energy/bootstrap estimate used by `DriftPartialCorrectionBootstrap.partial_correction_bootstrap` (`Euler/DriftPartialCorrectionBootstrap.lean:23–74`) for an already existing partial mild path. Keep local existence/continuation upstream. The bounded obligation is to derive, from the actual full/spatial/drift/metric fields and radius derivative, the uniform surviving-time energy bound used in C07—rather than assume it or merely repeat the time-restriction wrapper. This is justified because it is the immediate remaining analytic supplier to the accepted family, and it would connect the map's order-independent scalar arithmetic to actual energy production. No new work is launched by this recommendation.
