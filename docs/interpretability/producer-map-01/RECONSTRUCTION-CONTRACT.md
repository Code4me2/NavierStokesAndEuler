# Reconstruction contract — finite Euler inviscid correction

**ID:** `RC-EU-FINITE-01`. **Exactly one target:** bounded viscous correction family → same finite inviscid path with retained energies and its literal signed-pressure equation. This is a next-phase human reconstruction contract, not its completed proof.

Pin: `5fdcfe346d399f68f19a820526b59b5326f28939`, source root `/home/velvet/Desktop/NavierStokesAndEuler`. Stable source IDs below resolve in [MECHANISM-ATLAS.json](MECHANISM-ATLAS.json), schema `mechanism-atlas/v1`. No source changes, builds, probes, installs, ref mutations or other work. Write only `/home/velvet/interpretability-producer-map-DMEgiB7x/`; all sources, old reports and refs are read-only.

## 1. Boundary and why it is bounded

Reconstruct the **post-viscous-family part** of `EulerDriftGlobalInviscidGevrey.exists_global_inviscid_gevrey_PDE` (C01), as instantiated by `EulerAllOrderDriftCorrection.finite_exists` (C02). Its two local producers are `exists_gevrey_inviscid_energy_limit` (C03) and `correction_limit_equation` (C04), followed by `correction_sobolev_hasDerivAt` (C05).

Start at the complete output of `EulerDriftViscousCorrectionFamily.exists_viscous_correction_family` (C06). Its supplier, `EulerDriftGlobalGevreyCorrection.exists_global_gevrey_correction` (C07), constructs actual solutions and their energy bounds from coefficient/residual budgets. **That viscous existence/bootstrap theorem is expressly accepted upstream input debt here.** Neither convergence nor a viscosity comparison estimate may be assumed. This is a complete meaningful local producer conditional on that debt, not a purported reconstruction of the entire finite solver from scratch.

The earlier root Euler NEXT-TARGET asked for both the full energy theory and compactness. The nested NEXT-TARGET chose physical transfer. This contract selects only the finite post-family boundary: the physical target is deferred, and full viscous existence is excluded. Evidence, not chronology of reports, determines this narrowing.

## 2. Exact inputs, fixed before taking a limit

Fix L>0, T>0, q≥6, and the actual coherent all-order Data A and Budget B of C02. In the initialized application A is `initializedCorrectionData` and B is `initializedAllOrderBudget`, via `initializedUniformBudget`; retain their actual approximation, residual, κ=k⁻¹ and direction. No replacement parent, primary, metric, residual or favorable new correction data.

Set

- D₂=A.atOrder(q+2), D₁=lowerData(D₂)=A.atOrder(q+1), D₀=lowerData(D₁)=A.atOrder(q), using the supplied jets/continuous operators and `A.lower_twice`;
- N=q−4, so N+6=q+2 exactly;
- ρ=B.radius, C=B.growthCoefficient, Δ=B.delta, ρ₀=B.initialRadius;
- K=A.metricBudget(B.metric,q+1), the **same inverse metric** on lifted L²;
- r=(B.spatial q).full.residual and M=metricAmplification(K.c)·(Δ/2)/weight(min(ρ₀/2,1),N).

Retain all enclosing Data/SpatialBudget/MetricBudget fields, not only these scalar abbreviations. In particular: coefficient jets and multiplier continuity at q+2,q+1,q; fixed κ,direction and bounds; positive/coercive metric coefficient; inverse metric symmetry, K≥c²I, inverse identity, time derivative and first spatial bounds; actual approximation/residual realizations; approximation lifted divergence; positive radius and weighted linear/quadratic bounds. The initialization suppliers are identified in C26–C30 below; their complete analytic production is not reopened.

The upstream scalar guards are C≥combinedConstant, 0<Δ≤1, ρ₀>0,

`2C(drift+Δ)T≤ρ₀/2`, `ρ₀ Rc≤1`, `2r exp(3CT)≤Δ/2`,
`ρ(t)=ρ₀−2C(drift+Δ)t`.

They fix ρ(t)≥ρ₀/2 before viscosity varies. The all-order scalar ledger has already been connected to actual initialized suppliers; do not replace it by a new threshold depending on q.

**Accepted family input (C06 at its local order q+1):** one family u_n∈C([0,T],H^(q+2)) on the full cylinder R³×(R/LZ), with ν_n=1/(n+1), such that for every n:

1. u_n(0)=0; every value belongs to the same lifted divergence-free subspace.
2. u_n is the literal zero-data `quadraticDuhamel` solution for ν_n and D₁.coefficients, not an arbitrary bounded approximate field.
3. ∀t, E_(N,ρ(t),K(t))(u_n(t))≤2r exp(3Ct) and ≤Δ/2.
4. ‖u_n‖_(C_tH^(q+2))≤M, with M independent of n.

C06 additionally exports a vanishing viscosity defect. Its short quantitative proof must be reproduced, not used as a substitute for nonlinear convergence. The mild law and energy estimates concern the same u_n. No convergence, compact support, spatial-tail bound, comparison bound or inviscid equation is an input.

## 3. Required output — one and the same e

Produce e∈C([0,T],H^(q+1)) with **whole-sequence** convergence of truncate(u_n) in that path norm, e(0)=0, lifted divergence freedom at every t, and ‖e‖≤M. For every P satisfying **both** P≤N and P+6≤q+1, every t∈[0,T], retain

`E_(P,ρ(t),K(t))(e(t))≤2r exp(3Ct)≤Δ/2`.

In particular P=N is generally unavailable: N+6=q+2 is the discarded top order. Do not silently claim the top energy survives. Finite energy is the sum over ordered cylinder words of weighted six-derivative metric block roots, not a physical H^P norm.

For each t∈(0,T), prove the H^q law

`d/dt truncate_q(e) = −D₀.rawSource(t,e(t)) − G₀(t) D₀.pressure(t,e(t))`,

where G₀ is the multiplier of D₀.metric. This pressure is the actual signed lifted-gradient solution of the coercive pressure operator on the same raw source; it is not yet a physical scalar pressure. Finally use `CorrectionData.source_sobolev`, valueOperator and `A.lower_twice` to recover **exactly C02's L²-valued derivative conclusion** and its energy/trace/divergence fields. No fresh solve in the final identification.

All time paths/traces/energies are closed-interval statements. Derivative laws are only interior; totalized `extendPath` is not evidence of an endpoint derivative. No all-order representative assembly or physical Euler reconstruction is an output of this local contract.

## 4. Worked analytic obligation (required, not already certified)

### A. Construct stability from the supplied coefficients, then derive Cauchy convergence

Expand `stabilityBudgetLower` (C08). It copies K's metric/inverse/time/space fields and obtains order-zero linear/quadratic bounds from the nonnegative zeroth term of the positive-radius weighted coefficient sums. This is not a supplied PDE stability inequality.

For any two members u,v at viscosities ν,μ, derive C09/C10's literal subtraction with d=u−v:

`d_t + transport(Z+u,d) + G(p(u)−p(v))`
`= ν Δ_cyl d − differenceRemainder(u,v) + (ν−μ) Δ_cyl v`.

Expand all four remainder terms (C11): transport(d,Z+v), linear(d), and the two algebraic quadratic terms with d in opposite slots. The common residual cancels. Here Δ_cyl is the four-coordinate artificial heat operator, not physical three-dimensional NS viscosity.

Let Zb=‖D₁.approximation‖, V=Cemb(L,q+1)(Zb+M),
`Lrem=A0+(4+2A2)Cemb(L,q+1)(Zb+M)`.
With Kb,Kx,Kt the inverse-metric bounds, derive

`E_d'=d/dt <K d,d> ≤ a E_d + b|ν−μ|²`,
`a=(Kt+2Kx V+4Kx²/c²+2Kb Lrem+1)/c²`, `b=(4Kb M)²`.

Show the actual pressure cancellation using K G=I, symmetry and lifted gradient/divergence orthogonality; the transport pairing bound Kx V‖d‖²; the heat bound 2Kx²‖d‖²/c²; the remainder bound Lrem‖d‖; and ‖Δ_cyl v‖₂≤4M. Use ν≤1, not an inverse-viscosity constant. Apply Young's inequality, zero trace, Gronwall and coercivity to obtain

`‖u−v‖_(C_tL²) ≤ sqrt(b T exp(aT))/c · |ν−μ|`.

C12–C14 provide the constant/energy/pointwise suppliers. The reconstruction must work through their local inequalities, not assume `correction_viscosity_pointwise` or `difference_metric_deriv_bound` as an opaque premise. Foundational Sobolev multiplication, translation integration by parts and coercive-pressure inversion may be imported with exact domains/orders and source citations; their general theory is upstream debt. No full global textbook proof of these foundations is requested.

### B. Obtain the strong lower-order limit without spatial compact embedding

For each ordered word w of length j with j+2≤q+2, derive from translation integration by parts

`‖D_i D_w(u−v)‖_(C_tL²)² ≤ 2M ‖D_w(u−v)‖_(C_tL²)`.

Iterate through words of length q+1, use the finite-coordinate path norm identity and completeness (C15/C16). This is global Cauchy convergence on the noncompact cylinder. **Do not demand or invent Rellich compactness, tightness, a spatial tail estimate, an Arzelà–Ascoli extraction, or a subsequence.** Zero trace, closed divergence-free membership and the norm bound pass through continuous evaluation/restriction (C17). Prove retained energies by cutoff monotonicity and continuity of finitely many surviving metric blocks (C18), not by smoothness or unproved top-order lower semicontinuity.

### C. Pass the actual nonlinear pressure-projected equation

Establish source restriction using transport, raw-source and coercive projected-source identities (C19). With v_n=truncate_(q+1)u_n, use the actual continuous quadratic coefficients of D₀ and

`Lip_M=‖projection‖(‖linear‖+2‖quadratic‖M)`

to show sourcePath(D₀,v_n)→sourcePath(D₀,e) in C_tH^q (C20). Projection includes pressure; pressure is not chosen independently after convergence. Explain why source restriction uses the same pressure inverse; general existence/regularity of that inverse can remain an explicit foundational input.

Recompute `‖ν_n Δ_cyl u_n‖_(C_tL²)≤4ν_n M→0` (C21). The source converges in H^q, but **this defect is only proved to vanish in L² by these inputs**. Thus do not assert that the entire viscous RHS converges in H^q. C22/C23 pass the actual mild derivative/integral law in C_tL²; prove the limit integral equation and interior derivative there.

Finally the proposed RHS is continuous in H^q. Commute the bounded injective H^q→L² map with its time integral, identify the stronger integral equation by injectivity, and differentiate (C24/C05). Injectivity alone does not lift differentiability; continuity of the stronger RHS and integral identity are essential. Match e through C01 to C02 with no witness substitution.

## 5. Identity, uniformity and acceptance gates

**Pass only if all hold:**

- One pinned supplier→family→limit→equation chain is explicitly bound to C02's A,B,q; all lowerings preserve κ,direction, metric coefficient, inverse metric, approximation and residual.
- The difference calculation above, word interpolation, retained-energy passage, nonlinear projection passage and integral derivative upgrade form a continuous derivation with no assumed target estimate.
- A field-use ledger separates coefficients used for comparison from energy/existence fields accepted at C06. Passing a whole record is not a claim every field is minimally necessary.
- All norm/order losses and domains are stated. Cauchy constants may depend on fixed q,T,A,B,M but not viscosity indices; no q-uniform comparison constant is demanded. All-order radius/target uniformity belongs to the upstream initialized Budget, not automatically to this comparison constant.
- Every accepted analytic input has a literal supplier and hypothesis-matched contract. No boundary is hidden behind “standard compactness” or “pressure is continuous.”
- Final output is a human reconstruction with an explicit unresolved-input ledger; no source change or build is necessary.

**Fail/stop:** an extra tail/domain/pressure hypothesis is needed but not supplied; convergence is only local/weak when global strong convergence is used; top energy is claimed after losing its derivatives; full RHS H^q convergence is asserted from the L² defect bound; pressure/source signs or restriction identities do not match; selected Q is identified with an existence exhibit; or the proof silently imports the desired Cauchy/limit conclusion. Report the exact missing implication as exposition debt or a possible stronger-interface requirement. Do not label it a Lean theorem failure without separate evidence.

## 6. What remains outside scope

C07's nonlinear Gevrey energy/bootstrap and viscous local/continuation proof; initialized profile recurrence and metric/pressure construction; complete foundational Sobolev/heat/inverse theory; all-order uniqueness/representative/pressure towers; graph-to-physical transfer; ApproximationResidual-to-physical Euler identity; ray amplification, sharp curvature renewal, scale closure and initial series; ordinary Euler stability/continuation and broad compact-curl bridge; all NS reconstruction, force deletion, Research and global dependency audits. RI-05/OBL-EUL-003 is narrowed, **not closed**. NC/PM and selected-preparation numerical-domain debts are untouched. Selected GeometryJoinedChoice exports physical errors/coefficient identity, not equality to the internal initialized Q or its scalar-radius formulas.

## 7. Pinned producer/consumer source register

The following inclusive ranges include each named declaration's body; enclosing file bytes, Git blob IDs, exact first-line anchors and range SHA-256 are in the JSON. Helpers named in a body are not thereby claimed audited transitively.

| ID | Producer/consumer declaration(s) | Source range at pin |
|---|---|---|
| C01 | `EulerDriftGlobalInviscidGevrey.exists_global_inviscid_gevrey_PDE` | `Euler/DriftGlobalInviscidGevrey.lean:21–67` |
| C02 | `EulerAllOrderDriftCorrection.finite_exists`<br>`EulerAllOrderDriftCorrection.Budget.family` | `Euler/AllOrderDriftFinite.lean:19–68` |
| C03 | `EulerDriftGevreyInviscidEnergyCompactness.exists_gevrey_inviscid_energy_limit` | `Euler/DriftGevreyInviscidEnergyCompactness.lean:28–92` |
| C04 | `EulerCorrectionLimitEquation.correction_limit_equation` | `Euler/CorrectionLimitEquation.lean:34–72` |
| C05 | `EulerInviscidSobolevEvolution.sobolev_hasDerivAt`<br>`EulerInviscidSobolevEvolution.CorrectionData.source_sobolev`<br>`EulerInviscidSobolevEvolution.correction_sobolev_hasDerivAt` | `Euler/InviscidSobolevEvolution.lean:24–71` |
| C06 | `EulerDriftViscousCorrectionFamily.exists_viscous_correction_family` | `Euler/DriftViscousCorrectionFamily.lean:20–53` |
| C07 | `EulerDriftGlobalGevreyCorrection.exists_global_gevrey_correction` | `Euler/DriftGlobalGevreyCorrection.lean:23–80` |
| C08 | `EulerGevreyStabilityBudget.coefficient_bound_le_weighted`<br>`EulerGevreyStabilityBudget.stabilityBudgetLower` | `Euler/GevreyStabilityBudget.lean:36–79` |
| C09 | `EulerCorrectionDifferencePDE.differenceRhs`<br>`EulerCorrectionDifferencePDE.differenceRhs_eq_sub`<br>`EulerCorrectionDifferencePDE.correction_difference_hasDerivAt` | `Euler/CorrectionDifferencePDE.lean:23–75` |
| C10 | `EulerCorrectionDifferenceMetric.difference_metric_deriv_bound` | `Euler/CorrectionDifferenceMetric.lean:25–121` |
| C11 | `EulerCorrectionDifference.differenceRemainder`<br>`EulerCorrectionDifference.rawSource_sub`<br>`EulerCorrectionDifference.differenceRemainder_norm` | `Euler/CorrectionDifference.lean:18–109` |
| C12 | `EulerCorrectionStabilityConstants.lowerConstant`<br>`EulerCorrectionStabilityConstants.velocityBound`<br>`EulerCorrectionStabilityConstants.growthConstant`<br>`EulerCorrectionStabilityConstants.defectConstant`<br>`EulerCorrectionStabilityConstants.differenceRemainder_uniform` | `Euler/CorrectionStabilityConstants.lean:14–67` |
| C13 | `EulerSobolevDifferenceEnergy.difference_transport_bound`<br>`EulerSobolevDifferenceEnergy.difference_heat_bound` | `Euler/SobolevDifferenceEnergy.lean:26–79` |
| C14 | `EulerCorrectionViscosityStability.correction_viscosity_pointwise` | `Euler/CorrectionViscosityStability.lean:24–99` |
| C15 | `EulerSobolevInterpolation.word_square_le_parent`<br>`EulerSobolevPathInterpolation.wordPath_difference_square_bound`<br>`EulerSobolevPathInterpolation.wordPath_cauchy_step` | `Euler/SobolevPathInterpolation.lean:23–140` |
| C16 | `EulerSobolevCauchyInterpolation.pathCoordinates_norm`<br>`EulerSobolevCauchyInterpolation.cauchy_restrict_of_value`<br>`EulerSobolevCauchyInterpolation.exists_limit_restrict_of_value` | `Euler/SobolevCauchyInterpolation.lean:46–94` |
| C17 | `EulerSobolevPathLimits.restrict_path_norm`<br>`EulerSobolevPathLimits.limit_norm_bound`<br>`EulerSobolevPathLimits.limit_zero_trace`<br>`EulerSobolevPathLimits.limit_divergenceFree` | `Euler/SobolevPathLimits.lean:21–54` |
| C18 | `EulerGevreyEnergyPathLimit.energyNorm_path_limit_bound` | `Euler/GevreyEnergyPathLimit.lean:16–31` |
| C19 | `EulerCorrectionSourceRestriction.truncate_transport`<br>`EulerCorrectionSourceRestriction.truncate_rawSource`<br>`EulerCorrectionSourceRestriction.truncate_source` | `Euler/CorrectionSourceRestriction.lean:19–74` |
| C20 | `EulerQuadraticSourceLimit.sourcePath_sub_bound`<br>`EulerQuadraticSourceLimit.sourcePath_tendsto` | `Euler/QuadraticSourceLimit.lean:21–37` |
| C21 | `EulerViscosityDefect.viscositySequence`<br>`EulerViscosityDefect.viscousDefect_bound`<br>`EulerViscosityDefect.viscousDefect_tendsto_zero` | `Euler/ViscosityDefect.lean:14–63` |
| C22 | `EulerViscousSourcePathLimit.viscousSourcePath_tendsto` | `Euler/ViscousSourcePathLimit.lean:33–50` |
| C23 | `EulerIntegralPathLimit.pathIntegralOperator`<br>`EulerIntegralPathLimit.integral_equation_limit`<br>`EulerIntegralPathLimit.hasDerivAt_of_integral_equation` | `Euler/IntegralPathLimit.lean:16–74` |
| C24 | `EulerInjectivePathDerivative.integral_equation_of_injective_map`<br>`EulerInjectivePathDerivative.hasDerivAt_of_injective_map` | `Euler/InjectivePathDerivative.lean:23–40` |
| C25 | `EulerCorrectionLimitPathDerivative.lower_mild_path_derivative` | `Euler/CorrectionLimitPathDerivative.lean:28–47` |
| C26 | `EulerPacketTerminalDatum.initializedAllOrderBudget` | `Euler/PacketInitializedAllOrderBudget.lean:64–132` |
| C27 | `EulerPacketTerminalDatum.initializedUniformBudget` | `Euler/PacketInitializedUniformBudget.lean:39–61` |
| C28 | `EulerPacketTerminalDatum.initializedCorrectionData` | `Euler/PacketInitializedCorrectionData.lean:32–55` |
| C29 | `EulerAllOrderCorrectionData.Data`<br>`EulerAllOrderCorrectionData.Data.atOrder`<br>`EulerAllOrderCorrectionData.Data.metricBudget` | `Euler/AllOrderCorrectionData.lean:56–130` |
| C30 | `EulerAllOrderCorrectionData.Data.lower_twice` | `Euler/AllOrderCorrectionCoherence.lean:14–25` |
| C31 | `EulerViscosityCauchy.correction_viscosity_norm`<br>`EulerViscosityCauchy.correction_family_cauchy` | `Euler/ViscosityCauchy.lean:42–70` |
| C32 | `EulerCorrectionFamilyCompactness.exists_limit_with_constraints`<br>`EulerCorrectionFamilyCompactness.exists_correction_family_limit` | `Euler/CorrectionFamilyCompactness.lean:31–66` |
| C33 | `EulerGevreyFamilyCompactness.exists_limit_of_gevrey_family` | `Euler/GevreyFamilyCompactness.lean:18–44` |
| C34 | `EulerCorrectionStabilityBudget.StabilityBudget`<br>`EulerCorrectionStabilityBudget.StabilityBudget.growth`<br>`EulerCorrectionStabilityBudget.StabilityBudget.comparisonConstant` | `Euler/CorrectionStabilityBudget.lean:16–67` |
| C35 | `EulerQuadraticSource.Coefficients`<br>`EulerQuadraticSource.Coefficients.ballLipschitz`<br>`EulerQuadraticSource.Coefficients.apply_sub_bound` | `Euler/QuadraticCoefficients.lean:16–73` |
| C36 | `EulerGevreyEnergyCutoff.energyNorm_cutoff_mono` | `Euler/GevreyEnergyCutoff.lean:45–55` |

C06→C03→C01→C02 is the selected producer/consumer spine; C04/C05 attach the equation to that same limit. C07 is accepted upstream debt, not a second reconstruction target.
