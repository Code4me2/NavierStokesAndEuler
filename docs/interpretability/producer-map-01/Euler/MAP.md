# Euler producer/consumer map

## Authority and scope

Pin **5fdcfe346d399f68f19a820526b59b5326f28939**; observed HEAD equals pin. All `Euler/*.lean:line–line` citations below refer to that commit, relative to `/home/velvet/Desktop/NavierStokesAndEuler`. Ranges include proof/definition bodies, not just signatures. MAP.json adds literal body anchors and pinned Git blob IDs. Source inspections concern these local bodies, not their complete imported dependency closures.

Read-only investigation; only this external Euler directory is written. No builds, Lean probes, installs, Comparator runs, git mutations, or research campaign. The supplied prior authentic Nanoda+Lean gates on df3d891 and final documentation-only 5fdcfe3 delta remain **prior evidence**, not a result of this mapping. Published main/simplify are not reset to 26e896e. Untracked REVIEW.md, SIMPLIFICATIONS.md and review-notes/ were left alone. The four H3 additions and Research are not used in this Euler route. No immutable upstream or paper source was substituted for retained production.

This is the **Euler branch deliverable**. No NS map is supplied here: write authority is confined to Euler. Historical 30-ID coverage is neither renamed nor represented as freshly audited. Navigation notes, companion README/SOURCE-MAP/INTERFACES/VALIDATION, chapter 04 and all three supplement ledgers were read. Chapters 05–07 concern NS; their recorded calculations and selected-domain limitations are context, not Euler evidence. Their complete chapter bodies were not independently re-audited.

Evidence: **source-inspected** = local statement, enclosing parameters and body inspected; **human-derived** = calculation here from explicit source inputs; **unexpanded** = located formal supplier without a full analytic reconstruction; **unresolved** = no established implication in this inspection. No unexpanded producer is thereby a formal proof gap.

## New information beyond navigation/chapter 04

1. **The small radius slope has a concrete cancellation producer.** The leading pulled-back packet has zero normal component because its physical tangency is transported through the adjoint inverse frame. The surviving normal component is one inverse frequency smaller. This, not small full velocity, yields the actual drift `2(3 Cv + Cn)/k`. See §Boundary B1.
2. **The all-order budget is not a choice of a new radius at each order.** Its actual supplier sets every scalar envelope independently of correction order: `B0=2Cv`, `B1=12Cv(4R)`, residual `2 exp(-0.7 X log k)`, drift `2(3Cv+Cn)/k`. The order dependence is only in finite realizations and cutoffs. `initializedDriftBudget_growth` is literally `rfl` after substituting those fields.
3. **Coherence uses a strictly smaller interface than existence.** `comparisonData` consumes the common metric, radius, base spatial budget at q=6 and divergence, but none of the all-order decay/smallness hypotheses. Independently chosen finite solves are identified by PDE uniqueness, not a compactness diagonal across derivative orders. Pressure is identified subsequently by raw-source restriction and the same coercive pressure operator.
4. **The physical error margin pays a visible derivative loss.** Cylinder weighted error `Cw Δ` becomes gradient/Hessian error `Kerr k Δ`, added to the finite approximation error `Kv/k` or `Kp/k`. Both are paid by the same fixed frequency guard before `GeometryJoinedChoice` is selected. The selected record exports the physical error bounds, not equality to the proof's internal `Q` or its numerical-radius formulas.
5. **Some seeming duplication has already been removed.** `Stage.next` is one shared forward/joined assembly. The remaining distinction includes a genuinely positive history parameter, initial-trace identity and different ratios. Replacing joined history by time zero is not a harmless simplification.

## Eight mechanisms (macrograph)

`M1 → M2 → M3 → M4 → M5 → M6 → M7 → M8`, with `M1 → M4`, `M4 → M6` and `(M4,M5,M6,M7) → M8`. This order describes production and use, not the import DAG. M1 fixes the numerical hierarchy; the recursive stage output also uses M2–M4 at each step.

### M1 — Fix the hierarchy, then recursively choose exact stages

**Input/output.** For each c≥0 and real floor B, ∃ one `Scales c B`; its J,D,X,δ and all-n numerical guards precede the recursion. Delivered instantiation fixes c=`requiredExponent` and B=`commonThreshold gradientConstant hessianConstant`, then defines `packets n : Stage constructionScales n` for every n. This is not ∀n∃ a new hierarchy.

**Representative estimates.** `Σ k_n^(-1/4) ≤ δ`, renewal series ≤1/4, base horizon ≤1; actual source scales satisfy `x_(n+1)=(J+n)^2 x_n`. The common choice theorem chooses D, then J, then X from an intersection of eventual conditions.

**Producer → actual consumer.** `EulerPacketInductionScales.exists_scales`, `PacketInductionScales.lean:122–192` (record at 83–112), is used by `EulerPacketInduction.constructionScales`, `PacketInfiniteConstruction.lean:59–66`. `stages` at 39–41 recurses through `Stage.successor` at 21–25: stage 0 uses `forwardNext`, positive stages use `joinedNext`. `chooseJoined`, `PacketJoinedSuccessor.lean:33–37`, consumes `S.secondary_frequency` with the actual restricted state's label bound and rewrites the actual input scale to supply the inverse-length guard. Forward counterpart: `PacketForwardSuccessor.lean:29–33`.

**Why this route needs it.** Summable low/pressure/renewal debts must coexist with large frequencies on the same future stages. A frequency chosen only after fixing one derivative order would not support the prescribed recursion. **Construction-specific requirement**; common-threshold numerical closure below `exists_common_guards` is **unexpanded**, not reproved by exponential-growth intuition. Record and caller bodies **source-inspected**.

### M2 — Initialized parametrix: tangency gives small drift, truncation gives residual

**Input/output.** Fix mean/transverse data M,D with M.T=D.T; positive history 0<τ<D.T; one history B, primary amplitude α>0, spike 0<δ≤1, terminal ξ, supported cutoff; joined/primary/normal/mean budgets and grade guards on one common radius R, coefficient agreement and multiplier budget BC. Fix k≥4 and N≥1 satisfying the actual tail-base guard. Construct the literal packet Z=k·(initializedPacketField N k⁻¹), with time changed to D.T, and residual obtained by applying the joined inverse coefficient before multiplying by k. Outputs are `WordBound 6 (4R) Cv 0`, normal bound `Cn/k`, and, if N≥X−1, residual amplitude `exp(-0.7 X log k)`.

**Producer → actual consumer.** `EulerPacketCylinderField.joinedPacket_normal_bound`, `PacketJoinedApproximationBounds.lean:51–75`, uses zero first mean and primary tangency to eliminate the first normal term. It is literally instantiated with `joinedTerminalPrimary`, its witness, budget and tangency in `EulerPacketTerminalDatum.initializedPacket_normal_bound`, `PacketInitializedBounds.lean:69–79`. `initializedNormalizedField_normal_bound`, `PacketInitializedCorrectionData.lean:64–70`, transports that statement to the actual all-order input. `initializedCorrection_drift`, `PacketInitializedCorrectionNorms.lean:63–78`, feeds it and the full bound into the weighted drift inequality; `initializedDriftBudget`, `PacketInitializedSpatialBudget.lean:101–113`, stores the result for M3.

**Equation.** `⟨(F⁻¹)*m₀,a₁⟩=0 ⇒ ⟨m₀,F⁻¹a₁⟩=0`; therefore `||b_Z||weighted ≤ 2(3Cv+Cn)/k`, while `||Z||weighted ≤2Cv`. The precise calculation is B1 below.

**Identity/need/classification.** The same initialized primary supplies the field, residual and tangent witness; normalized residual is not an arbitrary small function. **Core analytic cancellation plus construction-specific finite-profile recursion.** Profile recurrence, terminal-primary budget and high-order residual cancellations below `joinedSource_profile_budgets` / `joinedResidual_normalized_bound` remain **unexpanded**. Tangency transfer and the actual drift substitution are **source-inspected/human-derived**.

### M3 — One exact all-order correction from finite solves (central boundary)

**Input/output.** Fix L>0, T>0 and coherent data A on R³×(R/LZ), κ and direction fixed, plus one `Budget L hT A`. For every q≥6 produce e_q∈C([0,T],H^(q+1)), e_q(0)=0, solenoidal, with its literal projected Euler correction equation. Then construct **one** common L² path e, one smooth spatial representative, one pressure tower, and ∀P,t the metric Gevrey energy bound

`E_(P,ρ(t),K(t))(e) ≤ 2 R_(P+6) exp(3Ct) ≤ Δ/2`.

This is not a physical H^P norm. The base block contains all words through six; external weights are ρ^j/(j!)². A cutoff P needs derivatives through P+6; the source uses realization P+7.

**Producer → actual consumer.** `EulerPacketTerminalDatum.initializedAllOrderBudget`, `PacketInitializedAllOrderBudget.lean:64–132`, fills every Budget field. Actual constructor `initializedUniformBudget`, `PacketInitializedUniformBudget.lean:39–60`, inserts common-radius joined/primary/normal/mean budgets and `L.correctionCoefficients NB period`; five polynomial costs supply its five frequency guards. `EulerAllOrderDriftCorrection.finite_exists`, `AllOrderDriftFinite.lean:19–47`, calls `exists_global_inviscid_gevrey_PDE` with A at order q+2, N=q−4 and B's literal fields, then rewrites `A.lower_twice`. `Budget.family` at 63–68 selects the finite paths and their equations. `Budget.fieldTower_energy`, `AllOrderDriftCorrection.lean:82–92`, rewrites equality to the finite solution at q=P+6.

**Identity/need/classification.** `Classical.choose` at each finite order does not preserve witness identity by fiat: `FiniteFamily.compatible`, `CorrectionAssemblyCompatibility.lean:18–40`, invokes inviscid uniqueness on restrictions of the **same** A, zero initial data and divergence. `commonPath` is the L² value of the q=6 solve; evaluation fixes its representative. **Core analytic existence/uniqueness**, with **formalization adapters** for coherent Sobolev realizations. All-order existence is **unexpanded** below the finite solver's compactness/limit-equation call; field coherence is **source-inspected**. Full field-use expansion follows below.

### M4 — Physical reconstruction, controlled errors, and a renewable child

**Input/output.** Fix the M3 correction Q for initialized A, inverse physical coordinates X,Y with X(t,Y(t,x))=x, DX=F and det F=1, frame Gevrey bounds CF,R, κ=k⁻¹, direction=m₀. Weighted norms for the same e and its signed pressure at ρ=Q.initialRadius/4 imply physical correction gradient/Hessian ≤`Kerr k Δ`. Combined with initialized approximation bounds and the single frequency comparison, construct one graph flow G, exact parent child and `SmoothState`, labels k^80, displacement ≤k^(-1/4), source gradient/Hessian errors ≤k^(-1/4). A renewed frame and low budgets give `Stage S (n+1)`.

**Producer → actual consumer.** `Budget.physical_gradient_hessian_of_weighted`, `PacketWeightedPhysicalErrors.lean:47–110`, is called on Q in `initialized_uniform_flow_and_shear`, `PacketInitializedUniformFlow.lean:231–237`; final error combination is 238–254. That body's Q is `initializedUniformBudget` (143–144); G is built from **Q** by `physicalFlowData` (212–219), not selected afresh from an unrelated existence theorem. `ParentUniformJoinedChild.lean:91–110` obtains Q,G,E and uses q=6 in `initialized_uniform_child_label_bounds`, hence label exponent 10(6+2)=80. `exists_geometryJoinedChoice`, `ParentGeometryJoinedChoice.lean:46–70`, repackages that output; `chooseJoined` supplies actual stage parameters. `joinedState`, `joinedStep`, `joinedNext`, `PacketJoinedSuccessor.lean:43–110`, use the same selected F.

**Equation/identity.** Physical correction is `k⁻¹ F(t,Y) e(t,graph(k,m₀,Y))`. Pressure force uses `(F⁻¹)*` and the signed pressure tower; `kκ=1` is used to identify the potential Hessian. `GeometryJoinedChoice.coefficient` ties flow.A to Q's lifted packet coefficient. `SmoothState.packetChild`, `ParentState.lean:50–57`, passes the same B, residual,V,G to evolution and Sobolev regularity; oddness additionally needs parity. `Evolution.child`, `ParentEulerChild.lean:31–57`, assigns both scalar-pressure-gradient and zero-momentum proofs from the exact packet producers. A Budget alone does **not** assert its prescribed residual is the approximation's actual Euler residual: `ApproximationResidual` is separately supplied by `SmoothState.joinedChild`, `ParentInitializedState.lean:75–96`.

**Why/classification.** Small cylinder L² error alone cannot control graph restriction or preserve amplified strain. Graph evaluation, inverse-map derivatives, pressure identification and frame renewal are **core analytic/construction-specific** requirements. `Step.next` is already shared; casts/changeActivation are **formalization adapters**. Full renewal and the residual-to-physical Euler theorem below these calls remain **unexpanded**, not absent. Local identity chain and budget arithmetic **source-inspected/human-derived**.

### M5 — Common initial datum, not a limiting trajectory

**Input/output.** Fix the actual family P_n on one S, and for every n≠0 the literal identity `u_(n+1)(0)=u_n(0)+high(I_n,k_n)+mean(I_n,k_n)`. For each fixed m the increment norms are summable. Produce one smooth L² field u_init with all-order H_m convergence of u_n(0), solenoidal, and compact support after including the first datum.

**Representative estimate.** High majorant `ell_n^(-m) k_n^m K_m P_n^N_m exp(-x_n/8)` and mean majorant `ell_n^(-m) k_n^(-2) K_m P_n^N_m` have stage-independent constants for fixed m, not constants uniform over m. These majorant productions are inherited from `actual_high_summable` / `actual_mean_summable`, not independently reconstructed here.

**Producer → actual consumer.** `joinedNext_initial_velocity`, `PacketJoinedSuccessor.lean:114–118`, is used by `stages_initial_step`, `PacketInfiniteConstruction.lean:49–56`. `Stage.initialTailInput`, `PacketStageInitialLimit.lean:23–50`, uses **P_(1+i)** and exact scale shifts J'=J+1, X'=x₁; parameter envelope is `(sourceConstant 4,320,20,1000)`. `initialBase` at 52 retains all of u₁(0). `initial_velocity_partial` at 68–81 telescopes the actual hstep; `initialDataLimit_Hm` at 83–103 removes the finite index shift. `PacketInitialSmoothLimit.lean:48–79` sums high+mean in `SmoothL2Field`, identifies partial fields and passes common closed support to the sum. `initialDatum_Hm`, `PacketFiniteLifespan.lean:30–35`, supplies the literal recursion's hstep, not merely a family of matching norm estimates.

**Why/classification.** Identifying one representative across H_m and retaining the forward prefix is necessary for the same datum in M6. **Core summability**, **construction-specific amplitude gains**, **formalization adapter** for smooth representatives. Local telescoping/source instantiation **source-inspected**; physical majorants and smooth-series theorem **unexpanded**. No pointwise-in-time limit of the full packet family is asserted.

### M6 — H4-reference-controlled H3 stability against sampled escape

**Input/output.** Fix ordinary Euler reference U on [0,T], T≥0. Let exact V_n have nonnegative durations T_n eventually≤T, same limiting initial datum in H3, and sample times t_n∈[0,T_n]. Then the gradients DV_n(t_n,0) cannot tend to infinity. No uniform stage H4 bound is assumed.

**Estimate.** `M=||t↦H4(U(t))||C`, `C_U=1+1800 Cprod(1+M)`. For positive ε_n→0 dominating initial H3 error, eventually `640 ε_n exp(3 C_U T)≤1/2` and `sup_(t≤T_n) H3(V_n−U)≤640 ε_n exp(3 C_U T)`.

**Producer → actual consumer.** `referenceWordBound`, `OrdinaryEulerStability.lean:17–33`, derives WordBound 4 from the same reference's norm path. `Evolution.h3_stability`, `OrdinaryH3Envelope.lean:115–138`, uses regularized actual difference energy and quadratic stability. `eventually_h3_bound_varying`, `OrdinaryEulerVaryingHorizon.lean:28–48`, calls it on `U.restrictTime` but passes **U.referenceSize**, not the restricted norm or a stage-dependent constant. `GrowthData.no_evolution_of_eventually_covering`, `PacketStageContradiction.lean:32–72`, reindexes n↦n+N, converts each actual state's regularity to ordinary evolution, and proves both initial-norm and sampled-gradient identities before applying no-escape.

**Why/classification.** Three commuted derivatives of `(w·∇)U` include `w D⁴U`: H4 belongs to the reference. This is **core analytic derivative loss**, not a record artifact. The H4 explanation and envelope were already expanded in chapter 04; new evidence here is the actual restriction/representative binding. Product/pressure estimates beneath `energyDerivative_bound` remain **unexpanded**. Inspected consumers **source-inspected**.

### M7 — Positive finite maximal lifespan

**Input/output.** M5 supplies smooth all-order solenoidal u_init. General local theory gives a positive evolution. M4/M6 rule out existence on each packet horizon; nesting supplies eventual coverage. Thus there is one finite lifespan L with `0<T*≤inf_n T_n≤T_0≤1`.

**Producer → actual consumer.** `initialDatum_solenoidal`, `PacketFiniteLifespan.lean:39–54`, passes L² convergence to the closed solenoidal space, with explicit toLp/field-subtraction identity. `initialDatum_local` at 61–64 uses general `localEvolution`. `initialDatum_no_packet_horizon` at 82–88 calls M6 on `(packets n).toGrowthData` and `initialDatum_Hm 3`, coverage coming from `packets_horizon_antitone`. `initialDatum_finite_lifespan` at 90–93 supplies local existence and exclusion to `exists_finite_lifespan`; `lifespan` at 96 is its choice; 98–107 prove the upper bound by contradiction using L.shorter.

**Need/classification.** **Core local theory and maximality**, but not the construction producer. No equality of T* with the activation limit, and no claim t_n<T*. Packet existence, not any global minimality claim, motivates all M1–M4 inputs. The comment near the infimum is not used as a theorem identifying activation and horizon limits. Local existence/maximal theory below the calls **unexpanded**; assembly **source-inspected**.

### M8 — Small outer route to both exact delivered Euler statements

**Input/output.** Same `initialDatum` and `lifespan`. For every shorter S<T*, M4 displacement/initial support and Euler curl transport confine packet curls to one compact ball; M5/M6 pass that confinement to the canonical velocity. A hypothetical broad globally smooth finite-energy solution is upgraded to ordinary evolution using common compact curl; endpoint persistence past T* contradicts L.maximal. The scalar Sobolev adapters additionally give energy, local bounds, terminal C1 limsup and infinite vorticity integral.

**Producer → actual consumer.** `packets_vorticity_support` and `evolution_vorticity_support`, `CanonicalVorticityConfinement.lean:29–42,60–99`, use actual inverse particle maps and `S<T*≤T_n` (opposite restriction direction from M6's contradiction). `canonical_vorticity_confined` at 103–107 is passed literally to `no_global_solution_of_confined_vorticity`, `CompactVorticityContradiction.lean:70–107`, by the private assembly in `Solution.lean:27–30`. That body uses comparator agreement, continuity to T*, shifted competitor persistence and common-compact-curl upgrade; **BKM is not its final contradiction**.

**Exact endpoints.** `Euler.euler_breakdown_R3`, `Solution.lean:32–37`, chooses `initialDatum.field`. `Euler.exists_compact_smooth_euler_singularity`, 42–68, chooses the same field, `lifespan.duration`, `maximalVelocityExtension lifespan`, `maximalPressureExtension lifespan`, and explicitly invokes `maximal_sobolev_existence_iff`. Its class is all-order Sobolev on [0,T*), whereas broad exclusion uses jointly future-smooth velocity/scalar pressure, timewise L² and one global energy bound. `SolutionDefinitions.lean:64–80,87–120` supplies the complete class distinction: broad Euler has equation, divergence, trace, joint velocity/pressure smoothness, timewise MemLp and one global energy bound; Sobolev Euler has divergence, trace, SobolevSmoothOn velocity, interior spatial pressure differentiability and an existential SobolevSmoothOn strong time-derivative witness satisfying the interior law. SobolevSmoothOn explicitly carries spatial smoothness, velocity/jet MemLp and velocity/jet L² continuity. Its `toL2` fallback outside MemLp is not a substitute for these integrability fields. Neither smoothness nor finite energy alone supplies all spatial L² derivatives. **Formalization/class adapter with substantial analytic input**; adapter calls inspected, compact-curl upgrade and endpoint-criterion dependency closures **unexpanded**.

## Typed edges and actual bindings

An edge may have separate mathematical-use and actual-instantiation evidence. No import-only edge is promoted to a proof use.

| Edge | Type | Actual binding/domain obligation |
|---|---|---|
| M1→M2/M4 | actual-instantiation | chooseJoined/chooseForward pass S.normal_frequency n, secondary frequency, actual input guard, actual restricted parent; n≠0 only for joined. |
| M2→M3 | actual-instantiation | initializedUniformBudget→initializedAllOrderBudget→initializedDriftBudget for the very initializedCorrectionData; κ=k⁻¹ and time change M.T=D.T. |
| M3→M4 | actual-instantiation | initialized_uniform_flow_and_shear defines Q once and uses its field/pressure/time towers, G and error estimates; selected GeometryJoinedChoice retains coefficient identity and physical errors. |
| M2→M4 | mathematical-use + actual-instantiation | approximation error and ApproximationResidual accompany Q; correction solvability alone does not certify physical Euler. |
| M4→M5 | actual-instantiation | joinedNext_initial_velocity→stages_initial_step→hstep argument of initialDataLimit_Hm; n≠0, base P1 retained. |
| M4→M6 | actual-instantiation | toGrowthData and ordinaryEvolution of the actual state; sampled activationGradient equality checked after reindexing. |
| M5→M6/M7 | actual-instantiation | initialDatum_Hm at s=3 for stability, s=0 for closed solenoidal membership. |
| M6→M7 | mathematical-use + actual-instantiation | T=T_N, eventual T_n≤T_N by antitonicity; no-packet-horizon plus independent local existence. |
| M4/M5/M6/M7→M8 | actual-instantiation | fixed displacement ball, actual initial limit, shorter S<T*≤T_n, same L and same datum. |
| M3 comparison interface→simplification | proposed-explanatory | separate finite existence from coherence in a human proof; no theorem route changed. |

`AllOrderDriftCorrection` imports assembly/time/parity modules: **mere-import** is the only evidence for any internal helper not called in the inspected bodies. No complete graph-edge audit is asserted for historical SOURCE-MAP.

## Central bundled boundary: actual all-order `Budget`

Chosen boundary: `EulerAllOrderDriftCorrection.Budget` (`AllOrderDriftBudget.lean:19–51`), consumed by `finite_exists` and `Budget.comparisonData`. We expand its producers rather than treating its name as an analytic explanation.

### B0. Ambient inputs are not hidden solvability assumptions

Enclosing parameters are L>0 (`Fact`), T>0, and `EulerAllOrderCorrectionData.Data L T`. Its complete fields (`AllOrderCorrectionData.lean:56–82`) are κ,direction, their bounds; metric coefficient tower plus L² continuity, coercivity/positivity; linear tower; three quadratic towers; approximation tower; residual tower. Each coefficient tower has **coefficient, jet, continuous** (28–34); each field tower has **field, realization, value_eq** (37–43). These concern prescribed functions, not correction solutions. `atOrder` takes approximation realization q+1 and residual realization q (85–97). `lower_atOrder` / `lower_twice` use actual truncation identities, not merely equal-looking coefficients.

The packet instantiation is `initializedCorrectionData`, `PacketInitializedCorrectionData.lean:23–38`: normalized packet `k·packet(N,k⁻¹)`, normalized residual `k·inverseCoefficient·actualResidual`, and κ=k⁻¹. Exact physical cancellation also needs the separate `ApproximationResidual` input discussed in M4; no assertion that arbitrary Data.residual is already the true residual.

### B1. Why the drift is small when the normalized field is not

Write Cv=`velocity R H Cmul`, Cn=`normal R H Cmul`, Dg=`2(3Cv+Cn)` (`PacketCorrectionConstants.lean:11–16`). In `joinedPacket_normal_bound` the proof constructs the *actual* profile array a, then obtains:

- a₀=0 from `profiles_zero`;
- a₁.mean=0 from `profiles_one` and primary.mean=0;
- primary tangency against normal `(F⁻¹)*m₀`;
- by adjoint identity, `⟨m₀,F⁻¹ a₁.high⟩=0` (lines 63–72).

Thus the leading normalized O(1) term contributes **no** normal transport. `normalizedNormal_bound` bounds the surviving higher profiles by Cn/k. The full field only has bound Cv. For the actual lifted transport map, `PacketFieldDrift.lean:19–55` proves at each word, then block, then weighted sum:

`||velocityMap(κ,m₀) Z||weighted ≤ 3|κ| ||Z||weighted + ||m₀·Z||weighted`.

The two geometric-series estimates with ρ(4R)≤1/2 give 2Cv and 2Cn/k, hence

`||b_Z||weighted ≤ 6Cv/k+2Cn/k = Dg/k`.

`initializedCorrection_drift` makes precisely this substitution. No differentiation of a small order-zero normal bound is used: the normal estimate is itself a word bound. **Next genuine analytic obligation:** derive the recursive `joinedSource_profile_budgets` and `normalizedNormal_bound` with their support/grade constants from terminal-primary equations. They were called with actual primary data; their proofs are not reconstructed here. This is exposition debt, not a new missing Euler theorem.

### B2. Complete top-level field-use ledger

Literal supplier is `initializedAllOrderBudget` (lines 83–132 particularly); consumer is `finite_exists` (lines 32–47), unless separately stated.

| Budget field(s), all fields accounted for | Literal supplier / use |
|---|---|
| metric | `initializedMetricBudget ... 0`; repackaged by `A.metricBudget ... (q+1)` for finite existence, and unchanged for comparison. |
| radius | continuous scalar path `ρ := radius T cg dg ρg k (expansion k)`; same path every q. |
| growthCoefficient | cg=`growthCoefficient D L Kc (2Cv) (12Cv(4R))`; not dg/k. |
| delta | `exp(-sqrt(expansion k))`, call it Δ to distinguish packet spike δ. |
| initialRadius | ρg=`1/(1+8R+4M Rc+Rc)`. |
| spatial | for each q≥6, `initializedDriftBudget ... q hq` for A.atOrder(q+2), cutoff q−4, the same ρ. |
| growth_bound | `initializedDriftBudget_growth ... .le`; equality proof is rfl (`PacketInitializedSpatialBudget:115–122`). |
| delta_pos, delta_le_one | `delta_pos`, `delta_le_one`; finite solver target error admissibility. |
| radius_pos | `initialRadius_bounds ... .1`. |
| decay | `hscalar.2` from `correction_guards`; identical scalar inequality for every q. |
| scale | `initialRadius_bounds ... .2.2.2`, i.e. ρg Rc≤1. |
| small | `hscalar.1`: 2 Rres exp(3cg T)≤Δ/2. |
| radius_eq | rfl: drift is dg/k at every q. |
| divergence | `initializedCorrectionData_divergence` with actual Ξ, DΞ=F and det F=1; used for finite solenoidality and compatibility. |

**No top-level Budget field is declared globally unused.** All are passed into finite construction, directly or in its bundles. The narrower comparison projection (`AllOrderDriftBudget:55–60`) reads only metric, radius, `(spatial 6).full`, divergence. Growth/smallness/radius-decay are incidental to **that projection**, not to the existing route. Comparison itself uses the base spatial radius positivity and linear/quadratic bounds; its whole spatial input is not evidence that every estimate in that record is essential to uniqueness.

### B3. One layer lower: all fields of the finite budgets

`EulerDriftCorrectionBudget.Budget` (`DriftCorrectionBudget.lean:17–27`) contains exactly **full, drift, drift_nonneg, drift_bound**. The supplier sets drift=dg/k and uses B1. `full` is `SpatialBudget` (`CorrectionEnergyData.lean:24–79`), filled in `PacketInitializedSpatialBudget.lean:57–98`:

| Spatial fields | Literal supplier and mathematical role |
|---|---|
| Rc,M,B,A0,A2 | copied from Kc=`L.correctionCoefficients NB period` (actual caller in `PacketInitializedUniformBudget:54`). Coefficient series, H5/H6 pressure inverse and multiplier bounds. |
| B0,B1,residual | 2Cv, 12Cv(4R), `2 exp(-0.7 X log k)`, independent of q. |
| Rc_nonneg,M_one_le,B_nonneg,A0_nonneg,A2_nonneg | Kc fields, unchanged. |
| B0_nonneg,B1_nonneg,residual_pos | scalar positivity from actual Cv,R and exp. |
| radius_pos,radius_small | hρ and hpressure from ρg/2≤ρ≤ρg and `4M ρg Rc≤1`. |
| inverse_five,inverse_six | Kc inverse bounds at realization q+2, restricted to fixed base 5 and 6. |
| metric_derivatives,metric_base | Kc bounds at realization q+2, higher blocks `Rc^l(l!)²`, base r≤6. |
| background,background_derivative | `initializedCorrection_background` / `_background_derivative`, deriving weighted bounds from the actual normalized Field.WordBound; realization/cutoff relation q−4+6=q+2, extra realization for differentiation. |
| linear,quadratic | Kc.linear / Kc.quadratic; quadratic supplied actual κ=k⁻¹ and scale_bound. |
| residual_bound | `initializedCorrection_residual` with same N,k,X and actual initialized residual. |

The `MetricBudget` below metric has **metric, continuous, derivative, hasDeriv, c, c_pos, symmetric, coercive, inverse, bound, first, time, bound_nonneg, first_nonneg, time_nonneg, bound_le, first_le, time_le** (`CorrectionEnergyData:82–120`). `initializedMetricBudget` calls `sourceMetricBudgetOfFields D period k⁻¹ ...` on the **same normalized field and residual** (`PacketInitializedSpatialBudget:26–33`). `Data.metricBudget` copies every field unchanged at all q (`AllOrderCorrectionData:110–130`). The inverse metric's coercivity is c², not the forward coefficient's coercivity. Its first/time bounds feed growth constants; its inverse identity is needed for the pressure/energy structure.

The metric and Kc analytic suppliers beneath these calls are **unexpanded**, not silently replaced by arbitrary constants. Full nested record fields were read, but their internal estimate-use closure in the nonlinear energy theorem is **unknown here**; passing a record is not proof of minimal dependence of each field. This is the stopping boundary for pressure inversion and variable-metric commutators.

### B4. Worked scalar budget: no per-order shrinking radius

Let X=k^θ, θ=10⁻⁶, N=floor X; define εpow=k^(θ/100), Δ=e^(−√X), Rres=2e^(−0.7X log k). The five fixed costs are tail polynomial, coefficient multiplier, 12cgT, 8cgT·dg/ρg, 8cgT/ρg; each ≤εpow. `initializedUniformBudget:55–60` obtains these from one polynomial bound, not a new eventual threshold for each q.

1. **Truncation cost:** `tailBase ≤ Ctail N^222 ≤ k^(θ/100+222θ) ≤ k^(1/100)` (`PacketSourceFrequency:38–53`). Numerically θ/100+222θ=0.00022201<0.01. N is fixed by k, independent of correction Sobolev order q.
2. **Residual wins:** X≥64, log k≥1, 3cgT≤X/4. Since √X≤X/8 and log 8≤X/8,
   `log 8 −0.7X log k+3cgT ≤ (1/8−7/10+1/4)X = −13X/40 ≤ −√X`.
   Hence `2Rres e^(3cgT)=4e^(−0.7X log k+3cgT)≤Δ/2`. This is `residual_small`, `PacketCorrectionScalar:44–58`.
3. **Separate drift and error losses:** from `8cgT·dg≤ρg k`, `8cgT≤ρg e^√X`, obtain `2cgT(dg/k)≤ρg/4` and `2cgTΔ≤ρg/4`. Therefore `ρ(t)=ρg−2cg(dg/k+Δ)t≥ρg/2` on [0,T]. The denominator of ρg simultaneously gives `ρg(4R)≤1/2`, `4MρgRc≤1`, `ρgRc≤1` (`PacketCorrectionScalar:27–41,62–87`).

This calculation is **newly connected to every literal scalar supplier**; chapter 04 displayed abstract all-order inequalities but did not expose this common-order substitution or the normal cancellation that makes it feasible. It is not a fresh proof of the nonlinear Gevrey energy theorem.

### B5. Finite-order choices, pressure and physical-error lineage

Finite existence calls the inviscid solver at input q+2, retained q+1, equation q; its proof first obtains a Gevrey inviscid limit, then passes the actual correction equation (`DriftGlobalInviscidGevrey.lean:54–67`). This is where the next analytic obligation becomes visible: viscosity-regularized compactness with retained energy and convergence of the nonlinear projected source. We did not unfold that compactness proof.

The all-order assembly is **not** another compactness extraction: compatibility restricts e_(q+1) and invokes uniqueness against e_q. It uses equal equations after `A.lower_atOrder`, zero initial traces, and divergence of approximation and both corrections. `FiniteFamily.commonPath` is literally value(e₆), not a new limit choice. Realization order s is restriction of solve s+6; `solution_eq_realization` proves that the original solve at q already equals the tower at q+1, allowing the sharper P+7 energy realization. (`CorrectionAssemblyCommon:22–29,53–78`; `CorrectionAssemblyRealizations:15–38`.)

Pressure coherence is not a second arbitrary selection: rawSourcePath truncates by source restriction and correction compatibility; both pressure values reduce to the same coercive L² pressure operator on the same raw source (`CorrectionAssemblyPressure:29–60`). Signed pressure belongs to a lifted gradient space, not a scalar pressure function until the physical-potential bridge.

Finally weighted e/pressure estimates at common radius ρg/4 yield all pointwise word sums `(Cemb Cw Δ)ρ^(−n)(n!)²`. Inverse-coordinate reconstruction has `physicalRadius≤physicalRadiusCost·k`, so one physical derivative costs k (`PacketPhysicalFrequencyBounds:29–47,73–91`). `PacketWeightedPhysicalErrors:63–108` explicitly invokes these word bounds and the scalar potential Hessian identity; the common constant Kerr dominates both velocity and pressure losses.

With Kv,Kp,Kerr≤εpow≤k^(1/2) and Δ≤k^(−3),

`Kv/k + Kerr k Δ ≤ k^(−1/2)+k^(−3/2) ≤ 2k^(−1/2) ≤ k^(−1/4)`

when k^(1/4)≥2, and likewise for pressure. Source uses the slightly coarser two inverse-half bounds (`PacketUniformFrequencyMargin:17–60`). It separately needs k^(1/4)≥16 for flow smallness, not just this error inequality. Parent physical scaling ell reappears in flow jet radius `ell⁻¹ k^(5/4)` and label bounds; one must not apply the normalized-coordinate estimate as if ell disappeared from every derivative theorem.

**Choice barrier:** the body of `exists_geometryJoinedChoice` exhibits a Q with this derivation. `chooseJoined` later uses `Classical.choice` of the exported record. Its guaranteed fields are exactly hn,Q,flow,graph,coefficient,labels,label_constant,displacement_bound,errors (`ParentGeometryJoinedChoice:26–40`). Their consumers are respectively typed correction data/state; child construction; flow constraints and matching; next label/renewal guard; confinement; low/physical/renewal bounds. The errors field certifies both physical estimates for the very Q in the selected record. The exported record does **not** equate selected Q to `initializedUniformBudget`, nor export its concrete radius/Δ formulas. These formulas explain existence; they may not be attached to the selected Q without an additional theorem. No all-domain selected certificate is invented here.

## Complexity and debt disposition

- **Core analytic:** cancellation of the leading normal drift; retained Gevrey energy under a common radius; finite inviscid existence and uniqueness; graph-to-physical derivative/pressure transfer; initial-data summability; H4-dependent H3 comparison. Each has a consumer that would otherwise lack its needed estimate or identity in this route.
- **Construction-specific:** fixed tiny-power truncation, five cost envelopes, label exponent 80, positive-history guards, coupled low/pressure/frame renewal, common support/displacement. No global optimality or numerical minimality is claimed.
- **Formalization adapters:** all-order coefficient/field towers, value injectivity, truncation, representative identification, changeTime/changeActivation and scalar-class conversions. Several encode real mathematical identity obligations, so removal is not automatically sound.
- **Duplication candidate, not conclusion:** repeated argument spines around finite correction source/coefficient/tower conversions may be expositorily compressed. Forward/joined `Step.next` is already shared; their distinct history producers should not be merged merely because records look alike.
- **Exposition gaps:** terminal-primary/profile recurrence; variable-metric pressure inverse/commutator constants; finite inviscid compactness; full frame renewal; initial physical H_m majorants; ordinary local/continuation theory; finite-energy compact-curl upgrade. Located formal producers exist; no formal proof gap established.
- **Export gap / currently unproved attribution:** concrete scalar-radius lineage of the *selected* GeometryJoinedChoice.Q is not exported by that record. This is not needed by its delivered downstream consumers. Whether an identity or stronger invariant can be exported without altering the selection is unresolved; existence-witness history is insufficient.
- **New research:** any stronger physical theorem beyond these actual contracts would need separate premises/proof. No unforced-NS, autonomous-persistence, minimal-proof or A/B conclusion is made.

Highest-value bounded follow-up is specified in NEXT-TARGET.md. This map materially expands the central producer boundary, but is not a full human reconstruction of Euler singularity formation.
