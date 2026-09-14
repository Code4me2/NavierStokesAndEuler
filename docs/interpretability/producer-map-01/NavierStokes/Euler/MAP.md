# Producer/consumer mechanism map

Baseline and observed HEAD: `5fdcfe346d399f68f19a820526b59b5326f28939`. All citations below refer to Git objects at that pin; body quotes and line ranges are also in MAP.json. Live tracked source had no reported modifications; untracked REVIEW.md, SIMPLIFICATIONS.md and review-notes/ were left untouched. No builds, Lean probes, package operations, Comparator retries, commits, pushes or repository writes. No upstream manuscript/source substituted for retained producers.

This is source-body inspection and bounded human deduction, **not fresh kernel verification**. User-supplied existing authentic Nanoda+Lean gates on df3d891 and final doc-only 5fdcfe3 delta remain prior evidence. Published simplify/main are not treated as needing protection at superseded 26e896e. Research and four H3 additions are outside the delivered producer route examined here.

The historical 30-ID map is not reauthored. Nodes below are a new small mechanism graph; an inspected caller/callee body edge does not certify its entire dependency closure. `source-inspected` labels the cited local evidence, `unexpanded` labels analytic derivation debt, `unresolved` labels a specifically stronger claim not established here, and `human-derived` labels displayed budget arithmetic. No global minimality claim is made.

## Euler: eight mechanisms

E1 → E2 → E3 → E4 → E5 → E6 → E7 → E8

Edges in this macrochain are **mathematical-use**, not mere imports. Exact supplied-object relations appear under each node; intermediate calls are not mislabeled direct calls. No import-only edge is used as proof evidence.

### E1 — Forward once, then joined successors of one scale hierarchy

- **Input:** One S:Scales(q,B), q≥requiredExponent, B≥commonThreshold(Cg,Cp); full Stage S n.
- **Output:** Stage S(n+1), using forward at n=0 and joined at n≠0; actual sampled gradients diverge for packets.
- **Why needed here:** Joined history requires positive activation history, unavailable at zero. Full stage geometry is needed for renewal, not merely a gradient lower bound.
- **Equation/budget:** stages(0)=S.firstStage; stages(n+1)=stages(n).successor; nextTime depends on current frame.
- **Actual consumer relation:** chooseJoined calls exists_geometryJoinedChoice at k=frequency S.J S.X n, nextEll=supportScale(...,n+1), restrictedState, hterminal=rfl, label/frequency and inverse-scale guards. chooseForward uses distinct earlyRatio.
- **Construction identity:** constructionScales classically selects one Scales before recursion; chooseJoined selects a GeometryJoinedChoice satisfying its exported record, not equality with an internal exhibit.
- **Complexity classification:** construction-specific numerical hierarchy + core renewable packet mechanism
- **Limit:** Full Scales and Stage record closure not audited here; ray amplification production remains unexpanded.
- **Producer citation:** `Euler/PacketInfiniteConstruction.lean:39–44` `stages`; body at line 41: `| n+1 => (stages n).successor hq hB`.
- **Consumer citation:** `Euler/PacketInfiniteConstruction.lean:66–67` `packets`; body at line 66: `def packets (n : ℕ) : Stage constructionScales n := stages constructionScales le_rfl le_rfl n`.
- **Evidence:** source-inspected local bodies; analytic closure limited as above.

### E2 — Central boundary: all-order drift budget is produced from packet inputs

- **Input:** Fixed joined M,D,hTime, 0<τ<D.T, history B, support/cutoff, α>0, 0<δ≤1, coefficient agreement, joined/normal/mean budgets and RadiusPrimitives W; one guarded frequency k and actual volume-preserving map Ξ.
- **Output:** One Budget period D.T_pos (initializedCorrectionData ... truncation(k) ... k), with metric, radius, growthCoefficient, target delta and every-order spatial bounds.
- **Why needed here:** Finite solver must hold at all construction orders with one radius and one inverse metric; choosing a fresh parent/frequency for each order cannot give coherent correction.
- **Equation/budget:** ρ0=(1+8R+4M Rc+Rc)^-1; Δ=e^-sqrt(X); residual=2e^(-0.7X log k); ρ(t)=ρ0−2C(Ddrift/k+Δ)t.
- **Actual consumer relation:** period>0 typeclass; all q≥6 use A.atOrder(q+2), cutoff q−4 and common metric transported from order 1. Details of every Budget field and literal supplier below.
- **Construction identity:** initializedUniformBudget passes five bounded costs to initializedAllOrderBudget; initialized_uniform_flow_and_shear defines Q as precisely initializedUniformBudget internally. A selected GeometryJoinedChoice retains Q and its needed equations, not all discarded quantitative exhibit facts.
- **Complexity classification:** core drift-versus-full-background energy distinction; construction-specific frequency budget
- **Limit:** initializedDriftBudget analytic word estimates and genuine finite PDE existence are next unexpanded analytic obligations; no mathematical gap identified.
- **Producer citation:** `Euler/PacketInitializedAllOrderBudget.lean:64–134` `initializedAllOrderBudget`; body at line 107: `spatial := fun q hq => initializedDriftBudget M D hTime τ hτ hτT B δ hδ ξ hs α Cagree`.
- **Consumer citation:** `Euler/AllOrderDriftFinite.lean:19–49` `finite_exists`; body at line 39: `(B.scale q hq) (B.small q hq) (B.radius_eq q hq)`.
- **Evidence:** source-inspected local bodies; analytic closure limited as above.

### E3 — Uniqueness identifies finite solves with one all-order correction

- **Input:** Same A and Budget B; ∀q≥6 finite_exists gives continuous H^(q+1) correction with zero trace, lifted divergence constraint and literal projected PDE.
- **Output:** One common L2 path, Sobolev fieldTower at all orders, zero pointwise initial correction, and exact signed pressure time law.
- **Why needed here:** Independent finite choices do not automatically coincide. Restriction/uniqueness is what permits every energy bound and physical evaluation to refer to one correction.
- **Equation/budget:** truncate(e[q+1])=e[q]; energy_P(e)≤2R[P+6] exp(3Ct)≤Δ/2.
- **Actual consumer relation:** ComparisonData uses only B.metric,B.radius,(B.spatial 6).full,B.divergence. No radius-loss smallness needed for compatibility; finite energy cutoff P uses q=P+6 and realization P+7.
- **Construction identity:** Budget.solution chooses finite_exists at each order; family contains only solution/initial/divergence/equation, no assumed compatibility. fieldTower.realization q restricts solution(q+6); value_injective yields same-order identity.
- **Complexity classification:** core uniqueness/coherence + formalization Sobolev realization adapter
- **Limit:** inviscid_corrections_compatible energy/pressure proof and global finite solver not fully reconstructed. Weighted Gevrey sum is not ordinary physical Hm.
- **Producer citation:** `Euler/CorrectionAssemblyCompatibility.lean:18–42` `FiniteFamily.compatible`; body at line 28: `apply inviscid_corrections_compatible period hq T hT.le (A.atOrder period (q+1))`.
- **Consumer citation:** `Euler/AllOrderDriftCorrection.lean:82–94` `Budget.fieldTower_energy`; body at line 91: `rw [← B.solution_eq_realization period (P+6) (by omega)]`.
- **Evidence:** source-inspected local bodies; analytic closure limited as above.

### E4 — Same correction supplies flow, shear and pressure errors

- **Input:** Produced Q, same initialized normalized field V and derivative Vt; weighted bounds for Q field/pressure/time towers at ρ0/4; inverse particle map Y with X∘Y=id and det DX=1; common frequency guards.
- **Output:** One G with G.A=Q.liftedPacketCoefficient(V), graphConstraint=0, physical gradient/Hessian errors≤k^-1/4, displacement≤k^-1/4 and child labels k^80.
- **Why needed here:** Small cylinder energy is not a restriction-to-graph theorem. Physical derivative errors must be paid before the amplified packet can be used as exact child geometry.
- **Equation/budget:** error≤C/k+E k Δ≤2k^-1/2≤k^-1/4; liftedAmplitude·Rf·T≤1/8.
- **Actual consumer relation:** All t∈[0,D.T], all normalized x; physical child uses x/ell and inverse map, not unscaled graph variables. q=6 in joined_uniform_child turns label exponent 10(q+2) into 80.
- **Construction identity:** UniformFlow constructs G from Q.physicalFlowData; UniformChild keeps same hn,Q,G and coarsens actual fields; ParentUniformJoinedChild builds LC from those fields; GeometryJoinedChoice stores Q,flow,coefficient,graph,labels,errors.
- **Complexity classification:** core graph/pressure analytic transfer + construction-specific label renewal
- **Limit:** Weighted physical gradient/Hessian theorem and normalized packet error proofs are named actual obligations, not expanded energy-to-graph proofs. Selected record drops explicit ρ0 and Δ identities from existence exhibit: do not attribute them to chosen F.Q.
- **Producer citation:** `Euler/PacketInitializedUniformFlow.lean:73–259` `initialized_uniform_flow_and_shear`; body at line 234: `Q.physical_gradient_hessian_of_weighted D period X Y hXd hXY hY hdet`.
- **Consumer citation:** `Euler/ParentGeometryJoinedChoice.lean:46–77` `exists_geometryJoinedChoice`; body at line 60: `obtain ⟨hn,Q,G,hgraph,hG,herror,hdisplacement,LC,hLC⟩ := I.label.joined_uniform_child S.evolution.inverse I.low`.
- **Evidence:** source-inspected local bodies; analytic closure limited as above.

### E5 — Exact child bounds retain a sharper one-sided pressure budget

- **Input:** Selected GeometryJoinedChoice F; parent gradient CM, Hessian CH, upper quadratic curvature Kupper, source errors ev=ep=k^-1/4, geometry guards and support symmetry.
- **Output:** Exact child whole-horizon norm bounds; LowBounds with smaller pressure-upper cost using δ·goodRatio+badRatio; renewal and next Stage.
- **Why needed here:** Using the absolute Hessian norm cost in place of the one-sided curvature cost would lose the specific smallness budget used for renewable geometry.
- **Equation/budget:** |Du_child|≤CM+hchild(goodRatio+badRatio)+ev; <D²p_child z,z>≤[Kupper+2CM hchild(δ goodRatio+badRatio)+ep]|z|².
- **Actual consumer relation:** SourceErrors uses same B/Q and normalizedPacketVelocity/Pressure at every t,x. exactPacket_derivative_split transfers to physical derivatives at x/ell; pressure_hessian_eq_force identifies Euler force as ∇p, not forcing.
- **Construction identity:** joinedState=GeometryJoinedChoice.state of selected F; physical_bounds and lowBounds both consume F.errors. joinedStep supplies same parent/state and F.renewal, not independently chosen fields.
- **Complexity classification:** core signed pressure mechanism; construction-specific good/bad time split; forward/joined parallel code already shares Step
- **Limit:** good_step_bounds and renewed-frame perturbation analysis unexpanded. Duplication candidate only argument plumbing, not deletion of distinct history/early estimates.
- **Producer citation:** `Euler/PacketChildLowBounds.lean:187–220` `exactPacket_whole_horizon_low_bounds`; body at line 204: `by_cases ht : 1 ≤ scaledTime τ F.a F.epsilon t`.
- **Consumer citation:** `Euler/PacketJoinedSuccessor.lean:58–109` `joinedStep`; body at line 70: `low := (F).lowBounds (gradientConstant*previousShear S.J S.X n)`.
- **Evidence:** source-inspected local bodies; analytic closure limited as above.

### E6 — Common initial datum via literal joined increments

- **Input:** Full actual stage family and ∀n≠0 exact `u[n+1](0)=u[n](0)+high_n+mean_n`; physical majorants summable separately for each fixed m.
- **Output:** One smooth L2 datum uinit, Hm initial convergence for every fixed m; closed solenoidal subspace yields divergence-free limit.
- **Why needed here:** Convergence of unrelated packet profiles would not compare exact stage data to one reference. Exceptional forward first insertion must remain in base datum u1(0).
- **Equation/budget:** `u[1+N](0)=u1(0)+Σ[i<N](high[1+i]+mean[1+i])`; high gain exp(-x/8), mean gain k^-2.
- **Actual consumer relation:** Tail input uses P(1+i), J+1, X=scaleSequence(J,X,1); frequency_shift is equality, not reselection. Constants depend on m but not tail index.
- **Construction identity:** initialDatum := Stage.initialDataLimit packets; initialBase=(P 1).state.regularity.velocity zeroTime. joinedNext_initial_velocity supplied by same F; correction pointField_initial is zero.
- **Complexity classification:** core all-order summability + representative/support adapter
- **Limit:** Physical initial-amplitude majorants and smooth-series support proof unexpanded here; compact support asserted by delivered route, not deduced from merely L2 convergence.
- **Producer citation:** `Euler/PacketStageInitialLimit.lean:68–82` `initial_velocity_partial`; body at line 78: `rw [show 1+(N+1)=(1+N)+1 by omega,hstep (1+N) (by omega),ih]`.
- **Consumer citation:** `Euler/PacketFiniteLifespan.lean:30–38` `initialDatum_Hm`; body at line 35: `(fun n hn => stages_initial_step constructionScales le_rfl le_rfl n hn) s`.
- **Evidence:** source-inspected local bodies; analytic closure limited as above.

### E7 — H4-controlled H3 stability contradicts sampled escape

- **Input:** Hypothetical ordinary reference U:[0,T], stage horizons Tn≥0 eventually≤T, exact stages, H3 initial convergence, tn∈[0,Tn].
- **Output:** No gradient escape; hence initialDatum has no evolution to any packet horizon and 0<Tstar≤inf Tn≤1.
- **Why needed here:** H4 of the fixed reference controls derivative loss in the H3 difference estimate; no uniform stage H4 assumption. Horizon direction is necessary.
- **Equation/budget:** Hm=3 error≤640 εn exp(3 C(U) T), εn=d_n+1/(n+1); C(U) uses sup_t H4(U(t)).
- **Actual consumer relation:** Restriction retains original U.referenceSize and original T. Fixed N reference duration T_N covers later packet horizons. No requirement that tn<Tstar.
- **Construction identity:** initialDatum_Hm 3 + packets.toGrowthData; lifespan chosen from finite_lifespan theorem independently of any imagined limiting trajectory through packet activations.
- **Complexity classification:** core reference stability and finite-lifespan mechanism
- **Limit:** H3 energy/pressure estimate and ordinary local theory unexpanded in this pass; outer calculation already in chapter 04.
- **Producer citation:** `Euler/OrdinaryEulerVaryingHorizon.lean:28–49` `eventually_h3_bound_varying`; body at line 47: `(U.restrictTime_referenceWordBound (durations n) (hD n) (hDT n))`.
- **Consumer citation:** `Euler/PacketFiniteLifespan.lean:82–89` `initialDatum_no_packet_horizon`; body at line 87: `(eventually_atTop.mpr ⟨N,fun n hn => packets_horizon_antitone hn⟩)`.
- **Evidence:** source-inspected local bodies; analytic closure limited as above.

### E8 — Compact-vorticity class bridge and exact delivered theorems

- **Input:** Canonical finite lifespan for initialDatum plus canonical confined vorticity; scalar/Sobolev adapters and continuation/energy criteria.
- **Output:** Euler.euler_breakdown_R3 and Euler.exists_compact_smooth_euler_singularity for the same nonzero compact datum, Tstar≤1, energy/C1/BKM properties and broad global exclusion.
- **Why needed here:** Ordinary finite lifespan alone does not exclude globally smooth finite-energy velocities lacking proved all-order L2 jets; compact-curl upgrade supplies this bridge.
- **Equation/budget:** For S<Tstar≤Tn restrict stages to [0,S], unlike E7; canonical curl confinement then permits hypothetical competitor upgrade/restart.
- **Actual consumer relation:** Broad global class and lifespan Sobolev class differ. Closed existence iff T<Tstar; no solution value at totalized endpoint inferred. Restart is of hypothetical smooth global competitor.
- **Construction identity:** Both public theorem bodies use initialDatum.field; maximalVelocityExtension/maximalPressureExtension use same lifespan.
- **Complexity classification:** core class-bridge analysis + formalization adapters
- **Limit:** Compact-curl persistence/div–curl/time upgrade and full adapter bodies not newly audited. Prior four-target validation evidence only; no fresh kernel claim.
- **Producer citation:** `Euler/Solution.lean:27–31` `initialDatum_no_global_solution`; body at line 29: `no_global_solution_of_confined_vorticity lifespan canonicalVorticityBall`.
- **Consumer citation:** `Euler/Solution.lean:42–74` `exists_compact_smooth_euler_singularity`; body at line 58: `lifespan.duration_pos, lifespan_le_one, maximal_sobolevSolution lifespan,`.
- **Evidence:** source-inspected local bodies; analytic closure limited as above.

## Expanded central boundary: `EulerAllOrderDriftCorrection.Budget`

Pinned complete record: `Euler/AllOrderDriftBudget.lean:19–52`. Fix period>0, T>0 and **one coherent Data A**. The record has the following complete fields. All are used by finite existence; no field is certified incidental for the whole route.

| Field | Literal supplier in `initializedAllOrderBudget` | Consumption |
|---|---|---|
| metric | `initializedMetricBudget ... 0` | finite_exists via A.metricBudget; comparisonData |
| radius | ρ=`radius D.T cg dg ρg k (expansion k)` | every spatial budget and finite energy |
| growthCoefficient | cg=`growth ...` from full background constants | Gronwall constant and radius slope |
| delta | exp(-sqrt(expansion k)) | common target error, not packet spike δ |
| initialRadius | ρg=`initialRadius L.R Kc.M Kc.Rc` | scale, radius retention |
| spatial ∀q≥6 | `initializedDriftBudget ... q hq` | actual order-q coefficient/full/drift/residual bounds |
| growth_bound ∀q | `initializedDriftBudget_growth(...q...).le` | dominate combinedConstant uniformly in q |
| delta_pos, delta_le_one | scalar delta_pos / delta_le_one | finite solver bootstrap |
| radius_pos | initialRadius_bounds.1 | positive radius |
| decay ∀q | correction_guards output hscalar.2 | retain half radius |
| scale ∀q | initialRadius_bounds.2.2.2 | coefficient radius fits |
| small ∀q | hscalar.1 | residual beats actual Gronwall |
| radius_eq ∀q,t | rfl | same order-independent radius, no new radius at q |
| divergence ∀t | `initializedCorrectionData_divergence ... Ξ hΞ hF hdet` | actual lifted divergence of approximation |

Nested `MetricBudget`, `SpatialBudget`, drift Budget and coherent Data definitions were read completely (CorrectionEnergyData.lean:24–122, DriftCorrectionBudget.lean:17–28, AllOrderCorrectionData.lean:29–83). They are not free solver conclusions. Their complete analytic supplier closure is not expanded; this is an explicit scope limit. SpatialBudget contains Rc,M,B,B0,B1,A0,A2,residual with sign certificates; radius_pos; inverse_five/inverse_six; radius_small; metric_derivatives/metric_base; background/background_derivative; linear/quadratic; residual_bound. In initializedSpatialBudget (PacketInitializedSpatialBudget.lean:57–98), Kc supplies the coefficient constants, inverse bounds and coefficient jets; B0=2 velocity, B1=12 velocity·4R; initializedCorrection_background, initializedCorrection_background_derivative and initializedCorrection_residual supply the actual field estimates. The drift wrapper (101–113) adds drift=Ddrift/k, its nonnegativity and initializedCorrection_drift. These four field estimates, rather than record repetition, are the next analytic obligations. MetricBudget contains metric, continuous, derivative, hasDeriv, c/c_pos, symmetric, coercive, inverse, bound/first/time with nonnegativity and uniform bound_le/first_le/time_le. initializedMetricBudget uses sourceMetricBudgetOfFields of the same normalized field/residual at k^-1; that inverse-metric producer remains unexpanded. Coherent Data contains κ,direction and bounds, metric tower/continuity/coercivity, linear/quadratic towers, approximation/residual towers; each FieldTower has common field, realization and value_eq. Data.atOrder extracts these same fields, not independent order-dependent data. The supplied `ComparisonData` and `FiniteFamily` records **were** read completely. ComparisonData contains metric/radius/base-order spatial/divergence only. FiniteFamily contains solution/initial/divergence/equation only. Compatibility is proved, never a field assumed of that family.

### Actual instantiation, rather than hypothetical budget matching

`initializedUniformBudget` (PacketInitializedUniformBudget.lean:39 onward) creates joined, primary, normal and mean budgets on a common initialized radius, constructs `Scales.ofTimeProfile`, and sends five frequency cost inequalities to `initializedAllOrderBudget`. `initialized_uniform_flow_and_shear` defines Q using that exact uniform budget, uses its weighted field/pressure/time estimates, and constructs G via `Q.physicalFlowData`. `initialized_uniform_child_label_bounds` retains the same Q,G; `LabelData.joined_uniform_child` calls it at q=6, yielding k^(10(6+2))=k^80 labels. `exists_geometryJoinedChoice` packages the result, and `Stage.chooseJoined` selects from that record with actual `joinedInput`, `restrictedState`, frequency and scale guards.

Selection qualification: GeometryJoinedChoice has exactly hn,Q,flow,graph,coefficient,labels,label_constant,displacement_bound,errors. `state` consumes Q/flow/coefficient/graph/labels, `physical_bounds` and `lowBounds` consume errors; label_constant goes into joinedStep; displacement is relevant to later confinement, not read directly by the displayed physical norm estimate. hn fixes the same truncated approximation. No field is declared globally unused. The choice record **does not retain** all of the exhibit's explicit Q.delta/Q.initialRadius or weighted-tower equalities. The chosen F.Q is a Budget with exported errors/coefficient identity, not proved equal to the internal canonical Q. The downstream route needs the retained fields, so this is not a formal proof gap.

### Worked scalar budget (producer, not repeated bundle)

Write X=expansion k≥64, log k≥1, Δ=exp(-sqrt X), r=2exp(-0.7X log k), and 3CT≤X/4. Since sqrt X≤X/8 and log 8≤X/8,

    log 8 −0.7X log k +3CT ≤ X/8−0.7X+X/4 = −0.325X ≤ −sqrt X.

Therefore 2r exp(3CT)≤Δ/2. This is exactly the `residual_small` mechanism in PacketCorrectionScalar, not smallness of full approximate velocity. Separately, guards 8CT Ddrift≤ρ0 k and 8CT≤ρ0 exp(sqrt X) imply

    2CT(Ddrift/k+Δ)≤ρ0/4+ρ0/4=ρ0/2.

Thus ρ(t)≥ρ0/2 for all t∈[0,T]. Full background determines C; the **small actual drift Ddrift/k** determines slope. For ρ0=(1+8R+4M Rc+Rc)^-1, ρ0·4R≤1/2 and 4Mρ0 Rc≤1 pay distinct packet-series and pressure-inverse requirements.

### Same-field coherence, and the next physical obligation

finite_exists calls the genuine drift global inviscid solver with A.atOrder(q+2), lowers twice using `Data.lower_twice`, and returns the literal equation at order q. Independently chosen e_q have the same zero datum. `FiniteFamily.compatible` compares e_(q+1) restricted to H^(q+1) with e_q using only ComparisonData, and inviscid uniqueness proves equality. `fieldTower` uses restricted e_(q+6), while `solution_eq_realization` proves this equals e_q at its order. For energy cutoff P take q=P+6: P≤q−4 and P+6≤q+1 hold, and the same realization gets both residual and target bounds. There is no sequence of new exact physical children indexed by derivative order.

The weighted physical transfer is not an embedding without scale cost. A further inspected layer is `PacketWeightedPhysicalErrors.lean:47–121`, `Budget.physical_gradient_hessian_of_weighted`. Its literal correction velocity is k^-1 F(t,Y(t,x)) e(t,cylinderGraph(k,m,Y(t,x))); the pressure-force reconstruction is k^-1 FInv(t,Y(t,x))^adjoint times the pointwise signed pressure. It first uses `FieldTower.pointField_wordSum_gevrey` to obtain the all-word bound Σ|D_word e|≤(Cpt d)ρ^-n(n!)², Cpt=sobolevEmbeddingConstant(period,3)·Cw, and similarly for pressure. It then invokes `physicalReconstruction_power_bound` and `physicalPressureForce_power_bound` at physical derivative order 1, finally identifying the latter with the Hessian of `Q.physicalPotential`. The shared cost is ((1+9CF) physicalFixedCost(D,R,CF,ρ^-1,1))·Cpt. Thus the next unexpanded analytic layer is those reconstruction power bounds and the weighted point-evaluation proof, not merely the top bundled estimate. UniformFlow calls `Q.physical_gradient_hessian_of_weighted` with actual X,Y, inverse identity, determinant one, frame constants and weight radius ρ0/4. It then combines the approximate packet error C/k and correction error E k Δ. From C,E≤smallPower(k)≤k^(1/2), Δ≤k^-3:

    C/k≤k^-1/2,  E k Δ≤k^-3/2≤k^-1/2,
    C/k+E k Δ≤2k^-1/2≤k^-1/4  (2≤k^1/4).

This is the literal `physical_error_le_inverse_quarter` supplier. Flow smallness is separate: using Rf,T≤k^(1/8), liftedAmplitude≤2k^-1/2 gives amplitude·Rf·T≤2k^-1/4≤1/8 under 16≤k^1/4. Small graph flow and small differentiated physical correction are different inequalities.

One further consumed distinction: whole-horizon absolute Hessian control uses goodRatio+badRatio, but upper quadratic pressure control uses δ·goodRatio+badRatio. `exactPacket_whole_horizon_low_bounds` splits at scaledTime=1 and applies good_step_bounds versus absolute_step_bounds. `lowBounds` uses this sharper curvature budget in the T²/2, T, and boundaryLocalizationC2·r³T smallness inequality. This is a sign-sensitive analytic requirement, not administrative record size.

## New evidence and scope

Chapter 04 already explains abstract correction, initial summability and H4-reference stability. New evidence here is the literal five-cost-to-every-order budget supplier; the separation of finite-family existence from compatibility; the common-radius/base-order comparison contract; explicit same-Q flow/velocity/pressure supplier chain with its selection caveat; the k derivative loss paid in physical errors; and the distinct signed curvature cost.

Still missing as human reconstructions: initialized spatial word estimates; finite inviscid solver and pressure inverse; graph-to-physical weighted gradient/Hessian bound; renewed-frame perturbations; actual initial amplitude majorants; compact-curl broad-class upgrade. These are located source producers, not currently demonstrated mathematical gaps. Any stronger theorem retaining explicit canonical budget identities for an arbitrary selected GeometryJoinedChoice would first require an export or independence argument; it is not needed by the inspected successor.

## Complexity and debt disposition

No complexity judgment here is based on line count. Domain conversions and dependent records are adapters only where exact supplier identities establish that role. Native estimates, graph transfer, pressure signs and fixed-loss bounds remain analytic work. Parallel constructors are at most duplication candidates until witness/domain equivalence is established. No supposed missing human theorem is presented as an actual mathematical gap in the delivered proofs.
