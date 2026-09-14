# Producer/consumer mechanism map

Baseline and observed HEAD: `5fdcfe346d399f68f19a820526b59b5326f28939`. All citations below refer to Git objects at that pin; body quotes and line ranges are also in MAP.json. Live tracked source had no reported modifications; untracked REVIEW.md, SIMPLIFICATIONS.md and review-notes/ were left untouched. No builds, Lean probes, package operations, Comparator retries, commits, pushes or repository writes. No upstream manuscript/source substituted for retained producers.

This is source-body inspection and bounded human deduction, **not fresh kernel verification**. User-supplied existing authentic Nanoda+Lean gates on df3d891 and final doc-only 5fdcfe3 delta remain prior evidence. Published simplify/main are not treated as needing protection at superseded 26e896e. Research and four H3 additions are outside the delivered producer route examined here.

The historical 30-ID map is not reauthored. Nodes below are a new small mechanism graph; an inspected caller/callee body edge does not certify its entire dependency closure. `source-inspected` labels the cited local evidence, `unexpanded` labels analytic derivation debt, `unresolved` labels a specifically stronger claim not established here, and `human-derived` labels displayed budget arithmetic. No global minimality claim is made.

## NavierStokes: eight mechanisms

N1 → N2 → N3 → N4 → N5 → N6 → N7 → N8

Edges in this macrochain are **mathematical-use**, not mere imports. Exact supplied-object relations appear under each node; intermediate calls are not mislabeled direct calls. No import-only edge is used as proof evidence.

### N1 — Native cycle closes and retains coherence

- **Input:** Fix selected profile h>0, B,N0 with geometricThreshold≤N0, κ=10^-5. For current x and σ≥1/5, RunInvariant σ x.
- **Output:** RunInvariant (σ+1/10) (x.step fixedParameters commonContext); hence ∀J the literal initialized iterate has σJ=1/5+J/10.
- **Why needed here:** Native residual size without field/coefficient coherence cannot identify physical prefixes; periodicity also feeds the next particular source.
- **Equation/budget:** x[J+1]=step(x[J]); σ[J+1]=σ[J]+1/10.
- **Actual consumer relation:** Same B,N0 and fixedParameters at every J. RunInvariant has analytic, coherent, periodic fields; next_runInvariant_of_particular supplies these by analytic step, coherence step, periodicity step respectively.
- **Construction identity:** particularData uses actual_data R.analytic R.periodic; not a new favorable source. stepResult_of_particular passes staticData and concrete StepData to CorrectionAnalyticStep.step.
- **Complexity classification:** core analytic mechanism + construction-specific carrier/alias bookkeeping
- **Limit:** Complete signed/temporal/rank analytic StepData production not expanded here. Profile existence remains imported; these are exposition obligations, not identified proof gaps.
- **Producer citation:** `NavierStokes/ActualCyclePreservation.lean:768–776` `next_runInvariant`; body at line 773: `next_runInvariant_of_particular R hN hσ (particularData R hN hσ)`.
- **Consumer citation:** `NavierStokes/ActualCyclePreservation.lean:777–785` `state_runInvariant`; body at line 784: `exact next_runInvariant ih hN (ActualIterationLedger.sigma_admissible j)`.
- **Evidence:** source-inspected local bodies; analytic closure limited as above.

### N2 — Local particular control extends by zero germs, not global denominators

- **Input:** Current native residual all-jet class of exponent α; same-carrier and input-support invariants; j∈Z nonzero. Actual raw coefficient jets on controlPatch.
- **Output:** UniformWaveClass for literal strippedPotential at α+1/2, then current physical mode bounds and compatible glued particular fields.
- **Why needed here:** This is how the local selected solver enters physical estimates without asserting nonvanishing normal on every totalized point.
- **Equation/budget:** A_coeff=(i/ω) normalCoefficient(N,a); |ω^-1|≤sqrt(ε). Outside control cells the localized amplitude is zero as a germ.
- **Actual consumer relation:** raw_jets uses preserves_frequency hx; control cover is controlPatch OR actual amplitude zero germ. Common potential class enlarges local jets then uses common_amplitude_germ/common_zero_germs. Physical gluing uses same current state and compatible bands, not an unrelated copy-family representative.
- **Construction identity:** actual_potential_coefficient_class → potential_local_class → common_potential_class; original source extraction and transported frame of chapters 05–06 retained.
- **Complexity classification:** core inverse-carrier gain; construction-specific support cover; formalization adapter for local totalizations
- **Limit:** Current-mode pullback derivative proof is not fully reconstructed. Chapter 06 explicit numerical arrays still lack their selected full-domain bridge; no global selected certificate follows from this local-germ route.
- **Producer citation:** `NavierStokes/ActualCurrentParticularBounds.lean:150–179` `actual_potential_coefficient_class`; body at line 159: `have hr := ActualParticularStageControls.raw_jets x`.
- **Consumer citation:** `NavierStokes/GluedStageEstimates.lean:601–620` `current_potential_bound`; body at line 608: `(fun k hk => ActualCurrentParticularBounds.current_potential_mode_bound`.
- **Evidence:** source-inspected local bodies; analytic closure limited as above.

### N3 — Central boundary: five-field physical identity certificate

- **Input:** For all raw stages k: smooth A_k,D_k,P_k on t<1,q<qbig; StageRealizations on bands n≥Nr; ExteriorStages; 2Q_Nr≤qbig; CycleRepresentation of same iterate xJ.
- **Output:** ∀J PhysicalData B Nr xJ.state UJ pJ, where UJ=curl Σ[k≤J]A_k+Σ[k≤J]D_k and pJ=Σ[k≤J]P_k.
- **Why needed here:** The residual theorem estimates a native state. These exact local identities make that state the same physical prefix later subtracted from the diagonal.
- **Equation/budget:** q(forward z)<2Q_n≤2Q_Nr≤qbig; θbranch=θ+2πk ⇒ f(θbranch)=f(θ).
- **Actual consumer relation:** Nr=residualBand, not firstBand; prefix includes stage zero and J+1 summands. PhysicalData is PhysicalFields with U=ActualPolarCoverage.nativeDomain.
- **Construction identity:** Literal suppliers are stageRealizations, exteriorStages, stages_smooth, twice_residual_scale, cycle_representation of ActualCandidateConstruction; see full field expansion below.
- **Complexity classification:** formalization adapter with indispensable domain and periodicity identities
- **Limit:** Pointwise chart formulas for every native signed/mean constructor are not fully derived; actual suppliers are identified rather than their full analytic closure certified.
- **Producer citation:** `NavierStokes/ActualPhysicalPrefixFields.lean:438–474` `physicalFields_of_stages`; body at line 467: `exact H.velocity_germ hfloor hA J Hrep n hn ht hz`.
- **Consumer citation:** `NavierStokes/ActualCandidateAssembly.lean:974–984` `physicalData`; body at line 980: `ActualPhysicalPrefixFields.physicalFields_all (stageRealizations B N0 hN) (exteriorStages B N0 hN)`.
- **Evidence:** source-inspected local bodies; analytic closure limited as above.

### N4 — Native residual transfers through one comparable band and radial closure

- **Input:** Invariant σ x, unchanged base error, PhysicalData B N x.state u p, N≥4, N0 geometric. Native full residual bounds on lifted open strip.
- **Output:** ∀m, JetRate(originPast,q,R(u,p),m,h(1/2+σ)−fixedLoss(m)). For x=xJ weaken to gJ−fixedLoss(m), gJ=hJ/10.
- **Why needed here:** Fixed loss before J permits arbitrary target flatness later; radial-edge closure avoids losing estimates precisely at active-annulus boundaries.
- **Equation/budget:** q≤Q_n<2q; gain−βm−meanLoss(residualDegree,m)=gain−physicalLoss(h,β,m), β=2h.
- **Actual consumer relation:** SelectedGeometry has gap_le, annulus, in_domain, in_closure: smoothness on nativeDomain U; bounds on open strip V; chosen graph point in U∩closure(V). Exterior separately uses actual base germs.
- **Construction identity:** native_residual sums source oscillations + meanGoodResidual + excluded base/Gaussian/alias errors via fullResidual_decomposition. Base error preserved by every cycle; Gaussian and axis alias bounds usable at requested exponent.
- **Complexity classification:** core analytic fixed-loss transfer + construction-specific polar cover
- **Limit:** cartesianPull_jet_bound and native harmonic extraction still analytic next obligations; no assertion that mere smoothness gives quantitative bounds.
- **Producer citation:** `NavierStokes/ActualCycleResidualBounds.lean:909–949` `selected_residual_jet_bound`; body at line 938: `exact jet_bound_at_closure (hsmooth.contDiffAt (r.domain_open.mem_nhds hdom)) hcl k`.
- **Consumer citation:** `NavierStokes/ActualCycleResidualBounds.lean:1179–1197` `finite_residual_rates`; body at line 1191: `have he := (H J).residual_jetRate hGeom hN (actual_iterate_base_error p J) (d J) m`.
- **Evidence:** source-inspected local bodies; analytic closure limited as above.

### N5 — Raw and prefix estimates on the identical three sequences

- **Input:** Same RunData, mean input at firstBand N≥4, signed WaveData, coherence, ActualRepresentations, and PhysicalData at N+1.
- **Output:** StageEstimates h qbig A D P: ∀j≥1,m raw bound Cjm(1+|log q|)^pjm q^(gj−L(m)); ∀J,m background/residual rates with losses independent of J.
- **Why needed here:** Diagonal cutoffs require raw bounds; nonlinear subtraction also needs background bounds. Neither can be replaced by residual accuracy alone.
- **Equation/budget:** Lpotential=max(Lcurrent,LsignedMean); actual constructor simplifies max(L,L)=L.
- **Actual consumer relation:** Signed data remain native WaveData; particular is independently glued current-band field, then proved equal. N+1 residual floor relates to firstBand through actual construction, not a free extra domain.
- **Construction identity:** representations_of_signed_eqOn rewrites three initial and three positive component identities; initial direct field is actual initialized angular mean, not globally zero.
- **Complexity classification:** core norm/loss bookkeeping + adapters; max-self normalization is not new analysis
- **Limit:** Complete component bound closure unexpanded. StageEstimates contains no infinite residual hypothesis.
- **Producer citation:** `NavierStokes/GluedStageEstimates.lean:658–704` `actualStageEstimates`; body at line 669: `let E := stageEstimates_of_component_bounds R M hN W`.
- **Consumer citation:** `NavierStokes/ActualCandidateAssembly.lean:985–994` `estimates`; body at line 993: `(representations B N0 hN) (physicalData B N0 hN)`.
- **Evidence:** source-inspected local bodies; analytic closure limited as above.

### N6 — One diagonal produces residual flatness

- **Input:** StageEstimates for fixed raw sequences, 0<h<1/2, qbig>0; lower bound for a0 fixed.
- **Output:** ∃one integer doubling schedule a common to A,D,P; smooth presingular sums; ∀m,r≥0 residual JetRate m r, hence zero joint jets at (1,0).
- **Why needed here:** Same schedule and finite-prefix plateau let tail and finite residual estimates concern one subtraction, not three independently selected approximants.
- **Equation/budget:** |D^m[χ(a_jq)F_j]|≤2^-j q^(gj/2−Lcut(m)), m≤j+2. R(UJ+w,pJ+r)−R(UJ,pJ)=wt−Δw+∇r+UJ·∇w+w·∇UJ+w·∇w.
- **Actual consumer relation:** Fix m,r after a is selected, then choose J large. Laplacian needs m+2 velocity jets, curl another potential derivative. Constants/neighborhoods may depend on J,m,r. Raw stage zero is exempt from smallness.
- **Construction identity:** MixedDiagonalResidual.exists_physical_schedule_residual_zero selects once and weakens finite residual gain gJ to gJ/2; raw fields never reselected.
- **Complexity classification:** core diagonal analytic mechanism
- **Limit:** Six-term calculation already explained in chapter 03; new evidence here is literal constructor connection N3–N5, not a new flatness theorem.
- **Producer citation:** `NavierStokes/MixedCandidateAssembly.lean:67–101` `StageEstimates.exists_schedule`; body at line 90: `E.gain_zero E.gain_pos E.gain_mono E.gain_top E.finite_background E.finite_residual lower`.
- **Consumer citation:** `NavierStokes/GermCandidateAssembly.lean:180–282` `exists_candidate_witness_of_finite_stages`; body at line 212: `E.exists_schedule F.data.h_pos F.data.h_lt_half hqbig 1`.
- **Evidence:** source-inspected local bodies; analytic closure limited as above.

### N7 — Same sums give localized smooth force and both candidates

- **Input:** Same diagonal, local angular data, one shrinking-support constant, axis-zero correction germs, off-plane raw extensions on endpointRoot<qbig, anchored base extension.
- **Output:** Compact activated velocity/pressure and smooth compact-space force; periodic lift candidate from same sums. Force equals activated residual for 0≤t<1 and vanishes for t≥2.
- **Why needed here:** Flat origin jets alone cannot extend the residual at every spatial endpoint or preserve compact force support; anchored potential matters after cutting off.
- **Equation/budget:** curl(ρA)=ρ curl A+∇ρ×A; f= smoothExtension(traced actual residual), not an assumed force.
- **Actual consumer relation:** GermCandidateAssembly passes ASum,BSum,PSum to mixed_exists_force_with_consequences and exists_compact_candidate. ea,eb,ep extend these exact sums; force traces are actual derivative limits.
- **Construction identity:** selected_witness specializes B,N0; existential schedule extracted for periodic and compact routes. Separate force outputs in Witness are not asserted definitionally identical.
- **Complexity classification:** core extension/locality + construction-specific gauge and angular support
- **Limit:** Taylor–Borel gluing and raw endpoint model production remain human exposition debt; no new full kernel verification.
- **Producer citation:** `NavierStokes/CandidateFromLimits.lean:83–86` `force`; body at line 84: `SpacetimeGluing.smoothExtension 1 (tracedResidual u p L)`.
- **Consumer citation:** `NavierStokes/ActualCandidateAssembly.lean:1053–1069` `witness`; body at line 1065: `w.h3_blowup, w.forcing_decay, w.boundary_jets, w.compact_forcing,`.
- **Evidence:** source-inspected local bodies; analytic closure limited as above.

### N8 — Small outer route to exact forced delivered statements

- **Input:** Periodic CandidateProperties or compact R3 Properties extracted from selected_witness; fixed ν>0.
- **Output:** NavierStokes.Comparator.navier_stokes_breakdown_periodic and navier_stokes_breakdown_R3, with zero datum and rescaled smooth forcing.
- **Why needed here:** Uniqueness on shorter slabs identifies a global competitor; compact continuity through one contradicts candidate speed. Whole-space bridge additionally uses finite energy.
- **Equation/budget:** uν(t,x)=νu(νt,x), pν=ν²p(νt,x), fν=ν²f(νt,x).
- **Actual consumer relation:** Periodic: ComparatorTheorem.navier_stokes_breakdown_periodic calls selected_candidate then option_D_of_candidate. ComparatorSolution forwards exact theorem names. Whole-space competitor timewise L2 plus one global energy bound; periodic velocity AND scalar pressure periodic.
- **Construction identity:** No H3 addition reroutes these bodies. No Research producer used. Compact and periodic candidates extracted from original witness route.
- **Complexity classification:** formalization class/scaling adapter plus standard comparison mechanism
- **Limit:** Full pressure-recovery/class-bridge dependency audit not repeated. Existing four-target Nanoda+Lean evidence on df3d891 with final doc-only 5fdcfe3 delta is user-supplied prior evidence, not rerun.
- **Producer citation:** `NavierStokes/R3ActualCandidate.lean:18–24` `selected_compact_candidate`; body at line 22: `exact ⟨_, _, compactForcing, hcompact⟩`.
- **Consumer citation:** `NavierStokes/ComparatorR3Theorem.lean:53–61` `navier_stokes_breakdown_R3`; body at line 59: `exact option_C_of_candidate h ν hν`.
- **Evidence:** source-inspected local bodies; analytic closure limited as above.

## Expanded central boundary: `PhysicalData` is identity-only

Pinned definition: `ActualCycleResidualBounds.lean:1009–1032`, abbreviation at 1137. All five fields are consumed; none is incidental to the residual route. It is **not** a record of physical bounds.

| Complete field | Literal supplier in `physicalFields_of_stages` (ActualPhysicalPrefixFields.lean) | Actual use |
|---|---|---|
| velocity_smooth: for n≥Nr and cylindrical z in preterminal graph source, C² at forward z | `uncutVelocity_smooth` from hA,hD, using `source_sublevel` | `Invariant.stateRealization` passes to physical residual identity |
| pressure_differentiable: same domain, differentiability at forward z | finite sum of hP, `source_sublevel` | same `stateRealization` |
| velocity_germ: u∘forward equals frame(θ) times scaled base+increment in a neighborhood | `StageRealizations.velocity_germ`, then `velocity_prefix` and `velocity_pullback_germ` | residual derivatives transferred by chart-identity germ |
| pressure_germ: pressure pullback equals scaled actual base pressure+totalPressureIncrement locally | `StageRealizations.pressure_germ`, `pressure_prefix`, `pressure_pullback_germ` | same residual identity, with actual pressure |
| exterior: u,p equal selected base for t<1,q<Q_Nr outside active annulus | `HE.prefix_exterior` | `PhysicalFields.exterior_germs`, then exterior branch of `selected_residual_jetRate` |

No claim of unused nested fields follows from this table. `StageRealizations` has exactly potential/direct/pressure stagewise EqOn fields; `ExteriorStages` has exactly potential_zero, potential_succ, direct_zero (all k), pressure_zero, pressure_succ. Their full definitions and consumers were read. Direct zero here means **exterior zero**, including stage zero, not globally zero initialized direct field.

### Literal suppliers one layer further down

`ActualCandidateAssembly.stageRealizations` (954 onward) splits potential/pressure k=0 versus k=j+1. Zeroth suppliers add gauged base, initial primary wave and initialized stream/pressure. Positive suppliers add current particular, signed and mean pieces. Direct uses `direct_on_chart(meanCycleInput...)` at every k. `firstBand_le_residualBand` converts the band requirement. In `physicalData` (974 onward), all raw fields, qbig, parameterSequence, stage realization and cycle representation are from the same B,N0.

For the particular part, `particularPotential_on_chart` (628 onward) first uses `ActualValidBandWaves.potential_curl_germ` on the actual compatible glued field, then `ActualCurrentParticularAssembly.localPotential_curl_eqOn`. For the signed part, `signedPotential_on_chart` (861 onward) calls `ActualSignedPhysicalCoherence.cyclePotential_curl` with the **post-particular** primitive/reconstructed pressure, post-particular coherence, incoming labels, and the amplitude bound from `CurrentSignedCurl.amplitudeBound_of_mean`. These are different constructor obligations, not interchangeable WaveData bundles.

`exteriorStages` (603 onward) uses `initialPotential_stage`, `positive_stage`, `direct_stage`, `initialPressure_stage`. `positive_stage` is addition of actual particular, signed and stream/mean-pressure exterior germs. `PhysicalStage.exterior` also separately produces shrinking support and axis-zero germs; this existing shared predicate is already a successful simplification, not new duplication to eliminate.

### Worked domain/identity calculation: the honest extra residual band

Let N=firstBand and Nr=N+1, qbig=Q_N in this assembly. For a point in the residual chart, the normalized carrier supplies q/Q_n<2, hence

    q<2 Q_n≤2 Q_Nr≤qbig.

The strict first inequality gives an open physical neighborhood. Thus stage smoothness and stagewise EqOn, only known on q<qbig, really apply there. Replacing Nr by N would only give q<2qbig, insufficient. This is a construction-domain requirement, not a norm-loss estimate. The theorem accepts the more general contract `2Q_Nr≤qbig`.

A polar branch gives θ'=θ+2πk, not θ'=θ. `polarInput_cos_sin` derives equal sine/cosine from inverse-chart reconstruction; `periodic_eq_of_cos_sin` obtains integer k and invokes periodicity. `represented_oscillation_periodic` and `represented_pressure_periodic` derive that periodicity from the **stored harmonic representation**, then velocityTZ/pressureTZ preserve it. Since frames also agree under 2πk, the resulting physical germs are equal. This is why a native representation invariant is needed even after coefficient bounds are known.

Finally UJ=curl(sum k<J+1 A_k)+sum k<J+1 D_k matches xJ, not x[J+1]. Exterior finite sums reduce to A_base and p_base. Curl sees a germ, then `finalPotential_sameCurl` identifies velocity. No derivative of a globally arbitrary totalized raw field is justified outside the open domain.

### Next analytic obligation exposed by the identity boundary

`Invariant.native_residual` (ActualCycleResidualBounds.lean:839 onward) is independent quantitative work. It assembles the literal source sum, meanGoodResidual and all excluded errors. `selected_residual_jet_bound` selects n with q≤Q_n<2q, puts the graph point in nativeDomain **and closure of the bounded strip**, then uses smoothness to pass native jet estimates to that closure. Only then does `cartesianPull_jet_bound` transfer to physical jets with β=2h. Outside the active set, the base exterior residual is used instead. A future reconstruction must derive that pullback estimate and extraction/weighted-sum bounds, not repackage PhysicalData again.

## What is new relative to chapters 05–07

Not the modal energy calculation, reciprocal arrays, pulse interpretation or six-term flatness algebra. New inspected evidence is: local controlPatch-to-common potential transfer by a zero-germ alternative; all five PhysicalData suppliers and uses; angular branch periodicity from actual stored representation; the extra residual-band domain budget; separate U/closure(V) roles in residual transfer; and the literal calls connecting these identities to fixed-loss StageEstimates and one schedule.

The selected full-domain numerical-array assertion of chapter 06 remains unresolved as an export/exposition strengthening, not disproved and not a demonstrated formal theorem gap. Its eventual upstream construction cannot identify a classically selected preparation with the exhibited one. N2's local support alternative does not silently close that assertion.

## Complexity and debt disposition

No complexity judgment here is based on line count. Domain conversions and dependent records are adapters only where exact supplier identities establish that role. Native estimates, graph transfer, pressure signs and fixed-loss bounds remain analytic work. Parallel constructors are at most duplication candidates until witness/domain equivalence is established. No supposed missing human theorem is presented as an actual mathematical gap in the delivered proofs.
