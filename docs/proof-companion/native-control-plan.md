# One actual NS native weighted-control producer: derivation plan

## Scope, provenance, and ownership

**Status:** documentation-only planning with selected source bodies inspected; no completed chapter, independent mathematical review, or new formal validation. Audience: a graduate PDE reader, without Lean knowledge. The next fanout is **READ-ONLY and returns mathematical derivations**, not edits or another architectural review.

**Frozen source baseline:** `26e896edbdbe1215c0d50ddba24b2b6453646f5f` (short `26e896e`). Observed HEAD matches it; initial working-tree status was clean. Worktree: `/home/velvet/worktrees/proof-native-control-20260912T185404Z`. All source references below inherit this SHA. The companion's historical `597692fa…` provenance in [PLAN](PLAN.md), [README](README.md), [SOURCE-MAP](SOURCE-MAP.md), and [VALIDATION](VALIDATION.md) is not silently upgraded or rewritten.

Read repository README, Comparator instructions, validation plan, the companion's authoring/interface/obligation material and relevant NS construction chapter. No `AGENTS.md` was found in the worktree/searched parent tree or checked ancestors. Build recipes in repository instructions are **not authorization to execute them** for this task.

Prior read-only reports, read completely, are leads rather than certification:

```text
/home/velvet/.pi/agent/thread-phase/artifacts/
  astra-original-proof-human-core-2026-09-12T18-46-13-810Z-5672f1ce/
    cross-examine-and-synthesize.md
    inspect-hard-steps-0-bafdc0de22-ns-native-correction-2693db6b2e00cebcfb8dbba5.md
```

Their unresolved native-energy/source-transfer question is this task's center. Their Volterra calculation alone does not settle it; qualitative weighted-class membership is not equivalent to the explicit numerical joint-jet theorem.

**One producer:** `NavierStokes.ScaledActualParticularControl.scaledControl`, instantiated by `NavierStokes.ActualParticularStageControls.selectedControl` and identified with the literal tangent by `selectedActualControl`. Follow one selected active pair and one arbitrary lattice copy through energy, transported source jets, both real solves, ambient synthesis, endpoint jets, and native pressure. Preserve family uniformity while working at that fixed pair.

**Stop at:** the local raw velocity/pressure estimates of `NavierStokes.ActualParticularStageControls.selected_raw_jets` for this producer, with the input residual identified from the actual cycle. Do not reconstruct the signed inverse, temporal/rank repair, finite-head signed matching, complete cutoff/Gaussian-defect localization, periodization, Cartesian residual losses, diagonalization, Euler, whole-space pressure recovery, or external Clay correspondence. They remain separate obligations. In particular this can narrow part of OBL-NSC-004, not close OBL-NSC-004–006 wholesale.

| Phase/owner | Owned output | Contract |
|---|---|---|
| This coordinator | `native-control-plan.md` only | Source map, notation, derivation boundaries and task contracts. |
| Next four derivation workers | Returned reports, captured by the harness outside the repository | Read-only; no chapter, integration, source, configuration, or research edits. |
| Later single `native-control-author` | Reserved `native-control.md`; targeted integration links/status in `02-ns-construction.md`, companion `README.md`, `SOURCE-MAP.md`, `VALIDATION.md` | Own continuous chapter and integration together; reconcile returned derivations before writing. Preserve historical baselines and existing IDs; use new `NSN-001…` IDs for substantive chapter assertions. Do not create placeholder links now. |
| Separate later reviewer | Returned mathematical/source/cold-reading findings | Author cannot self-certify closure; test acceptance below. |

Use the model requirement in the existing companion plan for delegated agents; do not silently substitute. No workers were launched in this planning pass. No original-checkout or A/B-worktree edits or investigation; no Lean/config/dependency changes, probes, builds, installs, commits, or pushes. No new filesystem-immutability or approval machinery is needed. Later edits to existing companion files follow its ordinary preservation/backup convention.

## Identity and notation contract

Keep the following distinctions throughout; do not inherit the source's overloaded `n`, `j`, `P`, `F`, and `Plane` without translation.

1. Fix the existing profile, budget `B` (write `B_bud`), threshold `N0`, initializer `choice B N0`, slot system and its positive radius `r0`, and the incoming cycle state. For the actual run retain its geometric-threshold hypothesis. No new profile, frame, or residual is selected to fit an estimate.
2. Stage-control labels are `ℓ=(c,L₀) : Fin 2 × CorrectionInitialization.ActualPrimary.Label B N0`. The sign/slot index `c` is **not** a real/imaginary index or Fourier harmonic. Its spatial slot is `PartitionedCovariance.signedLabel (PrimaryGeometryAssembly.label nominal L₀) c`.
3. Use `b` for the current physical band and `b_r=BaseChartJets.cellBand L₀` for the reference band (also the first coordinate of that spatial slot). Active means `1≤b` and `b_r∈CommonWindow.levels b`; hence the two indices differ by at most four. Write `e(q)=(ℓ,b)` for the source's arbitrary selection `e : ℕ → ActivePair B N0`. The enumeration index `q` is not the physical terminal coordinate, nor necessarily a physical band. `selectedConstruction` reindexes through `((),q)`; no surjectivity of `e` is required for `selectedControl`.
4. Fix a nonzero harmonic `j∈ℤ`; reserve `d` or `r` for derivative order. Fix an arbitrary copy `k∈Frequency=ℤ×ℤ`. The assembly's designated `copy := 0` does not restrict the producer's universal copy estimate to zero.
5. Solver parameter `p=(R,(T,Z))∈Parameter=ℝ×(ℝ×ℝ)`. Native point `x=((p,θ),Y)`, `Y∈ℝ×ℝ`. The selected slow argument is `χ(p,θ)=(R,(Z,T))`; the auxiliary angle is forgotten by the frame, and the transverse copy coordinate is also only an auxiliary parameter. Source jets still differentiate all these coordinates.
6. Put `Q=ChartScales.Q b`, `Qr=ChartScales.Q b_r`, and `R_a=Q^a/Qr^a`. With `A_h=1/2+h`, `D_h=1/2−h`, the physical changes are
   \[
   \psi(R,(T,Z))=(R_{1/2}R,(R_1T,R_{D_h}Z)),\quad
   \phi(R,(Z,T))=(R_{1/2}R,(R_{D_h}Z,R_1T)).
   \]
   Thus `χ∘(ψ,id_θ)=φ∘χ`. Clock `c_t=R_{1+h}>0`, velocity multiplier `a_v=R_{1/2+h}`, normal multiplier `c_N=(K_r/K)R_{1/2}>0`, with `K=carrier h b`, `K_r=carrier h b_r`. Both frequencies are `jK,jK_r`; `j` cancels in `c_N`, including negative harmonics. Zero clock shift is essential here. These multipliers are not variables differentiated within one copy.
7. Reference construction `F_*` is the reindexed actual phase construction, not a new abstract choice. Write `S0=F_*`'s domain scale `=ChartScales.S b_r`; `S_b=selectedStrip.slow q`; `G=S_b max(1,δ(p)⁻¹)≥S_b≥1`. Source proves `S0≤25 S_b`. Do not silently identify `S0` and `G`. Set `ε=selectedStrip.epsilon q`, `w=ε^α sqrt(ζ(p))`. For the actual residual `α=1/2+σ`; the incoming invariant is the irreducible source-class input, not an output-wave bound.
8. Let `L=F_*.L((),q)>0`, `L_c=L/c_t`, `s=c_t v` (reference time versus scaled native integration time). Current endpoint `t_c=(g.coordinates k Y).2` lies in `(0,L_c)` on the patch; integration estimates hold for **all** `v∈[0,L_c]`, including both ends.
9. Norms: native parameter and cover spaces use iterated product/max norms; the two-dimensional modal `PrimaryODE.State=MovingFrameODE.Plane` and three-dimensional real `ProblemStatement.Space` use Euclidean norms. The complex vector is `Fin 3 → ℂ`, with its function/sup norm, not a complex Euclidean space by fiat. Jets are real Fréchet multilinear operator norms on the specified full domain, not physical spacetime tensors. Coordinate swaps above are actual isometries; real/imaginary extraction, complexification, modal synthesis, and affine argument maps require their actual operator norms or explicit upper bounds. For example coordinatewise extraction into real Euclidean three-space costs at most `sqrt 3` from complex sup norm. Never assert all these norms coincide.

Source anchors for this dictionary: [stage controls](../../NavierStokes/ActualParticularStageControls.lean) — `NavierStokes.ActualParticularStageControls.spatialLabel`, `Active`, `selectedLabel`, `selectedBand`, `selectedConstruction`, `selectedStrip`, `selectedSlot`, `selectedChi`, `selectedPhi`, `selectedClock`, `selectedNormal`, `selectedGap`, `selectedGeometry`, `selectedPatch`; [physical scales](../../NavierStokes/PhysicalParticularWave.lean) — `NavierStokes.PhysicalParticularWave.parameterChange`, `velocityWeight`, `clockWeight`, `normalWeight`, `pressure_scaling`; [coordinate swap](../../NavierStokes/ActualSignedGeometry.lean) — `NavierStokes.ActualSignedGeometry.slowChange`, `swapParameter`; [scaled producer](../../NavierStokes/ScaledActualParticularControl.lean) — `NavierStokes.ScaledActualParticularControl.normalWeight_harmonic`, `actualSlot_tangent_eq`.

In lists after a fully qualified name, adjacent short names inherit that same namespace, not a namespace guessed from the filename. Later chapter citations should spell out full names beside each assertion; line ranges below are supplemental navigation only.

## Required worked chain (source bodies already located)

### A. Actual phase geometry must produce the energy inputs

The concrete route is:

- [initializer](../../NavierStokes/CorrectionInitialization.lean), around 3003–3017: `NavierStokes.CorrectionInitialization.ActualPrimary.choice`, `phases`;
- [geometry assembly](../../NavierStokes/PrimaryGeometryAssembly.lean), 282–342: `NavierStokes.PrimaryGeometryAssembly.family`, `construction`. These insert the prepared actual base fields, representative shear, unit transverse direction, unstable eigenpair and rounded frequency into `FamilyData`;
- [base/phase estimates](../../NavierStokes/BasePhaseGeometry.lean): `NavierStokes.BasePhaseGeometry.phase_errors_on_mesh`, `frame_errors_of_normal_close`, `damping_error_of_normal_close`; `NavierStokes.BasePhaseGeometry.FamilyData.phase_estimates`, `base_estimates`, `coordinate_errors`, `modal_errors`, `damping_error`, `construction` (710–1017 for the main production/assembly);
- [selected control helpers](../../NavierStokes/ActualParticularControl.lean): `NavierStokes.ActualParticularControl.selected_energy`, `transported_errors`, `transported_coefficient`, `transported_energy`, `scaled_selected_copy_energy` (last at 770–797).

The required expanded intermediate comparison is
\[
 N_0=B_0(s_0,K_0),\quad \|K_0\|=1,\quad
 \|N-N_0\|,\ \|\dot N\|\le C_{\rm phase}/S0,\quad
 |F-F_0|,\ \|g-g_0\|\le16M_0^2/S0.
\]
Here `B_0` is normal size, `s_0` the signed slope, `g_0` the frozen shear, and `M_0` the prepared base bound, **not** `F_*.M`. Show how mesh size, normalized base C1 error, reference C2 control and rounding give this normal comparison, and how the selected large-band threshold supplies `C_phase/S0≤B_0/2`. The actual mesh lemma uses distance `≤3/S0³` and applies the primitive phase estimate at `S0/2`, with `S0² ε_ref²≤1`, `S0²/k_car≤1`, `ε_ref S0²≤1`; here `ε_ref` and `k_car` are the reference-band small parameter and rounded carrier, not the selected-strip weight parameter or lattice copy. Its resulting constant is `normalConstant M=8*PhaseEstimates.phaseConstant(2M)`. Expand the radial-slope, normalized-tail, rotating-frame and inverse-normal denominators; no output coercivity premise is allowed.

Two concrete calculations to retain:

- Difference of squares gives `|ν0‖N‖²−ν0B_0²(1+s_0²)|≤4M_0(2A+5)δ_N` when `ν0≤4`, `|s_0|≤A`, and `‖N−N_0‖≤δ_N≤B_0/2`. Normalization `ν0 B_0²=λ/((1+u²)sqrt(1+u²))` identifies reference damping, not merely some positive damping.
- If the three coordinate errors are `a,b,c`, and the eigenvector profile is `H_e` with logarithmic derivative `r_e`, moving to `X=z_++z_-`, `Y=H_e(z_+−z_-)` gives errors
  \[
  e_{11}=(a+H_eb+c/H_e-r_e)/2,\quad e_{12}=(a-H_eb+c/H_e+r_e)/2,
  \]
  \[
  e_{21}=(a+H_eb-c/H_e+r_e)/2,\quad e_{22}=(a-H_eb-c/H_e-r_e)/2.
  \]
  Bounds on `H_e`, its inverse and `r_e` yield `|e_ab|≤C_*/S0`; dropping `r_e` loses an actual changing-basis term.

[Moving-frame algebra](../../NavierStokes/MovingFrameODE.lean) — `NavierStokes.MovingFrameODE.modal_equations_iff`, `modal_errors_le`, `modal_error_opNorm_le`, `modal_energy_le` (634–766); [modal dynamics](../../NavierStokes/PrimaryODE.lean) — `NavierStokes.PrimaryODE.FrameData.energy_bound` (346–364).

For `m(s)=u/2+us/L`, write
\[
 \Lambda(s)=\lambda/\sqrt{1+m(s)^2},\quad
 d_{\rm ref}(s)=\lambda(1+m(s)^2)/[(1+u^2)\sqrt{1+u^2}],\quad
 r(s)=\Lambda(s)-d_{\rm ref}(s).
\]
The actual matrix is `A_j=diag(Λ,−Λ)−j²ν_eff I+E_mat`. The entrywise bound gives **Euclidean** `‖E_mat‖op≤4C_*/S0`; `j≠0`, `ν_eff≥0` imply `j²ν_eff≥ν_eff≥d_ref−E_*/S0`. Consequently
\[
 \langle z,A_jz\rangle\le[r+(E_*+4C_*)/S0]|z|^2.
\]
Here `C_*=F_*.C`, `E_*=F_*.E`, produced above. This is an upper energy bound (often called coercivity in the reports), not a lower coercivity estimate. Its derivation is mandatory.

### B. Clock, copy rectangle, and envelope must move together

Define the exact envelope, not a Gaussian surrogate:
\[
 P(s)=\exp\!\left(\int_{L/2}^{s}r(\tau)\,d\tau\right),\qquad P_c(v)=P(c_tv).
\]
It is positive, `P_c'=(c_t r(c_tv))P_c`. It is Gaussian-comparable on the slot, not asserted to be exactly a quadratic Gaussian.

[Envelope](../../NavierStokes/PrimaryPulseBounds.lean) — `NavierStokes.PrimaryPulseBounds.referenceP`, `referenceP_hasDerivAt`; [rates](../../NavierStokes/ViscousPropagator.lean) — `NavierStokes.ViscousPropagator.referenceEigenvalue`, `referenceViscosity`; [Gaussian definition](../../NavierStokes/GaussianEnvelope.lean) — `NavierStokes.GaussianEnvelope.referenceRate`.

Transported frame algebra gives `A_c(v)=c_t A_j(φχp,c_tv)`. Normal scaling cancels out of this modal matrix, but **not** out of the normal or its motion: `N_c=c_N N`, `Ndot_c=c_N c_t Ndot`. Thus
\[
 \langle z,A_cz\rangle\le[c_t r(c_tv)+\mu_c]|z|^2,\quad
 \mu_c=c_t(E_*+4C_*)/S0.
\]
The slot bound, rather than an assumed propagator bound, gives
\[
 L\le M_*S0,\quad L_c\le M_*25 S_b/c_{\min},\quad
 e^{\mu_cL_c}=e^{(E_*+4C_*)L/S0}\le e^{(E_*+4C_*)M_*}.
\]
In generic `scaledControl`, replace 25 by its argument `B`. Its actual record constant is
`K_ctl=M_* B/clock.lower + exp((E_*+4C_*)M_*) + C_geo + 1`.
The clock cancels **inside the exponential**; the length/coordinate bounds still depend on uniform scale bounds. Energy is uniform over all nonzero `j`; coefficient-jet constants may depend on fixed `j` through `|j|+1`.

For `g=transportGeometry g_ref gap 0 c_t`, use the actual formulas
\[
 (\xi_k,t_k)=g.basis^{-1}(\mathrm{cover}^{g.gap}Y-g.center-\mathrm{lattice}(k)),
 \quad Y_k(v)=g.point(k,(\xi_k,v)).
\]
They give `g.coordinates k (Y_k(v))=(ξ_k,v)`. The reference closed rectangle is `[-r0,r0]×[0,L]`. Transport sends `(ξ,v)` to `(ξ,c_tv)` and refines the cover; its image remains in the reference native region. Prove injectivity of the torus quotient on that region from the **actual** slot geometry; do not assume source periodicity on a finer torus. Concretely, the reference basis is `ξ v_r + timeCoefficient(h,b_r) v v_t`, centered at `slotCenter−r0 v_t`, and `timeCoefficient*L=2r0`. The clock window has padding `min(r0,L)/16`; its outer image lies in the slot set with both slot coefficients bounded by `2r0`. `clockWindow_injective` restricts the fixed slot system's injectivity to that outer image, and `slotGeometry_separated` restricts again to the closed integration rectangle. Distinguish this core rectangle from the still larger smoothness/cutoff window.

[Copy geometry](../../NavierStokes/CommonCoverSolve.lean) — `NavierStokes.CommonCoverSolve.Geometry.coordinates`, `point`, `path`, `coordinates_path`; [separation](../../NavierStokes/ActualSignedGeometry.lean) — `NavierStokes.ActualSignedGeometry.slotGeometry_separated`; [transport](../../NavierStokes/ActualParticularControl.lean) — `NavierStokes.ActualParticularControl.separated_transport`; [scaled costs](../../NavierStokes/ScaledActualParticularControl.lean) — `NavierStokes.ScaledActualParticularControl.geometry_cost`, `slot_geometry_cost`, `patch_envelope`.

### C. The current residual must produce the flat-edge path jets

The incoming source is the three actual harmonic residual components, with current Gaussian input and per-label alias input zero. It is **not assumed equal to a transported old source**. `withSource` overwrites only the source; frame transport establishes the other tangent fields.

[Cycle input](../../NavierStokes/ActualParticularCycleData.lean) — `NavierStokes.ActualParticularCycleData.native_residual`, `native_source_class` (262–291) reindex the incoming invariant through `(ℓ.2,ℓ.1)` and use `ActualCycleParameters.particularState x`. This name denotes the state presented to the particular producer; do not confuse it with the later post-particular state used by the signed correction. [Stage controls](../../NavierStokes/ActualParticularStageControls.lean) — `NavierStokes.ActualParticularStageControls.assembly`, `currentSource`, `current_source_class`, `selected_source_class`, `selected_envelope_eq`, `selected_tangent_eq`.

The grouped weight is a sum of rectangle-supported copy envelopes:
\[
 W_g(Y)=\sum_{k'}\mathbf1_{[-r0,r0]\times[0,L_c]}(g.coordinates(k',Y))P_c(t_{k'}).
\]
Separation says two contributing copies coincide. For **every** integration time,
\[
 W_g(Y_k(v))=P_c(v),\qquad 0\le v\le L_c.
\]
This is exact equality including entry and exit; it is not extrapolation from a bound at the current endpoint. No smoothness of the indicator-defined grouped envelope is required.

[Envelope transfer](../../NavierStokes/WaveEnvelopeTransport.lean) — `NavierStokes.WaveEnvelopeTransport.copy_unique`, `copyEnvelope_eq_copy`, `copyEnvelope_path`; [source argument](../../NavierStokes/CommonCoverClass.lean) — `NavierStokes.CommonCoverClass.sourceArgument`, `sourceArgument_affine`, `norm_sourceLinear_le`.

The map `T_k(x,v)=(x.1,Y_k(v))` is affine, with derivative independent of the lattice translation. If the incoming N-jet bound has constant `B_f`, growth exponent `b_f`, and `argumentCost(g)≤A_geo S_b^a`, then the full affine chain rule yields, for `d≤N`,
\[
 \|D^d(f\circ T_k)(x,v)\|
 \le B_f A_{geo}^{N}G^{b_f+aN}\,[\epsilon^\alpha\sqrt\zeta]\,P_c(v).
\]
The slow parameter does not move on the path, so `δ,ζ,ε,G` are unchanged there. All derivatives of `f` are nevertheless included; **one does not differentiate the majorant**. Preserve the exact flat weight, not merely unweighted smoothness or unspecified polynomial losses.

[Jet production](../../NavierStokes/ActualParticularControl.lean) — `NavierStokes.ActualParticularControl.source_path_bounds` (195–245), `frame_forcingLinear_jets`, `frame_input_jets` (264–386), `transported_frame_jets`; [Leibniz bound](../../NavierStokes/WaveEnvelopeTransport.lean) — `NavierStokes.WaveEnvelopeTransport.clm_apply_jet_bound_on`.

For projected forcing `b_c=Π_frame(f∘T_k)`, polynomial projection jets and source jets give `2^N B_frame C_source G^(q_frame+m_source) w P_c`. The proof takes `B_frame=C_coeff+C_proj+C_syn0+C_syn1`, `q_frame` the sum of their four degrees, and one final constant `B_frame+2^N B_frame C_source`. Coefficient and synthesis jets have no `wP_c` factor; only forcing does. Explain the actual projection columns and inverse eigenvector, not an assumed projected-forcing bound. In `PrimaryODE.FrameData`, writing the frame directions as `K_f,N_f` and radial slope as `ρ`, the forcing coordinates are `f_X=−(f_0−ρ⟨K_f,tail f⟩)/(1+ρ²)`, `f_Y=−⟨N_f,tail f⟩`, and modal forcing `((f_X+f_Y/H_e)/2,(f_X−f_Y/H_e)/2)`. Thus the projection includes the cancellation sign and the moving-eigenbasis normalization.

### D. Existing joint-ODE consumer, ambient reconstruction, and pressure

Only **after A–C** use [ParticularWaveBounds](../../NavierStokes/ParticularWaveBounds.lean), `NavierStokes.ParticularWaveBounds.forced_joint_jet_bound` (36–150). For `y'=A_c y+b_c`, `y(0)=0`, and one enlarged `K≥1` absorbing the control/input constants, the literal bound is
\[
 \|D^d y(x,t_c)\|\le
 w\,[2^{N+1}\operatorname{rescaleConstant}(N,K)^3]^{d+1}
 G^{(m+2)(d+1)}P_c(t_c),\qquad d\le N.
\]
Explain the existing endpoint rescaling `v=τt_c`, `τ∈[0,1]`, with coefficients `t_c A_c(x,τt_c)` and forcing `t_c b_c(x,τt_c)`. The open tube around the compact integration segment supplies **joint** parameter/endpoint differentiability, including estimates at `t_c=0,L_c`. This is not inferred from fixed-time smoothness, nor is it physical extension through the NS singular time. The native patch itself has strict current-time inequalities.

Require a constant ledger identifying `rescaleConstant(N,K)=2^N K²+K+1` (`NavierStokes.PrimaryPulseBounds.rescaleConstant`), the extra rescaling powers and the subsequent affine current-endpoint composition. If a returned derivation only recovers downstream class membership, say so explicitly; it cannot claim the displayed numerical theorem.

For each real part of the source, ambient synthesis is the source's tangent map with coordinates `X=y_++y_-`, `Y=H_e(y_+−y_-)`. Both complex parts solve on the **same geometry and frame**. With ambient amplitude `a`, normal `N`, native derivative `Ndot`, retained action `K_act`, damping `d_j`, and current real source `f`, recover
\[
 a'=-K_{act}a+\frac{\langle N,K_{act}a\rangle-\langle Ndot,a\rangle}{|N|^2}N
       -d_ja-\Pi_N f,
\]
\[
 c_p=\frac{\langle N,K_{act}a\rangle-\langle Ndot,a\rangle+\langle N,f\rangle}{|N|^2},
 \quad \pi=i c_p/\omega,\quad \omega=j\,\mathrm{carrier}(h,b).
\]
Tangency follows from `(<N,a>)'=-d_j<N,a>` and zero entry. Check `iωNπ=−c_pN`; hence principal cancellation is `a'+K_act a+d_j a+iωNπ=−f`. This is native principal cancellation, not cancellation of all localized nonlinear errors.

Real/imaginary assembly is `a=a_R+i a_I`, `π=π_R+iπ_I`, where **each** `π_R,π_I` already contains the factor `i/ω`. They are pressures associated with real-source solves, not the real and imaginary values of the final pressure. Normal jets, nonzero lower bound, normal-motion/action jets and the inverse-frequency bound give pressure class exponent `α+1/2` from velocity exponent `α`. The selected range constants are explicitly `normal.lower*F_*.b≤‖N_c‖≤normal.upper*(F_*.M²+3F_*.M)`; they precede label/band/copy and have no inverse-clock loss. At `α=1/2+σ` these are `1/2+σ` and `1+σ`.

[Projection/pressure](../../NavierStokes/TangentProjection.lean) — `NavierStokes.TangentProjection.projectedRhs`, `pressureCoefficient`, `normal_projectedRhs`, `pressure_cancellation`, `complex_pressure_sign`; [wave coefficients](../../NavierStokes/ParticularWaveBounds.lean) — `NavierStokes.ParticularWaveBounds.copyPressureReal`, `copyPressure`, `realData`, `imagData`, `complexCopyVelocity`, `complexCopyPressure`, `pressureCoefficient_class`, `pressure_class`; [geometric jets](../../NavierStokes/ScaledParticularFrameJets.lean) — `NavierStokes.ScaledParticularFrameJets.native_geometry_jets`, `native_normal_bounds`; [actual application](../../NavierStokes/ActualParticularStageControls.lean) — `NavierStokes.ActualParticularStageControls.selected_inverse_frequency`, `selected_raw_jets` (822–882). [Control consumer](../../NavierStokes/ParticularCopyBounds.lean) — `NavierStokes.ParticularCopyBounds.UniformModalControl`, `uniform_coefficients_jets`.

## Next fanout: four read-only derivation contracts

All workers read this plan and the two prior reports, inspect enclosing definitions/section hypotheses and relevant proof bodies at the frozen baseline, and return prose mathematics plus source references. They may inspect further dependencies in this worktree; no writes, source probes, builds, dependency operations, original/A-B edits, or launches of further workers. Reports must distinguish **derived here**, **literal source identity**, **source-only primitive input**, and **unresolved**. A list of declarations or a proposed record is not a derivation.

| Task | Primary responsibility | Required returned deliverable |
|---|---|---|
| **N1 — selected geometry to energy** | A and energy portion of B | Derive normal and normal-motion comparisons from mesh/rounding/base inputs, coordinate errors, moving eigenbasis, reference damping, entrywise operator bound, all-harmonic sign and `scaled_selected_copy_energy`. Trace actual prepared construction into `F_*.C,E,M`; return explicit constant/denominator ledger and the exact irreducible upstream input. Reject stopping at `F_*.modal_errors`, `F_*.damping_error`, or an assumed energy inequality. |
| **N2 — actual copy and flat-edge source** | Identity dictionary, geometric B, C | Derive the actual slot separation and its transport, active-band/gap/clock/cost bounds, copy uniqueness, full-path envelope equality and full affine source jets. Identify current residual and its exponent, not a transported-reference source. Return a diagram of every coordinate map with domain/norm plus the uniform quantifier order and projected-forcing Leibniz calculation. |
| **N3 — joint jets, components, pressure** | D | Use A–C as explicitly pending handoffs, not purported proofs. Reconstruct existing rescaled ODE estimate and endpoint argument; compute synthesis/projection norm costs, both real controls, current-endpoint composition, pressure numerator/inverse-normal and inverse-frequency gain. Return exact numerical-bound recovery or explicitly delimited class-level recovery, with signs checked. |
| **N4 — independent source/identity challenge** | Cross-check A–D, especially actual instantiation | Independently derive the selected-label/physical-band/copy ledger, frame/tangent/source identity and clock cancellation; challenge N1–N3 interfaces without waiting for their reports. Check no output estimate is smuggled into the inputs, no inactive-band uniformity is claimed, no real/complex/product norm is silently identified, and every constant precedes the indices it controls. Return concrete derivations/counterchecks and unresolved dependencies, not a general verdict alone. |

Each report includes: exact baseline; inspected source bodies with fully qualified declarations and supplemental line ranges; standalone mathematical statements with quantifiers; displayed derivations; notation translation; constants and dependencies; imported/exported handoffs; remaining source-only input and its actual supplier; discrepancy list; and a short graduate-reader explanation. Reports are returned to the coordinator/harness; workers do not own repository output paths. The later author integrates them into one continuous argument rather than concatenating four reports.

## Irreducible input and acceptance contract

**Allowed external boundary for this one-producer exposition:** the fixed prepared outgoing/profile/base data and their primitive normalized base regularity/error and cone/representative hypotheses, the actual slot system, and the incoming cycle residual invariant/frequency coherence. Their existence/previous-cycle production is outside this chapter; cite the actual initializer and cycle suppliers. Elementary finite-dimensional calculus and the existing linear ODE existence/uniqueness framework may be named with exact hypotheses. The detailed producer must expand the mesh-to-normal, normal-to-modal, separation-to-path-weight and projection-jet mechanisms from these inputs. If a primitive estimate cannot be expanded, give its exact mathematical statement and supplier, and mark the corresponding human derivation conditional. No reassuring label turns such a gap into a proof.

**Not allowed as irreducible input:** `UniformModalControl`, a solved wave or pressure class, the desired coercivity/energy inequality, already-projected forcing jets, or an unexplained equality of the grouped envelope along earlier times. `PhaseConstruction` alone contains precisely the analytic fields at issue; citing that record without tracing their actual production is a failure of scope.

Acceptance requires all of the following:

- One identifiable active pair from the initializer and incoming cycle, with the same harmonic, copy, clocks, normal, source, envelope and patch in every formula. Arbitrary-copy and family-uniform claims must have their correct quantifier order. Do not impose active-window bounds on inactive bands.
- A worked derivation of `scaled_selected_copy_energy` **including the production** of the selected damping/modal errors, not only multiplication of an assumed inequality by the clock.
- Exact flat-edge factor `ε^α sqrt ζ`, exact envelope `P_c(v)`, and full jets along the entire integration rectangle. Show separation is produced for the actual slot and survives transport; no differentiation of an envelope majorant or fictitious native source periodicity.
- Explicit inequalities for clock cancellation, geometry cost, affine-jet losses, projection Leibniz factor, modal norm conversion and joint endpoint rescaling. Distinguish derivative order, harmonic and enumeration indices.
- Both complex components and the actual pressure sign/scaling/class gain, with inverse-normal and inverse-frequency hypotheses supplied for the same selected frame. Record the cost of norm changes, not just “equivalent norms.”
- Every load-bearing statement has a fully qualified source trail, declared inputs and evidence status. An unresolved input remains visibly conditional and propagates to dependent conclusions. No new singularity theorem, complete native cycle, optimal constant, source flaw, kernel check or Clay equivalence is claimed.
- The later cold reader can reproduce the matrix energy calculation and path-source-jet calculation from the chapter without opening Lean. A separate reviewer checks their hypotheses and actual instantiation. Only this narrow contribution may update the existing obligation ledger.

**Planning preservation check:** only this new plan was written. Local read-only checks found all 33 relative file links resolve, no trailing whitespace, and no `git diff --check` diagnostics. HEAD remains the frozen baseline; status contains only this untracked plan. These checks certify neither mathematics nor Lean elaboration. No formal validation was run.
