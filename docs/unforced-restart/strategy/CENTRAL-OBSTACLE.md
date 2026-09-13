# Central obstacle: deleting the selected force

## Executive overview

The construction prescribes a growing viscous velocity, preserves its axial growth through corrections, and defines a smooth force equal to the remaining equation residual. This does **not** show that late forcing dynamically sustains the singular core. Deleting the force changes the initial-value problem unless the force can be absorbed into periodic pressure; whether growth then survives is unknown.

**No unforced route is presently supported as demonstrably feasible.** Fixed-restart shadowing is the cleanest diagnostic question, not an established promising method. The inspected viscous estimates concern auxiliary correction systems, not the complete pressure-coupled evolution of an error after force deletion. Exact residual removal would instead require a new fixed-domain convergence argument.

The principal source-understanding limitation remains prominent: we can reconstruct installed axis growth, viscous modal balance and stress matching, but not a complete causal account of the selected profile's physical advection–pressure–diffusion balance or the final force's growth-relevant contribution. No strategy follows merely from those partial reconstructions.

Recommend only a selected-data formula and one necessary linear-response estimate—or a precisely identified missing full-PDE bound—for the signed axial response of the **complete projected force**, after one fixed restart. Do not begin wholesale residual reconstruction, nonlinear implementation or another open-ended curl campaign. A scalar success would still leave nonlinear closure unresolved.

## Scope and evidence

This is source analysis and mathematical proposal, **not new Lean validation**. Targeted body inspection reconfirmed the mechanisms below at HEAD `1d16509bec4609ae418e64842e81b8b0ac07dcc7`; the companion is at `6da0731`. No builds or proof checks were run. Throughout, \(U,p,f\) mean the velocity, pressure and forcing of [WitnessFeasibility.selected](../../../Research/UnforcedRestart/Round3/WitnessFeasibility/Main.lean), not independently chosen witnesses.

The substantive new work here is correction of inference and narrowing of the diagnostic, not discovery of a new source theorem. Upstream finite-profile/modulation production and oriented edge certificates remain source-trusted rather than independently reconstructed.

## 1. Understood mechanism and the force's exact role

### Installed growth, not an autonomous cascade

[BaseResidual.baseVelocity_at_origin](../../../NavierStokes/BaseResidual.lean) evaluates the curl-defined velocity and eliminates positive-order axial coefficients. The resulting base value is
\[
U_{\rm base}(t,0)=j_*(1-t)^{-A}e_2,
\qquad A=\tfrac12+h,\quad 0<h<\tfrac12,\quad j_*>0.
\]
The similarity relation \(q-z^2q^{2h}=1-t\) gives \(q=1-t\) at the origin. Transverse and axial core scales are respectively \((1-t)^{1/2}\) and \((1-t)^{1/2-h}\).

[GermCandidateAssembly.origin_eventually_base](../../../NavierStokes/GermCandidateAssembly.lean) preserves the base through axis-zero potential germs, direct angular vanishing and the eventual plateau of the zeroth scale cutoff. This is a schedule-dependent preservation argument, not an autonomous growth estimate. The selected record exports candidate blowup; the exact quantitative axis identity needed below must still be transferred explicitly through its stage definitions, localization and selected schedule. Correction number measures residual accuracy, not physical time or a demonstrated energy cascade.

### Viscosity is substantive

[GrowingMode.scaled_growing_mode_bounds](../../../NavierStokes/GrowingMode.lean) proves positivity, a narrow cone and two-sided envelope bounds **assuming** a prescribed modal ODE, coefficient errors and reference envelope. Its reference rate is shear growth minus viscous damping. The reference pulse grows then damps, rather than amplifying indefinitely.

[ActualParticularControl.selected_energy](../../../NavierStokes/ActualParticularControl.lean) derives an upper quadratic-form bound from actual frame energy and damping/modal errors. Extra squared-harmonic damping is dissipative for every nonzero harmonic. These are genuine viscous controls. They do not control the full physical NS linearization. Native carrier scaling retains order-one viscosity times squared frequency; transverse diffusion and time differentiation also balance at slow-core scaling. An Euler interpretation discards an essential term.

[ActualPrimaryCovariance.viewSum_covariance_factor](../../../NavierStokes/ActualPrimaryCovariance.lean) identifies averaged wave covariance with partition factor times physical leading stress. This is engineered stress matching, not a positive physical energy-transfer law.

### Residual accounting is not causal necessity

With viscosity normalized to one,
\[
R(U,p)=\partial_tU+U\cdot\nabla U-\Delta U+\nabla p=f.
\]
The force equals the constructed trajectory's residual. It is **not proved to consist only of activation and outer-localization defects**, nor proved necessarily to sustain the singular core. Correction formulas retain phase/material errors, nonlinear interactions, mean and pressure repairs, aliases and cutoff derivatives; “retained” does not certify each contribution nonzero. Cutting potentials preserves divergence freedom, not the NS equation. Activation introduces switch-derivative and convection-mismatch terms; their disappearance after activation does not remove the underlying residual.

[MixedDiagonalResidual.residual_jetRate](../../../NavierStokes/MixedDiagonalResidual.lean) compares with finite uncut stages chosen according to the requested order, under \(q\to0\). Constants and neighborhoods may depend on that order. Arbitrary local residual flatness is not zero residual on a fixed presingular domain. Selected terminal-origin jets vanish; this does not assert a zero whole-cell terminal trace. Positive cumulative startup forcing work likewise says nothing decisive about necessary late work for concentration.

[SelectedExterior.selected_exterior_germs](../../../Research/UnforcedRestart/Round5/SelectedExterior.lean) literally retains stage zero's scale cutoff. Importing an uncut exterior identity needs additional plateau hypotheses. Even a forcing-free patch cannot determine the restarted global solution: pressure is nonlocal and diffusion crosses patch boundaries.

## 2. Two barriers, and unresolved source understanding

**Barrier 1: full autonomous comparison.** Deleting \(f\) at one late \(t_0\) gives an unforced IVP with \(v(t_0)=U(t_0)\). Auxiliary mode bounds neither estimate its complete deletion source under the full propagator nor close nonlinear feedback. No inspected embedding connects those operators with controlled pressure, localization and remainder terms.

For definiteness the proposed eventual shadowing argument targets a **contradiction conditional on global smooth regularity**: assume the unforced comparator is globally smooth, then seek transferred growth toward 1. Local existence from smooth data alone does not supply this comparator on every horizon. A constructive maximal-lifespan formulation would instead have to handle earlier breakdown or establish comparison and sufficient continuation control. Point evaluation transfers growth where the solution exists; it is not a continuation or nonlinear closure norm.

**Barrier 2, if reconstructing instead:** exact residual removal requires summable corrections and residual convergence on one common domain, with compatible restart trace and nonlinear/pressure closure. Diagonal flatness is no such contraction theorem. There is no demonstrated feasible reconstruction route either.

**Selection versus numerical provenance.** [Prepared](../../../NavierStokes/PrimaryGeometryAssembly.lean) exports low-order base estimates, all-order polynomial jets, radius, cone and large-band conditions. These remain usable. It does not automatically export every enlarged-chart range or threshold domination used in the companion's explicit arrays. [Companion chapter 06](../../../../proof-native-control-20260912T185404Z/docs/proof-companion/06-primitive-derivative-bounds.md), §1, explicitly qualifies that bridge. A classical choice is not definitionally the internally exhibited witness; silently raising its threshold or replacing its constants is invalid.

This gap limits the explicit numerical reconstruction, not necessarily the qualitative diagnostic. Symbolic certificates may suffice; eventual numerical bounds might be supplemented by separate finite-band estimates. That is a possible repair, not an established transfer. The complete selected physical balance and its signed force response remain unreconstructed even if this domain issue is repaired.

## 3. Review dispositions and A/B distance

- **Causality corrected:** residual equality is exact accounting, not demonstrated late-force necessity.
- **Different IVP qualified:** on the torus same-velocity pressure absorption is exactly \(\mathbb Pf=0\) throughout the slab, where Leray projection retains constant divergence-free modes. Curl-free plus zero spatial mean suffices for a smooth periodic gradient; curl-free alone does not. Nonzero local curl or nonzero mean can reject absorption. One terminating curl/mean test is legitimate, but not a persistence strategy.
- **Smallness quantifiers corrected:** late restart is a possible parameter. A shorter forcing interval competes with increasingly singular coefficients; no favorable balance is known. The target is \(\exists t_0<1\;\exists\rho\in(0,1)\;\forall t\in(t_0,1)\), with one datum and evolution, not a new restart for each horizon.
- **Cancellation and lifespan corrected:** a large upper bound proves no large response. A large component can defeat a triangle-inequality certificate, not necessarily the total margin. Growth transfer is separate from continuation and nonlinear closure.
- **Domain concern proportioned:** exported jets survive; explicit numerical provenance remains conditional.

**B (periodic):** smooth nonzero restart data and the forced equation are available; full linear response and nonlinear closure are not. **A (whole space):** additionally needs coherent decaying/finite-energy data and justified global pressure, flux and comparison bounds. A periodic comparator is not finite-energy whole-space data. Neither A nor B is presently credibly feasible; B is the more directly posed diagnostic. Restarting from time zero only recovers zero under smooth unforced uniqueness.

## 4. At most three candidate tools

| Tool | Exact useful output now | Feasibility evidence and limit |
|---|---|---|
| Selected residual/covariance accounting | A coherent complete forcing source and exact averaged leading-stress identity | Direct source identities; no signed response estimate or smallness theorem |
| Viscous frame/envelope estimates | Conditional modal lower/envelope bounds and actual-frame upper energy bounds, retaining harmonic damping | Proven for auxiliary systems; no controlled embedding into the full NS propagator |
| Weighted particular inverse and prepared jet bounds | Weighted correction control for construction sources, with certified polynomial coefficient jets | Existing native inverse machinery suggests a reconstruction language, not fixed-domain contraction; explicit numerical use needs the domain bridge |

These tools are relevant, not demonstrated solutions. Do not interpret operator analogies as evidence that endpoint response estimation is tractable.

## 5. Next bounded experiment: one signed total-response diagnostic

**Proposal only; not launched.** Fix one admissible late \(t_0\), after activation and the transferred axis plateau. First deliver the selected-data formula and dependency audit below, then require one actual estimate for its pairing—or precisely name the missing full-PDE estimate—before expanding every residual component or primitive constant.

Let \(\mathbb P\) retain the torus zero mode and define
\[
L_Uz=\partial_tz-\Delta z+
\mathbb P(U\cdot\nabla z+z\cdot\nabla U),\qquad
L_Uz=\mathbb Pf,\quad z(t_0)=0.
\]
The sign convention is \(w=U-v\): exactly
\(L_Uw=\mathbb Pf+\mathbb P(w\cdot\nabla w)\).
Thus \(z\) is its linear response, not the full error.

After explicitly transferring \(U(t,0)=j_*(1-t)^{-A}e_2\), target
\[
\mathcal J(T)=\ell_T(z(T)),\qquad
\ell_T(a)=(1-T)^Ae_2\cdot a(0),
\]
\[
\mathcal J(T)=\int_{t_0}^{T}
\left\langle\Phi_U(T,s)^*[(1-T)^Ae_2\delta_0],
\mathbb Pf(s)\right\rangle ds,\qquad T<1.
\]
Here \(\Phi_U\) is the **full** homogeneous propagator of \(L_U\). Justify finite-horizon duality, for example on divergence-free periodic \(H^m\), \(m>3/2\), whose dual contains point evaluation restricted to that subspace. Establish evolution and Duhamel pairing in those spaces; do not treat \(\delta_0\) as an \(L^2\) functional. Smooth finite-horizon coefficients do not furnish uniform endpoint constants.

Keep the complete residual, including cutoffs and mean, in the formula. Separate exported smoothness/jets and exact identities from new propagator assumptions. Identify the first constant uncontrolled as \(T\uparrow1\). Split at one fixed \(\tau\in(t_0,1)\), for \(T>\tau\): the early term is \(\ell_T\Phi_U(T,\tau)z(\tau)\). Endpoint flatness cannot erase this seeded error, and addresses the late contribution only with adequate spatial/propagator bounds.

**Acceptable outcomes:** (i) a certified total margin \(\sup_{t_0<T<1}|\mathcal J(T)|\le\rho j_*\), \(\rho<1\); (ii) a certified violation of that specified margin; or (iii) one precise missing full-PDE pairing bound, listing selected source/axis dependencies and any genuinely needed domain transfer.

A violation requires a lower bound on the total absolute signed response, or one component lower bound minus upper bounds for all other components exceeding the margin. Large unsigned upper bounds merely fail a certificate. Even actual linear-margin failure rejects this perturbative criterion, not every nonlinear shadowing mechanism. Conversely, scalar success needs a further space controlling both observation and quadratic Duhamel feedback before implying nonlinear promise.

**Stop** when only native-mode or unsigned global energy estimates are available, or the first necessary endpoint constant lacks control. Do not substitute them for the required pairing. Do not yet launch nonlinear formalization, whole-space transplantation, exhaustive local curl bookkeeping or fixed-domain exact-cancellation iteration.

**Decision:** interpretation has isolated the correct source, operator and quantifiers. Neither the inspected tools nor this diagnostic yet establishes a feasible way to control autonomous persistence.
