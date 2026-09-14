# Timing response — provisional draft pending adversarial audit

## Result and evidence boundary

**No sign, nonzero timing excitation, or asymptotic timing coefficient for actual selected force removal is established.** Combining and adjudicating the supplied drafts yields an exact improvement over derivative calibration: an amplitude–time variation cancels the explicit quadratic convection source, leaving a specific **diffusion/differentiated-force/seed correlation**. It does not estimate that correlation or show that the error is a time shift.

This is human mathematical analysis, not Lean validation. I fully read the [central obstacle](../CENTRAL-OBSTACLE.md), [final force-response report](../force-response/FINAL-REPORT.md), and [historical calculation](../force-response/CALCULATION.md). Historical (13)–(14) are excluded, not hypotheses. Fresh read-only HEAD checks matched research `1d16509bec4609ae418e64842e81b8b0ac07dcc7` and companion `6da0731071d900b7a1cf3fb9c009aa7cf6bc6c7f`.

Decisive source cross-checks:

- [WitnessFeasibility/Main.lean](../../../../Research/UnforcedRestart/Round3/WitnessFeasibility/Main.lean): one `selected` record supplies schedule, candidate, globally smooth forcing and terminal-origin jets; no force-removal theorem.
- [ProblemStatement.lean](../../../../NavierStokes/ProblemStatement.lean): viscosity-one residual, periodic velocity/pressure/force, and presingular smoothness.
- [CorrectionInitialization.lean](../../../../NavierStokes/CorrectionInitialization.lean):2962–2972 identifies the actual nominal witness. [EntranceAlignedBase.lean](../../../../NavierStokes/EntranceAlignedBase.lean):757–765 and [BaseResidual.lean](../../../../NavierStokes/BaseResidual.lean):59–86 supply axial coefficients and origin evaluation.
- [TimeLocalization.lean](../../../../NavierStokes/TimeLocalization.lean):27–31,68–87 confirms literal activation and late spacetime germ equality.
- [ActualParticularControl.lean](../../../../NavierStokes/ActualParticularControl.lean):43–54 controls auxiliary modal energy; [ActualPrimaryCovariance.lean](../../../../NavierStokes/ActualPrimaryCovariance.lean):382–398 is an unweighted native covariance identity, not an adjoint-weighted PDE estimate.
- Companion chapter 06 §1 was checked: its selected enlarged-chart bridge remains qualified, not repaired here.

The previous calculation's selected-germ transfer and mean cancellation are retained as accepted inputs, not independently exhaustively re-audited. No local flatness of the projected force is inferred from unprojected terminal jets.

## 1. What “timing” measures

Fix one sufficiently late restart \(t_0=1-\delta\), for all subsequent horizons. Write \(q_t=1-t\), \(A\in(1/2,1)\), \(j_*>0\), and use the complete selected fields:
\[
Y=U_t,\quad N=\mathbb P(U\cdot\nabla U),\quad
F=Y-\Delta U+N,
\]
\[
G=\Delta-\mathbb P(U\cdot\nabla\,\cdot+\,\cdot\,\cdot\nabla U),
\qquad L_U=\partial_t-G.
\]
Leray retains constants. For deletion error \(w=U-v\), with unforced \(v(t_0)=U(t_0)\),
\[
L_Uw=F+\mathbb P(w\cdot\nabla w).
\]
Its linear diagnostic is \(L_Uz=F\), \(z(t_0)=0\), not the nonlinear error itself.

The accepted axis identity gives \(Y_2(T,0)=Aj_*q_T^{-A-1}\). Set
\[
\kappa_T(v)=\frac{q_T^{A+1}}{Aj_*}v_2(0),\qquad
\alpha(T)=\kappa_Tz(T).
\]
Then \(\kappa_TY(T)=1\), but this is only an axial observation in infinitesimal-time units, not a spectral projection. Since
\[
J(T)=q_T^Az_2(T,0)=\frac{Aj_*}{q_T}\alpha(T),
\]
the selected linear margin \(|J|\le\rho j_*\) requires \(|\alpha|\le\rho q_T/A\). A nonzero limiting \(\alpha\) violates this linear criterion only.

On every finite slab, smooth coefficients yield parabolic evolution \(\Phi(T,s)\) on divergence-free periodic \(H^4\). Point evaluation is continuous there. The distributional dual
\[
\beta_T(s)=\Phi(T,s)^*\kappa_T\in H^{-4}
\]
satisfies \(-\partial_s\beta_T=G^*\beta_T\). Thus
\[
\alpha(T)=\int_{t_0}^T\langle\beta_T,F\rangle ds.
\]
There is no endpoint adjoint assumption. Because \(L_UY=F_t\),
\[
\langle\beta_T(s),Y(s)\rangle
=1-\int_s^T\langle\beta_T,F_t\rangle dr.
\]
Normalization holds only at the terminal time. Earlier renormalization could divide by zero and would generally spoil the homogeneous adjoint equation.

## 2. New actual-source cancellation

Put \(d=t-t_0\). Product differentiation gives
\[
L_U(U+dY)=F+N+Y+dF_t
=\boxed{2F+\Delta U+dF_t}.
\]
The explicit convection source cancels since \(N+Y=F+\Delta U\). Consequently,
\[
2z(T)=U(T)+d_TY(T)-\Phi(T,t_0)U(t_0)
-\int_{t_0}^T\Phi(T,s)[\Delta U+d_sF_t]ds.
\]
Pairing yields the substantive new reduction:
\[
\boxed{2\alpha(T)=T-t_0+q_T/A-\mathcal C_T},
\]
\[
\mathcal C_T=\langle\beta_T(t_0),U(t_0)\rangle
+\int_{t_0}^T\langle\beta_T,\Delta U+d_sF_t\rangle ds.
\]
At restart, \(\mathcal C_{t_0}=\delta/A\), exactly giving zero response. If a limit \(\mathcal C_T\to C_*\) were proved, then \(\alpha\to(\delta-C_*)/2\). The margin is exactly
\[
|T-t_0+q_T/A-\mathcal C_T|\le 2\rho q_T/A.
\]
Thus even \(C_*=\delta\) would not suffice: the rate of cancellation matters.

This is not a hidden symmetry. On a finite slab take
\[
V_\lambda(t)=\lambda U(t_0+\lambda d),\qquad
p_\lambda(t)=\lambda^2p(t_0+\lambda d).
\]
At fixed viscosity and unchanged torus,
\[
R(V_\lambda,p_\lambda)
=\lambda^2 f(t_0+\lambda d)
+\lambda(\lambda-1)\Delta U(t_0+\lambda d).
\]
Its derivative is the displayed identity. The viscosity defect and changed seed \(V_\lambda(t_0)=\lambda U(t_0)\) are essential. All selected cutoffs and repairs are differentiated; no boundary flux is discarded. Pressure gradients vanish only after projection; convection pressure remains in \(G\).

**No sign, limit, or endpoint bound for \(\mathcal C_T\) is supplied.** Smooth \(F_t\) does not control its growing adjoint pairing; diffusion and propagated seed may be singular. The explicit positive term is not evidence of excitation. This removes an explicit quadratic source, not convection from the propagator.

## 3. Full-field gauge: derivative inhomogeneity survives

A legitimate finite-time decomposition is
\[
\psi=Y/\|Y\|_{L^2}^2,\qquad a=\langle\psi,z\rangle,
\qquad r=z-aY,\quad\langle\psi,r\rangle=0.
\]
The nonzero axial value ensures a positive denominator. Because \(a\) depends only on time,
\[
L_U(aY)=a'Y+a(Y_t-GY)=\boxed{a'Y+aF_t}.
\]
Hence
\[
L_Ur=F-a'Y-aF_t,\qquad a(t_0)=0=r(t_0),
\]
\[
a'=\langle\psi,F\rangle-a\langle\psi,F_t\rangle
+\langle\psi'+G^*\psi,r\rangle.
\]
Orthogonality does not give an invariant complement. Neither \(Y\) nor this coordinate is a homogeneous neutral mode or canonical phase.

Pure timing \(r=0\) requires the full-space identity \(F=a'Y+aF_t\), including restart collinearity \(F(t_0)=a'(t_0)Y(t_0)\). Neither this identity nor its failure has been established. A necessary axial ODE gives the **conditional** bound \(|a|\le C\delta^{A+2}\); [CALCULATION.md](CALCULATION.md) derives it. It is not a bound on the actual response, whose remainder coupling is unknown.

## 4. Nonlinear clock and same datum

For \(W(t)=U(\theta(t))\), with sampled times presingular and unchanged viscosity,
\[
R(W,p\circ\theta)=f(\theta)+(\theta'-1)Y(\theta).
\]
For unforced \(v\), \(e=W-v\) obeys exactly
\[
L_We=F(\theta)+(\theta'-1)Y(\theta)
+\mathbb P(e\cdot\nabla e).
\]
Taking \(\theta(t_0)=t_0\) preserves zero comparison error. A constant shift instead leaves seed \(U(t_0+\varepsilon)-U(t_0)\), and is defined only while sampled times remain below one. Ramping it from zero introduces the clock-rate defect.

An exactly unforced pure clock must satisfy spatial collinearity
\[
F(\theta)=-(\theta'-1)Y(\theta).
\]
The axis forces \(\theta'-1=-F_2(\theta,0)/Y_2(\theta,0)=O(q_\theta^{A+1})\); that scalar choice must still cancel the entire field. Thus arbitrary clock absorption is invalid, but the particular selected pure-clock scheme is **not rigorously excluded** by the inspected contracts.

With our deletion sign, \(w\approx aY\) would mean \(v\approx U(t-a)\): positive constant \(a\) would represent delay, not advance, if such an approximation were justified. Once \(|a|\) is comparable to \(q_t\), first-order expansion ceases to be reliable. Large linear timing response can coexist with shifted growth, deformation, translation, or destructive error.

A sufficient conditional persistence target constructs one increasing clock reaching one at finite \(T_*\), with \(0<c\le\theta'\le C\), and
\[
\limsup_{t\uparrow T_*}(1-\theta(t))^A|e_2(t,0)|<j_*.
\]
Then axial growth transfers. This requires existence on the interval and a norm controlling nonlinear Duhamel feedback, not just evaluation. Global solvability may be assumed for contradiction; local existence alone does not supply that interval. A moving spatial center needs corresponding remainder control. No such theorem is obtained here.

Translations are torus symmetries when the force is translated too; their tangents satisfy \(L_U\partial_iU=\partial_iF\). Galilean boosts change the mean/datum. Amplitude alone is not a symmetry, and arbitrary continuous dilation changes the fixed torus. No enlarged modulation family is established as sufficient.

## 5. Two bounded follow-ups, not an implementation plan

1. **Selected correlation:** seek a signed asymptotic estimate for \(\mathcal C_T\), with rate if testing the margin. The exact source identity makes this a precise target; inspected modal energy and unweighted covariance provide no endpoint estimate. Feasibility beyond the algebra is currently unsupported. Stop rather than replace it with a projected generic contraction.
2. **Pure-clock compatibility test:** evaluate \(F-F_2(t,0)Y/Y_2(t,0)\) against one independent spatial functional. A certified nonzero value would exclude exact clock absorption, not general modulation. Smoothness and axial data alone do not decide it; a finite-time test avoids endpoint adjoints but requires additional actual-source information. Full nonlinear persistence is substantially harder and is not an automatic successor.

## Does this favor disproving A/B?

The original ambition already was a counterexample, not proof of universal regularity. One admissible unforced counterexample refutes the corresponding universal assertion. The negative unrestricted-operator obstruction uses \(F_t\) and a nonzero seed, not deletion source \(F\) with zero seed; it proves no unforced blowup. Existential versus universal quantifiers do not rank difficulty. Periodic B and whole-space A have separate scope; B does not automatically refute A. **Neither is resolved or newly favored by a persistence estimate here.**

## Draft handoff

Challenge the cancellation identity, seed/sign bookkeeping, conditional-only pure-timing bound, and distinction between axial response and nonlinear persistence. No final adversarial audit is claimed. Only these two new timing-response documents were written. Local Markdown link targets exist. Snapshot comparison found prior source/document files in both worktrees unchanged, no companion additions, and unchanged HEAD/index/ref state. Build/dependency directories were outside the snapshot. These checks are administrative, not mathematical validation. No Lean edits, builds, installations or Git writes were performed; the overview is below 2,200 words.
