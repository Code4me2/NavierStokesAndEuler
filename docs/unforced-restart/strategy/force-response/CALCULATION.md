# Selected force response: completed bounded calculation

**Outcome (iii).** Exact selected-axis transfer, zero-mean cancellation, a signed full-PDE identity, and axial damping are available. The complete *direct projected-source* contribution is uniformly small after late restart. One diffusion–transport–response-pressure pairing remains uncontrolled. Neither a total margin nor its violation follows.

**Evidence/status.** Source interpretation was independently checked against the decisive definitions and proof bodies at main HEAD `1d16509bec4609ae418e64842e81b8b0ac07dcc7`; companion HEAD `6da0731071d900b7a1cf3fb9c009aa7cf6bc6c7f`. The central obstacle and companion chapters 05/06 were read fully. Links below identify inspected suppliers, not new formal theorems. All PDE arguments here are **human analytic derivations; new formal results: none**. No builds or Lean checks were run. Only this file and `REPORT-DRAFT.md` are added; prior evidence is not rewritten.

## 1. Resolve the selected-field interface

Use only [WitnessFeasibility.selected](../../../../Research/UnforcedRestart/Round3/WitnessFeasibility/Main.lean). Its schedule is \(a\); budget and initialization threshold remain fixed. In [CorrectionInitialization](../../../../NavierStokes/CorrectionInitialization.lean), `ActualPrimary` abbreviates the actual profile's outgoing data, nominal witness, certificate and modulation. Write
\[
 W=\texttt{ActualPrimary.nominal},\quad j_*=W.\mathrm{axis}.j>0,
 \quad A=\tfrac12+h,\quad D=\tfrac12-h,\quad 0<h<\tfrac12.
\]
This identifies the nominal witness used by `ActualCandidateAssembly`; it is not a second profile choice. Distinguish the outer schedule \(a\) from the base's internal `FinalSlowBase.scales`.

Choose a fixed terminal window \(0<\delta_*<\min\{1/4,q_{\rm big},(2a(0))^{-1}\}\). Eventually choose **one** \(0<\delta\le\delta_*\), set \(t_0=1-\delta\), and keep that restart for every \(T\in(t_0,1)\). Write \(q_t=1-t\).

The selected record exports `SelectedSchedule`: \(a(0)\ge1\), divergence of the real scale sequence, smoothness of all three sums, and \(1/a(j)<q_{\rm big}\). At the origin `physicalQ` equals \(q_t\); hence the local-domain and strict zeroth-cutoff plateau conditions hold on this entire interval.

Here is the checked transfer, rather than an appeal to the internal witness of an existence proof:

* [ActualCandidateAssembly](../../../../NavierStokes/ActualCandidateAssembly.lean), `potentialStages`, `initialPotential_stage`, `positive_stage`, and `PhysicalStage.axisZeroOn`, identify stage zero as base gauge potential plus finite initialization, and positive stages as particular + signed + stream-mean increments, with zero potential germs at every relevant axis point.
* [GermCandidateAssembly](../../../../NavierStokes/GermCandidateAssembly.lean), `potentialSum_eq_base_germ`, intersects only finitely many germs by local finiteness. The plateau removes the zeroth multiplier. Curl preserves this equality; [TailGaugePotential](../../../../NavierStokes/TailGaugePotential.lean), `finalPotential_sameCurl`, removes the gauge.
* The actual direct stages are `LocalAngularDiagonal.rawSeries`. [DirectAngularDiagonal](../../../../NavierStokes/DirectAngularDiagonal.lean), `angularField` and `AngularData`, give annular zero germs at the axis; local finiteness again applies.
* [BaseResidual](../../../../NavierStokes/BaseResidual.lean), `baseVelocity_at_origin` (59–86), applies using [FinalSlowBase](../../../../NavierStokes/FinalSlowBase.lean), `scales_strictMono`, `coefficients_smooth`, `leading_origin`, and [EntranceAlignedBase](../../../../NavierStokes/EntranceAlignedBase.lean), `modulated_positive_axis`.
* [MixedPeriodicAssembly](../../../../NavierStokes/MixedPeriodicAssembly.lean), `periodicVelocity_eventuallyEq` and `periodicVelocity_origin` (111–133), transfer **germs**, not just values. The literal [spatial cutoff](../../../../NavierStokes/SpatialLocalization.lean) is one for \(x_0^2+x_1^2<1/32,\ |x_2|<1/8\), with support inside the unit cell. [TimeLocalization](../../../../NavierStokes/TimeLocalization.lean), `activatedVelocity_eventuallyEq_late`, removes activation for \(t>3/4\).

Consequently, throughout this fixed interval,
\[
 U(t,0)=j_*q_t^{-A}e_2.                                      \tag{1}
\]
There is additional exact information. `modulated_leading_axis` states \(d_{\rm axial,0}(0,\eta)=4\eta+j_*\) for \(|\eta|\le1\); positive axial coefficients vanish there. The same germ argument along nearby axial points and [AxisymmetricFields](../../../../NavierStokes/AxisymmetricFields.lean), `velocity_on_axis` (192–206), give
\[
 U_2(t,0,0,\zeta)=q^{-A}(4\zeta q^{-D}+j_*),
 \qquad q-\zeta^2q^{2h}=1-t.
\]
The stream average at radius zero equals its axial coefficient, as in the inspected `baseVelocity_at_origin` proof. Differentiation gives \(q_\zeta(t,0)=0\). The base's smooth axial component depends on transverse squared radius, so its transverse derivatives at zero vanish. Therefore
\[
 \partial_2U_2(t,0)=4/q_t,\qquad
 \partial_0U_2(t,0)=\partial_1U_2(t,0)=0.                     \tag{2}
\]
Only a local base germ is used; the complete field is not assumed globally axisymmetric.

## 2. Complete source, including projection and mean

Let \(c_j=\texttt{scaledCutoff}(a(j),\texttt{physicalQ})\), and let \(\mathcal A=\sum_jc_jA_j\), \(\mathcal B=\sum_jc_jB_j\), \(\mathcal Q=\sum_jc_jP_j\) be the literal selected sums. With spatial cutoff \(\eta\), periodization \(\mathcal E\), and switch \(\theta\),
\[
 V=\operatorname{curl}\mathcal E(\eta\mathcal A)+\mathcal E(\eta\mathcal B),
 \quad\Pi=\mathcal E(\eta\mathcal Q),\quad U=\theta V,\ p=\theta\Pi.
\]
[CandidateProperties.navier_stokes](../../../../NavierStokes/ProblemStatement.lean) fixes the residual, at viscosity one. With \(R(V,\Pi)=V_t-\Delta V+V\cdot\nabla V+\nabla\Pi\),
\[
 F:=\mathbb Pf=\theta\mathbb PR(V,\Pi)+\theta'V
       +(\theta^2-\theta)\mathbb P(V\cdot\nabla V)
   =U_t-\Delta U+N,\qquad N=\mathbb P(U\cdot\nabla U).         \tag{3}
\]
For \(t>t_0\), activation defects vanish, not the underlying residual. Formula (3) retains every cutoff derivative, initialization, particular/signed/mean repair and nonlinear cross-product. Leray removes the **whole periodic pressure gradient**, not the pressure-coupled part of convection:
\(\mathbb P=I-\nabla\Delta^{-1}\operatorname{div}\), with inverse on mean-zero scalars and Fourier multiplier \(\mathbb P_0=I\).

There is a real mean cancellation. The periodic curl has zero mean. Every direct stage has form \(b(t,r,x_2)(-x_1/r,x_0/r,0)\); its scheduled, spatially cut sum is odd under the transverse half-turn. Integrating its compact lift, then periodizing, proves \(\bar U=0\). Integrating (3) gives \(\bar F=0\). Both linear convection terms are divergences, so zero restart data imply \(\bar z=0\). This proves absence of the zero mode here without deleting it from Leray's definition.

Selected smoothness and periodicity give fixed finite seminorms
\[
 M_m=\sup_{1-\delta_*\le s\le1}\|f(s)\|_{H^m(\mathbb T^3)}<\infty. \tag{4}
\]
Terminal-origin jets also give \(|f_2(s,0)|\le C_Nq_s^N\) for every integer \(N\), with constants on this fixed window. They assert neither whole-cell terminal vanishing nor local flatness of \(F\): Leray is nonlocal.

## 3. Finite-horizon full evolution and signed identity

Use the unit-volume torus and \(X^m=H^m_\sigma\), including constants, with \(m=4\). Define
\[
 C_Uz=U\cdot\nabla z+z\cdot\nabla U,
 \quad L_Uz=z_t-\Delta z+\mathbb PC_Uz,
 \quad L_Uz=F,\quad z(t_0)=0.
\]
On each compact slab \([t_0,T]\), \(T<1\), coefficients are smooth and \(\mathbb PC_U:X^4\to X^3\) is bounded. Commuting four spatial derivatives, divergence freedom cancels the leading transport energy term. Pair an \(H^3\) source with the \(H^5\) diffusion norm and absorb by Young's inequality. This gives
\[
 \sup_{[t_0,T]}\|z\|_{H^4}^2+\int_{t_0}^T\|z\|_{H^5}^2
 \le C_{t_0,T}\bigl(\|z(t_0)\|_{H^4}^2+\|F\|_{L^2H^3}^2\bigr).
\]
Fourier-Galerkin approximation, weak compactness and the same estimate for differences give existence and uniqueness; the \(H^5,H^4,H^3\) energy triple gives
\(z\in CX^4\cap L^2X^5\), \(z_t\in L^2X^3\). The homogeneous evolution \(\Phi_U(t,s)\) is consistent on overlapping slabs. Its generator on \(X^4\) has domain \(X^6\); the differential expression maps \(X^4\) to \(X^2\), not to \(X^4\). Smooth selected data allow the pointwise calculations below. None of these constants is claimed endpoint-uniform.

Put \(\ell_Tv=q_T^Ae_2\cdot v(0)\) and
\[
 a_T(s)=\Phi_U(T,s)^*[q_T^A\mathbb P(e_2\delta_0)].
\]
Here \(*\) is distributional duality over \(X^4\), not the Hilbert adjoint obtained by an \(H^4\) Riesz identification. The terminal distribution belongs to \(X^{-4}\), not \(L^2\). Parabolic smoothing for \(s<T\) gives
\[
 -\partial_sa_T-\Delta a_T-\mathbb P(U\cdot\nabla a_T)
       +\mathbb P((\nabla U)^Ta_T)=0.
\]
Duhamel and smooth terminal approximation converging in \(H^{-4}\) prove
\[
 J(T):=\ell_Tz(T)=\int_{t_0}^T\langle a_T(s),F(s)\rangle\,ds. \tag{5}
\]
Because \(\bar z=0\), \(e_2\delta_0\) can be replaced by \(e_2(\delta_0-1)\). The adjoint constant stays constant: \(\mathbb P(\nabla U)^Tc=\mathbb P\nabla(U\cdot c)=0\).

There is exact source cancellation, not merely an estimate. From (3), \(L_UU=F+N\), whence
\[
 \boxed{J(T)=j_*-\ell_T\Phi_U(T,t_0)U(t_0)
    +\int_{t_0}^T\!\int_{\mathbb T^3} S(a_T):(U\otimes U)\,dx\,ds.} \tag{6}
\]
Indeed \(z=U-\Phi_UU(t_0)-\int\Phi_UN\) and
\(\langle a,N\rangle=-\int\nabla a:(U\otimes U)\). Symmetry removes the antisymmetric gradient; \(\operatorname{div}a=0\) also removes the isotropic trace. Terminal-end integrals mean the preceding duality limit. Formula (6) retains cancellation between all three terms; no separate large term proves failure.

Other exact variations do not solve the problem: \(L_U\partial_tU=\partial_tF\), \(L_U\partial_iU=\partial_iF\), not \(F\). Continuous NS dilation changes the fixed unit torus and selected schedule/cutoffs. Local symmetry does not define an invariant one-dimensional response subspace.

## 4. Improvement: isolate damping and the complete direct source

Split the linear pressure **before estimating**:
\[
 \pi_f=\Delta^{-1}\operatorname{div}f,\qquad
 \pi_z=-\Delta^{-1}\operatorname{div}C_Uz.
\]
Then \(z_t-\Delta z+C_Uz+\nabla\pi_z=F\). Equations (1)–(2), with \(b(s)=z_2(s,0)\), imply exactly
\[
 b'+4q_s^{-1}b=F_2(s,0)+\mathcal K_U(s)z(s),
\]
where the remaining spatial functional is
\[
 \mathcal K_U(s)v=\Delta v_2(0)-j_*q_s^{-A}\partial_2v_2(0)
       +\partial_2\Delta^{-1}\operatorname{div}C_Uv(0).       \tag{7}
\]
It is bounded on \(X^4\) at each finite time: diffusion leaves \(H^2\), while the convection/pressure term lies in \(H^3\). Thus
\[
 \boxed{J(T)=D_F(T)+R_U(T),\quad
 (D_F,R_U)=q_T^{A+4}\int_{t_0}^Tq_s^{-4}
       \bigl(F_2(s,0),\mathcal K_U(s)z(s)\bigr)\,ds.}        \tag{8}
\]
The coefficient \(+4/q\) is genuine damping. With \(C_{\rm ev}\) the \(H^4\) evaluation constant and Leray contractive in the Fourier Sobolev norm,
\[
 |D_F(T)|\le\frac{C_{\rm ev}M_4}{3}
       (q_T^{A+1}-q_T^{A+4}\delta^{-3}),\qquad
 \boxed{\sup_T|D_F(T)|\le C_{\rm ev}M_4\delta^{A+1}/3.}      \tag{9}
\]
This also controls the nonlocal **forcing-pressure** contribution, with no false flatness assumption. It improves the bare local-source reduction in the combined drafts. If pressure is not split, the direct unprojected term has the sharper jet bound, for \(N>3\),
\[
 \sup_T\left|q_T^{A+4}\int_{t_0}^Tq_s^{-4}f_2(s,0)ds\right|
 \le C_N\delta^{A+N+1}/(N-3),
\]
but its omitted pressure part is not flat. Bound (9) closes that particular interface.

**First missing quantity:** the signed \(R_U(T)\) in (8), including its possible cancellation with \(D_F\). Base transverse diffusion has rate \((q^{1/2})^{-2}=q^{-1}\); axial transport has rate \(q^{-A}(q^D)^{-1}=q^{-1}\). There is no interval-length small parameter relative to damping. The response pressure in (7) samples all spatial modes.

## 5. A concrete failed closure test, not evidence of response growth

The full heat parametrix gives
\[
 z=\int_{t_0}^te^{(t-s)\Delta}F(s)ds
       -\int_{t_0}^te^{(t-s)\Delta}\mathbb PC_Uz(s)ds.
\]
The heat source alone has weighted observation at most \(C_{\rm ev}M_4\delta^{A+1}\). The \(H^4\) algebra and one-derivative heat estimate yield, with \(Z_T=\sup_{t_0<s\le T}q_s^A\|z(s)\|_{H^4}\),
\[
 q_T^A\|z(T)\|_{H^4}\le M_4\delta^{A+1}+K(T)Z_T,
 \quad K(T)=C\int_{t_0}^T(T-s)^{-1/2}(q_T/q_s)^A\|U(s)\|_{H^4}ds.
\]
Equation (1) implies \(\|U(s)\|_{H^4}\ge j_*q_s^{-A}/C_{\rm ev}\). Restricting to \(T-q_T<s<T\), where \(q_T\le q_s\le2q_T\), proves
\[
 K(T)\ge c j_*q_T^{1/2-A}=c j_*q_T^{-h}\longrightarrow\infty. \tag{10}
\]
Thus this particular positive contraction majorant cannot become uniformly small by late restart. Unlike speculative derivative scaling, (10) uses a lower bound for the actual total field. It is **not** a lower bound for the integral operator, \(R_U\), or \(|J|\). Cancellation can invalidate any such inference.

For fixed \(\tau>t_0\), the total response contains
\(\ell_T\Phi_U(T,\tau)z(\tau)\). In (8) the scalar seed contributes
\(q_T^{A+4}q_\tau^{-4}b(\tau)\), but all other components of \(z(\tau)\) continue feeding \(\mathcal K_Uz\). Late flatness cannot discard them.

Why native tools stop here: [ActualParticularControl.selected_energy](../../../../NavierStokes/ActualParticularControl.lean) (43–54) controls a selected moving-frame modal ODE, retaining extra harmonic damping. [ActualPrimaryCovariance.viewSum_covariance_factor](../../../../NavierStokes/ActualPrimaryCovariance.lean) (382–398) averages native leading-wave products with an **unweighted fast-variable average**. It cannot be inserted against \(S(a_T)\). The full Fourier convection is
\[
 2\pi i\,\mathbb P_k\sum_l\bigl[
 (\widehat U_{k-l}\cdot l)\widehat z_l
 +(\widehat z_l\cdot(k-l))\widehat U_{k-l}\bigr].             \tag{11}
\]
In particular the second, cross-mode strain term is not bounded by those modal/covariance certificates against the axial adjoint. Weighted native inverses solve construction sources on native patches, not this operator with its complete pressure and restart trace. Chapter 06's selected enlarged-chart threshold bridge remains missing for its explicit arrays on every actual label; repairing it would not estimate (11).

## 6. Exact stopping point and a noncircular sufficient theorem

The target remains
\[
 \exists t_0<1\ \exists\rho\in(0,1)\ \forall T\in(t_0,1):
             |D_F(T)+R_U(T)|\le\rho j_*.                    \tag{12}
\]
Equivalently estimate the **total** expression (6). For example, (9) can be made \(\le j_*/4\) with one fixed restart; a uniform \(|R_U|\le j_*/2\) would then suffice with \(\rho=3/4\). That latter bound is **not established or assumed**.

A source-independent sufficient operator theorem would be the axial Green bound
\[
 \|\Phi_U(T,s)^*\mathbb P[e_2(\delta_0-1)]\|_{H^{-4}}
       \le C(q_s/q_T)^\gamma,\qquad 0\le\gamma\le A,         \tag{13}
\]
with \(C,\gamma\) fixed on the terminal window, before \(t_0,s,T\). It gives directly from (5)
\[
 |J(T)|\le\frac{CM_4}{\gamma+1}q_T^{A-\gamma}\delta^{\gamma+1}
       \le\frac{CM_4}{\gamma+1}\delta^{A+1}.
\]
This is one sufficient norm certificate, not a claim that absolute operator control is necessary for selected-source cancellation.

To avoid merely assuming the desired response under another name, a verifiable **coefficient-level sufficient hypothesis** for (13) is as follows. On the mean-zero \(X^4\) subspace let \(G_U=\Delta-\mathbb PC_U\). Suppose there is a differentiable self-adjoint family \(Q(t)\), bounded on \(X^4\), with fixed \(0<c\le C_0\),
\[
 cI\le Q(t)\le C_0I,\qquad
 \langle v,Q'(t)v\rangle_{H^4}
 +2\operatorname{Re}\langle Q(t)v,G_U(t)v\rangle_{H^4}
 \le(2\gamma/q_t)\langle v,Q(t)v\rangle_{H^4}                \tag{14}
\]
for every smooth divergence-free mean-zero test field and \(0\le\gamma\le A\). Differentiating this energy along the homogeneous equation proves its norm grows by at most \(\sqrt{C_0/c}(q_s/q_T)^\gamma\); bounded evaluation then proves (13). These assumptions concern only the selected coefficients and a uniformly coercive quadratic form, not \(z\), \(f\), or the desired margin. **No such form or alternative signed Green estimate has been supplied.** The scalar damping alone does not verify (14).

What can be extracted **now** is exactly the selected germ/axis identities, the direct-angular mean cancellation, smooth source seminorms, and the damping calculation (7)–(9). These genuinely reduce the source/observable interface. No inspected auxiliary proof tool currently reduces the remaining full-PDE operator estimate without a new embedding/remainder theorem. Controlling that pairing is genuinely new PDE analysis beyond the original native machinery, not just a missing selected-axis declaration or a numerical constant lookup.

This bounded calculation stops here. Under periodic B, global comparator smoothness may be assumed for contradiction, not stability. Even linear success would leave nonlinear closure, since \(w=U-v\) obeys \(L_Uw=F+\mathbb P(w\cdot\nabla w)\). Whole-space A is outside scope.

Companion links: [05 §§3–8](../../../../../proof-native-control-20260912T185404Z/docs/proof-companion/05-native-weighted-control.md); [06 §§1,3,6–10](../../../../../proof-native-control-20260912T185404Z/docs/proof-companion/06-primitive-derivative-bounds.md). Prior [CENTRAL-OBSTACLE.md](../CENTRAL-OBSTACLE.md) is preserved as prior evidence, not silently updated by this calculation.
