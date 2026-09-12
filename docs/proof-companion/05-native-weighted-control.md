# 05 — One selected native weighted-control producer

This chapter follows one actual particular-wave copy from its rounded phase to its raw velocity and pressure estimates. The main mechanism is not coercivity in the sense of a positive lower quadratic form: an unstable reference system gives an **upper energy-growth bound**, viscosity improves that bound at every nonzero harmonic, and separation transfers the incoming residual weight along the entire integration path.

**Evidence and scope.** Source baseline `26e896edbdbe1215c0d50ddba24b2b6453646f5f`, verified by `git rev-parse HEAD`. This is a documentation reconstruction using the supplied N1–N3 reports, the [plan](native-control-plan.md), its two prior reports, and selected actual proof-body cross-checks. It is not a fresh Lean check or independent PDE review. The [new ledger](native-control-validation.md) separates calculations from source-only inputs. The older [validation ledger](VALIDATION.md) remains historical. In particular, the higher-order base-jet and inverse-frequency producers below are **not completely rederived**. No conclusion here closes the whole correction-cycle obligation.

Read after [chapter 02's particular-wave step](02-ns-construction.md#nsc-005). We stop at native raw jets; cutoff defects, signed matching, mean repair, periodization and physical residual estimates are not consequences of this chapter alone.

<a id="native-control-identity"></a>
## 1. Fix the construction before choosing a copy

Fix the actual profile with \(0<h<1/2\), budget \(B_{\rm bud}\), admissible initialization threshold \(N_0\), slot system of radius \(r_0>0\), and incoming cycle invariant with frequency coherence. Let
\[
a=(\texttt{ActualPrimary.choice}\ B_{\rm bud}\ N_0).\texttt{prepared},
\qquad M_0=a.M\ge1,\quad 0<u=a.u\le M_0.
\]
The state given to the particular producer is \(x_P=\texttt{particularState}(x_{\rm cycle})\), not the later post-particular state used by signed correction.

Choose an arbitrary selector \(e:\mathbb N\to\mathrm{ActivePair}\). At index \(q\), write
\[
e(q)=(\ell,b),\qquad \ell=(c,L_0),\qquad b_r=\mathrm{cellBand}(L_0).
\]
Here \(c\in\mathrm{Fin}\,2\) chooses a **phase sign**, not a complex component. Activity implies \(b\ge1\), \(|b-b_r|\le4\); preparation puts \(b_r\) above its large-band threshold, in particular \(b_r\ge4\). No surjectivity of \(e\) is required. Let \(F_*\) be `selectedConstruction e`, with reference scale \(S_0=S(b_r)\) and slot length \(L=F_*.L((),q)>0\).

Fix a nonzero integer harmonic \(j\) and an arbitrary lattice copy \(k\in\mathbb Z^2\). A native point is
\[
x=((p,\theta),Y),\qquad p=(R,(T,Z)),\quad Y\in\mathbb R^2,
\qquad \chi(p,\theta)=(R,(Z,T)).
\]
Native parameter and cover spaces have iterated product/**max** norms. Modal states \(\mathbb R^2\) and real ambient vectors \(\mathbb R^3\) have Euclidean norms. Complex ambient vectors have the componentwise sup norm. All jets below are full real Fréchet multilinear operator norms, not just spatial derivatives.

Write \(Q=Q_b,Q_r=Q_{b_r}\), \(R_a=Q^a/Q_r^a\). The fixed maps and multipliers are
\[
\phi(R,(Z,T))=(R_{1/2}R,(R_{1/2-h}Z,R_1T)),\quad
c_t=R_{1+h}>0,\quad c_N=\frac{K_r}{K}R_{1/2}>0,
\]
where \(K,K_r\) are the two carriers. The same \(j\) in \(jK,jK_r\) cancels in \(c_N\), even for \(j<0\). Set
\[
L_c=L/c_t,\qquad S_b=\mathrm{selectedStrip.slow}(q),\qquad
G=S_b\max(1,\delta(p)^{-1})\ge S_b\ge1,
\quad w=\epsilon^\alpha\sqrt{\zeta(p)},\quad \alpha=\tfrac12+\sigma.
\]
The selected strip's \(\epsilon\) is distinct from the reference-band \(\epsilon_r\) used in phase rounding. Also \(S_0\le25S_b\); we do **not** replace \(S_0\) by \(G\) in an energy-error denominator.

**Quantifiers.** The energy constants below depend only on fixed prepared/slot data and precede \(e,q,k,j,x,v,z\). For jets, fix \(e,j\) and each finite order \(N\); constants \(C_N,m_N\) are then supplied before \(q,k,x,d\le N,v\). Jet constants may depend on \(j\), unlike energy. Write \(\mathcal D_{\rm strip}\) for the selected strip domain and \(\mathcal C_{\rm ref}((),q)\) for the selected reference-cell carrier. The full-path hypotheses are the conjunction
\[
\operatorname{Adm}_{q,k}(x,v)\iff
 (p,\theta)\in\mathcal D_{\rm strip}\ \land\
 \phi\chi(p,\theta)\in\mathcal C_{\rm ref}((),q)\ \land\
 \xi_k(Y)\in[-r_0,r_0]\ \land\ v\in[0,L_c].
\]
Here \(\xi_k\) and \(t_k\) are the copy coordinates defined in §5. Strip membership does not replace reference-carrier membership: the latter is needed for normal comparison and energy. Full-path estimates hold for every sampled \(v\) under this predicate, without requiring the current time \(t_k(x)\) to be interior. Current-copy jets in §8 additionally require \(t_k(x)\in(0,L_c)\), so an interior germ identifies the actual solution with its smooth representative.

**Actual identity trail.** [CorrectionInitialization](../../NavierStokes/CorrectionInitialization.lean): `NavierStokes.CorrectionInitialization.ActualPrimary.choice`, `NavierStokes.CorrectionInitialization.ActualPrimary.phases`; [PrimaryGeometryAssembly](../../NavierStokes/PrimaryGeometryAssembly.lean): `NavierStokes.PrimaryGeometryAssembly.family`, `NavierStokes.PrimaryGeometryAssembly.construction`; [stage controls](../../NavierStokes/ActualParticularStageControls.lean): `NavierStokes.ActualParticularStageControls.selectedConstruction`, `NavierStokes.ActualParticularStageControls.selectedControl`, `NavierStokes.ActualParticularStageControls.selected_tangent_eq`, `NavierStokes.ActualParticularStageControls.selectedActualControl`. The last identity uses incoming frequency coherence. Reindexing retains the same frame; `withSource` changes only the source. Thus the estimates below do not select a more favorable auxiliary system.

<a id="native-control-normal"></a>
## 2. A signed reference instability and a rounded normal

### The primitive input boundary

At the representative slow point \(\bar q\), write
\[
F_0=F_{\rm ref}(\bar q),\qquad
 g_0=(\bar R F_{{\rm ref},R}(\bar q),G_{{\rm ref},R}(\bar q)).
\]
The permitted prepared cone says
\[
F_0>0,\qquad (g_0)_0<0,\qquad 2F_0(g_0)_0+|g_0|^2>0.                 \tag{2.1}
\]
Put \(n_0=g_0/|g_0|\), \(K_0=-Jn_0\), where \(J\) is the quarter-turn. Then \(JK_0=n_0\), \(|K_0|=1\), \(K_0\perp g_0\). For \(\gamma=2F_0(n_0)_0\), (2.1) gives \(\gamma<0<\gamma+|g_0|\). Hence
\[
\lambda=\sqrt{-\gamma(\gamma+|g_0|)}>0,\quad c_0=\lambda/\gamma<0,
\quad \lambda/c_0=2F_0(JK_0)_0,
\quad \lambda c_0=-[2F_0(JK_0)_0+\langle JK_0,g_0\rangle].           \tag{2.2}
\]
This elementary signed eigenpair, not an abstract spectral assertion, drives the calculation. Replacing \(c_0\) by a positive ratio would change it. Preparation bounds \(|g_0|,\lambda,|c_0|\) between \(M_0^{-1}\) and \(M_0\), and bounds \(|F_0|\), radii and reciprocal radii by \(M_0\). It also includes \(1/(2r_0)\le M_0\) and \(4r_0T_g\le M_0\), used in the inverse-length and enlarged-slot estimates.

On a convex enlarged cell, prepared normalized errors give
\[
|F-F_{\rm ref}|\le M_0\epsilon_r^2,\quad
\|DF-DF_{\rm ref}\|,\|DG-DG_{\rm ref}\|\le M_0\epsilon_r^2,
\]
with reference first/second derivative and the needed actual directional bounds by the prepared majorant \(M_0\). Any doubling needed to pass from primitive normalized estimates to these local bounds has already been absorbed in that prepared majorant. For example \(\|DF\|\le M_0\epsilon_r^2+M_0\le2M_0\). **These base estimates and the existence of (2.1) are source-only primitive inputs here.** Their production from the summed profile would require expanding `BaseChartJets.actual_estimates` and the modulated profile-cone construction. The body of `NavierStokes.PrimaryGeometryAssembly.exists_prepared` calls [BaseChartJets](../../NavierStokes/BaseChartJets.lean): `NavierStokes.BaseChartJets.exists_actual_positive_charts`; [FinalSlowBase](../../NavierStokes/FinalSlowBase.lean): `NavierStokes.FinalSlowBase.scales_admissible_on`; [AlignedProfileSpectralCone](../../NavierStokes/AlignedProfileSpectralCone.lean): `NavierStokes.AlignedProfileSpectralCone.modulated_representative_bounds` and `NavierStokes.AlignedProfileSpectralCone.modulated_positive_reference_cone` for these inputs. Nothing below assumes modal errors or energy as primitive data.

### Mesh, rounding, and a genuine producer inequality

The representative is in a one-mesh support, the evaluation point \(\widehat q\) in its two-mesh enlargement. Coordinatewise triangle inequalities in the slow max norm give
\[
d_q=\|\widehat q-\bar q\|\le3/S_0^3.
\]
The mean-value estimate on the convex cell gives
\( |F_R(\widehat q)-F_{{\rm ref},R}(\bar q)|\le M_0(d_q+\epsilon_r^2)\), and similarly for \(G_R\). Expand the radius before estimating the shear:
\[
|RF_R-\bar RF_{{\rm ref},R}|\le
M_0d_q+M_0^2(d_q+\epsilon_r^2).
\]
Adding coordinate estimates and using \(S_0^2\epsilon_r^2\le1\) yields
\[
|F-F_0|,\ |g-g_0|\le16M_0^2/S_0.                              \tag{2.3}
\]

There are two roundings. The carrier \(k_r=\lceil\epsilon_r^{-1/2}\rceil\) gives \(1\le\nu_0=\epsilon_r k_r^2\le4\). The phase's `nonzeroRound` gives angular error \(|p_\theta-\mathrm{target}|\le k_r^{-1}\). Let
\[
D_u=(1+u^2)\sqrt{1+u^2},\quad B_0=\sqrt{\lambda/(\nu_0D_u)},\quad
b_0=\sqrt{(1/M_0)/(4D_u)}\le B_0\le M_0.
\]
Thus \(\nu_0B_0^2=\lambda/D_u\) **exactly**. For sign \(\varsigma=\pm1\), the unrounded transverse frequency is
\[
B_0K_0-\frac{\varsigma B_0u}{L|g_0|^2}g_0;
\]
its shear pairing is \(-\varsigma B_0u/L\). In reference slot time \(s\), the actual normal and its derivative are
\[
N(s)=\left(\varsigma B_0u/2-s(p_\theta F_R+p_zG_R),\ p_\theta/R,
 p_z-\epsilon_rs(p_\theta F_Z+p_zG_Z)\right),
\]
\[
\dot N=(-(p_\theta F_R+p_zG_R),0,-\epsilon_r(p_\theta F_Z+p_zG_Z)).
\]
Set \(s_0=\varsigma(u/2+us/L)\), \(N_{\rm ref}=B_0(s_0,K_0)\). To see the actual error production, use a common majorant \(M\), angular rounding error \(\omega\), diameter \(d_q\), and derivative discrepancy \(e_D\). Expanding the three coordinates gives
\[
\begin{split}
|N-N_{\rm ref}|\le{}&|s|(M\omega+2Me_D)+M\omega+M^3d_q\\
 &+2B_0u/(L|g_0|)+3M^2\epsilon_r|s|.                         \tag{2.4}
\end{split}
\]
The terms are respectively radial accumulation, angular rounding/radius change, representative tilt, and axial drift. The exact formula for \(\dot N\) is bounded separately: **we do not differentiate (2.4)**.

Here is the source's constant ledger:
\[
\begin{gathered}
M_f=M_0+M_0(M_0+M_0^4)+(M_0+M_0^4)+M_0^2+4,\\
p(M)=8M^3+2M^4,\qquad C_{\rm ph}=8p(2M_f).
\end{gathered}
\]
The primitive phase estimate is \(p(M)(S^{-1}+S\epsilon_r^2+S/k_r+\epsilon_rS)\). The actual diameter is \(3/S_0^3\), so its application uses \(S=S_0/2,M=2M_f\), not \(S=S_0\). The large-band inequalities
\[
S_0^2\epsilon_r^2\le1,\quad S_0^2/k_r\le1,\quad \epsilon_rS_0^2\le1
\]
bound that parenthesis by \(8/S_0\). Therefore
\[
|N-N_{\rm ref}|,\ |\dot N|\le\delta_N=C_{\rm ph}/S_0
\le b_0/2\le B_0/2.                                         \tag{2.5}
\]
The final smallness is ensured by choosing the prepared band threshold after \(M_0,u\); it is not an assumed normal-comparison output.

**Source trail.** [PrimaryRepresentatives](../../NavierStokes/PrimaryRepresentatives.lean): `NavierStokes.PrimaryRepresentatives.ReferenceCone.c0_neg`, `NavierStokes.PrimaryRepresentatives.ReferenceCone.lambda0_div_c0`, `NavierStokes.PrimaryRepresentatives.ReferenceCone.lambda0_mul_c0`; [PhaseEstimates](../../NavierStokes/PhaseEstimates.lean): `NavierStokes.PhaseEstimates.explicit_normal_estimate`, `NavierStokes.PhaseEstimates.rounded_normal_estimates`; [BasePhaseGeometry](../../NavierStokes/BasePhaseGeometry.lean): `NavierStokes.BasePhaseGeometry.phase_errors_on_mesh`, `NavierStokes.BasePhaseGeometry.FamilyData.phase_estimates`, `NavierStokes.BasePhaseGeometry.FamilyData.base_estimates`, `NavierStokes.BasePhaseGeometry.FamilyData.phase_error_small`. These are producers, not fields of the eventual control record.

<a id="native-control-energy"></a>
## 3. From the normal to the full modal energy

Let \(\beta=|\operatorname{tail}N|\), \(K_f=\operatorname{tail}N/\beta\), \(N_f=JK_f\), \(\rho=N_{\rm rad}/\beta\). The tail of (2.5) gives
\[
|\beta-B_0|\le\delta_N,\quad \beta\ge B_0/2,\quad |N|\ge B_0/2.
\]
A lower bound only on \(|N|\) would not justify normalization of its tail. Quotient expansion gives
\[
|\rho-s_0|\le2(1+|s_0|)\delta_N/B_0,\quad
|K_f-K_0|,|N_f-JK_0|\le4\delta_N/B_0.
\]
Moreover
\[
\dot\beta=\langle\operatorname{tail}N,\operatorname{tail}\dot N\rangle/\beta,
\quad \dot\rho=(\dot N_{\rm rad}-\rho\dot\beta)/\beta,
\quad \dot K_f=(\operatorname{tail}\dot N-\dot\beta K_f)/\beta.
\]
Thus \(|\dot\beta|\le\delta_N\), \(|\dot\rho|\le2(1+|\rho|)\delta_N/B_0\), and \(|\dot K_f|,|\mathrm{rot}|\le4\delta_N/B_0\), where \(\mathrm{rot}=\langle N_f,\dot K_f\rangle\). Unit-frame differentiation yields \(\dot K_f=\mathrm{rot}N_f,\dot N_f=-\mathrm{rot}K_f\). On the enlarged slot, \(|s_0|\le3M_0\), \(|\rho|\le1+6M_0\).

An ambient tangent vector has coordinates \(a_{\rm amb}=(X,-\rho XK_f+YN_f)\). The retained action is
\[
K_{\rm act}a=(-2F(\operatorname{tail}a)_0,\ a_0(2Fe_\theta+g)).
\]
Projection onto the moving tangent frame gives the undamped coordinate entries
\[
a_{11}=\frac{\rho(\langle K_f,g\rangle-\dot\rho)}{1+\rho^2},\quad
 a_{12}=\frac{2F(N_f)_0-\rho\mathrm{rot}}{1+\rho^2},\quad
 a_{21}=-(2F(N_f)_0+\langle N_f,g\rangle)+\rho\mathrm{rot}.       \tag{3.1}
\]
Both slope and rotation terms matter. For explicit bookkeeping put
\[
A_0=3M_0,\quad G_0=M_0+2+2A_0,\quad
\eta=16M_0^2/S_0+8(1+A_0)\delta_N/b_0.
\]
The preceding primitive errors are bounded by \(\eta\); inner-product errors by \((1+G_0)\eta\). The denominator estimate
\[
|(1+\rho^2)^{-1}-(1+s_0^2)^{-1}|\le|\rho-s_0|(|\rho|+|s_0|)
\]
shows, for example, that the error in \(a_{12}\) is at most
\(\bigl((2+3G_0)+4G_0^2\bigr)(1+G_0)\eta\le16G_0^2(1+G_0)\eta\).
The same expansion bounds all three coordinate errors by \(C_{\rm coord}/S_0\), where
\[
C_{\rm coord}=16G_0^2(1+G_0)
 \left(16M_0^2+\frac{8(1+3M_0)C_{\rm ph}}{b_0}\right).          \tag{3.2}
\]

Now set
\[
m(s)=u/2+us/L,\quad \Lambda=\lambda/\sqrt{1+m^2},\quad
H_e=c_0\sqrt{1+m^2},\quad r_e=H_e'/H_e=m(u/L)/(1+m^2).
\]
By (2.2), the frozen entries in (3.1) are \(0,\Lambda/H_e,\Lambda H_e\). Write their errors as \(a,b,c\). In the **time-dependent** eigenbasis
\(X=z_++z_-,\ Y=H_e(z_+-z_-)\), differentiation gives
\[
\begin{array}{ll}
e_{11}=(a+H_eb+c/H_e-r_e)/2,&e_{12}=(a-H_eb+c/H_e+r_e)/2,\\
e_{21}=(a+H_eb-c/H_e+r_e)/2,&e_{22}=(a-H_eb-c/H_e-r_e)/2.
\end{array}                                                   \tag{3.3}
\]
Here \(|H_e|,|H_e^{-1}|\le H_0=M_0(2+3M_0)\), and the slot bound gives \(|r_e|\le3M_0^3/S_0\). Discarding a harmless factor \(1/2\) gives
\[
|e_{ab}|\le C_*/S_0,\qquad C_*=(1+2H_0)C_{\rm coord}+3M_0^3.    \tag{3.4}
\]

Damping is equally concrete. Since \(|N_{\rm ref}|\le M_0(A_0+2)\), \(|N|\le M_0(A_0+3)\),
\[
\begin{split}
|\nu_0|N|^2-\nu_0B_0^2(1+s_0^2)|
&\le4\,|N-N_{\rm ref}|\,(|N|+|N_{\rm ref}|)\\
&\le4M_0(6M_0+5)C_{\rm ph}/S_0.
\end{split}
\]
The exact normalization in §2 identifies the second term as
\[
d_{\rm ref}(s)=\lambda(1+m^2)/D_u.
\]
Consequently
\[
\nu_{\rm eff}=\nu_0|N|^2\ge0,\quad
|\nu_{\rm eff}-d_{\rm ref}|\le E_*/S_0,\quad
E_*=4M_0(6M_0+5)C_{\rm ph}.                                  \tag{3.5}
\]
These are the actual output constants \(F_*.C=C_*\), \(F_*.E=E_*\). Its upper bound is \(M_*=F_*.M=M_f+3M_0+M_0^2+4\), **not** \(M_0\).

The modal matrix is
\[
A_j=\operatorname{diag}(\Lambda,-\Lambda)-j^2\nu_{\rm eff}I+E_{\rm mat}.
\]
Entrywise (3.4) implies \(|(E_{\rm mat}z)_i|\le2C_*|z|/S_0\); bounding Euclidean norm by the sum of coordinate absolute values gives \(\|E_{\rm mat}\|_{\rm op}\le4C_*/S_0\). Since \(j^2\ge1\), (3.5) yields the full inequality
\[
\begin{split}
\langle z,A_jz\rangle
&\le(\Lambda-j^2\nu_{\rm eff})|z|^2+|z|\,|E_{\rm mat}z|\\
&\le\left[\Lambda-d_{\rm ref}+\frac{E_*+4C_*}{S_0}\right]|z|^2.
\end{split}                                                    \tag{3.6}
\]
This is uniform over **all** nonzero harmonics. It does not assert negative definiteness; the reference positive eigenvalue is intentional.

**Source trail.** [MovingFrameODE](../../NavierStokes/MovingFrameODE.lean): `NavierStokes.MovingFrameODE.projectedRhs_eq_tangentMotion`, `NavierStokes.MovingFrameODE.scalar_coefficients_close`, `NavierStokes.MovingFrameODE.modal_equations_iff`, `NavierStokes.MovingFrameODE.modal_energy_le`; [BasePhaseGeometry](../../NavierStokes/BasePhaseGeometry.lean): `NavierStokes.BasePhaseGeometry.frame_errors_of_normal_close`, `NavierStokes.BasePhaseGeometry.FamilyData.coordinate_errors`, `NavierStokes.BasePhaseGeometry.FamilyData.modal_errors`, `NavierStokes.BasePhaseGeometry.FamilyData.damping_error`, `NavierStokes.BasePhaseGeometry.FamilyData.construction`. The construction body inserts the estimates just derived, rather than assuming them.

<a id="native-control-clock"></a>
## 4. Transport the same matrix and the same integration interval

Every reference field is now evaluated at \((\phi\chi(p,\theta),c_tv)\). Under `transportedFrame`, \(\rho,K_f,N_f,H_e\) are pulled back only; \(F,g,\Lambda,\nu_{\rm eff},\dot\rho,\mathrm{rot},r_e\) acquire \(c_t\). The normal scale and its derivative become \(c_N\beta,c_Nc_t\dot\beta\). Substitution in (3.1)–(3.3) proves literal identities
\[
E_{{\rm mat},c}=c_tE_{\rm mat},\quad A_{c,j}=c_tA_j,\qquad
N_c=c_NN,\quad \dot N_c=c_Nc_t\dot N.                          \tag{4.1}
\]
Normal scaling disappears from the modal matrix, not from pressure or normal-motion estimates. The native frame ignores its auxiliary transverse coordinate, so reindexing to **any** copy \(k\) leaves (4.1) unchanged.

Let \(r=\Lambda-d_{\rm ref}\) and define the exact envelope
\[
P(s)=\exp\left(\int_{L/2}^{s}r(\tau)\,d\tau\right),\qquad P_c(v)=P(c_tv)>0.
\]
The damping normalization makes \(r(s)=\lambda[(1+m(s)^2)^{-1/2}-(1+m(s)^2)/D_u]\) vanish at \(s=L/2\), where \(m=u\): it is positive before and negative after that point on \([0,L]\). Thus \(P\) peaks at \(L/2\). This is not asserted to be an exact quadratic Gaussian. For \(0\le v\le L/c_t\), we have \(0\le c_tv\le L\). Multiplying (3.6) by \(c_t>0\) proves the actual selected-copy estimate
\[
\boxed{\ \langle z,A_{c,j}(x,v)z\rangle
 \le[c_tr(c_tv)+\mu_c]|z|^2,\qquad
 \mu_c=c_t(E_*+4C_*)/S_0.\ }                                 \tag{4.2}
\]
Also \(P_c'=c_tr(c_tv)P_c\). The slot estimate \(L\le M_*S_0\) gives the worked cancellation
\[
\boxed{\ e^{\mu_cL_c}
 =\exp\left(\frac{c_t(E_*+4C_*)}{S_0}\frac L{c_t}\right)
 =e^{(E_*+4C_*)L/S_0}\le e^{(E_*+4C_*)M_*}.\ }                \tag{4.3}
\]
Activity gives \(c_{\min}=2^{-4(1+h)}\le c_t\le2^{4(1+h)}=c_{\max}\). Hence \(L_c\le25M_*S_b/c_{\min}\). With geometry constant \(A_{\rm geo}\) from §5, the literal control constant is
\[
K_{\rm ctl}=25M_*/c_{\min}+e^{(E_*+4C_*)M_*}+A_{\rm geo}+1.     \tag{4.4}
\]
Only the exponential has no inverse-clock loss.

**Source trail.** [ActualParticularControl](../../NavierStokes/ActualParticularControl.lean): `NavierStokes.ActualParticularControl.transported_errors`, `NavierStokes.ActualParticularControl.transported_coefficient`, `NavierStokes.ActualParticularControl.transported_normalMotion`, `NavierStokes.ActualParticularControl.scaled_selected_copy_energy`; [ScaledActualParticularControl](../../NavierStokes/ScaledActualParticularControl.lean): `NavierStokes.ScaledActualParticularControl.scaledControl`. Its energy field is now explained by a producer calculation, not used as a premise.

<a id="native-control-source"></a>
## 5. Separation transfers the incoming source weight at every time

For selected cover geometry \(g\), put
\[
C_g=g.\mathrm{basis}^{-1}\circ\mathrm{cover}^{g.\mathrm{gap}},\quad
D_g=(\mathrm{cover}^{g.\mathrm{gap}})^{-1}\circ g.\mathrm{basis},
\]
\[
(\xi_k(Y),t_k(Y))=g.\mathrm{basis}^{-1}
 (\mathrm{cover}^{g.\mathrm{gap}}Y-g.\mathrm{center}-\mathrm{lattice}(k)),
\quad Y_k(v)=g.\mathrm{point}(k,(\xi_k(Y),v)).
\]
Then \(g.\mathrm{coordinates}_k(Y_k(v))=(\xi_k(Y),v)\). The affine source map on the full parameter/time space is
\[
T_k(x,v)=((p,\theta),Y_k(v)),\quad
L_g(x,v)=(x.1,D_g((C_gx.2).1,v)).
\]
Its derivative is \(L_g\), independent of the lattice translation. In max norms,
\[
\|L_g\|\le\mathcal A(g):=1+\|C_g\|+\|D_g\|(1+\|C_g\|).        \tag{5.1}
\]

Why is the entire integration rectangle separated? In reference coordinates the basis is \(\xi v_r+a_rs v_t\), center \(\mathrm{slotCenter}-r_0v_t\), with \(0<a_r\le1\) and \(a_rL=2r_0\). Its outer window has padding \(\eta=\min(r_0,L)/16\). For \(|\xi|\le r_0+2\eta\) and \(-2\eta\le s\le L+2\eta\),
\[
|\xi|\le\tfrac98r_0\le2r_0,\qquad |a_rs-r_0|\le\tfrac98r_0\le2r_0.
\]
Thus the outer image lies in the fixed slot set where the slot system supplies torus-quotient injectivity. Restrict to the closed rectangle. Zero-shift transport sends \((\xi,v)\) to \((\xi,c_tv)\); \([0,L_c]\) maps into \([0,L]\). Cover refinement leaves this native image unchanged, so injectivity survives. This uses slot-system injectivity, **not** periodicity of the source on a fictitious finer torus.

Define the rectangle-supported grouped envelope
\[
W_g(Y)=\sum_{k'}\mathbf1_{[-r_0,r_0]\times[0,L_c]}
 (g.\mathrm{coordinates}_{k'}Y)P_c(t_{k'}(Y)).
\]
Two contributing copies would give two native representatives with the same torus quotient in the separated region. They coincide, so their lattice difference is zero. Thus at most one term contributes, and
\[
W_g(Y_k(v))=P_c(v)\quad
 (\xi_k(Y)\in[-r_0,r_0],\ v\in[0,L_c]).                       \tag{5.2}
\]
This includes both time endpoints and transverse sides; no differentiability of \(W_g\) is claimed.

For completeness, the source pays a quadratic band loss in (5.1). The active gap is bounded by a fixed \(D=\mathrm{CommonWindow.gap}(h)+\mathrm{SlotColoring.nativeGap}(h)\). Let
\[
\mathcal H_D=1+\sum_{d=0}^{D}(\|\mathrm{cover}^d\|+\|(\mathrm{cover}^d)^{-1}\|),
\quad U_D=1+\mathcal H_D(2+c_{\max}+c_{\min}^{-1}).
\]
Writing \(B_{\rm slot}\) for the fixed slot-chart equivalence, set
\[
K_s=1+\mathcal H_{0}\|B_{\rm slot}\|+(1+T_g)\|B_{\rm slot}^{-1}\|\mathcal H_{0},
\quad A_s=(1+K_s)^2.
\]
Here \(\mathcal H_{0}\) is the cover sum at index zero and \(T_g=\mathrm{ChartScales.Tg}\) is the fixed time-scale constant. Reference basis estimates give \(\mathcal A(g_r)\le A_sS_0\). Transport bounds each linear map by \(U_D\) times its reference norm. For \(T=U_D\mathcal A(g_r)\ge1\),
\[
\mathcal A(g)\le1+T+T(1+T)\le4T^2
\le A_{\rm geo}S_b^2,\qquad A_{\rm geo}=4U_D^2(25A_s)^2.       \tag{5.3}
\]
These fixed costs may be large; the degree is the important uniform feature.

The **incoming** invariant is the source input, not an output-wave estimate. For a fixed real-linear extraction \(\mathrm{part}:\mathbb C^3_\infty\to\mathbb R^3_2\), let \(f\) be that part of the actual current residual. Through order \(N\) its all-jet class gives constants \(B_f,b_f\) such that
\[
\|D^df(z)\|\le B_fG(z)^{b_f}\epsilon^\alpha\sqrt{\zeta(z)}W_g(z.2),\quad d\le N.
\]
**Input status at use:** production of this invariant by previous cycles is outside the chapter. The actual binding is to the current carrier and Gaussian residual with per-label alias input zero, not to a transported reference zero source. `native_residual` reindexes labels \((c,L_0)\mapsto(L_0,c)\); `selected_envelope_eq` identifies exactly the weight above.

Since \(T_k\) preserves the slow parameter, (5.1)–(5.3) and the full affine chain rule give
\[
\begin{split}
\|D^d(f\circ T_k)(x,v)\|
&\le\|D^df(T_k(x,v))\|\|L_g\|^d\\
&\le B_fG^{b_f}wP_c(v)(A_{\rm geo}G^2)^d\\
&\le C_sG^{m_s}wP_c(v),\qquad
 C_s=B_fA_{\rm geo}^{N},\quad m_s=b_f+2N.                     \tag{5.4}
\end{split}
\]
We differentiated the source, **not its majorant** \(G,w,W_g\). This is why the exact flat factor survives all mixed derivatives in \(p,\theta,Y,v\). A weighted zeroth-order bound alone would not suffice.

**Source trail.** [ActualSignedGeometry](../../NavierStokes/ActualSignedGeometry.lean): `NavierStokes.ActualSignedGeometry.clock_outer_in_slot`, `NavierStokes.ActualSignedGeometry.slotGeometry_separated`; [WaveEnvelopeTransport](../../NavierStokes/WaveEnvelopeTransport.lean): `NavierStokes.WaveEnvelopeTransport.copy_unique`, `NavierStokes.WaveEnvelopeTransport.copyEnvelope_path`; [CommonCoverClass](../../NavierStokes/CommonCoverClass.lean): `NavierStokes.CommonCoverClass.sourceArgument_affine`, `NavierStokes.CommonCoverClass.norm_sourceLinear_le`; [scaled control](../../NavierStokes/ScaledActualParticularControl.lean): `NavierStokes.ScaledActualParticularControl.slot_geometry_cost`; [cycle data](../../NavierStokes/ActualParticularCycleData.lean): `NavierStokes.ActualParticularCycleData.native_residual`, `NavierStokes.ActualParticularCycleData.native_source_class`; [stage controls](../../NavierStokes/ActualParticularStageControls.lean): `NavierStokes.ActualParticularStageControls.selected_envelope_eq`; [control](../../NavierStokes/ActualParticularControl.lean): `NavierStokes.ActualParticularControl.source_path_bounds`.

<a id="native-control-projection"></a>
## 6. Project the source without losing its flat factor

For the same frame, forcing coordinates and modal projection are
\[
f_X=-\frac{f_0-\rho\langle K_f,\operatorname{tail}f\rangle}{1+\rho^2},
\quad f_Y=-\langle N_f,\operatorname{tail}f\rangle,\qquad
\Pi f=\tfrac12(f_X+f_Y/H_e,f_X-f_Y/H_e).                       \tag{6.1}
\]
These minus signs implement cancellation. The projection is built from its three columns \(\Pi e_a\), not supplied as an assumed forcing estimate. Normalization involves \(\beta^{-1},\rho,K_f,N_f,(1+\rho^2)^{-1},H_e^{-1}\). Section 3 supplies positive denominator bounds. Smooth reciprocal/normalization maps have bounded derivatives on the resulting compact ranges.

**Higher-order input still unexpanded:** order-zero normal comparison does not imply all-order normal or base jets. The source supplies polynomial jets of the actual phase and base on an open enlarged slot. `NavierStokes.PhaseJetBounds.PhaseFamily.frameData_jets_of_phase_comparison` combines those primitive jets with (2.5); `NavierStokes.PhaseJetBounds.normalGeometry_jets` and `NavierStokes.PhaseJetBounds.FrameJets.forcing` apply normalization and product calculus. This chapter explains those operations but does not reproduce every polynomial witness or compact derivative constant from the summed base. Completing that part requires expanding the all-order phase/base jet suppliers and their composition constants. The following jet conclusions inherit that source-only input; energy (4.2) does not.

**Finite-order dependency ledger (this algebraic stage).**

| Required family | Jet orders needed for an order-\(N\) output |
|---|---|
| Primitive base fields \(F,G\) | Through \(N+1\) |
| Normal, explicit normal motion, shear/frame, coefficient and projection | Through \(N\) |
| Incoming residual | Through \(N\) |
| Joint solution and synthesized amplitude | Through \(N\) |

`NavierStokes.PhaseJetBounds.PhaseFamily.polynomial_jets` uses `hF.directional` and `hG.directional`: first directional derivatives of the base fields therefore consume one additional base order. The all-order supplier absorbs this shift, but its numerical witnesses remain NC-D3 debt. Normal motion is estimated from its explicit formula, not by differentiating a comparison inequality; no additional base-order shift is introduced by that step.

Activity also bounds \(\|\phi\|\le1+2^{4|1/2|}+2^{4|1/2-h|}+2^4\), by applying \(R_a\le2^{4|a|}\) to the diagonal slow map. Transport of a reference jet bound \(CS_0^m\) through order \(N\) costs at most
\(C25^m(\|\phi\|+c_{\max})^NS_b^m\), times any frozen field multiplier. No derivative of band, clock or harmonic occurs. Coefficient jets may depend on the fixed \(j\), via a bound \(|j|+1\).

Let \(C_c,C_p,C_0,C_1\) and \(m_c,m_p,m_0,m_1\) be polynomial witnesses for coefficient, projection and two synthesis columns, after pullback to \((x,v)\). Put
\[
B_{\rm fr}=C_c+C_p+C_0+C_1,\quad q_{\rm fr}=m_c+m_p+m_0+m_1.
\]
Each family is bounded by \(B_{\rm fr}G^{q_{\rm fr}}\). With \(b_c=\Pi(f\circ T_k)\), Leibniz and (5.4) give
\[
\|D^db_c\|\le\sum_{i=0}^d\binom di
 B_{\rm fr}G^{q_{\rm fr}} C_sG^{m_s}wP_c(v)
\le2^NB_{\rm fr}C_sG^{q_{\rm fr}+m_s}wP_c(v).
\]
Thus the literal common choices are
\[
C_{\rm in}=B_{\rm fr}+2^NB_{\rm fr}C_s,\qquad m=q_{\rm fr}+m_s. \tag{6.2}
\]
Coefficient and synthesis jets have bound \(C_{\rm in}G^m\); only forcing has the additional \(wP_c(v)\). This reconstructs the affine/Leibniz producer, conditional only on the explicitly located higher-order inputs, not on already-projected jets.

**Source trail.** [PhaseJetBounds](../../NavierStokes/PhaseJetBounds.lean), declarations just named; [ActualParticularControl](../../NavierStokes/ActualParticularControl.lean): `NavierStokes.ActualParticularControl.frame_forcingLinear_jets`, `NavierStokes.ActualParticularControl.transported_frame_jets`, `NavierStokes.ActualParticularControl.frame_input_jets`.

<a id="native-control-joint"></a>
## 7. Recover the exact joint parameter/endpoint estimate

Now solve \(y'=A_{c,j}y+b_c,\ y(0)=0\). Choose, before the copy and point,
\[
K=C_{\rm in}+K_{\rm ctl}+1\ge1,\qquad S=G.
\]
Sections 4–6 supply \(L_c\le KS\), \(e^{\mu_cL_c}\le K\), and through order \(N\),
\(\|D^dA_c\|\le KS^m\), \(\|D^db_c\|\le wKS^mP_c\).
Smoothness on an open parameter neighborhood times an open interval containing \([0,L_c]\) is supplied separately by the smooth frame/source construction, not by the indicator envelope.

Here is why the numerical constant has its particular form. For a general smooth parameter family \(u'=Au+f\) on \([a,a+\ell]\), with \(\ell,\mu,X,F_0,M\ge0\) and positive \(W\), divide by \(W(t)e^{\mu(t-a)}\), where \(W'=rW\). The quadratic-form bound makes the transformed homogeneous operator dissipative. The norm differential inequality (regularized at zeros) implies
\[
|u(t)|\le C(X+\ell F_0)W(t)
\]
if \(e^{\mu\ell}\le C\), \(|u(a)|\le XW(a)\), \(|f|\le F_0W\). There is no inverse-propagator loss.

For the parameter-jet induction, assume explicitly, at the parameter under estimation and for every \(0\le d\le N\) and \(t\in[a,a+\ell]\),
\[
\|D_p^d u_0(p)\|\le XW(a),\qquad
\|D_p^d f(p,t)\|\le F_0W(t),\qquad
\|D_p^d A(p,t)\|\le M,
\quad u_0(p)=u(p,a).
\]
The initial-data and forcing assumptions hold at **every order**, not just at order zero; these are `hxj` and `hfj` in `NavierStokes.WeightedODEJets.norm_jet_solution_le`. Smoothness on an open parameter neighborhood justifies the derivatives. A value bound on \(u_0\) alone cannot control its parameter jets.

Differentiate the constructed Volterra equation. For an ordered set of \(d\) directions,
\[
u_{[d]}'=Au_{[d]}+f_{[d]}
 +\sum_{\varnothing\ne I\subseteq[d]} A_Iu_{I^c}.
\]
Every solution derivative on the right has smaller order. Bounded linear integration commutes with differentiation; uniqueness identifies this variational solution with the derivative. With coefficient jets bounded by \(M\), induction gives
\[
\|D^du\|\le B R^dW,\qquad
B=C(X+\ell F_0),\quad R=1+C\ell2^NM.
\]
Indeed the next source costs \(F_0+2^NMBR^d\), and
\(C[X+\ell(F_0+2^NMBR^d)]\le BR^{d+1}\).
Unit-direction estimates give the full multilinear norm without a dimension factor.

In the actual application the initial family is **identically zero**, so all initial jets vanish (also after terminal-time rescaling); §§5–6 supply every forcing jet through \(N\). We may therefore use the harmless common upper bound \(X=F_0\), rather than the sharper \(X=0\). Take \(C=K,M=KS^m,X=F_0=wKS^m,\ell\le KS\), with \(S,K\ge1\). Then
\[
B\le w(2^{N+1}K^3)S^{m+1},\qquad
R\le(2^{N+1}K^3)S^{m+1},
\]
so the fixed-interval parameter estimate is
\(w(2^{N+1}K^3)^{d+1}S^{(m+1)(d+1)}W\).

To include the terminal time as a parameter, fix \(t\in[0,L_c]\) and use \(v=\tau t\), \(0\le\tau\le1\):
\[
\widetilde A((x,t),\tau)=tA_c(x,\tau t),\qquad
\widetilde b((x,t),\tau)=tb_c(x,\tau t).
\]
The linear map \((x,t)\mapsto(x,\tau t)\) is contractive in the product/max norm. Differentiating the prefactor is essential; for instance
\(\partial_t[tA_c(x,\tau t)]=A_c+\tau t\partial_vA_c\).
Leibniz gives the uniform bound \(2^N(KS)(KS^m)\). Thus define exactly
\[
K'=\operatorname{rescaleConstant}(N,K)=2^NK^2+K+1.
\]
The rescaled input exponent is \(m+1\). The rescaled weight is \(P_c(\tau t)\), rate \(tc_tr(c_t\tau t)\), error \(t\mu_c\); since \(t\ge0\), energy transports with the correct inequality sign and \(e^{t\mu_c}\le K'\).

The preimage of the open smoothness domain under \(((x,t),\tau)\mapsto(x,\tau t)\) contains \(\{(x,t)\}\times[0,1]\). Compactness gives an open product tube around this segment. Hence the unit-interval solution is genuinely jointly smooth in \((x,t)\), **including at \(t=0,L_c\)**. Applying the preceding induction on \([0,1]\) with \(K',m+1\) yields exactly
\[
\boxed{\ \|D^dy(x,t)\|\le
w\left[2^{N+1}\operatorname{rescaleConstant}(N,K)^3\right]^{d+1}
G^{(m+2)(d+1)}P_c(t),\qquad d\le N.\ }                        \tag{7.1}
\]
This is the numerical bound, not merely weighted-class membership. Strictly, \(y\) here is the smooth `JointODE.reparamSolution` representative. Uniqueness identifies its values with the original zero-entry solution on the closed interval. Equality there does not identify endpoint jets of an arbitrary clamped extension; the subsequent current-copy jet argument uses an **interior germ**.

**Source trail.** [WeightedODEJets](../../NavierStokes/WeightedODEJets.lean): `NavierStokes.WeightedODEJets.jet_solution_eq_solution`, `NavierStokes.WeightedODEJets.norm_iteratedFDeriv_odeFamily_le_polynomial`; [PrimaryPulseBounds](../../NavierStokes/PrimaryPulseBounds.lean): `NavierStokes.PrimaryPulseBounds.rescaleConstant`; [ParticularWaveBounds](../../NavierStokes/ParticularWaveBounds.lean): `NavierStokes.ParticularWaveBounds.forced_joint_jet_bound`; [JointODE](../../NavierStokes/JointODE.lean): `NavierStokes.JointODE.reparamSolution_eq_actualSolution`. These existing ODE layers need no replacement framework.

<a id="native-control-output"></a>
## 8. Current endpoint, both complex components, and pressure

For this same copy, the current endpoint is \(t_k(x)=(g.\mathrm{coordinates}_kY).2\in(0,L_c)\) on the native patch. Synthesis is
\[
a_{\rm amb}=(X,-\rho XK_f+YN_f),\quad X=y_++y_-,\quad Y=H_e(y_+-y_-).
\]
Orthonormality gives
\[
|a_{\rm amb}|^2=(1+\rho^2)X^2+Y^2
\le2\max(1+\rho^2,H_e^2)|y|^2.
\]
The two columns are \((1,-\rho K_f\pm H_eN_f)\); their jets, not just their values, were included in (6.2). The source's synthesis constant is
\(C_{\rm amb}(N)=2^N(\|\mathrm{proj}_0\|+\|\mathrm{proj}_1\|)=2^{N+1}\).
The affine endpoint map \(J_k(x)=(x,t_k(x))\) has derivative norm at most \(\mathcal A(g)\); translations in \(k\) cost nothing. Write \(\mathcal B=2^{N+1}\operatorname{rescaleConstant}(N,K)^3\). The literal downstream majorant is
\[
\|D^da_{\rm copy}(x)\|\le
 C_{\rm amb}(N)\,[w\mathcal B^{N+1}G^{(m+2)(N+1)}P_c(t_k(x))]
 (KG^m)\mathcal A(g)^d.                                      \tag{8.1}
\]
Using \(\mathcal A(g)\le K_{\rm ctl}G^2\), a common constant and degree through order \(N\) are
\[
C_{\rm amb}(N)\mathcal B^{N+1}K K_{\rm ctl}^N,
\qquad (m+2)(N+1)+m+2N.
\]

Real and imaginary extraction from \(\mathbb C^3_\infty\) into \(\mathbb R^3_2\) each cost at most \(\sqrt3\); enlarge the incoming constants accordingly. Two real solves use the **same** geometry, normal and matrix, with their respective sources. Complexification into the sup norm and multiplication by \(i\) cost at most one, and addition costs the sum of the two estimates. No Euclidean/sup norm equality is used.

For one real source let \(n=N_c\). The projected ambient equation is
\[
a'=-K_{\rm act}a+
 \frac{\langle n,K_{\rm act}a\rangle-\langle\dot n,a\rangle}{|n|^2}n
 -d_ja-\Pi_nf.
\]
It implies \((\langle n,a\rangle)'=-d_j\langle n,a\rangle\), so zero entry preserves tangency. Define
\[
c_p=\frac{\langle n,K_{\rm act}a\rangle-\langle\dot n,a\rangle+
 \langle n,f\rangle}{|n|^2},\quad
\pi=ic_p/\omega,\qquad \omega=j\,\mathrm{carrier}(h,b)\ne0.
\]
Then \(i\omega n\pi=-c_pn\) and
\[
a'+K_{\rm act}a+d_ja+i\omega n\pi=-f.                         \tag{8.2}
\]
This is native principal cancellation, not vanishing of every localized nonlinear error. Recombination is
\(a=a_R+ia_I\), \(\pi=\pi_R+i\pi_I=(-c_I+ic_R)/\omega\).
Each real-source pressure already contains \(i/\omega\); the subscripts are not the final pressure's real and imaginary values.

For pressure jets the same positive normal bounds are
\[
\mathrm{normal.lower}\,F_*.b\le|n|\le
\mathrm{normal.upper}(M_*^2+3M_*),\qquad
F_*.b=\min(b_0/2,1/M_0)>0.
\]
The numerator has weight \(wP_c\) by Leibniz using amplitude/source jets and unweighted normal/action/motion jets. For \(q_n=|n|^2\), differentiating \(q_nq_n^{-1}=1\) gives a triangular recurrence
\[
D^d(q_n^{-1})=-q_n^{-1}
 \sum_{\varnothing\ne I\subseteq[d]}D_Iq_n\,D_{I^c}(q_n^{-1}).
\]
The positive lower bound controls its denominators, so division preserves the single weighted factor.

**Pressure input still source-only:** polynomial normal/action jets inherit §6's debt. The inverse-frequency band estimate supplies a further \(\epsilon^{1/2}\) gain, but its numerical producer is not expanded here. Completing a fully numerical pressure bound requires expanding both `normalInverse_unweighted` and `harmonic_inverse_bandBound` with their constants. The recovered pressure conclusion is therefore the source's **class-level** conclusion: velocity exponent \(\alpha=1/2+\sigma\), pressure exponent \(\alpha+1/2=1+\sigma\), conditional on these named inputs. It is not a new explicit pressure analogue of (7.1).

Finally, (5.2), (5.4), and (7.1) include the closed integration ends. Smoothness comes from an open neighborhood, not the rectangle indicator. Where the weighted class is valid and \(w=0\), its all-jet inequalities force those derivatives to vanish. A radial boundary outside that open domain requires a separate continuity/support extension argument; no global flat extension, nor extension through the physical NS singular time, is inferred here.

**Source trail.** [ParticularWaveBounds](../../NavierStokes/ParticularWaveBounds.lean): `NavierStokes.ParticularWaveBounds.copySolve_jet_bound_from_modal`, `NavierStokes.ParticularWaveBounds.pressureCoefficient_class`, `NavierStokes.ParticularWaveBounds.pressure_class`; [ParticularCopyBounds](../../NavierStokes/ParticularCopyBounds.lean): `NavierStokes.ParticularCopyBounds.uniform_coefficients_jets`; [TangentProjection](../../NavierStokes/TangentProjection.lean): `NavierStokes.TangentProjection.normal_projectedRhs`, `NavierStokes.TangentProjection.pressure_cancellation`, `NavierStokes.TangentProjection.complex_pressure_sign`; [ScaledParticularFrameJets](../../NavierStokes/ScaledParticularFrameJets.lean): `NavierStokes.ScaledParticularFrameJets.native_normal_bounds`; [CurlClassBounds](../../NavierStokes/CurlClassBounds.lean): `NavierStokes.CurlClassBounds.normalInverse_unweighted`; [UniformPrimaryWeights](../../NavierStokes/UniformPrimaryWeights.lean): `NavierStokes.UniformPrimaryWeights.harmonic_inverse_bandBound`; [stage controls](../../NavierStokes/ActualParticularStageControls.lean): `NavierStokes.ActualParticularStageControls.selected_inverse_frequency`, `NavierStokes.ActualParticularStageControls.selected_raw_jets`.

## What this has and has not supplied

The displayed producer calculations turn primitive mesh/base/cone inputs into normal comparison, signed moving-frame errors, two-sided damping comparison and all-harmonic energy. Actual slot separation then turns the incoming **all-jet** residual invariant into full-path forcing bounds without differentiating a flat majorant. The clock and endpoint rescalings recover the exact numerical modal theorem and its ambient affine loss.

This narrows the particular-wave portion of OBL-NSC-004; it does not close it. Summed-profile preparation, all-order primitive jet production, fully numerical inverse-normal/frequency estimates, boundary extension and the rest of the native correction cycle remain explicit debt. In particular, the **entire producer has not been independently reconstructed** merely because the control record now has an explanation. See the [claim/source/obligation ledger](native-control-validation.md).
