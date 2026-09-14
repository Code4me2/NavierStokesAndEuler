# Timing response — concise calculation

**Provisional pending adversarial audit.** Human analysis using the selected inputs and evidence boundary in [OVERVIEW.md](OVERVIEW.md); no Lean validation. All identities below first hold on a fixed compact presingular slab. No endpoint limit is assumed.

## 1. Signs, evolution and duality

Use the complete selected periodic fields, viscosity one, and
\[
F=U_t-\Delta U+N,\quad N=\mathbb P(U\cdot\nabla U),\quad
Gv=\Delta v-\mathbb P(U\cdot\nabla v+v\cdot\nabla U),\quad
L_U=\partial_t-G.
\]
Spatial Leray commutes with time differentiation, so
\[
L_UU=U_t-\Delta U+2N=F+N,\qquad L_UY=F_t,\quad Y=U_t.
\]
For unforced \(v=U-w\), expanding its quadratic term gives
\[
0=F-L_Uw+\mathbb P(w\cdot\nabla w),
\]
fixing the deletion-source sign as positive.

On divergence-free \(H^4(\mathbb T^3)\), the smooth finite-slab coefficients have bounded spatial derivative norms; convection maps \(H^4\) into \(H^3\). The diffusion energy estimate with one derivative absorbed yields evolution \(\Phi\), with constants depending on the slab. Its generator is unbounded on \(H^4\); equations are understood on smooth data or in weaker spaces. Point evaluation is in the distributional dual \(H^{-4}\).

For \(\kappa_Tv=q_T^{A+1}v_2(0)/(Aj_*)\), set \(\beta_T(s)=\Phi(T,s)^*\kappa_T\), where the star denotes duality, not an \(H^4\) Riesz representation. Then
\[
-\partial_s\beta_T=G^*\beta_T,
\quad
G^*b=\Delta b+\mathbb P(U\cdot\nabla b)-\mathbb P((\nabla U)^Tb).
\]
For smooth \(H\),
\[
\frac{d}{ds}\langle\beta_T,H\rangle=\langle\beta_T,L_UH\rangle.
\]
This proves all Duhamel pairings by integration, or smooth terminal approximation. In the alternative convention \(L_U=\partial_t+B\), \(B=-G\), the same adjoint equation is \(-\partial_s\beta_T+B^*\beta_T=0\): the two supplied drafts have consistent signs.

## 2. Amplitude–time identity including the seed

Set \(d=t-t_0\), \(H=U+dY\). Then
\[
L_UH=F+N+Y+dF_t=2F+\Delta U+dF_t.
\]
To check independently, put \(\theta_\lambda=t_0+\lambda d\), \(V_\lambda=\lambda U(\theta_\lambda)\), \(p_\lambda=\lambda^2p(\theta_\lambda)\). Temporal derivative, convection and pressure acquire \(\lambda^2\); diffusion acquires only \(\lambda\). Thus
\[
R(V_\lambda,p_\lambda)
=\lambda^2[U_t+U\cdot\nabla U+\nabla p-\Delta U](\theta_\lambda)
+(\lambda^2-\lambda)\Delta U(\theta_\lambda).
\]
Differentiating at one and projecting proves the same formula. This parameter variation is legitimate near one on each finite slab, not uniformly up to the singular endpoint.

Since \(H(t_0)=U(t_0)\), Duhamel gives
\[
H(T)-\Phi(T,t_0)U(t_0)
=2z(T)+\int_{t_0}^T\Phi(T,s)(\Delta U+d_sF_t)ds.
\]
The axis gives \(\kappa_TU(T)=q_T/A\), \(\kappa_TY(T)=1\). Therefore
\[
2\alpha(T)=d_T+q_T/A-\mathcal C_T,
\quad
\mathcal C_T=\langle\beta_T(t_0),U(t_0)\rangle+
\int_{t_0}^T\langle\beta_T,\Delta U+d_sF_t\rangle ds.
\]
It is the total signed correlation, not separate absolute estimates, that determines the diagnostic. At \(T=t_0\) the formula vanishes exactly. Although the explicit \(N\) source is gone, its linearization remains in \(\Phi\). No new uniform bound follows from this algebra.

## 3. Gauge calculation and conditional bound

For a time scalar \(a\), spatial operators commute with multiplication by \(a(t)\), hence
\[
L_U(aY)=(aY)_t-aGY=a'Y+a(Y_t-GY)=a'Y+aF_t.
\]
With \(\psi=Y/\|Y\|_2^2\), \(z=aY+r\), \(\langle\psi,r\rangle=0\), differentiating the last identity and using \(r_t=Gr+F-a'Y-aF_t\) gives
\[
a'=\langle\psi,F-aF_t\rangle+\langle\psi'+G^*\psi,r\rangle.
\]
This is not a closed scalar equation for the actual gauge coefficient.

If, additionally, \(r\equiv0\), the full-space condition is \(F=a'Y+aF_t\). At the axis put
\[
g=F_2(t,0)/Y_2(t,0),\qquad k=(F_t)_2(t,0)/Y_2(t,0).
\]
Then \(a'+ka=g\), \(a(t_0)=0\), and
\[
a(t)=\int_{t_0}^t\exp\!\left(-\int_s^t k(r)dr\right)g(s)ds.
\]
Selected global force smoothness and periodicity give bounded \(F,F_t\) in \(H^4\) on a fixed closed terminal window. Thus for a fixed \(K\), independent of a later choice of restart,
\[
|g(t)|+|k(t)|\le Kq_t^{A+1},\qquad
|a(t)|\le e^{K\delta^{A+2}/(A+2)}\frac{K\delta^{A+2}}{A+2}.
\]
This is a necessary bound for a hypothetically exact pure timing response. It proves neither collinearity nor actual-response smallness. In particular it cannot discard the \(r\)-correlation above.

## 4. Exact nonlinear clock; pressure adjudication

For \(W=U\circ\theta\), \(P_\theta=p\circ\theta\),
\[
R(W,P_\theta)=f(\theta)+(\theta'-1)Y(\theta).
\]
Subtracting the unforced equation for \(v=W-e\) gives, before projection,
\[
e_t-\Delta e+W\cdot\nabla e+e\cdot\nabla W
+\nabla(P_\theta-p_v)
=f(\theta)+(\theta'-1)Y(\theta)+e\cdot\nabla e.
\]
The total pressure difference here is **not merely the linear response pressure**. After projection the linear part can equivalently be represented with
\[
\pi_{\rm lin}=-\Delta^{-1}\operatorname{div}(W\cdot\nabla e+e\cdot\nabla W),
\]
while both source and quadratic term on the right are projected. This resolves the potentially ambiguous pressure wording in the supplied drafts.

For \(\theta=t-a(t)\), the projected defect has first variation
\[
F(\theta)+(\theta'-1)Y(\theta)=F-aF_t-a'Y+\text{higher-order terms}
\]
on finite slabs only. It agrees with the gauge equation, and keeps both derivative terms. The seed is zero if \(a(t_0)=0\); otherwise it is \(U(t_0-a(t_0))-U(t_0)\).

Exact clock absorption requires \(F(\theta)+(\theta'-1)Y(\theta)=0\) as a field. Canceling only its axial value leaves
\[
F(\theta)-\frac{F_2(\theta,0)}{Y_2(\theta,0)}Y(\theta).
\]
No supplied identity makes this remainder zero or certifies it nonzero. Neither linear diagnostic growth nor failure of an unmodulated approximation resolves nonlinear survival of blowup.
