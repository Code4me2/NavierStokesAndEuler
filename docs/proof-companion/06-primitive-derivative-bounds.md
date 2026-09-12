# 06 — Primitive derivative bounds for the selected native producer

Chapter 05 explains why a particular wave can be solved with its flat weight intact. Two ingredients there remained opaque: derivatives of the **summed** background, and derivatives of the frame obtained by normalizing its phase normal. Smoothness alone does not give constants uniform over bands. Nor does closeness of two normals control their derivatives. This chapter supplies those numerical producers, then returns their output to the [projection](05-native-weighted-control.md#native-control-projection) and [pressure](05-native-weighted-control.md#native-control-output) calculations of chapter 05.

The mechanism has three parts. A single diagonal schedule absorbs the growth of individual coefficient derivatives; a finite head preserves the full small power lost by a crude tail estimate. A frozen dilation then prevents an artificial inverse-band loss. Finally, a positive **tail-normal** bound permits a finite reciprocal/product calculation for the actual moving frame. Nothing requires analytic or Gevrey growth in derivative order.

**Evidence.** Baseline `26e896edbdbe1215c0d50ddba24b2b6453646f5f`. This is an integrated prose derivation using the supplied PD-A/PD-B reports and additional author source-body checks, not an independent final review or a Lean check. The [separate validation ledger](primitive-derivative-validation.md) records exact-file source anchors, assumptions and outstanding gates. Chapter 05 and its historical ledger/plan are preserved unchanged; statements about their former debt remain historical. The requested filename here supersedes the different reservation in the unchanged [primitive plan](primitive-derivative-plan.md).

<a id="primitive-interface"></a>
## 1. The fixed witness and the statement we will produce

Fix the same selected outgoing profile, nominal certificate `H`, solved finite modulation `v`, budget \(B_{\rm bud}\), initializer threshold \(N_0\), and slot system as chapter 05. Put
\[
0<h<\tfrac12,\quad A=\tfrac12+h,\quad D_h=\tfrac12-h,\quad C_{\rm axis}>0,
\qquad d=\operatorname{FinalSlowBase.coefficients}(H,v),
\]
\[
\mathbf a=\operatorname{FinalSlowBase.scales}(H,v,\mathrm{upper},B_{\rm bud}).
\]
The bold \(\mathbf a\) is the Borel schedule, not the preparation \(a\). Neither is reselected when a derivative order is requested. Write \(l=\mathrm{activeLeft}>0\), \(u=\mathrm{activeRight}>l\), and use \(u_{\rm slope}\), not \(u\), for the preparation's slope parameter.

**Finite-coefficient input at first use.** We take the already selected finite profile and its identities as source inputs, including ambient smoothness of each aligned coefficient (also at \(\eta=\pm1\)). For every stress order \(j\ge2\), its two components have radial support in a coefficient-dependent compact interval strictly inside the active annulus, for all parameter values. This is stronger than support only on the closed parameter strip and is the input needed for the smooth quotient in §3. Individual compact derivative suprema may be used only for these specified smooth functions. No summed-field estimate is assumed. The finite-profile positivity, true cone and oriented edge certificates are stated at their separate use in §6; their upstream construction is not rederived.

For a slow point \(p=(R,(Z,T))\), the normalized chart is
\[
\rho-Z^2\rho^{2h}=T,\qquad X=R^2/(2\rho),\qquad \eta=Z\rho^{-D_h}.
\tag{1.1}
\]
Here \(T>0\) is backward time, not physical time. Above a single geometric threshold, the actual enlarged positive-time cells have
\[
R\ge r_*:=\sqrt l/2,\quad \|p\|_{\max}\le M_{\rm cell}:=\max(2\sqrt u+1,3),
\quad \tfrac14<\rho<4,\quad l/2<X<2u,\quad |\eta|<1.
\tag{1.2}
\]
Section 6 proves these ranges eventually without assuming chart jets. Their validity on the entire label domain of the actual classically selected preparation is an unresolved bridge; estimates (1.4) and their numerical downstream applications are conditional on that bridge, not on a silent further restriction of labels. Throughout the base estimates we also require \(4Q_b\le1\), imposed once, not at each derivative order.

The literal normalized frequency and axial field are
\[
F_b(p)=\frac{\rho^{-A}}R\frac{\sqrt{2X}}{C_{\rm axis}}
 \operatorname{slowSum}_{\mathbf a,h}(d_\phi)(Q_b\rho,X,\eta),
\qquad
G_b(p)=\rho^{-A}\operatorname{slowSum}_{\mathbf a,h}(d_{\rm axial})(Q_b\rho,X,\eta).
\tag{1.3}
\]
Their reference fields replace each sum by its zeroth coefficient. We prove, for every order \(n\), fixed finite nonnegative numbers
\[
\begin{split}
\|D^nF_{\rm ref}\|&\le L^F_n,&\|D^nG_{\rm ref}\|&\le L^G_n,\\
\|D^n(F_b-F_{\rm ref})\|&\le E^F_nQ_b^{2h},&
\|D^n(G_b-G_{\rm ref})\|&\le E^G_nQ_b^{2h}.
\end{split}
\tag{1.4}
\]
Thus \(f_n=L^F_n+E^F_n\), \(g_n=L^G_n+E^G_n\) bound the actual fields uniformly on those cells. These arrays have **band degree zero**. Constants depend on the fixed profile and order, not band, cell, sign or copy. All-order means \(\forall N\,\exists\) finite constants through \(N\), not one constant for every derivative order.

**Why these are the actual fields.** At positive scale, one finite sum works for every inner point \((X,\eta)\): the cutoff weights depend only on the summation coordinate. Differentiation in \(X\) therefore commutes with that finite sum. To see the curl identification explicitly, let \(q>0\) be the physical similarity scale, \(s\) the physical squared radius divided by two, and \(X=s/q\). At fixed physical time and axial coordinate, \(q,\eta\) are independent of \(s\). Write \(\mathscr P f\) for the radial primitive, with \(\partial_X\mathscr P f=f\) and \(X\operatorname{average}f=\mathscr P f\). The integrated stream and swirl potential are respectively
\[
sH=q^{1-A}\operatorname{slowSum}(\mathscr P d_{\rm axial}),\qquad
\mathcal A_\theta=-C_{\rm axis}^{-1}q^{1/2-A}\operatorname{slowSum}(\mathscr P d_\phi).
\]
Their radial derivatives give
\[
u_z=\partial_s(sH)=q^{-A}\operatorname{slowSum}(d_{\rm axial}),\qquad
u_\theta=-\sqrt{2s}\,\partial_s\mathcal A_\theta
=q^{-A}\frac{\sqrt{2X}}{C_{\rm axis}}\operatorname{slowSum}(d_\phi).
\]
These are actual curl components, not merely membership in the same estimate class. At the physical band point
\[
(1-Q_bT,(\sqrt{Q_b}R,0,Q_b^{D_h}Z))
\]
the similarity coordinates are \((Q_b\rho,X,\eta)\), and
\(Q_b^A(Q_b\rho)^{-A}=\rho^{-A}\). This gives (1.3): frequency is normalized angular velocity **divided by \(R\)**. That factor cannot be dropped before using \(X=R^2/(2\rho)\).

The source identity spine is `FinalSlowBase` → `BaseChartJets` → `PrimaryGeometryAssembly` → `PrimaryTargetBounds` → `CorrectionInitialization.ActualPrimary.choice`. The later `selectedConstruction` only reindexes those phase fields. [Exact suppliers](primitive-derivative-validation.md#primitive-source-identity) and §6 distinguish defined restrictions from classical selection.

<a id="primitive-calculus"></a>
## 2. A finite calculus for constants

All derivatives are full real Fréchet multilinear operator norms. Parameter products carry max norms; real modal and ambient spaces carry Euclidean norms; complex ambient vectors carry the componentwise sup norm. A coordinate projection is contractive in the appropriate norm, but assembly into Euclidean space is bounded by the **sum** of coordinate bounds. We never identify these different norms.

For nonnegative derivative arrays define
\[
(P\star Q)_n=\sum_{i=0}^n\binom niP_iQ_{n-i},\qquad [c]=(c,0,0,\ldots).
\tag{2.1}
\]
This bounds products, inner products, scalar-vector multiplication and operator application, whose bilinear norms are at most one. A bilinear norm \(L\) costs \(L(P\star Q)\). Indeed the ordered-direction Leibniz formula has one term per subset of the differentiated directions; subsets of size \(i\) number \(\binom ni\). Taking the supremum over unit directions proves the full operator estimate. Assembling an operator from Euclidean basis columns costs the sum of their bounds.

For composition, for \(n\ge1\), put
\[
\operatorname{Comp}(H,P)_n
 =\sum_{\pi\in\operatorname{Part}([n])}H_{|\pi|}\prod_{B\in\pi}P_{|B|}.
\tag{2.2}
\]
Order zero is the outer range bound \(H_0\), supplied separately. Differentiating a partition term either creates a singleton block or joins an existing block; induction gives exactly (2.2), with no missing multiindex factors. An affine map of linear norm \(L\) costs only \(L^n\).

If \(|q|\ge b>0\) and \(P_n\) bounds \(D^nq\), define
\[
\mathcal I_b(P)_0=b^{-1},\qquad
\mathcal I_b(P)_n=b^{-1}\sum_{i=1}^n\binom niP_i\mathcal I_b(P)_{n-i}.
\tag{2.3}
\]
Differentiate \(q q^{-1}=1\), isolate the term without a derivative on \(q\), and divide by \(q\). Induction proves (2.3); \(q\) need not be positive. For \(x\in[a,b]\), \(a>0\), power derivatives have bounds
\[
H_{\gamma,n}=|\gamma_{\underline n}|\max(a^{\gamma-n},b^{\gamma-n}),
\quad \gamma_{\underline0}=1.
\tag{2.4}
\]
Together (2.2) and (2.4) produce square roots and inverse square roots. Negative powers need no upper endpoint. These recurrences replace unexplained compact normalization constants; they are not claims that Lean's noncomputable constants have these literal values. [Calculus source correspondence](primitive-derivative-validation.md#primitive-source-calculus).

<a id="primitive-sum"></a>
## 3. Individual coefficients, one schedule, full small-power recovery

### The only compact seminorms used at this stage

For a smooth individual coefficient \(f_j\), write \(w=(X,\eta)\) and
\[
U_j(r,w)=\chi(a_jr)r^{2hj}f_j(w)\quad(j\ge1),\qquad U_0=0,
\quad \operatorname{slowSum}(r,w)=f_0(w)+\sum_{j\ge1}U_j(r,w).
\]
The fixed smooth cutoff is supported in \([-1,1]\) and equals one near zero. The auxiliary power
\(\operatorname{localPower}_\gamma(s)=\chi(4(s-1))s^\gamma\)
is globally smooth: its cutoff vanishes on a neighborhood of every nonpositive \(s\), and it agrees with \(s^\gamma\) near one. For a fixed compact inner set \(K\), form the explicit joint template
\[
\mathcal T_j(c,s,w)=\chi(cs)\operatorname{localPower}_{2hj}(s)f_j(w),\qquad
T_{j,n}=1+\sup_{[0,1]\times\{1\}\times K}\|D^n\mathcal T_j\|.
\tag{3.1}
\]
This is a finite number by continuity of derivatives of this **individual** ambient smooth function on a compact set. Restricting to the \((s,w)\) directions costs at most one in max norm.

Freeze \(r>0\), and let \(\mathfrak D^nU_j(r,w)\) mean the derivative of \((s,w')\mapsto U_j(rs,w')\) at \((1,w)\). If \(a_jr\le1\), the germ at that point is
\[
U_j(rs,w')=r^{2hj}\mathcal T_j(a_jr,s,w').
\]
Consequently
\[
\|\mathfrak D^nU_j\|\le T_{j,n}r^{2hj},\qquad
\|D^nU_j(r,w)\|\le T_{j,n}r^{2hj-n}\quad(0<r\le1).
\tag{3.2}
\]
The second estimate uses the inverse linear dilation of norm \(r^{-1}\). If \(a_jr>1\), the stage vanishes on an **open germ**, so every jet vanishes. At equality use (3.1), not an open-zero assertion.

### The actual enlarged bundle, not a second Borel choice

The selected schedule controls the function/sup-norm seven-component bundle
\[
\bigl(\operatorname{average}d_{{\rm axial},j},
 -C_{\rm axis}^{-1}\operatorname{primitive}d_{\phi,j},
 d_{{\rm pressure},j},d_{\theta\text{-stress},j},d_{z\text{-stress},j},
 d_{{\rm axial},j},d_{\phi,j}\bigr),
\]
paired, in max norm, with
\[
H_j=0\ (j\le1),\qquad
H_j=\zeta^{-1}(d_{\theta\text{-stress},j},d_{z\text{-stress},j})\ (j\ge2).
\tag{3.3}
\]
Its scheduling compact is \([0,\operatorname{boxRadius}]\times[-1,1]\). By the support assumption in §1, each higher numerator vanishes on neighborhoods of the radial edges and exterior. Inside the active region \(\zeta>0\), so its quotient is smooth; on those other neighborhoods the total quotient is zero. This proves ambient smoothness of (3.3). Flatness of \(\zeta\) alone would not prove it.

Projection to the first bundle and then coordinates 5 (axial) and 6 (\(\phi\)) is contractive. There is no factor seven or \(\sqrt7\), and no new schedule. `FinalSlowBase.scales_admissible_on` restricts precisely this schedule to \(K=[l/2,2u]\times[-1,1]\), using \(2u\le\operatorname{boxRadius}\).

**Existence witness versus selection.** A witness constructed inside an existence proof, a classically selected object, and the properties exported for that object are distinct. `Classical.choose` supplies the existential specification, not equality with the proof's exhibited witness. Even proofs of \(\exists n:\mathbb N,\mathrm{True}\) exhibiting different integers do not identify the selected integer with either exhibit.

Here is the numerical construction **proving existence**. For template witnesses of the enlarged bundle at stage \(j\ge1\), finitely many conditions
\[
T^{\mathcal W}_{j,n}r^{hj}\le2^{-j},\qquad n\le j+2,
\quad 0<r\le1/b_j
\tag{3.4}
\]
are imposed. A sufficient local integer would exceed
\[
\max\left(1,\max_{n\le j+2}(2^jT^{\mathcal W}_{j,n})^{1/(hj)}\right).
\]
Inside the existence proof, the source chooses small-interval integer witnesses, then takes
\(\widehat a_0=\max(1,b_0)\), \(\widehat a_{j+1}=\max(b_{j+1},2\widehat a_j)\), incorporating the initial budget at zero. These ceilings illustrate a sufficient construction of \(\widehat{\mathbf a}\), not an identity for the selected \(\mathbf a\). Multiplying (3.2) by the absorption bound (3.4) on \(r\le1/\widehat a_j\le1/b_j\), and using the zero germ off support, proves `ordinary` and `blown` for the existence witness.

**Transfer by specification.** `EntranceAlignedBase.scales_spec` certifies budget and `AdmissibleScales` for the actual \(\mathbf a\). Contractive bundle projections and `FinalSlowBase.scales_admissible_on` transfer that specification to the two components and smaller compact. Its `blown` and `ordinary` fields give, for \(0<r\le1\), \(j\ge1\),
\[
\|\mathfrak D^nU_j\|\le2^{-j}r^{hj},\qquad
\|D^nU_j\|\le2^{-j}r^{hj-n},\qquad n\le j+2.
\tag{3.5}
\]
Thus (3.5) holds for every admissible schedule, including the selected one. The preceding construction explains the proof producing admissibility; transfer uses its certified specification. No internal template constants, absorption constraints (3.4), or envelope identity are asserted for the selected schedule. For the finite head, any valid (3.1) constants work.

### Why differentiation is legitimate, and why the head matters

At any \(r_0>0\), take a neighborhood with \(r>r_0/2\). Since the doubling schedule tends to infinity, all sufficiently large stages vanish throughout that neighborhood. The series is locally a finite sum. Thus every finite derivative commutes with summation by finite-sum differentiation; no interchange at \(r=0\) is being claimed.

For requested order \(n\), split at \(J=\max(n,1)\). The head keeps its full exponent: \(r^{2hj}\le r^{2h}\) for \(j\ge1\), \(r\le1\). In the tail, \(n\le j+2\), and
\[
\sum_{j>J}2^{-j}r^{hj}
 \le2^{-J}r^{h(J+1)}\le2^{-J}r^{2h}.
\]
Therefore
\[
\boxed{\ \|\mathfrak D^n(\operatorname{slowSum}-f_0)\|
 \le E_nr^{2h},\qquad E_n=\sum_{j=0}^{J}T_{j,n}+2^{-J}.\ }
\tag{3.6}
\]
The positive stage-zero template constant is harmless since that stage is zero. Estimating every stage by (3.5) from the start would lose the first stage's full \(2h\) power.

For \(v(X)=\sqrt{2X}/C_{\rm axis}\), (2.4) gives
\[
V_n=\frac{\sqrt2}{C_{\rm axis}}|(1/2)_{\underline n}|
 \max((l/2)^{1/2-n},(2u)^{1/2-n}).
\]
The normalized swirl correction has array \(E^{\rm sw}=V\star E^\phi\); the axial correction has \(E^{\rm ax}\). These are the inputs to §5. [Source bodies for this entire sum calculation](primitive-derivative-validation.md#primitive-source-sum).

<a id="primitive-chart"></a>
## 4. Derivatives of the actual stable inverse chart

An inverse function theorem supplies a smooth branch, but not numerical jet constants. We now compute them. Set \(\alpha_h=2h\in(0,1)\), \(D_h=(1-\alpha_h)/2\). In forward coordinates \(y=(r,(s,z))\), the map to backward-time coordinates is
\[
\Psi(y)=(r-z^2r^{\alpha_h},s,z),\qquad
\Delta(y)=1-\alpha_hz^2r^{\alpha_h-1}.
\]
On the stable branch \(\Delta=1-\alpha_h\eta^2\ge1-\alpha_h>0\). Its inverse differential is exactly
\[
L(y)v=\left(\frac{v_T+2zr^{\alpha_h}v_z}{\Delta(y)},v_s,v_z\right).
\tag{4.1}
\]
All functions in this formula are smooth on a neighborhood of
\(K_1=\{1\}\times[l/2,2u]\times[-1,1]\), including the axial endpoints.

For a lift \(g\), recursively define tensor-valued functions
\[
J_0[g]=g,\qquad J_{n+1}[g]=\operatorname{uncurry}(DJ_n[g]\circ L).
\tag{4.2}
\]
The chain rule proves by induction that \(D^n(g\circ\Psi^{-1})=J_n[g]\circ\Psi^{-1}\) on the positive branch. Currying is isometric. This is the source's actual inverse-jet recursion, not assumed inverse-coordinate bounds.

Here is a finite producer on \(K_1\). Let \(Z=(1,1,0,\ldots)\) and \(E^{\gamma}_n=|\gamma_{\underline n}|\), bounding \(z\) and \(r^\gamma\) at \(r=1\). Set
\[
D^\#=[1]+\alpha_h(Z\star Z\star E^{\alpha_h-1}),\quad
R^\#=\mathcal I_{1-\alpha_h}(D^\#),\quad
V^\#=2Z\star E^{\alpha_h},\quad
L^\#=R^\#+V^\#\star R^\#+[1].
\tag{4.3}
\]
These bound \(\Delta,\Delta^{-1},2zr^{\alpha_h},L\) respectively. The last \([1]\) pays the unchanged \((s,z)\) projection. Starting from elementary power/product arrays for
\(g_q=r\), \(g_X=s/r\), \(g_\eta=zr^{-D_h}\), use the \(s\)-array \((2u,1,0,\ldots)\) and define
\[
A_{0,t}[g]\ge\sup_{K_1}\|D^tg\|,\qquad
\boxed{\ A_{n+1,t}[g]=\sum_{i=0}^t\binom tiA_{n,t-i+1}[g]L^\#_i.\ }
\tag{4.4}
\]
Leibniz applied to (4.2) proves \(\|D^tJ_n[g]\|\le A_{n,t}[g]\). Only \(n+t\le N\) is needed through inverse order \(N\). The displayed initial suprema can thus be replaced by the explicitly stated elementary arrays; no compact supremum of an unexplained inverse map remains.

The physical dilation in backward-time coordinates is
\(\delta_r(T,s,z)=(rT,rs,r^{D_h}z)\). For \(0<\rho\le q_{\rm hi}\),
\[
\|\delta_{\rho^{-1}}\|\le H/\rho,\qquad H=\max(1,q_{\rm hi}^{1-D_h}).
\]
The three lifts have homogeneity degrees \(1,0,0\). Freeze \(\rho\) at the evaluation point and rescale to \(K_1\); hence
\[
\|D^n\rho\|\le A_{n,0}[g_q]H^n\rho^{1-n},\quad
\|D^nX\|\le A_{n,0}[g_X]H^n\rho^{-n},\quad
\|D^n\eta\|\le A_{n,0}[g_\eta]H^n\rho^{-n}.
\tag{4.5}
\]
These are derivatives in \((T,s,z)\), before the radial substitution. Replacing the extra \(\rho\) in the first estimate by \(\max(1,q_{\rm hi})\) reproduces the source's common \(\rho^{-n}\) loss. This does not bound physical derivatives uniformly near a vanishing physical terminal scale.

To obtain derivatives in \(p=(R,(Z,T))\), compose with \((T,R^2/2,Z)\). In the source, `physicalInput` first writes physical time \(1-T\); converting it back to backward time gives exactly this map. Its first derivative is bounded by \(B_1=\max(1,M_{\rm cell})\), its second by \(B_2=1\), and higher derivatives vanish. Time reflection and coordinate swaps cost one. With \(q_{\rm lo}=1/4,q_{\rm hi}=4\), define, for \(n\ge1\),
\[
\widetilde C^q_n=A_{n,0}[g_q]H^n\max(q_{\rm lo}^{1-n},q_{\rm hi}^{1-n}),\quad
\widetilde C^X_n=A_{n,0}[g_X]H^nq_{\rm lo}^{-n},\quad
\widetilde C^\eta_n=A_{n,0}[g_\eta]H^nq_{\rm lo}^{-n}.
\]
Apply (2.2) to each with \(B\), supplying zeroth ranges \(4,2u,1\). Call the resulting arrays \(C^q,C^X,C^\eta\); \(C=C^q+C^X+C^\eta\) is a conservative array for the full normalized chart. Everything is a finite calculation.

As a first-order check directly from (1.1),
\[
d\rho[v]=\frac{v_T+2Z\rho^{\alpha_h}v_Z}{1-\alpha_h\eta^2},\quad
 dX[v]=\frac R\rho v_R-\frac X\rho d\rho[v],\quad
 d\eta[v]=\rho^{-D_h}v_Z-D_h\frac\eta\rho d\rho[v].
\tag{4.6}
\]
These agree with (4.1) followed by the radial substitution. [Inverse-chart source trail](primitive-derivative-validation.md#primitive-source-chart).

<a id="primitive-base"></a>
## 5. Frozen rescaling: no inverse \(Q_b\) loss

For either error \(e(r,w)\) of §3, freeze the point \(r=Q_b\rho\). Writing \(\mathrm{scaleMap}(c)(s,w)=(cs,w)\), the exact identity is
\[
e\circ\mathrm{scaleMap}(Q_b)=
(e\circ\mathrm{scaleMap}(Q_b\rho))\circ\mathrm{scaleMap}(\rho^{-1}).
\]
The last linear map has norm at most \(\max(1,q_{\rm lo}^{-1})\), not \(Q_b^{-1}\). Since \(Q_b\rho\le1\), (3.6) gives
\[
\boxed{\ \|D^n[e(Q_b\rho,w)]\|
 \le E_nq_{\rm hi}^{2h}\max(1,q_{\rm lo}^{-1})^n Q_b^{2h}
 =4^{2h+n}E_nQ_b^{2h}.\ }
\tag{5.1}
\]
Here derivatives on the left are in \((\rho,w)\), before composition with the nonlinear slow chart. The band is fixed; we do not differentiate its majorant.

For reproducible witnesses in (1.4), let
\[
U^\phi_n=\sup_{[l/2,2u]\times[-1,1]}\|D^nd_{\phi,0}\|,
\qquad U^{\rm ax}_n=\sup_{[l/2,2u]\times[-1,1]}\|D^nd_{{\rm axial},0}\|.
\]
These are allowed individual-coefficient seminorms, finite by ambient smoothness. Let \(P\) be the array for \(\rho^{-A}\), obtained by (2.4) on \([1/4,4]\) and composition with \(C^q\). Put \(I_n=n!r_*^{-n-1}\), the bound for \(R^{-1}\). Then valid arrays are
\[
\begin{array}{ll}
L^F=(P\star I)\star\operatorname{Comp}(V\star U^\phi,C),&
L^G=P\star\operatorname{Comp}(U^{\rm ax},C),\\
E^F=(P\star I)\star\operatorname{Comp}((4^{2h+n}E^{\rm sw}_n)_n,C),&
E^G=P\star\operatorname{Comp}((4^{2h+n}E^{\rm ax}_n)_n,C).
\end{array}
\tag{5.2}
\]
Outer functions independent of \(\rho\) are lifted contractively; order zero in each composition uses its displayed outer range bound. Leibniz and the partition rule prove (5.2) and hence (1.4). The sole \(Q_b^{2h}\) factor is taken outside the entire error computation.

**Quantitative status.** On cells satisfying the stated chart ranges and scale threshold, this recovers the actual all-order small-power estimate and degree-zero base bound of `BaseChartJets.actual_estimates`, with explicit relative numerical witnesses. It is not merely an unweighted smoothness corollary. Our constants may be more conservative than its chosen witnesses; we do not assert equality of those numbers. In particular we will not replace the source's low-order constants inside an already selected preparation. [Base and low-order suppliers](primitive-derivative-validation.md#primitive-source-base).

<a id="primitive-preparation"></a>
## 6. Geometry and low-order constants in that same preparation

### Uniform positive-time cells, without a positive time floor

The reference compact has the lifted description
\[
\tfrac12\le\rho\le2,\quad R\ge0,\quad l\le R^2/(2\rho)\le u,
\quad T=\rho-Z^2\rho^{2h}\ge0.
\]
The lifted set is closed and bounded: in particular \(|\eta|\le1\); its continuous forward image is compact. Even at \(T=0\) its stable Jacobian satisfies \(1-2h\eta^2\ge1-2h>0\). The inverse function theorem gives an open stable-branch neighborhood. Continuity and strict slack give an open neighborhood with the radius, cell-coordinate, scalar and inner-radial ranges of (1.2), and positive stable Jacobian. We do **not** impose \(|\eta|<1\) there: the reference compact contains \(T=0\), hence \(|\eta|=1\). On intersection with \(T>0\), the identity \(T=\rho(1-\eta^2)\) and \(\rho>0\) imply \(|\eta|<1\). Only that positive-time intersection satisfies all of (1.2).

A representative is within one mesh of its grid center; the open three-mesh box is within four meshes of that representative. Compactness supplies a fixed thickening inside the above open neighborhood, and four meshes tend to zero. One band threshold therefore puts every positive-time three-mesh cell inside it. Intersecting the box with \(T>0\) is open and convex. Keep three distinct domains: **one mesh** for mask support, **two meshes** for phase carrier, **three meshes intersected with positive time** for the convex base domain. No positive lower bound on \(T\) is used. This regular auxiliary chart at \(T=0\) is not physical localization or an extension of the singular solution.

### The finite-profile boundary and its transport

**Additional input here.** The selected profile has \(f>0\), \(d_{\phi,0}=C_{\rm axis}f\), \(d_{{\rm axial},0}=U\), its profile identities, and the strict interior true cone. At the two edges we retain the actual oriented activation/terminal factor certificates, not an assumed positive minimum of stress amplitude. Their suppliers are `LeadingStressWeights.closed_shear_positive`, `inner_direction_positive`, and `outer_direction_positive`; production of their finite-profile certificates remains source-trusted.

Using (1.1) to simplify (1.3),
\[
F_{\rm ref}=\rho^{-A-1/2}f>0,\qquad
 g_{\rm ref}=(RF_{{\rm ref},R},G_{{\rm ref},R})=F_{\rm ref}(-a_s,-c_s),
\]
where the profile identities identify \(a_s=-2Xf_X/f\), \(c_s=-2XU_X/E\) with the actual angular and signed axial shears. Explicitly, \(E(X,\eta)=\sqrt{2X}\,f(X,\eta)\). Indeed \(G_{{\rm ref},R}=\rho^{-A}U_XR/\rho=-F_{\rm ref}c_s\), since \(R/\sqrt\rho=\sqrt{2X}\); this is the cancellation in `NominalConeAssembly.modulated_shears_eq`. The finite cone and its edge certificates give, on the closed profile annulus,
\[
a_s>0,\qquad v_s=a_s(1+(c_s/a_s)^2)>2.
\]
Thus \((g_{\rm ref})_0<0\) and
\[
2F_{\rm ref}(g_{\rm ref})_0+|g_{\rm ref}|^2
 =F_{\rm ref}^2(a_s^2+c_s^2-2a_s)>0.
\]
With \(n_0=g_{\rm ref}/|g_{\rm ref}|\), \(\gamma=2F_{\rm ref}(n_0)_0<0\),
\[
\lambda=\sqrt{-\gamma(\gamma+|g_{\rm ref}|)}>0,\qquad
c_0=\lambda/\gamma<0,\qquad c_0^2=(v_s-2)/2.
\tag{6.1}
\]
This is precisely chapter 05's signed eigenpair. The stable extensions of these expressions are continuous on the reference compact and agree with the physical reference fields at positive time. Taking upper bounds for
\(R,F_{\rm ref},|g_{\rm ref}|,\lambda,|c_0|\) and for
\(R^{-1},|g_{\rm ref}|^{-1},\lambda^{-1},|c_0|^{-1}\)
gives one finite reference majorant before representatives are chosen.

For clarity, the edge input says that in inward logarithmic distance \(x>0\),
\[
S_{\rm edge}(\eta,x)=\frac{\operatorname{edge}_{c}(x)}{x^m}B_{\rm edge}(\eta,x),
\]
with an ambient smooth factor, \(B_{\rm edge}(\eta,0)\ne0\), positive first component at the edge and a strict directional collar. Here \(c\) is the actual activation-time square at the inner edge and \(4\) at the outer edge. The multiplier is positive in the interior collar. If \(t=B_2/B_1\), \(k=c_s/a_s\), its collar inequalities are
\[
1+kt>0,\qquad 2(1+kt)^2-(v_s-2)(t-k)^2>0.
\]
For \(T_{\rm dir}=B/|B|\), direct scalar products imply
\[
\langle T_{\rm dir},n_0\rangle<0,\qquad
\left|c_0\frac{\langle T_{\rm dir},-Jn_0\rangle}{\langle T_{\rm dir},n_0\rangle}\right|^2
 =\frac{v_s-2}{2}\frac{(t-k)^2}{(1+kt)^2}<1.
\tag{6.2}
\]
The interior true cone supplies the same inequalities for the actual nonzero stress. Normalizing stress in each edge collar equals normalizing its factor. These equal germs glue its direction continuously through both zero-amplitude edges. Compactness now gives an inward margin and a maximum ratio \(r<1\). Choose \(u_{\rm slope}>0\) with \(r<u_{\rm slope}/\sqrt{1+u_{\rm slope}^2}\); for example \((1-r^2)^{-1/2}\) suffices when \(0\le r<1\). Uniform continuity near the diagonal of the compact product preserves smaller strict margins for mixed pairs \((p,\bar p)\). A fixed \(\delta>0\), then \(3/S_b^3<\delta\), supplies the representative target margin. We used neither a lower stress-amplitude bound at the edge nor arbitrary new edge directions.

### Constants first; large-band threshold last

The source extracts common error bounds \(C_F,C_G\) through order one and reference bounds \(B_F,B_G\) through order two from the same all-order proof. It sets
\[
K_{\rm base}=C_F+C_G+B_F+B_G+1,\qquad B_{\rm base}=2K_{\rm base}.
\tag{6.3}
\]
The doubling pays, for example, \(\|DF_b\|\le K_{\rm base}Q_b^{2h}+K_{\rm base}\le2K_{\rm base}\). With \(\epsilon_b=Q_b^h\), its squared small parameter is exactly \(Q_b^{2h}\). For the preparation exhibited in this existence proof, this supplies the C1-error/C2-reference hypotheses of [chapter 05 §2](05-native-weighted-control.md#native-control-normal), not an assumed `Prepared.base` estimate.

`PrimaryGeometryAssembly.exists_prepared` orders its choices as follows:

1. Same-profile reference/target bounds, \(u_{\rm slope}\), margin and target threshold.
2. Positive chart ranges; the literal enlarged-bundle schedule restricted to the enlarged box; actual estimates with \(4Q_b\le1\); (6.3).
3. A common \(M_0\ge1\) dominating the reference majorant, \(B_{\rm base},u_{\rm slope},(2r_0)^{-1},4r_0T_g,M_{\rm cell},2/\sqrt l\).
4. A final threshold above these thresholds and \(N_0\), with
   \[
   b\ge4,\ S_b\ge2,\ S_b^2\epsilon_b^2\le1,\ S_b^2/K_b\le1,
   \ \epsilon_bS_b^2\le1,\ C_{\rm ph}(M_0)/S_b\le b_0/2,
   \]
   where \(K_b\) is the carrier and
   \(b_0=\sqrt{(1/M_0)/(4(1+u_{\rm slope}^2)\sqrt{1+u_{\rm slope}^2})}>0\).

There is no derivative order in this existence-proof cutoff. **Selected-record boundary:** `PrimaryGeometryAssembly.prepared` selects from `Nonempty Prepared`; `ActualPrimary.choice` selects from `Nonempty Choice`. Neither selection is identified with the exhibited construction. The actual record certifies `base`, `frequency_jets`, `axial_jets`, radius bounds, parameters, cone and `LargeBand`. Use its certified `base` bounds for chapter 05's low-order comparison, not the intermediate constants (6.3) or their domination history. In particular (5.2) need not be bounded by its \(M_0\).

**Unresolved domain bridge.** These record fields do not export the enlarged-chart threshold or all ranges required by (5.2) on its entire label domain. The eventual geometry argument above does not prove that the actual record's threshold dominates that threshold. Applying our numerical §5 arrays to every actual label therefore remains conditional on an additional domain/threshold theorem. We neither raise the selected threshold nor treat its stored all-order jets as a numerical reconstruction. Those certified jets support the source consumer, but leave this part of the human numerical reconstruction incomplete.

Finally `PrimaryTargetBounds.exists_constructed_bounds` applies a later covariance cutoff and returns `a.restrict N hN`. That restriction retains fields, representatives, target, \(M_0,u_{\rm slope}\), and Fourier modes; only admissible labels change. `CorrectionInitialization.ActualPrimary.choice_nonempty` uses this result. Covariance construction itself is an imported selection step, not rederived here. The defined operation `restrict` preserves these data for any given input record; this does not identify the classically selected `choice` with that internal restricted witness. Both signs use the actual choice's certified preparation fields. Our explicit arrays apply to both signs only subject to the domain bridge above. [Geometry, cone and restriction sources](primitive-derivative-validation.md#primitive-source-preparation).

<a id="primitive-normal"></a>
## 7. One base derivative pays for normal, motion and shear

Return to the same reference carrier and open enlarged slot of chapter 05. Let \(S_0=S(b_r)\ge1\) and let its actual common phase bound be \(M=M_*\ge1\), so
\[
|\epsilon_r|,|p_\theta|,|p_z|,|x_0|\le M,\quad r_*\le R\le M,
\quad |s|\le MS_0.
\]
The phase coefficients are frozen under point differentiation. For the numerical derivation below, bounds \(f_n,g_n\) come from §5 **conditional on the §6 selected-domain bridge**. Alternatively the actual record supplies certified base jets, but their numerical production on its full domain has not been reconstructed here. Define
\[
H_n=M(f_{n+1}+g_{n+1}),\quad \mathsf R=(M,1,0,\ldots),
\quad \mathsf V=(MS_0,1,0,\ldots),\quad I_n=n!r_*^{-n-1}.
\]
Unit directional derivatives of \(F,G\) cost one higher full derivative. Consequently both \(A_R=p_\theta F_R+p_zG_R\) and \(A_Z=p_\theta F_Z+p_zG_Z\) have array \(H\). The literal formulas give
\[
N=(x_0-sA_R,p_\theta/R,p_z-\epsilon_rsA_Z),\qquad
\dot N=(-A_R,0,-\epsilon_rA_Z),\qquad g=(RF_R,G_R),
\]
\[
\boxed{\ P=[2M]+(1+M)(\mathsf V\star H)+MI,\qquad
 T=(1+M)H,\qquad
 \Gamma=\mathsf R\star(f_{n+1})_n+(g_{n+1})_n.\ }
\tag{7.1}
\]
These are nonnegative polynomial arrays in \(S_0\). Expanded, the slot term at order \(n\) is \(MS_0H_n+nH_{n-1}\), taking \(H_{-1}=0\); the shear entry is \(Mf_{n+1}+nf_n+g_{n+1}\).

A first-order check exposes the Hessians:
\[
DN[v,\tau]=\left(
-\tau A_R-s\{p_\theta D^2F(v,e_R)+p_zD^2G(v,e_R)\},
-\frac{p_\theta v_R}{R^2},
-\epsilon_r\tau A_Z-\epsilon_rs\{p_\theta D^2F(v,e_Z)+p_zD^2G(v,e_Z)\}
\right).
\tag{7.2}
\]
Thus order-one normal jets really need second base derivatives. Motion is estimated from its **explicit** formula, not by differentiating normal comparison, or by asking for order \(N+1\) of an assembled normal. No extra shift occurs.

| Output through order \(N\) | Inputs through which orders? |
|---|---|
| Actual base \(F,G\) | Individual coefficient head seminorms through \(N\), fixed schedule tail constraints; chart triangle through \(N\) |
| Normal, explicit normal motion, shear | Base through \(N+1\) |
| Normalized frame, modal coefficient, projection, synthesis | Base through \(N+1\), positive denominator/range bounds |
| Projected forcing | Those frame jets and incoming residual through \(N\) |
| Joint solution and amplitude | Coefficient, forcing and synthesis through \(N\); zero initial family at every order |
| Inverse-square normal and pressure | Normal/motion/action, amplitude and current source through \(N\); no additional base shift at this algebraic stage |

This is the `hf.bound (N + 1)` → directional derivative → `PhaseFamily.polynomial_jets` handoff. [Exact normal suppliers](primitive-derivative-validation.md#primitive-source-normal).

<a id="primitive-frame"></a>
## 8. Normalize the actual tail, then assemble the frame numerically

**Downstream input at this use.** We now import chapter 05's proved mesh/rounding comparison, using the actual record's certified low-order bounds (not an identification with (6.3)):
\[
\|N-B_0(s_0,K_0)\|\le\delta_N\le b_0/2\le B_0/2,\qquad |K_0|=1.
\]
Tail projection is contractive, so
\[
\bigl||\operatorname{tail}N|-B_0\bigr|\le\delta_N,
\quad \beta:=|\operatorname{tail}N|\ge B_0/2,\quad |N|\ge B_0/2.
\tag{8.1}
\]
Total-normal separation alone would be insufficient. Use the source's smaller common bound
\(b_* =\min(b_0/2,1/M_0)>0\) and its upper bound \(U_*=M_*^2+3M_*\). Replace only the zeroth entry of \(P\) in (7.1) by \(U_*\); all its derivative entries are retained.

Put \(Q^\beta=P\star P\), bounding derivatives of \(\beta^2\). Its range lies in \([b_*^2,U_*^2]\). Equations (2.2)–(2.4) give arrays \(\mathsf B,\mathsf I\) for \(\beta,\beta^{-1}\). In this section write \(\varrho=N_{\rm rad}/\beta\) for the **frame slope**, to distinguish it from the chart coordinate \(\rho\). The actual definitions yield
\[
\begin{array}{c|l}
\text{field}&\text{array}\\ \hline
\varrho & P_\varrho=P\star\mathsf I\\
K_f=\operatorname{tail}N/\beta,\quad N_f=JK_f & P_K=P\star\mathsf I\\
\dot\beta & P_{\dot\beta}=(P\star T)\star\mathsf I\\
\dot\varrho & P_{\dot\varrho}=(T+P_\varrho\star P_{\dot\beta})\star\mathsf I\\
\dot K_f & P_{\dot K}=(T+P_{\dot\beta}\star P_K)\star\mathsf I\\
\mathrm{rot}=\langle N_f,\dot K_f\rangle & P_{\rm rot}=P_K\star P_{\dot K}\\
(1+\varrho^2)^{-1} & \mathsf D=\mathcal I_1([1]+P_\varrho\star P_\varrho).
\end{array}
\tag{8.2}
\]
For example \(\dot\beta=\langle\operatorname{tail}N,\operatorname{tail}\dot N\rangle/\beta\) proves its row by two products. The other rows follow from explicit quotient derivatives. The quarter-turn costs one. Conversely
\(\dot\beta\varrho+\beta\dot\varrho=\dot N_{\rm rad}\) and
\(\dot\beta K_f+\beta\dot K_f=\operatorname{tail}\dot N\); hence the reconstructed frame motion is precisely the explicit \(\dot N\) of §7, not a newly assumed derivative family.

For the eigenbasis let \(m(s)=u_{\rm slope}/2+(u_{\rm slope}/L)s\). Prepared slot/eigenpair bounds give
\[
|u_{\rm slope}/L|S_0\le M,\quad |m|\le M+M^2,\quad
b_*\le|c_0|\le M,\quad 0<\lambda\le M.
\]
Use \((M+M^2,M,0,\ldots)\) for \(m\). With \(E_m=1+m^2\ge1\), elementary power arrays give bounds for
\[
H_e=c_0\sqrt{E_m},\quad H_e^{-1}=c_0^{-1}E_m^{-1/2},\quad
\Lambda=\lambda E_m^{-1/2},\quad r_e=m(u_{\rm slope}/L)E_m^{-1}.
\tag{8.3}
\]
Here \(c_0^{-1}\) is a frozen scalar bounded by \(b_*^{-1}\), and \(E_m\le1+(M+M^2)^2\). No inverse eigenvector constant is unexplained.

For an entirely explicit modal algorithm, define arrays
\[
\begin{split}
A_{11}^\#&=P_\varrho\star(P_K\star\Gamma+P_{\dot\varrho})\star\mathsf D,\\
A_{12}^\#&=(2f\star P_K+P_\varrho\star P_{\rm rot})\star\mathsf D,\\
A_{21}^\#&=2f\star P_K+P_K\star\Gamma+P_\varrho\star P_{\rm rot}.
\end{split}
\]
They bound the actual entries (3.1) of chapter 05. Let
\(a^\#=A_{11}^\#\),
\(b^\#=A_{12}^\#+P_\Lambda\star P_{H_e^{-1}}\),
\(c^\#=A_{21}^\#+P_\Lambda\star P_{H_e}\).
Each of the four moving-eigenbasis error entries has common array
\[
\mathsf E=\tfrac12(a^\#+P_{H_e}\star b^\#+P_{H_e^{-1}}\star c^\#+P_{r_e}).
\]
Summing four entry bounds pays the Euclidean operator norm. The reference viscosity is \(\nu_0|N|^2\), with frozen \(1\le\nu_0\le4\). Thus a valid array for the full coefficient is
\[
P_{\rm coeff}=P_\Lambda+4j^2(P\star P)+4\mathsf E.
\tag{8.4}
\]
This explains why coefficient jets are for **fixed harmonic \(j\)** although the energy estimate of chapter 05 is uniform over nonzero harmonics.

For projection of a Euclidean unit input \(f_{\rm in}\),
\[
f_X=-\{(f_{\rm in})_0-\varrho\langle K_f,\operatorname{tail}f_{\rm in}\rangle\}(1+\varrho^2)^{-1},
\qquad f_Y=-\langle N_f,\operatorname{tail}f_{\rm in}\rangle.
\]
Each modal projection column is bounded by
\[
\mathsf L_\Pi=([1]+P_\varrho\star P_K)\star\mathsf D+P_K\star P_{H_e^{-1}}.
\]
The two half factors in \(((f_X+f_Y/H_e)/2,(f_X-f_Y/H_e)/2)\) cancel against the sum bound for its Euclidean norm. There are three columns: \(3\mathsf L_\Pi\) bounds the projection operator. Each synthesis column \((1,-\varrho K_f\pm H_eN_f)\) has array
\[
[1]+P_\varrho\star P_K+P_{H_e}\star P_K.
\tag{8.5}
\]
Equations (8.2)–(8.5) now supply the numerical higher-order input previously left source-only in chapter 05 §6. They preserve its full derivative orders and polynomial uniformity, but are conservative witnesses, not its literal compact-composition constants. [Frame source correspondence](primitive-derivative-validation.md#primitive-source-frame).

<a id="primitive-transport"></a>
## 9. The selected copy: transport, inverse normal and inverse frequency

**Domain and transport inputs here.** Retain chapter 05's arbitrary active selector \(e(q)=(\ell,b)\), nonzero harmonic \(j\), arbitrary lattice copy \(k\), reference band \(b_r\), and positive frozen \(\phi,c_t,c_N\). Its full-path predicate requires selected-strip membership, \(\phi\chi(p,\theta)\) in the reference carrier, transverse copy coordinate in \([-r_0,r_0]\), and sampled time \(v\in[0,L/c_t]\). For current-point jets additionally require current time \(t_k\in(0,L/c_t)\). We use that actual `selectedPatch`, not the whole strip.

Chapter 05's active-window bounds supply \(\|\phi\|\le\Phi\), \(c_t\le c_{\max}\), \(0<n_{\min}\le c_N\le n_{\max}\) and \(S_0\le25S_b\). Thus the sampled-time pullback of a reference array \(A\) is bounded by
\[
\mathsf T_n(A)=(\Phi+c_{\max})^nA_n(25S_b).
\]
The literal identities are
\[
N_c=c_NN\circ(\phi\chi,c_tv),\qquad
\dot N_c=c_Nc_t\dot N\circ(\phi\chi,c_tv).
\tag{9.1}
\]
The modal coefficient and retained action acquire the multiplier \(c_t\); modal projection and the two synthesis columns are pulled back without a multiplier. Thus their sampled-time arrays are respectively \(c_{\max}\mathsf T(P_{\rm coeff})\), \(\mathsf T(3\mathsf L_\Pi)\), and \(\mathsf T\) of each array (8.5). This is the same transported frame used by the ODE, not normalization of a separately chosen normal.

Current-endpoint composition adds at most \(\mathcal A(g)^n\le(A_{\rm geo}\mathcal G^2)^n\), where \(\mathcal G=S_b\max(1,\delta^{-1})\ge1\) is chapter 05's growth majorant, not the axial field. Replace \(S_b\) by \(\mathcal G\) only in upper polynomials. Translations in \(k\) have no derivative cost. Normal, motion, action, source and amplitude must all be on this **same current-point domain** before taking products.

Let \(P^c,T^c\) be these current-point arrays, with frozen multipliers \(n_{\max}\), \(n_{\max}c_{\max}\), respectively. The retained action
\(K_{\rm act}a=(-2F(\operatorname{tail}a)_0,a_0(2Fe_\theta+g))\)
has reference operator array \(4f+\Gamma\); apply the same pullbacks and its multiplier \(c_t\) to obtain \(A^c\). The actual normal range is
\[
b_{\rm nat}:=n_{\min}b_*>0,\qquad b_{\rm nat}\le|N_c|\le n_{\max}U_*.
\tag{9.2}
\]
No inverse-clock factor occurs in this lower bound. It follows from (8.1) and (9.1), rather than assuming an inverse-normal class.

Set \(Q=P^c\star P^c\), bounding \(q_N=|N_c|^2\). Then
\[
R_0=b_{\rm nat}^{-2},\qquad
\boxed{\ R_n=b_{\rm nat}^{-2}\sum_{i=1}^n\binom niQ_iR_{n-i}.\ }
\tag{9.3}
\]
This is (2.3) for \(q_N\ge b_{\rm nat}^2\). In particular
\[
Q_1=2P^c_0P^c_1,\quad Q_2=2P^c_0P^c_2+2(P^c_1)^2,
\qquad R_1=b_{\rm nat}^{-4}Q_1,\quad
R_2=b_{\rm nat}^{-4}Q_2+2b_{\rm nat}^{-6}Q_1^2.
\tag{9.4}
\]
This expands the inversion mechanism of `normalInverse_unweighted`; that generic theorem's whole-strip hypotheses are **not** asserted for the selected patch application.

For the **selected-strip** \(0<\epsilon\le1\), its carrier is
\(K_b=\lceil\epsilon^{-1/2}\rceil_{\mathbb N}\). The ceiling gives
\[
1\le K_b\sqrt\epsilon\le1+\sqrt\epsilon,
\quad |j|\ge1,
\quad \boxed{\ |(jK_b)^{-1}|\le K_b^{-1}\le\sqrt\epsilon.\ }
\tag{9.5}
\]
All positive-order point derivatives of this multiplier vanish. The source's band witness is literally **constant 1, degree 0**, even for varying nonzero integer harmonics. To apply it to the actual cycle we use the incoming frequency coherence:
\[
\operatorname{selectedBackground.frequency}(q)=j\,\operatorname{carrier}(h,b).
\]
`selected_inverse_frequency` rewrites this identity and uses the selected epsilon, not \(\epsilon_r\). This coherence is an input from the incoming state, not a consequence of base differentiation. [Transport and inverse source trail](primitive-derivative-validation.md#primitive-source-inverses).

<a id="primitive-pressure"></a>
## 10. A finite numerical pressure bound, and the return to chapter 05

**Final imported inputs, explicitly.** Use chapter 05's actual slot separation and envelope identity along the full closed integration path; the incoming residual's all-jet invariant and frequency coherence; open-neighborhood smoothness of frame/source; and its weighted joint-ODE argument with identically zero initial family at every order. Section 8 supplies that argument's frame/coefficient/projection/synthesis constants conditional on the unresolved selected-domain bridge in §6. All numerical applications in this section retain that condition. We are not producing the incoming invariant or localization beyond the patch.

For completeness, the constants needed to instantiate its ODE consumer can be chosen by a finite algorithm. Through \(N\), bound the transported coefficient, projection and two synthesis arrays by pairs \((C_c,m_c),(C_p,m_p),(C_0,m_0),(C_1,m_1)\). For incoming real-source constants \(B_f,b_f\), chapter 05's affine path cost gives
\[
C_s=B_fA_{\rm geo}^{N},\quad m_s=b_f+2N,\quad
B_{\rm fr}=C_c+C_p+C_0+C_1,\quad q_{\rm fr}=m_c+m_p+m_0+m_1,
\]
\[
C_{\rm in}=B_{\rm fr}+2^NB_{\rm fr}C_s,\quad m=q_{\rm fr}+m_s,
\qquad K_{\rm ode}=C_{\rm in}+K_{\rm ctl}+1.
\tag{10.1}
\]
Here \(K_{\rm ctl}\) is the fixed energy/length/geometry constant already calculated in chapter 05 (4.4), not a carrier. Coefficient and synthesis bounds are unweighted; only forcing carries \(wP_c\), with \(w=\epsilon^\alpha\sqrt\zeta\).

Chapter 05's numerical ambient estimate gives, for every \(d\le N\), a common amplitude array entry
\[
U_d(\mathcal G)=2^{N+1}\mathcal B^{N+1}K_{\rm ode}K_{\rm ctl}^{N}
 \mathcal G^{(m+2)(N+1)+m+2N},\qquad
\mathcal B=2^{N+1}(2^NK_{\rm ode}^2+K_{\rm ode}+1)^3.
\tag{10.2}
\]
It bounds amplitude jets after removing the single factor \(wP_c(t_k)\). This retains the actual modal/ambient consumer's numerical formula, with our valid (possibly larger) input constants. The solution is still the same zero-entry solve by uniqueness. Let \(V\) bound **current-source** jets with that same factor removed; this comes from the incoming invariant and the exact current-copy envelope identity. It does not come from differentiating the envelope majorant, and is distinct from the affine path-source input in (10.1).

With \(P^c,T^c,A^c\) from §9, define
\[
\boxed{\ B=P^c\star(A^c\star U)+T^c\star U+P^c\star V,\qquad C=R\star B.\ }
\tag{10.3}
\]
Each numerator term contains exactly **one** weighted field, amplitude or source. Leibniz leaves the single \(wP_c\) factor intact, and (9.3) pays division by \(|N_c|^2\). Then (9.5) gives, for a real-source pressure,
\[
\boxed{\ \|D^d\pi\|\le C_d(\mathcal G)
 \epsilon^{\alpha+1/2}\sqrt\zeta\,P_c(t_k),\qquad d\le N.\ }
\tag{10.4}
\]
There is no square of the flat weight. In particular the full order-two constant is
\[
C_2=b_{\rm nat}^{-2}B_2+2b_{\rm nat}^{-4}Q_1B_1+
 (b_{\rm nat}^{-4}Q_2+2b_{\rm nat}^{-6}Q_1^2)B_0.
\tag{10.5}
\]
This is a finite pressure normalization calculation, not just a recovered class exponent.

The sign is unchanged:
\[
c_p=\frac{\langle N_c,K_{\rm act}a\rangle-\langle\dot N_c,a\rangle+
 \langle N_c,f\rangle}{|N_c|^2},\qquad \pi=ic_p/(jK_b),
\quad i(jK_b)N_c\pi=-c_pN_c.
\]
Apply (10.1)–(10.5) separately to real and imaginary source extraction, each costing at most \(\sqrt3\) from complex sup norm into real Euclidean three-space. Complexification and multiplication by \(i\) cost at most one; recombination costs the **sum** of the two bounds:
\(\pi_R+i\pi_I=(-c_I+ic_R)/(jK_b)\). The subscripts denote real-source solves, not final real and imaginary pressure components. At the actual residual exponent \(\alpha=1/2+\sigma\), pressure has exponent \(1+\sigma\).

Every array used is a finite nonnegative polynomial in \(\mathcal G\ge1\). To extract a common pair through order \(N\), take the largest degree and \(1+\) the sum of all coefficients through \(N\). This chooses constants before bands, labels, copies and points. Their finite inputs are individual coefficient/template seminorms through the needed head orders, certified admissible tail estimates, the inverse-chart triangle, retained prepared geometry/denominator numbers, fixed transport costs, incoming residual constants, \(N\), and fixed \(j\). They are explicit **relative** constants, not evaluated decimals for arbitrarily smooth input profiles. [Actual pressure consumer and source binding](primitive-derivative-validation.md#primitive-source-pressure).

## What has changed, and what has not

Relative to the retained finite-profile inputs, §§3–5 produce numerical summed-base estimates on the stated geometric domains; §6 explains a preparation existence construction, not the provenance of the actual classical selection. Its full-domain bridge remains unresolved. Sections 7–8 remove its unnamed all-order normalization constants by finite recurrences. Sections 9–10 recover the literal constant-one frequency gain and a numerical pressure calculation for the **actual selected local raw producer**, conditional on that bridge and the stated downstream inputs. These retain the source's finite-order quantifiers, small powers and domains; they are not merely weaker smoothness or order-zero corollaries. Except for explicitly identified arithmetic witnesses such as (9.5), equality with Lean's noncomputable numerical choices is not asserted.

This narrows NC-D1, supplies a relative numerical derivation for NC-D3 and the inverse/pressure portion of NC-D4, but does not certify their unconditional closure. Finite outgoing/modulation selection, oriented edge production and covariance/slot selection remain upstream inputs; NC-D2's incoming residual production and NC-D5's radial extension, cutoff defects and physical localization remain outside scope. Closed sampled-time estimates concern the smooth ODE representative; they do not identify endpoint jets of an arbitrary clamped extension. The supplied independent reviews support the principal finite calculations subject to the recorded qualifications; they do not sign off this repaired text. No complete correction cycle, singularity proof, source repair or formal validation is claimed. The [new ledger](primitive-derivative-validation.md) records this progress without rewriting the historical one.
