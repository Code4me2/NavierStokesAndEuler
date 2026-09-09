# 02 — The singular base and its coherent corrections

**Owner:** ns-construction. **Baseline:** `597692fa5d55e07d810b2d96ead1a67972585425`.

This chapter explains how the repository constructs increasingly accurate, but singular, approximate Navier–Stokes fields. Viscosity is **one**, terminal time is **one**, and
\[
\mathcal R(u,p)=\partial_tu+(u\cdot\nabla)u-\Delta u+\nabla p.
\]
The target is an extendible residual, not a zero residual. The force, localization, comparison, and nonextension arguments belong to the analysis chapter.

**Evidence key.** *Source-established* means that the cited declaration and relevant local proof were inspected, not that its dependency closure was independently verified. *Conditional exposition* means a mathematical argument using explicitly identified source-only analytic inputs. *Unexpanded lemma* marks missing human derivation, even when the source supplies a theorem without that premise. No new-research theorem is asserted here. In particular, the complete analytic construction is **not** independently reconstructed below: the representative cycle is complete as field/error bookkeeping, with its unresolved native estimates exposed rather than replaced by an unspecified witness.

Prerequisites are multivariable differentiation, vector potentials, Fourier averages, linear ODE variation of constants, and weighted estimates. No Lean knowledge is needed for the narrative; the declaration names provide an audit trail.

**Reading transition.** Start with the [integrated scope summary](README.md#scope); then the partial [scope chapter](01-scope.md); external translation remains open. This chapter exports one gauged physical run, not independent witnesses for blowup and residual estimates. Continue from NSC-009 to [NSA-001](03-ns-analysis.md#nsa-001), keeping exactly those fields and fixed parameters. The [source map](SOURCE-MAP.md) and [review ledger](VALIDATION.md) track the remaining analytic inputs.

## Coordinates, profiles, and what remains singular

<a id="nsc-001"></a>
### NSC-001 — Definition and calculation: the positive terminal coordinate

Fix \(0<h<1/2\). Write \(x=(x_0,x_1,z)\), \(s=(x_0^2+x_1^2)/2\), and \(\tau=1-t>0\). Define \(q=q(t,x)>0\) by
\[
q-z^2q^{2h}=\tau,\qquad
X=\frac{s}{q},\qquad \eta=\frac{z}{q^{1/2-h}},\qquad a_h=\frac12+h.
\tag{1}
\]
Thus \(q\) is independent of the radial variable \(s\), and
\[
\tau=q(1-\eta^2),\qquad |\eta|<1,\qquad
\partial_q(q-z^2q^{2h})=1-2h\eta^2\ge1-2h>0.
\]
For completeness, any positive solution must have \(q^{1-2h}>z^2\). On that interval the left side is strictly increasing, begins at zero, and tends to infinity. This proves existence and uniqueness; the displayed slope gives smooth dependence for \(t<1\). At \(z=0\), \(q=1-t\) exactly. As \((t,x)\to(1,0)\) from \(t<1\), \(q\to0\): otherwise \(q\ge\epsilon\) along a subsequence would give \(z^2q^{2h-1}\to0\) and \(\tau\ge\epsilon/2\), a contradiction.

We use \(D^m=D_{t,x}^m\) for the full Fréchet derivative tensor with operator norm. Write \(|D^{\le m}F|=\max_{0\le k\le m}\|D^kF\|\). Coordinate mixed derivatives and these tensors control each other with constants depending on order and dimension; they are not literally identical norms. An estimate \(D^mF=O(q^b)\) near the terminal origin means there are \(C>0\) and a neighborhood \(U\) of \((1,0)\) such that \(\|D^mF(t,x)\|\le Cq(t,x)^b\) on \(U\cap\{t<1\}\). Constants and neighborhoods may depend on every fixed parameter and the specified derivative order.

**Dependencies:** none. **Status:** source-established coordinate definitions; displayed argument is a prose deduction. **Sources:** [SimilarityCoordinates](../../NavierStokes/SimilarityCoordinates.lean) — `NavierStokes.SimilarityCoordinates.coordinateQ`, `NavierStokes.SimilarityCoordinates.coordinateQ_spec`, `NavierStokes.SimilarityCoordinates.coordinateEta`; [SimilarityProfile](../../NavierStokes/SimilarityProfile.lean) — `NavierStokes.SimilarityProfile.q`, `NavierStokes.SimilarityProfile.X`, `NavierStokes.SimilarityProfile.eta`; [PhysicalWaveSum](../../NavierStokes/PhysicalWaveSum.lean) — `NavierStokes.PhysicalWaveSum.physicalQ`. **Obligations:** no additional analytic input to this calculation; independent review pending.

<a id="nsc-002"></a>
### NSC-002 — The closed profile route and the actual Borel base

The input is not an arbitrary formal similarity solution. The source first constructs an outgoing profile, a nominal entrance-to-terminal cone, and a finite modulation satisfying a true-cone condition. The order of choices matters:

1. Choose a reset bound \(M\), then amplitude \(P\ge\max(2,\text{amplitude threshold}(M))\).
2. Choose the outgoing scale below the clean-cone cap and choose the height below the corresponding height threshold. The prepared profile records \(h\le1/1000\); it is not decreased later to repair an estimate.
3. Choose matching radius above the compensated-family, clean-cone, repair-cone, and terminal thresholds. The proof takes a maximum of these floors.
4. Solve the finite modulation and retain its full true-cone certificate for the same profile.

The outcome is `FinalSlowBase.ProfileData`: an outgoing profile \(F\), nominal witness \(W\), certificate \(H\), loop data, modulation \(v\), and `FullTrueCone v`. The last condition is a conclusion of the existence route, not a free assumption about an edited stress. Mathematical interface details and explicitly unresolved definitions are recorded in the [interface sheet](INTERFACES.md).

> **Unexpanded lemma U1 — closed prepared and modulated profile.**
> `NavierStokes.PreparedOutgoing.exists_prepared` has no external mathematical premise and produces `Nonempty PreparedProfile`. Its record includes the actual profile specification, schedule bounds, terminal small-tail condition, amplitude and height bounds, and the quantified clean-cone assertion: for each left endpoint \(\ell\le0\), some \(R_0>0\) works for every matching radius \(R>R_0\). `NavierStokes.NominalConeAssembly.exists_nominal_cone` and `NavierStokes.FinalSlowBase.profileData_nonempty` likewise have no external profile/cone premise. By contrast, `assembly_exists(d)` requires precisely a `PreparedOutgoing.PreparedProfile d`.
>
> These are source-established existence theorems, **not a human derivation of the profile ODE, schedule, moment repair, or true-cone inequalities**. OBL-NSC-001 remains open. The four-step explanation above is the inspected assembly order, not a proof of those analytic producers.

Here is the subsequent field reconstruction, which is quite explicit. The aligned coefficient family consists of five smooth functions for each slow order \(k\ge0\):
\[
d_k=(J_k,\Phi_k,\Pi_k,T_{\theta,k},T_{z,k})(X,\eta).
\]
The source bundles seven components: the radial average of \(J_k\), the negative radial primitive of \(\Phi_k\) divided by the fixed normalization \(C_*\), pressure, both stresses, and the two original coefficients. Explicitly the first two components are
\[
F_k^{(0)}(X,\eta)=\int_0^1J_k(rX,\eta)\,dr,\qquad
F_k^{(1)}(X,\eta)=-C_*^{-1}\int_0^X\Phi_k(r,\eta)\,dr.
\]
The average is smooth at \(X=0\), where it equals \(J_k(0,\eta)\). Bundling prevents incompatible cutoff choices for derivatives and primitives. These definitions are `NavierStokes.ProfileHistories.average` and `NavierStokes.ProfileHistories.primitive` in [ProfileHistories](../../NavierStokes/ProfileHistories.lean).

Let \(\chi\) be smooth, equal to one for \(|r|\le1/2\), and zero for \(|r|\ge1\). For a coefficient family \(F_k\), its slow sum is
\[
\mathscr S F(q,X,\eta)=F_0(X,\eta)+
 \sum_{k\ge1}\chi(b_kq)q^{2hk}F_k(X,\eta),
\tag{2}
\]
where the increasing integer sequence \(b_k\) is chosen for that common bundle on a fixed compact profile box. It is **not** the later cycle-diagonal sequence \(a_j\). For \(q>0\), only finitely many summands are nonzero locally. By choosing \(b_k\) sufficiently large, the source controls normalized derivatives of each positive order; the leading coefficient in (2) is uncut.

For the seven-component bundle \(F\), define
\[
H_b=q^{-a_h}\mathscr S F^{(0)},\qquad
K_b=q^{1/2-a_h}\mathscr S F^{(1)},\qquad
p_b=q^{-2a_h}\mathscr S F^{(2)}.
\tag{3}
\]
All expressions on the right are evaluated at \((q(t,s,z),X(t,s,z),\eta(t,s,z))\). The Cartesian vector potential and velocity are
\[
A_b=(-x_1H_b/2,\ x_0H_b/2,\ K_b),\qquad u_b=\nabla\times A_b.
\tag{4}
\]
Unlike a cylindrical formula involving division by radius, (4) makes sense at the axis. Differentiating it gives
\[
u_b=\left(x_1\partial_sK_b-\frac{x_0}{2}\partial_zH_b,
 -x_0\partial_sK_b-\frac{x_1}{2}\partial_zH_b,
 H_b+s\partial_sH_b\right).
\tag{5}
\]
This proves solenoidality for smooth profiles by divergence of curl. The common Borel schedule preserves this exact construction, not merely a coefficientwise divergence identity.

On the physical parameter strip \(\eta\in[-1,1]\), the normalized stress \(\mathsf T=\mathscr S(T_{\theta,k},T_{z,k})\) vanishes radially outside \([X_L,X_R]\). No vanishing for \(|\eta|>1\) is asserted. On \((X_L,X_R)\times[-1,1]\), the leading stress and correction satisfy
\[
c\zeta(X,\eta)\le|\mathsf T_0(X,\eta)|,
\quad
|D_{X,\eta}^m\mathsf T_0|\le C_m\zeta\,\delta^{-N_m},
\quad
|\operatorname{blown}D^m(\mathsf T-\mathsf T_0)|
 \le C_mq^h\zeta\,\delta^{-N_m}.
\tag{6}
\]
Put \(a=\log X_L\), \(b=\log X_R\), and \(c=(\text{activation time})^2>0\). On this annulus the weights are explicitly
\[
\delta=\min(1,\log X-a,b-\log X),\qquad
\zeta=\exp[-c/(\log X-a)^2-4/(b-\log X)^2].
\]
The weight is extended by zero outside the radial interval. These are `activeDelta` and `activeZeta`; see [ActiveAnnulusWeight](../../NavierStokes/ActiveAnnulusWeight.lean) and [FlatCutoff](../../NavierStokes/FlatCutoff.lean). For a profile \(F(q,X,\eta)\), the blown tensor means
\(D_{r,X,\eta}^m[F(qr,X,\eta)]|_{(1,X,\eta)}\), with \(q>0\) frozen. Neither tensor in (6) is a physical \(D_{t,x}^m\) estimate. Physical losses remain U6.

Only the **leading** stress is nondegenerate in (6). Weighted remainder smallness is not uniform relative smallness at flat edges: locally \(T_0=\zeta e_1\), \(T=\zeta(1-q^h/\delta)e_1\) obey bounds of this form with larger derivative edge losses, yet vanish at \(\delta=q^h\). Positive primary amplitudes use the actual leading target and cone/matrix argument, not this inference; see [PrimaryTargetBounds](../../NavierStokes/PrimaryTargetBounds.lean), `targetAmplitude_lower`. This example is not a counterexample to that constructor.

The exact base residual decomposition is
\[
\mathcal R(u_b,p_b)=F_{\rm stress}+e_b.
\tag{7}
\]
The stress force is formed from the physical tangential stress components, whose common factor is \(q^{-a_h-1/2}\). It is not the final external force. Equation (7) alone is algebraic: the substantial assertion is that all derivatives of \(e_b\) have arbitrary nonnegative powers of \(q\) on the specified physical approaches.

> **Unexpanded lemma U2 — quantitative base error.**
> In `NavierStokes.FinalSlowBase.error_jetRate`, fix outgoing \(F\), nominal \(W\), certificate \(H\), loop data and modulation \(v\), any box parameter `upper`, integer budget \(B\), a filter \(l\), and `P : BaseResidual.PhysicalApproach l F.data.h 0 radius`, with `radius ≤ boxRadius W upper`. For every \(m\in\mathbb N\) and real \(N\ge0\), the error has `JetRate l (cartesianChart h ·).1 ... m N`. The leading lower bound and leading profile jets in (6) require `LeadingStressWeights.FullTrueCone v`; `FinalSlowBase.weighted_jets` for the correction does not add that premise.
>
> The finite coefficient identities, Borel remainder estimate, and coordinate derivative losses establishing this claim are not derived here. OBL-NSC-002 is open. Neither local finiteness nor (7) supplies this estimate by itself.

**Dependencies:** NSC-001 and U1. **Status:** (2)–(5) are reconstructed definitions/calculations; (6) and U2 are source-only analytic inputs. **Sources:** [PreparedOutgoing](../../NavierStokes/PreparedOutgoing.lean) — `NavierStokes.PreparedOutgoing.PreparedProfile`, `NavierStokes.PreparedOutgoing.exists_prepared`; [NominalConeAssembly](../../NavierStokes/NominalConeAssembly.lean) — `NavierStokes.NominalConeAssembly.assembly_exists`, `NavierStokes.NominalConeAssembly.exists_nominal_cone`; [SlowBorelBase](../../NavierStokes/SlowBorelBase.lean) — `NavierStokes.SlowBorelBase.Coefficients`, `NavierStokes.SlowBorelBase.coefficientBundle`, `NavierStokes.SlowBorelBase.slowSum`, `NavierStokes.SlowBorelBase.streamFactor`, `NavierStokes.SlowBorelBase.swirlPotential`, `NavierStokes.SlowBorelBase.basePressure`; [AxisymmetricFields](../../NavierStokes/AxisymmetricFields.lean) — `NavierStokes.AxisymmetricFields.potential`, `NavierStokes.AxisymmetricFields.velocity`; [FinalSlowBase](../../NavierStokes/FinalSlowBase.lean) — `NavierStokes.FinalSlowBase.ProfileData`, `NavierStokes.FinalSlowBase.profileData_nonempty`, `NavierStokes.FinalSlowBase.scales_spec`, `NavierStokes.FinalSlowBase.leading_lowerBound`, `NavierStokes.FinalSlowBase.leading_radial_jets`, `NavierStokes.FinalSlowBase.weighted_jets`, `NavierStokes.FinalSlowBase.residual_identity`, `NavierStokes.FinalSlowBase.error_jetRate`. **Obligations:** OBL-NSC-001–002 propagate below.

<a id="nsc-003"></a>
### NSC-003 — Exact axis identity and the gauge that must survive localization

Assume the coefficient and scale hypotheses above, \(J_k(0,0)=0\) for \(k>0\), and \(J_0(0,0)=j_*>0\). These axis properties are supplied for the aligned modulation. At \(x=0\), (5) reduces to \(H_b e_2\), the radial average has value \(J_k(0,0)\), and (1) gives \(q=1-t\). Consequently
\[
u_b(t,0)=j_*(1-t)^{-a_h}e_2,\qquad t<1.
\tag{8}
\]
Every positive-order term vanishes at that point, independently of \(b_k\). This is an identity, not merely a lower bound. Since \(a_h>0\), the norm diverges as \(t\uparrow1\).

The actual base potential is nevertheless **not** the ungauged potential in (4). Replace
\[
K_b(t,s,z)\quad\hbox{by}\quad
\widehat K_b(t,s,z)=K_b(t,s,z)-K_b(t,1,z).
\tag{9}
\]
The anchor is physical \(s=1\), not \(X=1\). Because \(\partial_s\widehat K_b=\partial_sK_b\), (5) and hence the entire curl are unchanged. The difference of potentials is an axial field depending only on \(t,z\), so its spatial curl is zero.

Why keep (9)? In the heat exterior the anchored primitive is an integral from \(1\) to \(s\) of the extended heat coefficient. Its normalization eliminates a time-dependent integration constant. The source proves a genuine one-sided extension at every terminal point away from the origin for this particular potential. This cannot be inferred from smoothness of its curl. Indeed, for a spatial cutoff \(\rho\) and curl-free \(G\),
\[
\nabla\times[\rho(A+G)]-\nabla\times(\rho A)=\nabla\rho\times G.
\tag{10}
\]
The analysis chapter must therefore use `finalPotential`, not substitute a convenient curl-equivalent potential.

> **Unexpanded lemma U3 — exterior gauge extension.**
> `NavierStokes.TailGaugePotential.finalPotential_awayExtensions` takes the same \(F,W,H\), loop/modulation \(v\), `upper` and \(B\) as (3), and concludes `JointResidualLimits.AwayExtensions (finalPotential H v upper B)` without an extra exterior-extension premise. The comparison to the heat primitive, uniform terminal neighborhoods, and nonzero-axial extension branch remain unexpanded here (OBL-NSC-003).

**Dependencies:** NSC-001–002. **Status:** (8)–(10) are worked deductions; existence of their actual profile hypotheses and U3 remains source-only. **Sources:** [BaseResidual](../../NavierStokes/BaseResidual.lean) — `NavierStokes.BaseResidual.baseVelocity_at_origin`, `NavierStokes.BaseResidual.baseVelocity_axis_tendsto_atTop`; [FinalSlowBase](../../NavierStokes/FinalSlowBase.lean) — `NavierStokes.FinalSlowBase.leading_origin`, `NavierStokes.FinalSlowBase.axis_tendsto`; [TailGaugePotential](../../NavierStokes/TailGaugePotential.lean) — `NavierStokes.TailGaugePotential.radialAnchor`, `NavierStokes.TailGaugePotential.radialNormalize`, `NavierStokes.TailGaugePotential.partialS_radialNormalize`, `NavierStokes.TailGaugePotential.finalPotential_sameCurl`, `NavierStokes.TailGaugePotential.finalPotential_awayExtensions`. **Obligations:** OBL-NSC-001–003.

## One representative correction cycle

<a id="nsc-004"></a>
### NSC-004 — Definition: weighted accuracy and the fixed ledger

There are three different discrete indices: \(J\) counts completed cycles, \(j\) indexes physical increments, and \(n\) indexes similarity bands. Within a band, Fourier modes are denoted \(k\in\mathbb Z\) and labels by \(\ell\). Never differentiate with respect to these indices.

The strip geometry consists of an open coefficient domain \(\Omega\), scales \(0<\epsilon_n\le1\), slow factors \(S_n\ge1\), edge distance \(\delta(y)>0\), and smooth nonnegative weight \(\zeta(y)\). A family \(F_n\) is in \(\mathcal C_w^\alpha\) when it is smooth on \(\Omega\) and
\[
\forall m\ \exists C_m\ge0,p_m\in\mathbb N\ \forall n,y\in\Omega,
\quad |D^{\le m}F_n(y)|\le
 C_m\epsilon_n^\alpha
 [S_n\max(1,\delta(y)^{-1})]^{p_m}w_n(y).
\tag{11}
\]
Here derivatives are in coefficient coordinates, not yet Cartesian spacetime. Mean class uses \(w=\zeta\), wave class uses \(w=\sqrt\zeta P_{\ell,n}\), with \(0\le P_{\ell,n}\le1\). A uniform labeled class chooses the constants before \(\ell\) as well. A larger exponent is stronger since \(\epsilon_n\le1\). Products add exponents and polynomial degrees by Leibniz; sums may use the smaller exponent.

Fix the actual profile, gauge, carrier geometry, rank patch, normalization, scale budget \(B_{\rm bud}\), and label threshold \(N_0\ge\texttt{geometricThreshold}\). These are fixed **before all cycles**. In the source the budget argument is named `B`; it is unrelated to the direct field \(B_j\) below. The chosen loss parameter is \(\kappa=1/100000\), and the actual \(h>0\) is supplied by the profile. The native band small parameter is \(\epsilon_n=Q_n^h\).

| Quantity | Fixed or variable? | Value/role |
|---|---|---|
| \(h\), \(\kappa\), geometry, primary family | Fixed throughout run | \(0<h<1/2\), \(\kappa=10^{-5}\) |
| \(\sigma_J\) | Accuracy after \(J\) cycles | \(1/5+J/10\) |
| Input accuracy for positive increment \(j\) | \(j\ge1\) only | \(\sigma_{j-1}=1/10+j/10\) |
| Raw physical gain \(g_j\) | Increasing with \(j\) | \(hj/10\) |
| Tail band threshold for signed matching | Fixed within a given cycle | Not an assertion about all \(n\) |
| Physical first/residual band floors, \(q_{\rm big}\) | Fixed for the run | Valid coordinate and support range |
| Constants and log degrees | May depend on increment and derivative order | Never on the subsequently chosen diagonal cutoff |
| Derivative loss functions | Depend on order and fixed data | Not on \(J\) or \(j\) |

In particular, \(g_j\to\infty\) for this one fixed \(h\), not uniformly as \(h\downarrow0\). Arithmetic does not construct a single wave.

**Dependencies:** NSC-002. **Status:** source-established definitions and elementary arithmetic. **Sources:** [WeightedClasses](../../NavierStokes/WeightedClasses.lean) — `NavierStokes.WeightedClasses.StripData`, `NavierStokes.WeightedClasses.MemClass`, `NavierStokes.WeightedClasses.MeanClass`, `NavierStokes.WeightedClasses.WaveClass`; [ChartScales](../../NavierStokes/ChartScales.lean) — `NavierStokes.ChartScales.kappa`; [ActualIterationLedger](../../NavierStokes/ActualIterationLedger.lean) — `NavierStokes.ActualIterationLedger.sigma_formula`, `NavierStokes.ActualIterationLedger.inputSigma_formula`, `NavierStokes.ActualIterationLedger.gain_tendsto_atTop`; [ActualCyclePreservation](../../NavierStokes/ActualCyclePreservation.lean) — `NavierStokes.ActualCyclePreservation.staticData`. **Obligations:** OBL-NSC-001–002 for actual initialization; no new obligation for (11).

<a id="nsc-005"></a>
### NSC-005 — Conditional reconstruction: all four updates and the pressure refresh

Fix a cycle input of accuracy \(\sigma\ge1/5\). It stores a mean field, oscillatory field \(v\), oscillatory and reconstructed mean pressure, covariance, and separate base, Gaussian, and alias errors. Its finite Fourier coefficients must represent those very fields. An analytic invariant also records solenoidality, real-valued reconstruction, finite mode bands, carrier support, periodicity, radial moments, primitive identities, and the classes (11). Without the representation identity, estimates on stored coefficients would say nothing about the velocity.

The following is one entire cycle, in the source order. We write \(U\) for the incoming physical velocity only when discussing the universal residual algebra; \(v\) denotes the oscillatory part in a fixed normalized chart.

**1. Particular wave: remove the current nonzero-mode error.** Compute each mode source from the current residual block, including its current Gaussian error, with the per-label alias slot zero. Solve for the particular coefficients on their actual native cells, sum the finite modes and labels, and obtain \(w_P,\pi_P\). The native solve is a complex Volterra solve; both real and imaginary modal estimates are required. Its homogeneous frame, transported source, localization, pressure projection, and exact curl are part of the constructor, not adjustable output hypotheses.

The sign to check is that the old source **plus** the particular linear-good residual is higher order:
\[
E_{\ell,n,k}+L^{\rm good}_{v}(w_P,\pi_P)_{\ell,n,k}
 \in\mathcal W^{1+\sigma-3\kappa},\quad k\ne0.
\tag{12}
\]
Here \(L^{\rm good}\) is the source's retained linear block, with excluded Gaussian terms separately stored; (12) is not an exact inverse of the full nonlinear NS operator. Set \(v_1=v+w_P\) and reconstruct pressure/covariance. The mean velocity is unchanged at this wave stage, but its residual is not unchanged.

**2. Signed wave: respond to the new mean residual, not the old one.** Compute the tangential/axial residuals \(r_\theta,r_z\) of the actual post-particular state. The stress request consists of their moving radial primitives, with radial weights indexed by 2 and 1 respectively. Apply the source's normalization and angular lift to this request. In particular, its sign is already encoded by the primitive constructor; one must not introduce another guessed minus sign.

Here is that cancellation in ordinary radial calculus. Freeze the slow variables, let \(r>0\) be radial distance in the moving shell, and write \(\bar f(r)\) for the torus-averaged residual. Let \(\mu_e(r)\) be the source's smooth interior bump normalized by \(\int_0^\infty r^e\mu_e(r)\,dr=1\). Put
\[
M_e=\int_0^\infty r^e\bar f(r)\,dr,\quad
f_{\rm adj}=\bar f-\mu_eM_e,\quad
\Sigma_e(r)=-r^{-e}\int_0^r s^ef_{\rm adj}(s)\,ds.
\tag{13a}
\]
For smooth shell-supported data, zero adjusted moment makes this primitive zero both below and above the shell. Differentiation gives
\[
(\partial_r+e/r)\Sigma_e=-f_{\rm adj},\qquad
\bar f+(\partial_r+e/r)\Sigma_e=\mu_eM_e.
\tag{13b}
\]
Use \(e=2\) for the angular stress and \(e=1\) for the axial stress. This shows both the cancellation sign and the **remaining bump/moment error**: compact stress cannot remove an arbitrary nonzero radial moment. In the actual constructor the bump and primitive are scaled with the local positive similarity scale, and the torus average precedes the primitive. The identities above are conditional on smoothness and supported data at that frozen scale. Their source versions are `NavierStokes.SignedStressPrimitive.physicalBarSigma_eq_negative_primitive`, `NavierStokes.SignedStressPrimitive.physical_angular_divergence`, and `NavierStokes.SignedStressPrimitive.physical_axial_divergence` in [SignedStressPrimitive](../../NavierStokes/SignedStressPrimitive.lean); those global declarations require a smooth everywhere-positive scale on their parameter domain and smooth physically supported input. Application on the actual local slow region uses the local-domain machinery in NSC-005's U4, not an assumed positive global extension of \(q\).

The elementary covariance solve is transparent. Let \(H\) be the same invertible two-by-two integrated primary matrix used at initialization, \(T\) its primary target, and \(a_i>0\) its primary amplitudes. For an arbitrary signed request \(R\), put
\[
b_i=\frac{(H^{-1}R)_i}{2a_i}.
\qquad
H(2a_i b_i)_i=HH^{-1}R=R.
\tag{13}
\]
No positivity of \(R\) is needed. The cone lower bound is instead needed for the **denominators** \(a_i\). In the native field, the quotient is also multiplied by \(\sqrt{\epsilon_n}\), masks, and transported vectors. Equation (13) is the matrix identity, not a claim that those factors can be omitted from the physical field.

Let \(w_T\) be the resulting tangent wave and \(w_C\) the literal curl correction; the signed wave is \(w_S=w_T+w_C\). Add its pressure \(\pi_S\), keeping its Gaussian defect, and set \(v_2=v_1+w_S\). The complete covariance increment is **not** just the matched tensor. If \(v_*\) is the fixed primary field and \(d=v_1-v_*\), angular averaging gives
\[
\begin{aligned}
\langle v_2\otimes v_2-v_1\otimes v_1\rangle
={}&\underbrace{\langle v_*\otimes w_T+w_T\otimes v_*\rangle}_{\mathsf C_{\rm match}}\\
&+\langle d\otimes w_T+w_T\otimes d\rangle\\
&+\langle v_1\otimes w_C+w_C\otimes v_1\rangle\\
&+\langle w_T\otimes w_T+w_T\otimes w_C
+w_C\otimes w_T+w_C\otimes w_C\rangle.
\end{aligned}
\tag{14}
\]
Thus the signed square and curl errors are retained. Finite-label support and the carrier identities justify the actual covariance bounds; arbitrary overlapping waves would introduce cross-label terms not covered by a single-label computation.

The native wave inputs and the covariance/mean outputs used in this cycle are:

| Actual coefficient/quantity | Class exponent (wave unless marked mean/tensor) |
|---|---:|
| Particular velocity; pressure | \(1/2+\sigma\); \(1+\sigma\) |
| Signed tangent; curl difference | \(1/2+\sigma-\kappa\); \(1+\sigma-2\kappa\) |
| Signed pressure; signed linear-good error | \(1+\sigma-\kappa\); \(1+\sigma-4\kappa\) |
| Particular covariance increment (tensor) | \(1+\sigma\) |
| Full signed covariance increment (tensor) | \(1+\sigma-\kappa\) |
| Temporal and rank increments; mean pressure difference | \(1+\sigma-2\kappa\) |

For example, the first covariance exponent is \(1/2+(1/2+\sigma)=1+\sigma\). For (14), the incoming old-minus-primary bound has exponent \(17/25\). Adding the particular wave preserves that bound since \(1/2+\sigma\ge7/10>17/25\); hence \(d=v_1-v_*\) has the same conservative exponent. Its tangent cross term has exponent
\[
17/25+1/2+\sigma-\kappa=1+\sigma+9/50-\kappa
\ge1+\sigma+17/100+\kappa,
\tag{15}
\]
using \(2\kappa\le1/100\). The signed square exponent is
\[
1+2\sigma-2\kappa\ge1+\sigma+17/100+\kappa,
\tag{16}
\]
since \(\sigma\ge1/5\) and \(3\kappa\le3/100\). These computations explain why a signed linear cross correction can improve the error despite its unavoidable square. They do **not** prove the complete native derivative estimates: phase differentiation, edge weights, averaging and temporal reconstruction still require their own bounds.

**3. Temporal mean repair.** Apply the normalized temporal torus inverse to \(r_\theta,r_z\) of the post-signed state. A periodic derivative cannot invert its zero mean, so the averaged residual must already have been made smaller by step 2. More precisely, if \(\omega_n=T_g^{\operatorname{index}(n)}Q_n^{1+h}\), the angular increment is
\[
-\omega_n^{-1}\mathcal I_T(r_\theta-\overline{r_\theta}),
\]
where \(\mathcal I_T\) is the periodic temporal inverse, normalized so its temporal derivative is its zero-mean input. Its fast temporal derivative is therefore \(-(r_\theta-\overline{r_\theta})\), leaving the average rather than cancelling it. This is `NavierStokes.MeanChartCompatibility.temporalAtIndex` in [MeanChartCompatibility](../../NavierStokes/MeanChartCompatibility.lean). The axial input is passed through a radial stream primitive; the radial and axial components are then the corresponding stream derivatives, preserving divergence. The difference between the realized axial component and its temporal target is recorded in the temporal alias, not dropped. Reconstruct pressure after this update.

**4. Rank repair.** Measure the remaining debt from the post-temporal state. The fixed reserved rank patch, nonzero rank coefficient, and normalized radial geometry determine the angular rank correction and desired axial correction. Realize the latter through another radial stream. This addresses a compatibility condition that the temporal zero-mean inverse cannot solve. The temporal alias remains subtracted in the axial residual estimate. Both mean repairs preserve the actual angular and axial radial moments (weights 2 and 1); preservation of these moments is necessary for supported primitive reconstruction at the next cycle.

**5. Refresh radial pressure alias once.** Recompute the mean pressure from the new state. Replace the old radial pressure alias by the current one, instead of accumulating both. If \(G\) denotes stored Gaussian error and \(\mathcal A\) stored alias error, the exact bookkeeping is
\[
\begin{aligned}
v^+&=v+w_P+w_S,\\
G^+&=G+G_P+G_S,\\
\mathcal A^+&=\mathcal A+\mathcal A_T(v_2)
 +\mathcal A_p(\text{after rank})-\mathcal A_p(\text{incoming}),\\
e_b^+&=e_b.
\end{aligned}
\tag{17}
\]
The pressure contains both added oscillatory pressures and the reconstructed mean pressure change. Pressure is essential to the residual equation; it is not an external force being silently discarded.

Finally, for the total physical increment \(w\) including both mean repairs and total pressure increment \(\pi\), the exact check on all nonlinear terms is
\[
\mathcal R(U+w,p+\pi)=\mathcal R(U,p)+\partial_tw-\Delta w+\nabla\pi
 +(U\cdot\nabla)w+(w\cdot\nabla)U+(w\cdot\nabla)w.
\tag{18}
\]
Equivalently, the stress increment is \(U\otimes w+w\otimes U+w\otimes w\). Under divergence freedom its divergence gives the three advection terms. Formula (14) is precisely the oscillatory mean part of this expansion, not a different nonlinear model.

> **Unexpanded lemma U4 — the complete analytic step, with exact source interface.**
> Fix a label type, geometry \(G\), time exponent \(h\), common index sequence, axial directions, particular and signed parameter families, rank data \(r\), context \(c\), cycle state \(x\), primary blocks, envelopes \(P\), and closed supports \(S\). Assume exactly:
> * `CorrectionAnalyticStep.StaticData G h index axial r c κ` (same strip/gauge/region, operator and base bounds, fast temporal coefficient, slow base fields, normalized nonzero rank geometry strictly inside the patch);
> * `CorrectionStep.CycleAnalyticInvariant G c primary P S σ x`;
> * \(\sigma\ge1/5\), \(\kappa\le1/100000\);
> * `CorrectionAnalyticStep.StepData ... D H hσ`: the native wave classes and linear identities above; smoothness, Gaussian all-power bounds, solenoidality, support and periodicity; primary finite bandwidth; envelopes in \([0,1]\); closed supports inside the controlled cells; normal and frequency bounds on those cells; the same signed assembly and labels, old/particular support, primary regularity, rank geometry; and `cross_tail` only for \(n\ge\texttt{tailStart}\).
>
> Then `NavierStokes.CorrectionAnalyticStep.step` returns `StepResult`: the invariant at \(\sigma+1/10\), temporal/rank and mean-pressure difference bounds at \(1+\sigma-2\kappa\), coefficient velocity/pressure differences at \(1/2+\sigma-\kappa\) and \(1+\sigma-\kappa\), and post-signed mean residual bounds. Operator bounds also imply \(\kappa\ge0\).
>
> This typed interface is retained to avoid an inaccurate weakening of its many geometric hypotheses. The paragraph descriptions are not replacements for the record fields. The native Volterra estimate, signed quotient derivative bounds, and temporal/rank gain closure are **unexpanded** (OBL-NSC-004). Equations (12), the table, and the claimed gain depend on them. This chapter does not present (15)–(18) as a complete proof of U4.

**Dependencies:** NSC-002–004 and NSC-006 for finite heads. **Status:** conditional exposition, with complete update/error accounting but source-only native analysis. **Sources:** [CycleConstruction](../../NavierStokes/CorrectionStep/CycleConstruction.lean) — `NavierStokes.CorrectionStep.CycleParameters.particularBlock`, `NavierStokes.CorrectionStep.CycleParameters.signedRequest`, `NavierStokes.CorrectionStep.CycleParameters.afterParticular`, `NavierStokes.CorrectionStep.CycleParameters.afterSigned`, `NavierStokes.CorrectionStep.CycleParameters.afterTemporal`, `NavierStokes.CorrectionStep.CycleParameters.afterRank`, `NavierStokes.CorrectionStep.CycleParameters.next`, `NavierStokes.CorrectionStep.CycleParameters.next_alias_error`, `NavierStokes.CorrectionStep.CycleParameters.next_preserve_masses`; [SignedCovariance](../../NavierStokes/SignedCovariance.lean) — `NavierStokes.SignedCovariance.increment`, `NavierStokes.SignedCovariance.cross_reconstruct`; [SignedWaveUpdate](../../NavierStokes/SignedWaveUpdate.lean) — `NavierStokes.SignedWaveUpdate.CovarianceControl`, `NavierStokes.SignedWaveUpdate.CovarianceControl.inverse_class`, `NavierStokes.SignedWaveUpdate.signedScalar`; [LocalSignedRequest](../../NavierStokes/LocalSignedRequest.lean) — `NavierStokes.LocalSignedRequest.requestedStress`, `NavierStokes.LocalSignedRequest.fullRequest`; [VariableGaugeMean](../../NavierStokes/VariableGaugeMean.lean) — `NavierStokes.VariableGaugeMean.temporalIncrementState`, `NavierStokes.VariableGaugeMean.rankIncrementState`; [CorrectionAnalyticStep](../../NavierStokes/CorrectionAnalyticStep.lean) — `NavierStokes.CorrectionAnalyticStep.WaveData`, `NavierStokes.CorrectionAnalyticStep.StaticData`, `NavierStokes.CorrectionAnalyticStep.StepData`, `NavierStokes.CorrectionAnalyticStep.StepResult`, `NavierStokes.CorrectionAnalyticStep.step`. **Obligations:** OBL-NSC-001–004.

<a id="nsc-006"></a>
### NSC-006 — Worked lemma: retain the finite-band matching defect

The matrix algebra (13) does not establish global matching of the assembled physical waves. The actual assumption is
\[
n\ge n_{\rm tail}\ \Longrightarrow\
\operatorname{meanBar}(\mathsf C_{\rm match}^{0,i+1})
 =\operatorname{requestedStress}_i(\text{after particular}),\quad i=0,1.
\tag{19}
\]
`meanBar` is the source's torus average; it is additional to the angular averaging defining the covariance in (14). The requested stress already contains that averaged moving radial primitive.

Let \(D_n\) be either literal difference in (19), on **all** bands. Assume its baseline estimate (11) with \(\alpha=1+\sigma-\kappa\), \(w=\zeta\), and vanishing on the open strip for \(n\ge n_{\rm tail}\). For any desired real exponent \(\beta\), set
\[
M_{\alpha,\beta}=1+\sum_{n<n_{\rm tail}}\epsilon_n^{\alpha-\beta}<\infty.
\]
For \(n<n_{\rm tail}\),
\[
\epsilon_n^\alpha=\epsilon_n^{\alpha-\beta}\epsilon_n^\beta
\le M_{\alpha,\beta}\epsilon_n^\beta.
\]
For later bands, every derivative of \(D_n\) vanishes since the domain is open and the field is zero there. Hence
\[
|D^{\le m}D_n(y)|\le C_mM_{\alpha,\beta}\epsilon_n^\beta
 [S_n\max(1,\delta^{-1})]^{p_m}\zeta(y).
\tag{20}
\]
The edge weight and polynomial degree are unchanged. This is stronger and more precise than saying “a finite number of errors are harmless.” A mere unweighted bound would not give (20) near flat spatial edges. The constants can grow with \(\beta\) and the fixed tail threshold; no uniformity in either is asserted.

The baseline class is established in source from the moving-field regularity of both the cross tensor and the actual reconstructed post-particular residual. Thus (20) upgrades an **already weighted** defect. In the step proof it is used at \(\beta=1+\sigma+17/100+\kappa\), the exponent appearing in (15)–(16).

**Dependencies:** only the abstract weighted definition NSC-004 for the proof; its application uses the inputs of NSC-005, not its conclusion. **Status:** complete conditional calculation; source-established application interface. **Sources:** [FiniteHeadClass](../../NavierStokes/FiniteHeadClass.lean) — `NavierStokes.FiniteHeadClass.comparison`, `NavierStokes.FiniteHeadClass.jet_bound`, `NavierStokes.FiniteHeadClass.meanClass_all_exponents`; [SignedCrossDefectClass](../../NavierStokes/SignedCrossDefectClass.lean) — `NavierStokes.SignedCrossDefectClass.residual_defects_mem`, `NavierStokes.SignedCrossDefectClass.residual_defects_all_exponents_of_primitive`; [CorrectionAnalyticStep](../../NavierStokes/CorrectionAnalyticStep.lean) — `NavierStokes.CorrectionAnalyticStep.StepData.cross_tail`, `NavierStokes.CorrectionAnalyticStep.step`. **Obligations:** OBL-NSC-004 for actual baseline bounds and tail matching; the elementary exponent transfer is expanded here.

## Iteration, physical prefixes, and the analysis interface

<a id="nsc-007"></a>
### NSC-007 — One run, including the singular zeroth physical stage

Fix the ledger of NSC-004. Initialize once, then use the same fixed cycle parameters to define \(x_{J+1}=\operatorname{step}(x_J)\). The source propagates not only the analytic invariant but coherence and periodicity. Induction is now straightforward: \(\sigma_0=1/5\) and U4 gives \(\sigma_{J+1}=\sigma_J+1/10\). This induction is useful only because the concrete native constructors supply U4's data from the current state; no new signed request or independent velocity is selected at a later stage.

The physical sequences are increments \((A_j,B_j,P_j)\), where \(A_j\) is a vector potential, \(B_j\) a direct angular velocity, and \(P_j\) pressure. They are literally
\[
\begin{aligned}
A_0&=A_{b,\rm gauged}+A_{\rm initial},&
 B_0&=B_{\rm initial},&P_0&=p_b+P_{\rm initial},\\
A_{J+1}&=A_{P,J}+A_{S,J}+A_{\rm stream,J},&
 B_{J+1}&=B_{\rm angular,J},&
P_{J+1}&=P_{P,J}+P_{S,J}+P_{\rm mean,J}.
\end{aligned}
\tag{21}
\]
The initial potential includes the initial primary wave and the initialized temporal/rank stream. It is not just the primary wave. The initial direct field is the initialized angular mean, not an invented zero. The positive stream is the sum of the temporal and rank stream increments of the cycle; positive mean pressure is a difference of reconstructed pressures.

Define the physical uncut prefixes **including index zero**:
\[
U_J=\nabla\times\sum_{j=0}^{J}A_j+\sum_{j=0}^{J}B_j,
\qquad p_J=\sum_{j=0}^{J}P_j.
\tag{22}
\]
The state after \(J\) cycles corresponds to (22), not to a prefix with only \(J\) terms. A curl applied to the initialized potential is the initial oscillatory velocity plus stream velocity, with the gauged base curl added.

Physical realization means equality of field **germs** on every valid chart, so the derivatives entering the residual also agree. For example, the chart's velocity scaling \(Q_n^{-a_h}\) cancels the coefficient representation factor \(Q_n^{a_h}\); pressure uses \(Q_n^{-2a_h}\) and \(Q_n^{2a_h}\). Angular frame rotation and its inverse cancel as well. A pointwise identity at a chart center alone would not suffice.

The source's `PhysicalData` additionally requires velocity twice differentiable and pressure differentiable on the chart domains, and equality with the same base outside the active annulus when \(q<Q_N\). Its `StageRealizations` are only for bands above the fixed residual floor. This is a second band restriction, distinct from (19).

Each initialization correction and every positive potential/direct/pressure stage vanishes as a germ off the active annulus within \(t<1,q<q_{\rm big}\). On the axis the annulus is absent. This gives a common geometric reason that corrections preserve the core, including after taking curl. The singular base itself is **not** such a vanishing stage. The later diagonal has an eventual origin identity because its zeroth cutoff also has to reach one; (8) is not asserted for the final field at every earlier time.

> **Unexpanded lemma U5 — coherent physical realization.**
> For every budget \(B_{\rm bud}\), threshold \(N_0\ge\texttt{ActualCarrierGeometry.geometricThreshold}\), and \(J\), `NavierStokes.ActualCyclePreservation.state_runInvariant` supplies the invariant for the literal iterated state. For those same arguments, `NavierStokes.ActualCandidateAssembly.physicalData` identifies (22) with that state in `ActualCycleResidualBounds.PhysicalData`, using the run's `residualBand`.
>
> The source proof assembles initial, particular, signed, mean, and exterior identities. A complete human proof of native-copy transport, overlap compatibility, and the initial primary/mean construction is missing (OBL-NSC-005). This is not an additional existence premise in those source theorems, but it is an unresolved derivation in this companion.

**Dependencies:** NSC-002–006. **Status:** source-established definitions and inspected assembly; conditional human reconstruction. **Sources:** [ActualCyclePreservation](../../NavierStokes/ActualCyclePreservation.lean) — `NavierStokes.ActualCyclePreservation.state_runInvariant`, `NavierStokes.ActualCyclePreservation.state_coherent`; [ActualCandidateAssembly](../../NavierStokes/ActualCandidateAssembly.lean) — `NavierStokes.ActualCandidateAssembly.initialPotential`, `NavierStokes.ActualCandidateAssembly.initialDirect`, `NavierStokes.ActualCandidateAssembly.zerothPotential`, `NavierStokes.ActualCandidateAssembly.positivePotential`, `NavierStokes.ActualCandidateAssembly.positivePressure`, `NavierStokes.ActualCandidateAssembly.potentialStages_zero`, `NavierStokes.ActualCandidateAssembly.directStages_zero`, `NavierStokes.ActualCandidateAssembly.stageRealizations`, `NavierStokes.ActualCandidateAssembly.physicalData`, `NavierStokes.ActualCandidateAssembly.PhysicalStage.axisZeroOn`; [ActualCycleResidualBounds](../../NavierStokes/ActualCycleResidualBounds.lean) — `NavierStokes.ActualCycleResidualBounds.PhysicalFields`, `NavierStokes.ActualCycleResidualBounds.PhysicalData`. **Obligations:** OBL-NSC-001–005.

<a id="nsc-008"></a>
### NSC-008 — Quantified finite-prefix and raw-increment theorem

For the **same** sequences (21), fixed parameters, and a fixed positive \(q_{\rm big}\), the source constructs functions \(L_A,L_B,L_P,L_{\rm bg},L_R\) of derivative order, independent of the stage. On
\(\mathcal D=\{t<1,\ 0<q<q_{\rm big}\}\), all raw stages are smooth. For \(F_j=A_j,B_j,P_j\), respectively,
\[
\forall j\ge1\ \forall m\ \exists C_{j,m},\ell_{j,m}\quad
\|D^mF_j(t,x)\|
\le C_{j,m}(1+|\log q|)^{\ell_{j,m}}q^{g_j-L_F(m)}
\quad ( (t,x)\in\mathcal D,\ q\le1).
\tag{23}
\]
The constants and log powers can depend on stage and order. They cannot depend on the cutoff \(a_j\), which has not yet been chosen. Stage zero is exempt from (23).

For every \(J,m\), the actual prefixes (22) satisfy, near the terminal origin from the past,
\[
D^mU_J=O(q^{-L_{\rm bg}(m)}),\qquad
D^m\mathcal R(U_J,p_J)=O(q^{g_J-L_R(m)}).
\tag{24}
\]
Each statement has its own constant and neighborhood, possibly depending on \(J,m\). Uniformity means **loss functions independent of \(J\)**, not uniform constants for the entire iteration.

The native-to-physical arithmetic can be checked independently. For positive increment \(j\), the conservative native exponents are
\[
\begin{aligned}
\alpha_A(j)&=j/10+3/5-\kappa,\\
\alpha_P(j)&=j/10+11/10-\kappa,\\
\alpha_M(j)&=j/10+11/10-2\kappa.
\end{aligned}
\]
Since \(\epsilon_n=Q_n^h\), for example
\[
h\alpha_A(j)=g_j+h(3/5-\kappa)\ge g_j.
\tag{25}
\]
Likewise the residual class after \(J\) cycles has native exponent \(1/2+\sigma_J=7/10+J/10\), so
\[
h(1/2+\sigma_J)=g_J+7h/10\ge g_J.
\tag{26}
\]
The fixed spatial/time rescaling powers and chart differentiation losses are absorbed in the \(L\)'s, not in a new value of \(h\). Slow polynomial growth becomes the logarithmic factor in (23); weighted edge decay controls the physical chart edges. Equations (25)–(26) alone do not justify these coordinate transfers.

> **Unexpanded lemma U6 — physical estimates on the realized fields.**
> `NavierStokes.ActualCandidateAssembly.estimates B N0 hN` has precisely the budget/threshold hypotheses of U5 and returns `MixedCandidateAssembly.StageEstimates h (qbig B N0)` for its literal `potentialStages`, `directStages`, and `pressureStages`. This record contains stage smoothness, raw bounds (23), monotone unbounded gain, and both finite-prefix bounds (24).
>
> The residual producer `NavierStokes.ActualCycleResidualBounds.finite_residual_rates` requires a fixed \(N\ge4\), geometric threshold, a parameter sequence, the analytic invariant for **every** iterate beginning at `initialCycleState`, and `PhysicalData B N` for **those same** velocities and pressures. Its conclusion has loss `fixedLoss m` chosen before \(J\). `ActualCandidateAssembly.physicalData` supplies that realization in the actual run; it is not inferred from arithmetic.
>
> The all-order native-to-Cartesian estimates, stage-independent loss closure, and gluing estimates remain unexpanded (OBL-NSC-006). Thus (23)–(24) are source-established inputs to the next chapter, not independently derived analytic results here.

Why these precise estimates? The finite residual gain in (24) permits a prefix with arbitrarily accurate residual. The background estimate controls products with a small diagonal tail. Raw bounds (23) allow one cutoff schedule to make that tail small in all required derivative orders. A gain without the same-field identities of U5, or losses increasing uncontrollably with \(J\), would not serve this purpose.

**Dependencies:** NSC-004–007. **Status:** source-established theorem interface, conditional exposition; (25)–(26) are expanded arithmetic. **Sources:** [ActualCandidateAssembly](../../NavierStokes/ActualCandidateAssembly.lean) — `NavierStokes.ActualCandidateAssembly.estimates`; [MixedCandidateAssembly](../../NavierStokes/MixedCandidateAssembly.lean) — `NavierStokes.MixedCandidateAssembly.StageEstimates`; [CutStageEstimates](../../NavierStokes/CutStageEstimates.lean) — `NavierStokes.CutStageEstimates.RawStageBounds`; [ActualCycleResidualBounds](../../NavierStokes/ActualCycleResidualBounds.lean) — `NavierStokes.ActualCycleResidualBounds.finite_residual_rates`, `NavierStokes.ActualCycleResidualBounds.fixedLoss`; [GluedStageEstimates](../../NavierStokes/GluedStageEstimates.lean) — `NavierStokes.GluedStageEstimates.actualStageEstimates`; [ActualIterationLedger](../../NavierStokes/ActualIterationLedger.lean) — `NavierStokes.ActualIterationLedger.wave_physical_gap`, `NavierStokes.ActualIterationLedger.pressure_physical_gap`, `NavierStokes.ActualIterationLedger.mean_physical_gap`, `NavierStokes.ActualIterationLedger.residual_physical_gap`. **Obligations:** OBL-NSC-001–006.

<a id="nsc-009"></a>
### NSC-009 — Handoff: one diagonal, not a new construction

Use one increasing sequence of positive integers \(a_j\), with \(a_{j+1}\ge2a_j\) and \(1/a_j<q_{\rm big}\), simultaneously for
\[
A_\infty=\sum_{j\ge0}\chi(a_jq)A_j,\quad
B_\infty=\sum_{j\ge0}\chi(a_jq)B_j,\quad
P_\infty=\sum_{j\ge0}\chi(a_jq)P_j,
\qquad U_\infty=\nabla\times A_\infty+B_\infty.
\tag{27}
\]
All three sums are locally finite for \(q>0\). They use exactly (21). Presingular local finiteness says nothing by itself about endpoint residual smoothness.

The cutoff product estimate is also explicit. If \(|D^k\chi(aq)|\le Q_kq^{-k}\) uniformly in \(a\ge0\), Leibniz and (23) give
\[
|D^m[\chi(aq)F_j]|
\le K_{j,m}(1+|\log q|)^{\ell'_{j,m}}
q^{g_j-\widehat L_F(m)},
\quad
\widehat L_F(m)=\operatorname{finiteBound}(L_F,m)+m.
\tag{28}
\]
Indeed, the term with \(k\) derivatives on the cutoff has exponent \(g_j-L_F(m-k)-k\); bounding \(k\le m\) and all lower-order losses yields (28), while \(\sum_k\binom mk=2^m\) controls constants. The finite bound is the source's nonnegative upper envelope, not an assumption that \(L_F\) is monotone.

One spends part of the positive raw gain to absorb the stage constant and logarithm and obtain summable cutoff bounds. For example, for fixed \(j\ge1\), \(q^{g_j/2}(1+|\log q|)^\ell\to0\). Taking \(a_j\) large makes the remaining factor at most \(2^{-j}\) on \(q\le1/a_j\), simultaneously for finitely many orders \(m\le j+2\) and all three fields. Thus the effective gain is smaller than the raw gain; it must not be silently identified with it. There is no smallness demand of this type on \(j=0\).

A different finite head now appears. In the diagonal-minus-prefix calculation, for each fixed \(J\),
\[
\sum_{j=0}^J(\chi(a_jq)-1)A_j=0
\quad\text{as a germ when }q<\frac1{2\max_{j\le J}a_j},
\tag{29}
\]
and similarly for \(B,P\). The strict inequality gives an open plateau, so all derivatives agree. This is a **finite cycle-prefix head**, not the finite band head of NSC-006. Both are necessary. The remaining tail begins at \(J+1\), and curl costs one additional derivative of the potential.

The source consumer `StageEstimates.exists_schedule` assumes exactly the stage record in NSC-008, \(0<h<1/2\), \(q_{\rm big}>0\), and an arbitrary lower bound for \(a_0\). It produces one schedule, smooth sums, and vanishing joint residual jets. This chapter exports its inputs and the arithmetic (28)–(29); the full nonlinear flatness/endpoint argument is reserved for the analysis chapter. Its correct target quantifiers are \(\forall m,N\ \exists J,C,U\), not one common prefix for every order.

At the origin, the initial correction and positive correction germs vanish; the direct angular fields vanish there. Once \(a_0q<1/2\), the diagonal therefore retains (8). The gauge in NSC-003 must remain unchanged during spatial localization. Any later theorem about a different choice of fields or different schedule needs a new equality proof.

**Dependencies:** NSC-003, NSC-007–008. **Status:** conditional handoff; product/head calculations expanded, analytic cutoff derivative and physical estimates imported. **Sources:** [CutStageEstimates](../../NavierStokes/CutStageEstimates.lean) — `NavierStokes.CutStageEstimates.cut_product_bound`, `NavierStokes.CutStageEstimates.cutLoss`; [MixedCandidateAssembly](../../NavierStokes/MixedCandidateAssembly.lean) — `NavierStokes.MixedCandidateAssembly.StageEstimates.exists_schedule`; [ActualCandidateAssembly](../../NavierStokes/ActualCandidateAssembly.lean) — `NavierStokes.ActualCandidateAssembly.Witness`, `NavierStokes.ActualCandidateAssembly.selected_witness`; [GermCandidateAssembly](../../NavierStokes/GermCandidateAssembly.lean) — `NavierStokes.GermCandidateAssembly.origin_eventually_base`. **Obligations:** OBL-NSC-001–006; full schedule and endpoint review delegated to analysis, not declared complete here.

## Local source and obligation ledger

The citations above inherit the baseline SHA. This table identifies the load-bearing declarations rather than listing every imported module.

| Human assertion | Precise source declaration | What it does not establish by itself |
|---|---|---|
| NSC-001: actual positive coordinate | `NavierStokes.SimilarityCoordinates.coordinateQ_spec` | Cartesian all-order residual bounds |
| NSC-002: closed profile | `NavierStokes.PreparedOutgoing.exists_prepared`; `NavierStokes.NominalConeAssembly.exists_nominal_cone`; `NavierStokes.FinalSlowBase.profileData_nonempty` | An expanded human proof of the outgoing/cone/modulation construction |
| NSC-002: base remainder | `NavierStokes.FinalSlowBase.error_jetRate` | Vanishing of the stress force |
| NSC-003: axis and gauge | `NavierStokes.BaseResidual.baseVelocity_at_origin`; `NavierStokes.TailGaugePotential.finalPotential_sameCurl`; `NavierStokes.TailGaugePotential.finalPotential_awayExtensions` | Equality after cutting off an arbitrary different gauge |
| NSC-005: actual analytic cycle | `NavierStokes.CorrectionAnalyticStep.step` | Native inputs without its `StaticData`, invariant and `StepData` |
| NSC-006: finite head | `NavierStokes.SignedCrossDefectClass.residual_defects_all_exponents_of_primitive`; `NavierStokes.FiniteHeadClass.meanClass_all_exponents` | Exact matching in early bands |
| NSC-007: coherent induction | `NavierStokes.ActualCyclePreservation.state_runInvariant`; `NavierStokes.ActualCandidateAssembly.physicalData` | Smallness of the singular stage zero |
| NSC-008: physical rates | `NavierStokes.ActualCandidateAssembly.estimates`; `NavierStokes.ActualCycleResidualBounds.finite_residual_rates` | Uniform constants over all prefixes |
| NSC-009: common diagonal | `NavierStokes.MixedCandidateAssembly.StageEstimates.exists_schedule`; `NavierStokes.ActualCandidateAssembly.selected_witness` | A force-free presingular solution or prize certification |

### Open human-derivation obligations

All records below have owner **ns-construction**, status **open**, and history **identified during source inspection; no independent review or closure evidence yet**. A source theorem is not evidence that its human derivation has been supplied.

| ID | Missing assertion, hypotheses, and closure evidence | Affected conclusions/source leads |
|---|---|---|
| OBL-NSC-001 | Derive prepared outgoing profile, matching, finite modulation and true cone without assumed prepared data. Must respect the ordered reset/amplitude/scale/height/radius choices. Need worked ODE/moment/cone estimates and independent hypothesis review. | U1; NSC-002 onward. `PreparedOutgoing.exists_prepared`, `NominalConeAssembly.exists_nominal_cone`, `FinalSlowBase.profileData_nonempty`. |
| OBL-NSC-002 | Derive actual finite-profile identities and all-order base remainder on `PhysicalApproach`, including common bundle scales and weighted edge estimates. Need derivative-counted Borel remainder proof, not (7) alone. | U2; base estimates and every later residual conclusion. `NavierStokes.FinalSlowBase.error_jetRate`, `NavierStokes.FinalSlowBase.weighted_jets`. |
| OBL-NSC-003 | Prove anchored heat-primitive comparison and genuine compatible exterior extensions for the same gauged base potential, in both central and nonzero-axial branches. Need full neighborhood/regularity argument. | U3; localization/endpoint handoff. `TailGaugePotential.finalPotential_awayExtensions`. |
| OBL-NSC-004 | Expand native particular Volterra and signed quotient estimates, supported covariance assembly, actual tail identity, and temporal/rank/pressure gain closure under U4's full hypotheses. Need one analytic cycle, not only algebra (12)–(20). | U4; NSC-005–009. `CorrectionAnalyticStep.step`, its native-control producers and mean-gain calls. |
| OBL-NSC-005 | Derive initialization and transport/overlap identities identifying one coherent run with (21)–(22), retaining initial direct field, pressure differences and valid-band floors. Need chart-germ and exterior proofs for every component. | U5; same-field blowup/residual correspondence. `NavierStokes.ActualCandidateAssembly.stageRealizations`, `NavierStokes.ActualCandidateAssembly.physicalData`; `ActualCyclePreservation.state_runInvariant`. |
| OBL-NSC-006 | Expand all-order physical increment/background/residual estimates with losses fixed before stage, on the stated sublevel and terminal approach. Need complete native-to-Cartesian gluing and logarithmic-loss bookkeeping. | U6; (23)–(29) and downstream flatness. `GluedStageEstimates.actualStageEstimates`, `ActualCycleResidualBounds.finite_residual_rates`. |

**Integrator/analysis handoff.** Export NSC-001 (\(q\) and norms), NSC-003 (base axis/gauge), NSC-007 (literal sequences and prefix convention), NSC-008 (quantified physical inputs), and NSC-009 (single-schedule and finite-head requirements). No numbered external chapter lemma is imported. Every downstream human construction conclusion remains conditional on OBL-NSC-001–006 until those derivations and reviews are completed.

**Local mechanical check.** Relative source-file links resolve and all nine explicit human anchors are unique (read-only author check; this does not validate declaration hypotheses or mathematical implications). HEAD remained at the baseline during authoring and tracked source diff was not modified by this task.

**Validation status.** Authored using selected model `gpt-6-astra`; both prior Astra reports were read in full and treated as research leads. Selected source declarations and local proof bodies were independently inspected. No build, kernel check, independent mathematics review, or pedagogical cold-read was performed. The five plan gates are not claimed passed. This is an auditable partial reconstruction, not a completed self-contained proof or a certification claim.
