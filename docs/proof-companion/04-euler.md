# 04 — Euler: exact packet stages and a stability contradiction

**Baseline:** `597692fa5d55e07d810b2d96ead1a67972585425`, as specified in [PLAN.md](PLAN.md). **Owner:** `euler`. **Status:** documentation-only author draft; not an independently audited human proof.

This chapter concerns **unforced, zero-viscosity Euler**, not a Navier–Stokes theorem or prize certification.

The central idea is unusual enough to state first. Construct different exact Euler solutions \(u_n\), whose initial velocities approach one smooth compactly supported datum \(u_{\mathrm{init}}\). At selected times their gradients become arbitrarily large. If a sufficiently long, sufficiently regular evolution \(U\) from \(u_{\mathrm{init}}\) existed, stability would keep \(u_n\) close to \(U\) in a norm controlling gradients. That is the contradiction. It is **not** an explicit formula for a divergent trajectory of the limiting solution.

This chapter expands the outer argument, the numerical summability mechanism, a scalar growth comparison, and the minimal gradient invariant. The complete nonlinear insertion and its renewable geometry remain explicitly **unexpanded source inputs**. The conditional human proof below inherits those obligations even though the delivered Lean declarations have no packet-existence premise.

**Reading transition.** This is an independent branch after the [scope chapter](01-scope.md), not a consequence of chapters 02–03. Its local scales and spatial-only derivative notation restart below. Compare the two solution classes in EUL-001 before using EUL-010; consult the [source map](SOURCE-MAP.md) and [review ledger](VALIDATION.md) after the outer contradiction. The scope chapter supplies a partial internal class translation, not external-prose equivalence. There is no Euler-to-viscous-NS implication.

## Reading conventions and evidence labels

We write \(u(t,x)\), \(p(t,x)\), \(x\in\mathbb R^3\), with
\[
 \partial_tu+(u\cdot\nabla)u+\nabla p=0,\qquad \nabla\cdot u=0.
\]
The delivered source writes velocity and pressure as `v x t`, `p x t`; parent-packet fields instead use `(t,x)`. The word `force` in a parent Euler state means **\(\nabla p\)**. It is not an external forcing term. The source explicitly requires both the scalar-pressure identity and zero momentum residual.

Let \(D^r u=D_x^r u\) be the spatial Fréchet derivative tensor, with its multilinear operator norm, and set
\[
 \mathcal H_m(u)=\sum_{r=0}^m\left(\int_{\mathbb R^3}|D^r u(x)|^2\,dx\right)^{1/2}.
\]
This is the source's `tensorNorm`/`derivativeSum` for the smooth square-integrable representatives used here. It is equivalent, at each fixed order, to a conventional coordinate \(H^m\) norm: each coordinate derivative is an evaluation of the tensor on coordinate unit vectors; conversely a multilinear map is a finite sum of its coordinate entries. Integrating these pointwise comparisons and using the finite-sum Cauchy–Schwarz inequality proves equivalence, with constants depending on \(m\) and dimension. Numerical source constants below refer to \(\mathcal H_m\), not an arbitrarily renormalized \(H^m\).

The ordinary evolution class consists of actual spatially smooth fields with every spatial jet in \(L^2\), continuously in time. Its pressure-gradient field has the same all-order \(L^2\) continuity, velocity belongs to the closed solenoidal subspace, and the pressure field belongs to the closed gradient subspace. Its interior pointwise Euler time law yields a compatible strong time derivative with all-order regularity. Scalar pressure is recovered in that theory. We do not infer this class merely from joint classical smoothness and finite energy; that inference needs the compact-vorticity bridge in EUL-010.

Evidence labels:

- **Source-established:** the cited declaration and relevant interface/proof were inspected at this baseline; no fresh kernel run or complete dependency audit is implied.
- **Conditional exposition:** the displayed ordinary-mathematical argument is proved from its stated analytic inputs; unresolved inputs are carried forward.
- **Unexpanded lemma:** a load-bearing source input whose full human derivation is not supplied here.
- **New research:** a proposed result absent from this reconstruction, not an asserted theorem.

Norm sources: [OrdinaryH3Norms.lean](../../Euler/OrdinaryH3Norms.lean) — `EulerOrdinarySobolev.tensorNorm`, `EulerOrdinarySobolev.tensorNorm_three_le`, `EulerOrdinarySobolev.energy_le_tensorNorm_sq`; [PacketFieldPhysicalSobolev.lean](../../Euler/PacketFieldPhysicalSobolev.lean) — `EulerPhysicalL2Scaling.derivativeSum`. Equation source: [ParentEulerState.lean](../../Euler/ParentEulerState.lean) — `EulerParentPacketFrames.Evolution`, especially `pressure_gradient` and `momentum_zero`. Ordinary-class source: [OrdinaryEulerDifference.lean](../../Euler/OrdinaryEulerDifference.lean) — `EulerOrdinarySobolev.Evolution`, `EulerOrdinarySobolev.Evolution.derivative_continuous`, `EulerOrdinarySobolev.Evolution.energyDerivative_bound`.

<a id="eul-001"></a>
### EUL-001 — The delivered theorem and its two solution classes

**Statement translation; source-established. Dependencies:** the conventions above. **Obligations:** OBL-EUL-006, and for the human proof of existence all construction obligations below.

The declaration `Euler.exists_compact_smooth_euler_singularity` asserts the existence of a nonzero, divergence-free \(u_{\mathrm{init}}\in C_c^\infty(\mathbb R^3;\mathbb R^3)\), a time \(0<T_*\le1\), and an unforced scalar-pressure solution \((u,p)\) on \([0,T_*)\) such that:

1. Velocity and a strong time-derivative witness have continuous \(L^2\) spatial jets of every finite order. The pressure is spatially differentiable and the equation with this witness holds at **interior times**. No endpoint time-derivative condition is part of this class.
2. There is one finite bound for \(\|u(t)\|_2^2\) over \(0\le t<T_*\).
3. For every \(T>0\), an evolution from the same datum in this Sobolev class on the **closed** interval \([0,T]\) exists if and only if \(T<T_*\).
4. Define the extended nonnegative quantities
   \[
   C_1(t)=\sup_x|u(t,x)|+\sup_x\|Du(t,x)\|_{\rm op},\qquad
   W(t)=\sup_x|\omega(t,x)|,\quad \omega=\nabla\times u.
   \]
   For each \(0<T<T_*\), \(\sup_{0\le t\le T}C_1(t)<\infty\) and \(\int_{[0,T)}W(t)\,dt<\infty\), whereas
   \[
   \limsup_{t\uparrow T_*}C_1(t)=+\infty,\qquad
   \int_{[0,T_*)}W(t)\,dt=+\infty.
   \]
   These are pointwise spatial suprema and an extended nonnegative Lebesgue integral, not a conventionally zero-valued real integral of a nonintegrable function. A limsup is not asserted to be a limit.
5. There is no **global Comparator-class** solution from \(u_{\mathrm{init}}\). That class requires jointly smooth velocity and pressure on \(\mathbb R^3\times[0,\infty)\), Euler with the right-sided derivative convention at zero, divergence freedom, the initial trace, \(L^2\) velocity at every nonnegative time, and one energy bound over all future times. It does not assume global bounds on all derivative norms or pressure decay.

The datum also satisfies, for every integer \(m\ge0\) and real \(K\),
\[
 |D^m u_{\mathrm{init}}(x)|\le C_{m,K}(1+|x|)^{-K}.
\]
Indeed each derivative is compactly supported and smooth, so the continuous weighted derivative norm has a finite maximum. This is the direction of admissibility needed for the constructed datum.

A value assigned to the total function \(u(T_*,x)\) outside its specified time domain is not a classical terminal solution. In fact the adapter extends by zero outside the lifespan solely to obtain total functions.

**Sources:** [Solution.lean](../../Euler/Solution.lean) — `Euler.exists_compact_smooth_euler_singularity`, `Euler.euler_breakdown_R3`; [SolutionDefinitions.lean](../../Euler/SolutionDefinitions.lean) — `Euler.SobolevSmoothOn`, `Euler.EulerSobolevExistenceAndSmoothnessR3On`, `Euler.EulerExistenceAndSmoothnessR3`, `Euler.velocityC1Norm`, `Euler.vorticityNorm`; [InitialDataBridge.lean](../../Euler/InitialDataBridge.lean) — `Euler.initialVelocityConditionDecay_of_compact`; [ComparatorMaximalFields.lean](../../Euler/ComparatorMaximalFields.lean) — `Euler.ComparatorBridge.maximalVelocityExtension`.

<a id="eul-002"></a>
### EUL-002 — Fix one numerical hierarchy before constructing stages

**Source-established definitions and selection interface; conditional numerical explanation. Dependencies:** EUL-001 conventions only. **Obligation:** OBL-EUL-001.

All indices in this chapter are Euler-local. Fix integers \(J,D\), a large real \(X\), and write
\[
 j_n=J+n,\quad x_0=X,\quad x_{n+1}=j_n^2x_n.
\]
The insertion taking stage \(n\) to stage \(n+1\) uses scales
\[
 s_n=e^{x_n/j_n^5},\quad k_n=e^{x_n/j_n^2},\quad
 \delta_n=e^{-x_n/j_n^3},\quad \ell_n=e^{-x_n/j_n^{7/2}}.
\]
They respectively represent target shear, oscillation wavenumber in rescaled coordinates, a spike-amplitude factor, and the parent's physical localization scale. The physical oscillatory frequency is of order \(k_n/\ell_n\), not \(k_n\).

The shear already present, previous frequency, and older shear retain their exceptional base values:
\[
 a_0=X^{1000},\quad a_{n+1}=s_n;\qquad
 b_0=X^D,\quad b_{n+1}=k_n;\qquad
 o_0=1,\quad o_{n+1}=a_n.
\]
Put \(w_n=3x_{n+1}x_n/\sqrt{a_n}>0\). A stage has activation time \(t_n\) and horizon
\[
 T_n=t_n+2w_n.
\]
In particular, the horizon exceeds activation by **twice** the defined width. At the base, \(t_0=0\); \(T_0=2w_0\le1\). Neither the polynomial base shear nor the first frequency is obtained by substituting a negative index into an exponential formula.

The selected `Scales` record has \(J\ge3\), \(D\ge2000\), \(X\ge8\), and a separate total error budget \(\eta>0\) (the source record calls it `δ`; it is not \(\delta_n\)). It requires \(\eta\le1/16\), activation and geometric smallness, all-stage frequency guards, base localization, and simultaneous summable costs. In particular the correction costs \(k_n^{-1/4}\), initial-strain costs, pressure costs, and renewal costs are controlled; the renewal series has bound \(1/4\). `exists_scales` first selects \(D\), then an admissible offset \(J\), then a sufficiently large \(X\) satisfying a finite intersection of eventual conditions. It is not choosing a new \(X\) for each future stage.

Why this is possible at the level of elementary growth is visible from
\[
 \log k_n=x_n/j_n^2\gg\log s_n=x_n/j_n^5,
 \qquad x_n=X\prod_{i<n}(J+i)^2.
\]
Exponential decay in \(x_n/j_n^r\) beats fixed polynomial prefactors. But this observation alone does **not** check the whole ledger: the physical source costs, their powers, the base exceptions, and every renewal guard must first have the asserted form.

> **Unexpanded numerical closure.** For every real \(c\ge0\) and real threshold \(B\), `EulerPacketInductionScales.exists_scales` produces `Scales c B`, including `ActualBounds`, `FirstScaleGuards`, universal frequency conditions and all listed series. The source proof of the selection interface was inspected; the full common-guard and cost-estimate dependency closure has not been reproduced. OBL-EUL-001 is the missing all-budget verification, not a claim that the source lacks a scale choice.

**Sources:** [PacketSourceScaleSequence.lean](../../Euler/PacketSourceScaleSequence.lean) — `EulerPacketSourceScaleSequence.shear`, `EulerPacketSourceScaleSequence.frequency`, `EulerPacketSourceScaleSequence.spike`, `EulerPacketSourceScaleSequence.supportScale`, `EulerPacketSourceScaleSequence.previousShear`, `EulerPacketSourceScaleSequence.previousFrequency`, `EulerPacketSourceScaleSequence.olderShear`, `EulerPacketSourceScaleSequence.timeWidth`; [PacketInductionScales.lean](../../Euler/PacketInductionScales.lean) — `EulerPacketInductionScales.Scales`, `EulerPacketInductionScales.exists_scales`; [PacketInductionStage.lean](../../Euler/PacketInductionStage.lean) — `EulerPacketInduction.GrowthData`, `EulerPacketInduction.Stage`.

<a id="eul-003"></a>
### EUL-003 — Transport, polarization, and an explicit amplification calculation

**Conditional exposition with source-established scalar comparison. Dependencies:** EUL-002 for its application to packets, not for the scalar ODE. **Obligation:** OBL-EUL-002.

An Euler parent is actual particle geometry. If \(\Phi(t,a)\) is its particle map, then
\[
 \partial_t\Phi(t,a)=u(t,\Phi(t,a)),\qquad \det D_a\Phi=1,
\]
\[
 D_a\partial_t\Phi\,(D_a\Phi)^{-1}=Du(t,\Phi(t,a)),\qquad
 \partial_t^2\Phi=-\nabla p(t,\Phi).
\]
The source strain and curvature fields evaluate these physical quantities at labels \(\ell x\); curvature is the pressure Hessian, not an independent matrix. A packet's phase normal is pulled along the deformation. For a background matrix \(B(t)\), its ray \(m(t)\ne0\) and velocity polarization \(v(t)\ne0\) obey
\[
 m'=-B^\top m,\qquad
 v'=-Bv+2\frac{\langle m,Bv\rangle}{|m|^2}m.
\]
Here \(v\) is a finite-dimensional polarization, not the whole velocity field. Direct differentiation gives two useful identities:
\[
 \frac d{dt}\langle m,v\rangle
 =-\langle m,Bv\rangle-\langle m,Bv\rangle
   +2\langle m,Bv\rangle=0,
\]
\[
 \frac d{dt}|m|^2=-2\langle Bm,m\rangle.
\]
Thus transverse polarization stays transverse, and compression in the ray direction increases its length. This is why the induction retains both an angular/coupling condition and a compression margin. A claim about shear growth cannot be based on frequency alone.

Here is a complete scalar comparison consumed by the ray analysis. Suppose \(0\le\beta\le1/2\), \(T\ge0\), \(\beta T^2\le1\); let differentiable \(V\) have derivative \(V_1\), and assume its differentiable flux satisfies on \([0,T]\)
\[
 F=(1+\beta^2s^4)V_1,\qquad
 F'=2(1-\beta^2s^2)V,\qquad V(0)=1,\quad V_1(0)\ge0.
\]
Set \(D=1+\beta^2s^4\), \(c=2(1-\beta^2s^2)\). The hypotheses imply
\[
 1\le D\le2,\qquad1\le c\le2,\qquad V'=F/D,
\]
since \(0\le\beta s^2\le1\) and \(\beta^2s^2\le\beta\le1/2\). Compare with
\[
 V_*(s)=\cosh(s/\sqrt2),\quad F_*(s)=\sqrt2\sinh(s/\sqrt2),
 \quad V_*'=F_*/2,\quad F_*'=V_*.
\]
For \(z=V-V_*\), \(y=F-F_*\),
\[
 z'=y/D+F_*(1/D-1/2)\ge y/D,\qquad
 y'=cz+(c-1)V_*\ge cz.
\]
Both initial differences are nonnegative. The positive quadrant is invariant: at a first boundary contact the displayed system cannot point outward. To remove the possibility of a zero derivative at contact, add \(\varepsilon e^{3s}\) to each component, use the coefficient bounds to get strict inward derivatives, and let \(\varepsilon\downarrow0\). Consequently
\[
 V(s)\ge\cosh(s/\sqrt2),\qquad F(s)\ge\sqrt2\sinh(s/\sqrt2).
\]
If \(0<\beta\le1/16\), choose \(T=1/\sqrt\beta\ge4\). For \(T\ge4\),
\(e^{T/4}\ge2\), \(T/\sqrt2\ge T/2\), and therefore
\[
 \cosh(T/\sqrt2)\ge\tfrac12e^{T/\sqrt2}
 \ge\tfrac12e^{T/2}\ge e^{T/4}.
\]
This proves amplification at least \(e^{1/(4\sqrt\beta)}\).

The calculation is a finite-dimensional theorem. It does not by itself construct an Euler packet. One must identify the actual transported frame with the normalized ODE, bound its perturbations throughout the growth interval, and transfer the amplified component into the physical strain while renewing the geometry. Those are precisely the unexpanded parts of OBL-EUL-002. In particular \(\beta\) above is not silently identified with the stage tilt without checking that normalization.

**Sources:** [ParentPacketFrames.lean](../../Euler/ParentPacketFrames.lean) — `EulerParentPacketFrames.Parent`, `EulerParentPacketFrames.Parent.frame_det`, `EulerParentPacketFrames.Parent.strain_apply`, `EulerParentPacketFrames.Parent.curvature_apply`; [ParentEulerState.lean](../../Euler/ParentEulerState.lean) — `EulerParentPacketFrames.Evolution.acceleration_match`, `EulerParentPacketFrames.Evolution.strain_eq`, `EulerParentPacketFrames.Evolution.curvature_eq`; [PacketInductionStage.lean](../../Euler/PacketInductionStage.lean) — `EulerPacketInduction.Stage` (frame, coupling, tilt and compression inputs); [EulerProof/PacketGrowth.lean](../../Euler/EulerProof/PacketGrowth.lean) — `EulerPacketGrowth.cooperative_nonneg_of_bounded`, `EulerPacketGrowth.cosh_lower_of_flux_system`, `EulerPacketGrowth.equation30_cosh_lower`, `EulerPacketGrowth.equation30_endpoint_exponential`.

<a id="eul-004"></a>
### EUL-004 — What one insertion must preserve, and why correction is not forcing

**Unexpanded construction theorem with explicit interface and conditional algebra. Dependencies:** EUL-002, EUL-003. **Obligations:** OBL-EUL-001, OBL-EUL-002, OBL-EUL-003.

The precise successor interface fixes an integer construction exponent \(q\) at least `EulerParentNeighborThreshold.requiredExponent`, a real floor \(B\) at least `EulerParentNeighborThreshold.commonThreshold` evaluated at the fixed gradient and Hessian constants, and one `EulerPacketInductionScales.Scales (q : ℝ) B`. Given the **full** `EulerPacketInduction.Stage S n`, it produces `Stage S (n+1)`; the joined branch additionally requires \(n\ne0\). The full stage record, not merely the following abbreviated estimates, is the hypothesis of this unexpanded theorem.

A full stage contains much more than a large gradient. It contains an exact parent Euler state on \([0,T_n]\), its all-order Sobolev realization and odd symmetry, the physical gradient and pressure-Hessian bounds
\[
 \sup_{t\in[0,T_n],x}\|Du_n(t,x)\|\le C_g a_n,\qquad
 \sup_{t\in[0,T_n],x}\|D^2p_n(t,x)\|\le C_p a_no_n,
\]
a label bound \(b_n^{80}\), a scale \(\ell_n\), exterior/core strain and curvature budgets, a fixed core radius \(X^{-1000}\), and the frame needed for the next insertion. If \(\alpha_n=\langle\widehat m_n,B_n\widehat v_n\rangle\) is its coupling and \(\sigma_n\) its nonnegative tilt, the invariant includes
\[
 \tfrac12\le\alpha_n\le2,\qquad
 \tfrac12\le\sigma_n^2x_n^2\le2.
\]
The coupling error is bounded by twice the prefix sum of renewal costs; only earlier indices enter. For \(n>0\), compression has a margin exceeding the prior error \(b_n^{-1/4}\). The stage horizon and next activation obey
\[
 t_{n+1}=t_n+\frac{x_{n+1}}{\sqrt{\sigma_n^2\alpha_na_n}},\qquad
 T_{n+1}=t_{n+1}+2w_{n+1}<T_n.
\]
These are constraints on the same evolving frame, not freely chosen activation times. The actual step length lies between \(w_n/6\) and \(2w_n/3\). Together with the next-width guard this proves nesting; merely making the activation times increasing would not prove that all comparisons fit their horizons.

**Packet shape and initial trace.** In rescaled parent coordinates \(y=x/\ell_n\), the high part has form
\[
 h_n(x)=\ell_n H_n\bigl(y,k_n\langle m_{0,n},y\rangle\bigr),
\]
where the oscillatory profile is a finite inverse-frequency expansion, with cutoff order depending on \(k_n\). The high part is supported in the ball of radius \(\ell_n/2\). There is also a nonoscillating mean field \(\mu_n\), supported in a fixed ball of radius \(2\). For positive-history stages the exact identity is
\[
 u_{n+1}(0)=u_n(0)+h_n+\mu_n.
\]
The small initial amplitude is tied to the inverse of the proved growth, not just the factor \(\delta_n\); EUL-006 displays the indispensable gain \(e^{-x_n/8}\).

**Forward versus joined.** At \(n=0\), activation is at zero; the forward insertion uses its `earlyRatio` guard. For \(n>0\), the joined insertion uses a positive history interval and `badRatio`. The stage invariant supplies
\[
 t_n\ge T_0/12>0,\qquad t_n^{-1}\le12/T_0,
\]
which controls inverse-history-time losses. The joined normal is along the pullback \(F^\top(\widehat m\times\widehat v)\); the time-zero construction uses the forward normal. Substituting zero into joined-history bounds would be invalid. The all-order initial-data series consequently keeps the entire first insertion in the base field \(u_1(0)\).

For the joined constructor, the inspected physical bound has the concrete form
\[
 \|Du_{n+1}\|\le C_ga_n+s_n(r_{\rm good}+r_{\rm bad,n})+k_n^{-1/4},
\]
\[
 \|D^2p_{n+1}\|\le C_pa_no_n
       +2C_ga_ns_n(r_{\rm good}+r_{\rm bad,n})+k_n^{-1/4}.
\]
These hold at every point of the child horizon. The forward bounds replace \(r_{\rm bad,n}\) by the early ratio. Numerical guards must turn these into the next stage bounds; smallness of the final error alone does not control the large main packet terms.

The `GeometryJoinedChoice` input is an actual packet input \(I\), a smooth parent state, universal frequency \(k\), and \(0<\ell_{\rm next}\le1\). Its existence theorem additionally requires: equality of its terminal geometry, its full frequency guard, label constant at most \(k\), and \(\ell_{\rm parent}^{-1}\le k^{3/4}\). The output includes an all-order correction budget, a graph-constrained flow whose coefficient equals the corrected packet coefficient, labels of size \(k^{80}\), displacement at most \(k^{-1/4}\), and physical gradient/pressure-Hessian source errors each at most \(k^{-1/4}\). The child state and renewed frame are assembled from this **one** choice. Selecting a good gradient field and a different good-pressure field would not satisfy this interface.

**Why the residual is removed rather than declared to be a force.** In ordinary physical coordinates, if an approximation \((\widetilde u,\widetilde p)\) has residual \(r\), a correction \((e,\pi)\) must obey
\[
 \partial_te+(\widetilde u\cdot\nabla)e+(e\cdot\nabla)\widetilde u
       +(e\cdot\nabla)e+\nabla\pi=-r,\qquad \nabla\cdot e=0.
\]
Expanding the quadratic term verifies that \((\widetilde u+e,\widetilde p+\pi)\) then has exactly zero Euler residual. This is explanatory physical algebra; the source solves a lifted, variable-metric projected version and then proves the physical graph identities. Pressure cannot absorb an arbitrary \(r\): taking divergence requires
\[
 -\Delta p=\sum_{i,j}(\partial_i u_j)(\partial_j u_i),
\]
and the solenoidal component of the residual must actually be cancelled.

The inspected all-order solver uses one positive period, one coherent approximation/coefficient system \(A\), a genuine inverse metric with time derivative, and one radius path. For every construction order \(q\ge6\), let \(d_q\) be its drift envelope, \(R_{c,q}\) its coefficient scale, and \(R_q\) its residual bound. A common constant \(C\) dominates the proved full-background energy constants. With \(0<\Delta\le1\), \(\rho_0>0\), its hypotheses include
\[
 \rho(t)=\rho_0-2C(d_q+\Delta)t,\quad
 2C(d_q+\Delta)T\le\rho_0/2,\quad \rho_0R_{c,q}\le1,
\]
\[
 2R_qe^{3CT}\le\Delta/2,
\]
for **every** \(q\ge6\), using the same radius and metric and the approximation's lifted divergence constraint. Full background norms enter \(C\); the smaller actual transport drift enters the radius slope. Replacing one by the other is not harmless.

The output is one field \(e\) with zero initial trace and, for each external energy cutoff \(P\ge0\),
\[
 \mathcal E_{P,\rho(t),g(t)}(e(t))
       \le2R_{P+6}e^{3Ct}\le\Delta/2.
\]
Here \(\mathcal E\) denotes the source's radius- and metric-weighted Gevrey energy norm on the lifted cylinder, **not** an unweighted \(\mathcal H_P\) norm; \(g(t)\) denotes the common metric operator. The exact finite weighted norm is defined in the [interface sheet](INTERFACES.md); the finite-order inviscid solver and graph-to-physical gradient transfer remain unexpanded. Uniqueness identifies the finite-order solutions with one common path; the source supplies its strong projected time law, pressure term, pointwise initial zero, and spatial smoothness.

> **Unexpanded packet insertion / correction.** The foregoing interfaces are not a derivation of the packet recursion, lifted pressure estimates, finite-order solver, physical error bounds, or frame renewal. OBL-EUL-002 asks for one continuous physical packet derivation, including the amplification-to-initial-amplitude transfer. OBL-EUL-003 asks for the precise weighted norm, the analytic correction proof, its all-order coherence, and verification that the same corrected field has exact physical Euler dynamics and the renewed gradient invariant. Ordinary local existence cannot replace these quantitative inputs.

**Sources:** [ParentNeighborThreshold.lean](../../Euler/ParentNeighborThreshold.lean) — `EulerParentNeighborThreshold.requiredExponent`, `EulerParentNeighborThreshold.commonThreshold`; [PacketInductionStage.lean](../../Euler/PacketInductionStage.lean) — `EulerPacketInduction.Stage`; [PacketNestedHorizons.lean](../../Euler/PacketNestedHorizons.lean) — `EulerPacketNestedHorizons.stepLength`; [PacketStageRestriction.lean](../../Euler/PacketStageRestriction.lean) — `EulerPacketInduction.Stage.step_bounds`, `EulerPacketInduction.Stage.nextHorizon_lt`; [PacketForwardSuccessor.lean](../../Euler/PacketForwardSuccessor.lean) — `EulerPacketInduction.Stage.forwardPhysicalBounds`, `EulerPacketInduction.Stage.forwardNext`; [PacketJoinedSuccessor.lean](../../Euler/PacketJoinedSuccessor.lean) — `EulerPacketInduction.Stage.joinedPhysicalBounds`, `EulerPacketInduction.Stage.joinedNext`, `EulerPacketInduction.Stage.joinedNext_initial_velocity`; [ParentGeometryJoinedChoice.lean](../../Euler/ParentGeometryJoinedChoice.lean) — `EulerParentPacketFrames.GeometryJoinedChoice`, `EulerParentPacketFrames.exists_geometryJoinedChoice`; [AllOrderDriftBudget.lean](../../Euler/AllOrderDriftBudget.lean) — `EulerAllOrderDriftCorrection.Budget`; [AllOrderDriftCorrection.lean](../../Euler/AllOrderDriftCorrection.lean) — `EulerAllOrderDriftCorrection.Budget.solution_value_common`, `EulerAllOrderDriftCorrection.Budget.fieldTower_energy`, `EulerAllOrderDriftCorrection.Budget.fieldTower_hasDerivAt_pressure`, `EulerAllOrderDriftCorrection.Budget.pointField_initial`.

<a id="eul-005"></a>
### EUL-005 — The minimal invariant that forces growing gradients

**Conditional exposition; source-established algebra. Dependencies:** EUL-002 and EUL-004 to produce the family. **Obligations inherited:** OBL-EUL-001–003.

Suppose a family of exact parent states has all the `GrowthData` fields: parent and Sobolev state, odd symmetry, activation \(0\le t_n<T_n\), horizon identity and base-horizon bound, and a frame whose leading shear is \(a_n\). At activation let
\[
 M_n=Du_n(t_n,0)=B_n+Q_n+E_n,\qquad
 Q_n=a_n\widehat v_n\otimes\widehat m_n,
\]
where both hatted vectors are unit vectors. The source frame bounds and scale activation inequality give, for \(n\ne0\),
\[
 \|B_n\|+\|E_n\|\le a_n/2.
\]
Odd symmetry fixes the particle center at zero, so the frame strain is the physical derivative at the claimed point. Since the rank-one map is \(z\mapsto a_n\widehat v_n\langle\widehat m_n,z\rangle\), Cauchy–Schwarz gives \(\|Q_n\|\le a_n\), and testing \(z=\widehat m_n\) gives equality. Hence
\[
 a_n=\|Q_n\|=\|M_n-B_n-E_n\|
     \le\|M_n\|+\|B_n\|+\|E_n\|,
 \qquad \boxed{\|Du_n(t_n,0)\|\ge a_n/2.}
\]
The selected scales give \(a_n\ge n+1\), so the gradients tend to infinity. The exceptional stage \(n=0\) need not satisfy the half-shear lower bound.

This proof reads none of the successor's pressure or history bookkeeping directly. That is why the source separates the ten-field `GrowthData` from the full `Stage`. But dropping those extra fields **during construction** would remove the justification for having all future growth data.

The family itself is a coherent recursion: first stage, forward successor once, then joined successors. `packets` fixes the selected scale record and thresholds before defining every stage. The delivered source closes this recursion; it does not posit an arbitrary future family.

**Sources:** [PacketStageGrowth.lean](../../Euler/PacketStageGrowth.lean) — `EulerPacketInductionScales.Scales.previousShear_ge_index`, `EulerPacketInduction.GrowthData.gradient_lower`, `EulerPacketInduction.GrowthData.gradient_atTop`; [PacketInfiniteConstruction.lean](../../Euler/PacketInfiniteConstruction.lean) — `EulerPacketInduction.Stage.successor`, `EulerPacketInduction.stages`, `EulerPacketInduction.constructionScales`, `EulerPacketInduction.packets`, `EulerPacketInduction.packets_gradient_atTop`.

<a id="eul-006"></a>
### EUL-006 — Worked all-order convergence of the initial data

**Conditional exposition with source-established summability and limit interfaces. Dependencies:** EUL-002–004. **Obligations:** OBL-EUL-002–003 (physical majorants), OBL-EUL-004 (complete limit/support identification).

For each **fixed** derivative order \(m\), the actual high and mean initial increments have bounds of the form
\[
 \mathcal H_m(h_n)\le H_{m,n}:=\ell_n^{-m}k_n^m K_m P_n^{N_m}e^{-x_n/8},
\]
\[
 \mathcal H_m(\mu_n)\le M_{m,n}:=\ell_n^{-m}k_n^{-2} K_m P_n^{N_m},
\]
where \(K_m>0\), \(N_m\) are independent of \(n\) (enlarged to common constants for the two estimates if needed), and a source-parameter envelope is
\[
 P_n=Cj_n^p x_n^q\exp\!\left(c\frac{x_n}{(j_n-1)^3}\right),
 \quad C>0,\quad c\ge0,\quad p,q\in\mathbb N.
\]
The actual joined tail uses the shifted parameters \(J'=J+1\), \(X'=x_1\), with \(c=320,p=20,q=1000\) and a fixed source constant \(C\). Shifting is an identity for the scale sequence, not a replacement of the constructed stages.

Multiplying the literal exponentials yields
\[
 H_{m,n}=K_mC^{N_m}j_n^{pN_m}x_n^{qN_m}
 \exp\!\left[x_n\left(-\tfrac18+\tfrac m{j_n^2}
     +\tfrac m{j_n^{7/2}}+\tfrac{N_mc}{(j_n-1)^3}\right)\right],
\]
\[
 M_{m,n}=K_mC^{N_m}j_n^{pN_m}x_n^{qN_m}
 \exp\!\left[x_n\left(-\tfrac2{j_n^2}
     +\tfrac m{j_n^{7/2}}+\tfrac{N_mc}{(j_n-1)^3}\right)\right].
\]
For sufficiently large \(n\), depending on \(m,N_m,c\), the high exponent is at most \(-x_n/16\). For the mean exponent, divide its positive terms by \(j_n^{-2}\):
\[
 mj_n^{-3/2}+N_mc\frac{j_n^2}{(j_n-1)^3}\longrightarrow0.
\]
Thus its exponent is eventually at most \(-x_n/j_n^2\). This is why the full factor \(k_n^{-2}\) matters. Replacing it by a generic assertion of “small mean” would not prove all-order summability.

For completeness, fixed polynomial factors are harmless here. From the recurrence, \(\log x_n=\log X+2\sum_{i<n}\log(J+i)=O(n\log(J+n))\), while \(x_n\ge X4^n\) when \(J\ge2\). Consequently
\[
 \frac{\log j_n+\log x_n}{x_n/j_n^2}\longrightarrow0.
\]
Absorb the polynomial prefactors into half of either negative exponent. Eventually \(H_{m,n}\le e^{-x_n/32}\), \(M_{m,n}\le e^{-x_n/(2j_n^2)}\), and each right-hand side is bounded by \(2^{-n}\) for large \(n\). The finite head has finite norm and is retained. Therefore both majorant series converge, separately for every fixed \(m\).

The extra initial-amplitude gain has a checked source interface. For a joined geometric input, half-ball radius at least \(1/2\), a genuine history/join budget, parameter bound \(Y\ge1\), parent horizon and child shear at most \(Y\), spike at most one, history frame constant at most its polynomial source envelope, and \(\sigma x\le2\), the primary amplitude is bounded by
\[
 C_{\rm amp}Y^{N_{\rm amp}}e^{-x/8}.
\]
The proof bounds an inverse ray scale by the history frame envelope and multiplies the exponential growth estimate by a polynomial prefactor. The forward statement has a different, history-free prefactor. The lower ray-growth/geometry estimate supplying that exponential remains OBL-EUL-002; summability does not establish it retrospectively.

Now retain \(u_1(0)\) as the exceptional prefix and define
\[
 u_{\mathrm{init}}=u_1(0)+\sum_{n\ge1}(h_n+\mu_n).
\]
Absolute convergence in each \(\mathcal H_m\) gives a common distributional limit; uniqueness of the \(L^2\) limit identifies all the higher-order limits. Sobolev embedding at arbitrarily high fixed orders gives one smooth representative, with actual derivatives equal to those limits. The source's smooth-series construction packages this coherence. Uniform support of all increments in the radius-two closed ball passes to the continuous representative, and the first-stage datum is compactly supported as well. Divergence freedom passes in distributions (or in the closed solenoidal \(L^2\) subspace), hence pointwise for the smooth limit. In particular
\[
 \mathcal H_m(u_n(0)-u_{\mathrm{init}})\longrightarrow0\quad\text{for every fixed }m.
\]
No uniform statement over all orders \(m\) is claimed, and no pointwise-in-time limit of the full stage trajectories has yet been constructed.

**Sources:** [PacketInitialSummability.lean](../../Euler/PacketInitialSummability.lean) — `EulerPacketInitial.actual_high_summable`, `EulerPacketInitial.actual_mean_summable`; [StageInitialSupport.lean](../../Euler/StageInitialSupport.lean) — `EulerPacketInduction.stages_initial_support`; [PacketGeometryInitialAmplitude.lean](../../Euler/PacketGeometryInitialAmplitude.lean) — `EulerPacketSourceGeometry.Guards.primaryAmplitude_polynomial`, `EulerPacketSourceGeometry.ForwardGuards.primaryAmplitude_polynomial`; [PacketInitialScaleSummability.lean](../../Euler/PacketInitialScaleSummability.lean) — `EulerPacketInitialScale.high_expansion`, `EulerPacketInitialScale.mean_expansion`, `EulerPacketInitialScale.high_summable`, `EulerPacketInitialScale.mean_summable`; [PacketInitialSmoothLimit.lean](../../Euler/PacketInitialSmoothLimit.lean) — `EulerPacketInitial.actual_increment_summable`, `EulerPacketInitial.initialLimit_support`; [PacketStageInitialLimit.lean](../../Euler/PacketStageInitialLimit.lean) — `EulerPacketInduction.Stage.initialDataLimit_Hm`; [PacketFiniteLifespan.lean](../../Euler/PacketFiniteLifespan.lean) — `EulerPacketInduction.initialDatum_Hm`, `EulerPacketInduction.initialDatum_solenoidal`.

<a id="eul-007"></a>
### EUL-007 — Worked instability-versus-stability contradiction, with the H4 constant

**Conditional exposition of a source-established comparison argument. Dependencies:** EUL-005–006 for its packet application. **Obligation:** OBL-EUL-005 for the unexpanded product/pressure energy estimates, plus inherited construction obligations.

Here is a packet-independent statement. Let \(U\) be an ordinary Euler evolution on \([0,T]\), \(T\ge0\). Let \(u_n\) be exact ordinary evolutions on \([0,T_n]\), \(T_n\ge0\), with eventually \(T_n\le T\). Assume
\[
 d_n=\mathcal H_3(u_n(0)-U(0))\to0,\qquad t_n\in[0,T_n].
\]
Then \(\|Du_n(t_n,0)\|\) cannot tend to infinity. No uniform high-order bound on the stage family is assumed.

**Where H4 enters.** Let \(w=u_n-U\), \(\pi=p_n-p_U\). Subtract the two exact equations:
\[
 \partial_tw+(U\cdot\nabla)w+(w\cdot\nabla)U
                +(w\cdot\nabla)w+\nabla\pi=0,\qquad \nabla\cdot w=0.
\]
Commuting three spatial derivatives through \((w\cdot\nabla)U\) produces, among other terms, \(w\,D^4U\). Its \(L^2\) pairing is bounded using \(\|w\|_\infty\|D^4U\|_2\|D^3w\|_2\). Thus the source uses the fixed reference size
\[
 M_U=\max_{0\le t\le T}\mathcal H_4(U(t)),\quad
 C_U=1+1800C_{\rm prod}(1+M_U)>0,
\]
where \(C_{\rm prod}\ge0\) is its universal H3 product constant. Continuity of the fourth-order \(L^2\) jets on a compact time interval gives finite \(M_U\). Merely assuming bounded \(\mathcal H_3(U)\) would not justify this comparison constant.

For the source coordinate-word energy \(e(t)=\sum_{r=0}^3\sum_{i_1,\ldots,i_r}\|\partial_{i_1}\cdots\partial_{i_r}w(t)\|_2^2\), the genuine transport/pressure and commutator estimates give
\[
 e'\le3600C_{\rm prod}(M_U+\sqrt e)e,
 \qquad \mathcal H_3(w)\le40\sqrt e,
 \qquad e\le40\mathcal H_3(w)^2.
\]
The pressure cancellation here uses the ordinary evolution's solenoidal and recovered-gradient structure; these inequalities are analytic inputs, not assumptions about an arbitrary scalar pressure with unspecified behavior at infinity.

To avoid differentiating \(\sqrt e\) at zero, choose
\(\varepsilon_n=d_n+1/(n+1)>0\) and put
\[
 y_n(t)=40\sqrt{e_n(t)+\varepsilon_n^2}.
\]
Then
\[
 \mathcal H_3(w_n(t))\le y_n(t),\quad y_n(0)\le320\varepsilon_n,
 \quad y_n'\le C_U(y_n+y_n^2).
\]
For the initial bound, \(e_n(0)\le40\varepsilon_n^2\), so \(y_n(0)\le40\sqrt{41}\varepsilon_n\le320\varepsilon_n\). The derivative follows from
\(y_n'=20e_n'/\sqrt{e_n+\varepsilon_n^2}\) and the displayed energy inequality. These are precisely the regularized-envelope comparisons used in source.

For all sufficiently large \(n\),
\[
 A_n:=640\varepsilon_ne^{3C_UT}\le\tfrac12.
\]
A continuation bootstrap bounds \(y_n\) by \(A_n\) on its own horizon. Indeed while \(y_n\le1\), \(y_n'\le2C_Uy_n\), whence
\[
 y_n(t)\le320\varepsilon_ne^{2C_Ut}
       \le A_n/2<1.
\]
A first exit from the bound \(1\) is impossible by continuity. This proves, in particular, the slightly looser source estimate
\[
 \sup_{0\le t\le T_n}\mathcal H_3(u_n(t)-U(t))
          \le640\varepsilon_ne^{3C_UT}\longrightarrow0.
\]
For varying horizons, restrict \(U\) to \([0,T_n]\), but keep its original \(M_U\) and \(T\). Since \(C_U>0\) and \(T_n\le T\), its exponential is bounded by the same fixed factor. If coverage is only eventual, discard a finite prefix and reindex \(n\mapsto n+N\); convergence and gradient divergence survive. **Coverage means the stage horizons are eventually below the hypothetical reference horizon.** It is not a statement that the actual maximal solution reaches every activation.

In dimension three, the source derivative embedding gives
\[
 \|Du_n(t_n,0)-DU(t_n,0)\|
      \le9C_{\rm emb}\mathcal H_3(u_n(t_n)-U(t_n))\le9C_{\rm emb}A_n\to0.
\]
Continuity of \(DU(t,0)\) on \([0,T]\) gives a finite bound \(L_U\). Therefore
\[
 a_n/2\le\|Du_n(t_n,0)\|\le L_U+9C_{\rm emb}A_n,
\]
contradicting EUL-005. One needs no convergence rate measured against \(a_n\); convergence to zero and \(a_n\to\infty\) suffice. Large gradients belong to different exact solutions until this contradiction is applied.

**Sources:** [OrdinaryH3Envelope.lean](../../Euler/OrdinaryH3Envelope.lean) — `EulerOrdinarySobolev.stabilityConstant`, `EulerOrdinarySobolev.regularized_energy_bound`, `EulerOrdinarySobolev.Evolution.h3_stability`; [OrdinaryEulerStability.lean](../../Euler/OrdinaryEulerStability.lean) — `EulerOrdinarySobolev.Evolution.referenceNormPath`, `EulerOrdinarySobolev.Evolution.referenceSize`, `EulerOrdinarySobolev.Evolution.eventually_h3_bound`; [OrdinaryEulerVaryingHorizon.lean](../../Euler/OrdinaryEulerVaryingHorizon.lean) — `EulerOrdinarySobolev.Evolution.eventually_h3_bound_varying`, `EulerOrdinarySobolev.Evolution.no_gradient_escape_of_initial_tendsto_varying`; [PacketStageContradiction.lean](../../Euler/PacketStageContradiction.lean) — `EulerPacketInduction.GrowthData.no_evolution_of_eventually_covering`.

<a id="eul-008"></a>
### EUL-008 — From varying horizons to a positive finite maximal lifespan

**Conditional exposition; source-established assembly. Dependencies:** EUL-004–007. **Obligations:** OBL-EUL-005–006 plus inherited construction obligations.

The datum of EUL-006 is solenoidal and smooth in every \(L^2\) derivative order. General ordinary Euler local existence therefore supplies a positive closed interval of existence. The source obtains this by a regularized local construction, independently of the packet-growth contradiction.

The packet horizons are positive and decreasing: \(T_{n+1}<T_n\). For every fixed \(N\), an ordinary reference evolution on \([0,T_N]\) from \(u_{\mathrm{init}}\) would eventually cover all later packet horizons. EUL-007 rules it out. Thus the set of positive closed existence durations is nonempty and bounded. Let \(T_*\) be its maximal duration, in the source's `FiniteLifespan` construction. Restriction and uniqueness identify the shorter evolutions on overlaps and give a canonical evolution on \([0,T_*)\). If \(T_N<T_*\), restriction supplies the prohibited evolution on \([0,T_N]\). Hence
\[
 0<T_*\le\inf_n T_n\le T_0\le1.
\]
The source proves this inequality. We do **not** replace it by \(T_*=\lim_n t_n\), nor assume \(t_n<T_*\).

Why does closed-interval existence fail also at \(T_*\)? An ordinary solution on \([0,T_*]\) has a smooth solenoidal terminal datum. Local existence from that datum, followed by concatenation and uniqueness, extends past \(T_*\). This contradicts maximality. Consequently, for \(T>0\), closed ordinary existence holds exactly when \(T<T_*\). The Sobolev scalar-pressure adapter proves the same equivalence in the delivered class of EUL-001, including its interior-only time law.

Nonzeroness of the final datum is also consistent with this argument: zero initial datum admits the identically zero ordinary solution on every horizon, which would contradict EUL-007. This is a prose deduction; the delivered theorem's nonzeroness is separately assembled in source.

**Sources:** [PacketFiniteLifespan.lean](../../Euler/PacketFiniteLifespan.lean) — `EulerPacketInduction.initialDatum_local`, `EulerPacketInduction.packets_horizon_antitone`, `EulerPacketInduction.initialDatum_no_packet_horizon`, `EulerPacketInduction.initialDatum_finite_lifespan`, `EulerPacketInduction.lifespan_le_iInf_horizon`; [OrdinaryEulerContinuation.lean](../../Euler/OrdinaryEulerContinuation.lean) — `EulerOrdinarySobolev.Evolution.exists_extension`, `EulerOrdinarySobolev.FiniteLifespan.no_endpoint`; [ComparatorMaximalSolution.lean](../../Euler/ComparatorMaximalSolution.lean) — `Euler.ComparatorBridge.maximal_sobolevSolution`, `Euler.ComparatorBridge.maximal_sobolev_existence_iff`.

<a id="eul-009"></a>
### EUL-009 — Energy, C1 nonextension, and the vorticity integral

**Conditional exposition; source-established criteria. Dependencies:** EUL-008. **Obligation:** OBL-EUL-005 (local theory, continuation and whole-space logarithmic estimate), plus inherited obligations.

On each closed presingular interval the ordinary class has the genuine \(L^2\) cancellations
\[
 \langle u,(u\cdot\nabla)u\rangle=0,\qquad
 \langle u,\nabla p\rangle=0.
\]
The latter is the orthogonality of the solenoidal field and the recovered gradient; it does not require compact velocity support at positive times. With the strong \(L^2\) time derivative,
\[
 \frac d{dt}\|u(t)\|_2^2=2\langle u,\partial_tu\rangle=0.
\]
Identification of shorter solutions gives \(\|u(t)\|_2^2=\|u_{\mathrm{init}}\|_2^2\) for all \(t<T_*\). Physical kinetic energy is half this number. The gradient cascade is not energy blowup.

The continuation input says that a uniform finite bound on the partial integrals
\(\int_0^t\|Du(s)\|_\infty ds\), over all shorter evolutions, supplies an ordinary endpoint solution. If the gradient were uniformly bounded up to \(T_*\), these integrals would be bounded by that constant times \(T_*\), contradicting EUL-008. More precisely the unboundedness must occur arbitrarily near the endpoint: the initial compact time slab has a bounded derivative norm by all-order Sobolev continuity. A bound on a terminal interval combined with this early bound would bound the entire lifespan. This proves the stated infinite C1 limsup, since \(C_1\ge\|Du\|_\infty\). It does not prove monotone growth or a limit.

The vorticity conclusion needs more than unbounded gradient. The source's whole-space logarithmic inequality, for a smooth all-order \(L^2\) solenoidal field \(u\) and any finite bound \(W\ge\sup_x|\nabla\times u(x)|\), is
\[
 \|Du\|_\infty\le C_{\log}
 \left(1+\|u\|_2+W\log(e+\mathcal H_3(u))\right).
\]
Its Gaussian/elliptic proof is unexpanded here. Together with the ordinary high-order energy estimate it explains the BKM implication. Schematically, with \(H=\mathcal H_3(u)\) and \(Z=\log(e+H)\), that energy estimate gives
\[
 Z'\le C\|Du\|_\infty
 \le C'(1+\|u_{\mathrm{init}}\|_2)+C'WZ.
\]
If \(\int_0^{T_*}W\le G<\infty\), Gronwall yields the finite uniform bound
\[
 Z(t)\le\bigl(Z(0)+C'(1+\|u_{\mathrm{init}}\|_2)T_*\bigr)e^{C'G}.
\]
Substitution into the logarithmic inequality bounds every partial gradient integral. Continuation would then produce the forbidden endpoint solution. Thus \(\int_{[0,T_*)}W=+\infty\). This calculation is a conditional explanation of the criterion, not the literal norm-differentiation proof: source uses continuous norm paths and integral estimates to handle nonsmooth norm values. Its quantitative reduction directly bounds the gradient integral by
\[
 \exp\!\bigl(C_{\rm logG}(u_{\mathrm{init}})(T_*+G)\bigr)
\]
when all partial vorticity integrals are bounded by \(G\).

On any \([0,T]\) with \(T<T_*\), Sobolev continuity gives a finite spatial C1 bound and a continuous bounded vorticity norm path, so both local claims in EUL-001 follow. Infinite terminal integral and finite local integrals are compatible.

**Sources:** [OrdinaryEulerKineticEnergy.lean](../../Euler/OrdinaryEulerKineticEnergy.lean) — `EulerOrdinarySobolev.Evolution.velocity_derivative_inner_zero`, `EulerOrdinarySobolev.Evolution.kineticEnergy_conserved`; [OrdinaryEulerContinuation.lean](../../Euler/OrdinaryEulerContinuation.lean) — `EulerOrdinarySobolev.FiniteLifespan.gradient_unbounded_near_endpoint`; [OrdinaryLogarithmicGradient.lean](../../Euler/OrdinaryLogarithmicGradient.lean) — `EulerOrdinarySobolev.logarithmic_gradient_bound_solenoidal`; [OrdinaryBKMReduction.lean](../../Euler/OrdinaryBKMReduction.lean) — `EulerOrdinarySobolev.Evolution.gradientIntegral_of_vorticity_bound`; [OrdinaryEulerBKM.lean](../../Euler/OrdinaryEulerBKM.lean) — `EulerOrdinarySobolev.FiniteLifespan.vorticity_lintegral_eq_top`; [ComparatorMaximalFields.lean](../../Euler/ComparatorMaximalFields.lean) — `Euler.ComparatorBridge.maximalVelocityExtension_energy`, `Euler.ComparatorBridge.maximalVelocityExtension_c1_limsup`, `Euler.ComparatorBridge.maximalVelocityExtension_vorticity_integral`.

<a id="eul-010"></a>
### EUL-010 — Compact vorticity bridges to the broader global class

**Conditional exposition; source-established bridge interfaces. Dependencies:** EUL-006–009. **Obligation:** OBL-EUL-006 plus the construction and ordinary-theory obligations.

Finite ordinary lifespan alone does not exclude a jointly smooth, finite-energy global velocity whose high derivatives have not been shown to lie in \(L^2\). The source closes exactly this class gap using **vorticity** support, not compact support of the evolved velocity.

For Euler,
\[
 (\partial_t+u\cdot\nabla)\omega=(\omega\cdot\nabla)u.
\]
Along a smooth particle trajectory, \(z(t)=\omega(t,\Phi(t,a))\) solves
\(z'=Du(t,\Phi(t,a))z\). On a fixed smooth stage horizon the coefficient is bounded, so \(z(0)=0\) implies \(z(t)=0\), by Gronwall. If initial vorticity is supported in \(\overline B_2\) and particle displacement is at most \(D\), every later nonzero-vorticity point lies in \(\overline B_{2+D}\): use the inverse particle map to find its initial label; that label must have nonzero initial vorticity. Closure gives the same assertion for topological support.

The source proves preservation of zero curl through an equivalent frame calculation, rather than assuming a transported scalar. Along a label, write \(F=D_a\Phi\), \(G=\partial_tF\), and \(H=D^2p(t,\Phi)\). Then \(F'=G\), \(G'=-HF\), and symmetry of \(H\) gives
\[
 \frac d{dt}(F^\top G-G^\top F)
 =G^\top G-F^\top HF+F^\top H^\top F-G^\top G=0.
\]
Moreover \(F^\top G-G^\top F=F^\top(M-M^\top)F\), where \(M=GF^{-1}=Du(t,\Phi)\). Since \(F\) is invertible, zero initial curl (symmetric initial strain) implies symmetric later strain, hence zero later curl. This explains the actual source's Wronskian route and its pressure-Hessian requirement.

The construction supplies a finite common displacement cap through its cumulative displacement estimates, as well as the common initial support. Thus all stages have vorticity in one compact ball \(K\), throughout their respective horizons. This does not follow from the lower gradient bound; the displacement budget is another construction input.

To pass confinement to the canonical solution, fix \(S<T_*\). Now the horizon inequality goes in the **other direction** from EUL-007:
\[
 S<T_*\le T_n\quad\text{for every }n.
\]
Restrict each stage to \([0,S]\), and compare it with the canonical ordinary evolution on that interval. Initial H3 convergence and fixed-reference stability give pointwise convergence of first derivatives, hence of curls. Outside \(K\) all stage curls vanish; therefore the canonical curl vanishes there. This proves confinement for every \(t<T_*\), without assuming the canonical solution reaches the activation times.

Suppose next that a global Comparator solution \((v,p)\) from \(u_{\mathrm{init}}\) exists. The required source bridge has three analytic pieces:

1. Compact initial vorticity of a jointly smooth globally finite-energy solution persists in a common compact region for some positive time. The proof uses a finite-energy truncation family; it cannot simply assume a global Lipschitz velocity bound that the Comparator hypotheses do not supply.
2. On a closed positive interval with common compact vorticity support, div–curl elliptic recovery upgrades the **same velocity** to all-order spatial \(L^2\) fields, uniformly on the interval. Dense compact solenoidal test pairings and the projected Euler law provide the time regularity of an ordinary evolution. Joint smoothness alone does not give this whole-space upgrade.
3. Restart this local conversion at times of agreement with the canonical solution; ordinary uniqueness identifies the Comparator velocity with it throughout \([0,T_*)\).

The final contradiction can now be worked without invoking the BKM integral. By agreement, \(\operatorname{supp}\omega_v(t)\subset K\) for \(t<T_*\). At each fixed \(x\notin K\), joint smoothness makes \(t\mapsto\omega_v(t,x)\) continuous, so \(\omega_v(T_*,x)=0\). Closedness of \(K\) gives support in \(K\) at the endpoint. Restart compact-vorticity persistence for the shifted **hypothetical global** solution at \(T_*\). It gives some \(\delta>0\) and another compact ball containing vorticity through \(T_*+\delta\). Their union with \(K\) is compact. The common-compact-curl upgrade then produces an ordinary evolution on \([0,T_*+\delta]\) with datum \(u_{\mathrm{init}}\), contradicting maximality.

This is a legitimate restart because the hypothetical competitor is assumed smooth through \(T_*\). It is not a restart of the singular canonical solution. The delivered broad-class contradiction uses maximality; BKM is an additional delivered conclusion rather than this final proof's last step.

> **Unexpanded class bridge.** The elementary trajectory and endpoint arguments above are complete under their stated inputs. The actual cumulative displacement bound, finite-energy truncation/persistence proof, div–curl recovery, pressure/projected pairing closure, and precise scalar/Sobolev adapters remain OBL-EUL-006. Source interfaces were inspected; no claim is made that their dependency closure has received an independent human audit.

**Sources:** [PacketCurlTransport.lean](../../Euler/PacketCurlTransport.lean) — `EulerParentPacketFrames.Evolution.strain_symmetric_along_label`, `EulerParentPacketFrames.Evolution.curl_eq_zero_along_position`; [StageDisplacementBound.lean](../../Euler/StageDisplacementBound.lean) — `Euler.ComparatorBridge.support_subset_of_transport`; [CanonicalVorticityConfinement.lean](../../Euler/CanonicalVorticityConfinement.lean) — `EulerPacketInduction.packets_vorticity_support`, `EulerPacketInduction.canonical_vorticity_confined`; [ComparatorLocalEvolution.lean](../../Euler/ComparatorLocalEvolution.lean) — `Euler.ComparatorBridge.exists_evolution_of_commonCompactCurl`, `Euler.ComparatorBridge.compactCurlLocalUpgrade`, `Euler.ComparatorBridge.comparator_agrees_with_canonical`; [CompactVorticityContradiction.lean](../../Euler/CompactVorticityContradiction.lean) — `Euler.EulerExistenceAndSmoothnessR3.vorticity_support_subset_at_endpoint`, `Euler.ComparatorBridge.no_global_solution_of_confined_vorticity`. In [Solution.lean](../../Euler/Solution.lean), `initialDatum_no_global_solution` is a **private** assembly lemma, not a proposed public citation target; the public endpoints are those in EUL-001.

<a id="eul-011"></a>
### EUL-011 — What positive viscosity invalidates

**Conditional deduction and new-research boundary. Dependencies:** EUL-002, EUL-007, EUL-010. No viscous packet theorem is asserted.

The algebraic instability-versus-stability template could be reused at a **fixed** viscosity \(\nu>0\): exact unforced viscous stages, initial convergence in a gradient-controlling topology, divergent sampled gradients, eventual horizon coverage, and a suitable fixed-reference stability estimate would again contradict a long smooth reference. The Euler construction does not supply the viscous stages.

For a packet of physical frequency \(\xi\), viscosity introduces a leading damping rate \(\nu|\xi|^2\). Here the initial characteristic frequency is \(k_n/\ell_n\), with
\[
 \log (k_n/\ell_n)^2=2x_n/j_n^2+2x_n/j_n^{7/2},\qquad
 \log s_n=x_n/j_n^5.
\]
This compares frequency and target shear scales, not an integrated damping estimate. A rigorous adaptation must follow the transported wavevector and control
\[
 \nu\int_{\text{actual growth interval}}|\xi_n(t)|^2\,dt
\]
against the logarithmic amplification. Neither taking \(\nu\) small after fixing a stage nor invoking an inviscid-limit solver proves survival for infinitely many stages at one fixed positive viscosity.

The exact confinement argument also fails: Navier–Stokes vorticity obeys
\[
 (\partial_t+u\cdot\nabla)\omega=(\omega\cdot\nabla)u+\nu\Delta\omega.
\]
The value along a trajectory is no longer a homogeneous finite-dimensional ODE, so zero initial vorticity at that label does not imply zero later vorticity. Quantitative spatial tails and a replacement class bridge would be needed. The auxiliary viscous regularization used to construct an **inviscid** correction is not a retained-viscosity physical cascade.

These are precise missing tasks, not a theorem that every viscous adaptation is impossible. No implication to unforced Navier–Stokes A/B is obtained here.

## Local obligation ledger

All entries are owned by `euler`, **open**, and awaiting a separate reviewer. Creation history: recorded in this author draft after reading both requested reports, the prior Euler investigation, and the source interfaces cited above. No entry is closed merely because its endpoint is present in Lean.

| ID | Missing assertion under the stated hypotheses; source leads | Affected claims; evidence needed |
|---|---|---|
| **OBL-EUL-001** | Verify every `Scales c B` guard for one fixed selection, including base exceptions, actual cost powers and renewal sums. Leads: `EulerPacketInductionScales.exists_scales` and its common-guard imports. | EUL-002 and every constructed-family conclusion. Close with a full numerical ledger and independent checking of all physical-cost-to-numerical substitutions. |
| **OBL-EUL-002** | Derive one actual forward packet and one positive-history insertion: normalized ray growth, physical polarization/pressure, inverse-growth initial amplitude, transported normal, and renewed coupling/tilt/compression for the same child. | EUL-003–006 and all later applications. Leads: `EulerPacketGrowth.equation30_endpoint_exponential`, `EulerParentPacketFrames.exists_geometryJoinedChoice`, both `primaryAmplitude_polynomial` declarations. Close with continuous physical calculations, perturbation bounds and the explicit first-stage distinction. |
| **OBL-EUL-003** | Under the all-order drift budget, expand the weighted energy norm, finite-order solver and pressure estimates, uniqueness/coherence, and physical graph-to-Euler identities; prove the bounds apply to the same corrected child that retains growth. | EUL-004 onward. Leads: `EulerAllOrderDriftCorrection.Budget`, its `fieldTower_energy`, `fieldTower_hasDerivAt_pressure`, and `GeometryJoinedChoice`. Close with a full analytic correction proof and an independent same-field check. |
| **OBL-EUL-004** | Verify the actual physical Hm majorants, the shifted tail, exceptional first datum, and common compact support of the complete limiting datum. The elementary summability calculation here does not establish those input estimates. | EUL-006 onward. Leads: `EulerPacketInduction.Stage.initialDataLimit_Hm`, `EulerPacketInitial.actual_increment_summable`, and support imports of the confinement construction. Close with actual field identifications and a checked all-order representative/support argument. |
| **OBL-EUL-005** | Audit the H4-dependent H3 difference energy/pressure estimates, local existence, endpoint construction from bounded gradient integral, and whole-space logarithmic estimate in the precise ordinary class. | EUL-007–010. Leads: `EulerOrdinarySobolev.Evolution.h3_stability`, `EulerOrdinarySobolev.logarithmic_gradient_bound_solenoidal`, ordinary continuation/BKM declarations. Close with analytic proofs or a fully hypothesis-matched standard-theory replacement; keep source constants separate from equivalent norm constants. |
| **OBL-EUL-006** | Verify cumulative displacement, broad-class compact-vorticity persistence from finite energy, div–curl/time regularity recovery, canonical identification, and both directions of the closed Sobolev-class adapter. | EUL-001, EUL-008–010, especially broader global exclusion. Leads: `EulerPacketInduction.canonical_vorticity_confined`, `Euler.ComparatorBridge.compactCurlLocalUpgrade`, `Euler.ComparatorBridge.maximal_sobolev_existence_iff`. Close with exact solution-class translations and the truncation/elliptic/pressure dependency audit; do not assume global derivative bounds. |

Unexpanded analytic inputs are explanatory debt, not demonstrated counterexamples to source theorems. A fixed-positive-viscosity cascade and viscous confinement replacement are **new research**, not obligations claimed to be discharged by existing Euler declarations.

## Precise declaration index and handoff

Every citation inherits the baseline above. The following table highlights the exact load-bearing interfaces; the lemma sections supply additional many-to-many citations and hypotheses.

| Human ID | Source file | Fully qualified declaration(s) | Role / inspection limit |
|---|---|---|---|
| EUL-001 | [SolutionDefinitions.lean](../../Euler/SolutionDefinitions.lean) | `Euler.EulerSobolevExistenceAndSmoothnessR3On`; `Euler.EulerExistenceAndSmoothnessR3` | Literal classes inspected, not conflated. |
| EUL-001 | [Solution.lean](../../Euler/Solution.lean) | `Euler.euler_breakdown_R3`; `Euler.exists_compact_smooth_euler_singularity` | Public signatures and assembly inspected; no build. |
| EUL-002 | [PacketInductionScales.lean](../../Euler/PacketInductionScales.lean) | `EulerPacketInductionScales.Scales`; `EulerPacketInductionScales.exists_scales` | Numerical fields and choice proof inspected; guard closure unexpanded. |
| EUL-003 | [ParentEulerState.lean](../../Euler/ParentEulerState.lean) | `EulerParentPacketFrames.Evolution`; `EulerParentPacketFrames.Evolution.strain_eq` | Exact zero residual, gradient-pressure identity, physical strain. |
| EUL-003 | [EulerProof/PacketGrowth.lean](../../Euler/EulerProof/PacketGrowth.lean) | `EulerPacketGrowth.equation30_cosh_lower`; `EulerPacketGrowth.equation30_endpoint_exponential` | Scalar hypotheses and comparison proof inspected; full ray tower not audited. |
| EUL-004 | [ParentGeometryJoinedChoice.lean](../../Euler/ParentGeometryJoinedChoice.lean) | `EulerParentPacketFrames.GeometryJoinedChoice`; `EulerParentPacketFrames.exists_geometryJoinedChoice` | Exact guarded child interface; nonlinear estimates unexpanded. |
| EUL-004 | [PacketJoinedSuccessor.lean](../../Euler/PacketJoinedSuccessor.lean) | `EulerPacketInduction.Stage.joinedPhysicalBounds`; `EulerPacketInduction.Stage.joinedNext_initial_velocity` | Whole-horizon derivative bounds and actual positive-history increment. |
| EUL-004 | [AllOrderDriftCorrection.lean](../../Euler/AllOrderDriftCorrection.lean) | `EulerAllOrderDriftCorrection.Budget.solution_value_common`; `EulerAllOrderDriftCorrection.Budget.fieldTower_energy`; `EulerAllOrderDriftCorrection.Budget.fieldTower_hasDerivAt_pressure` | One common field, weighted error bound, actual time law; solver unexpanded. |
| EUL-005 | [PacketInductionStage.lean](../../Euler/PacketInductionStage.lean) | `EulerPacketInduction.GrowthData`; `EulerPacketInduction.Stage` | Minimal versus renewable invariant, with section hypotheses inspected. |
| EUL-005 | [PacketStageGrowth.lean](../../Euler/PacketStageGrowth.lean) | `EulerPacketInduction.GrowthData.gradient_lower`; `EulerPacketInduction.GrowthData.gradient_atTop` | Half-shear argument, excluding stage zero, inspected and worked. |
| EUL-005 | [PacketInfiniteConstruction.lean](../../Euler/PacketInfiniteConstruction.lean) | `EulerPacketInduction.stages`; `EulerPacketInduction.packets` | One recursion with forward/joined branch. |
| EUL-006 | [PacketInitialScaleSummability.lean](../../Euler/PacketInitialScaleSummability.lean) | `EulerPacketInitialScale.high_summable`; `EulerPacketInitialScale.mean_summable` | All fixed orders, true inverse-frequency square. |
| EUL-006 | [PacketStageInitialLimit.lean](../../Euler/PacketStageInitialLimit.lean) | `EulerPacketInduction.Stage.initialDataLimit_Hm` | Requires actual positive-stage increment identity; first datum retained. |
| EUL-007 | [OrdinaryH3Envelope.lean](../../Euler/OrdinaryH3Envelope.lean) | `EulerOrdinarySobolev.Evolution.h3_stability` | WordBound order four, positive epsilon and smallness threshold inspected. |
| EUL-007 | [OrdinaryEulerVaryingHorizon.lean](../../Euler/OrdinaryEulerVaryingHorizon.lean) | `EulerOrdinarySobolev.Evolution.eventually_h3_bound_varying`; `EulerOrdinarySobolev.Evolution.no_gradient_escape_of_initial_tendsto_varying` | Constants use original reference and horizon. |
| EUL-007 | [PacketStageContradiction.lean](../../Euler/PacketStageContradiction.lean) | `EulerPacketInduction.GrowthData.no_evolution_of_eventually_covering` | Eventual coverage reindexed explicitly. |
| EUL-008 | [PacketFiniteLifespan.lean](../../Euler/PacketFiniteLifespan.lean) | `EulerPacketInduction.initialDatum_local`; `EulerPacketInduction.lifespan_le_iInf_horizon` | Positive local existence and upper bound, not equality with activation limit. |
| EUL-008 | [ComparatorMaximalSolution.lean](../../Euler/ComparatorMaximalSolution.lean) | `Euler.ComparatorBridge.maximal_sobolevSolution`; `Euler.ComparatorBridge.maximal_sobolev_existence_iff` | Scalar-pressure class endpoint adapter. |
| EUL-009 | [OrdinaryEulerKineticEnergy.lean](../../Euler/OrdinaryEulerKineticEnergy.lean) | `EulerOrdinarySobolev.Evolution.kineticEnergy_conserved` | Genuine noncompact cancellations, norm squared. |
| EUL-009 | [OrdinaryEulerBKM.lean](../../Euler/OrdinaryEulerBKM.lean) | `EulerOrdinarySobolev.FiniteLifespan.vorticity_lintegral_eq_top` | Extended integral conclusion; logarithmic proof unexpanded. |
| EUL-010 | [CanonicalVorticityConfinement.lean](../../Euler/CanonicalVorticityConfinement.lean) | `EulerPacketInduction.packets_vorticity_support`; `EulerPacketInduction.canonical_vorticity_confined` | Fixed compact ball and short-slab H3 passage inspected. |
| EUL-010 | [ComparatorLocalEvolution.lean](../../Euler/ComparatorLocalEvolution.lean) | `Euler.ComparatorBridge.exists_evolution_of_commonCompactCurl`; `Euler.ComparatorBridge.comparator_agrees_with_canonical` | Broad-to-ordinary conversion and agreement; underlying analytic tower unexpanded. |
| EUL-010 | [CompactVorticityContradiction.lean](../../Euler/CompactVorticityContradiction.lean) | `Euler.ComparatorBridge.no_global_solution_of_confined_vorticity` | Endpoint continuity, restart of hypothetical competitor, maximality contradiction. |

**Exports:** EUL-001–011 and OBL-EUL-001–006. **Imports:** no numbered NS lemmas; this is an independent branch after the scope chapter. The integrator should align EUL-001 terminology with that chapter rather than infer any Euler-to-NS implication. Local notation \(n,J,D,X,a_n,k_n,\ell_n,t_n,T_n\) is Euler-only; \(T_*\) is the canonical lifespan, \(\mathcal H_m\) the tensor Sobolev sum, \(C_1\) the sum of two spatial suprema, and \(W\) the actual curl supremum.

**Worked calculations exported:** scalar flux comparison; rank-one half-shear estimate; two distinct initial summability mechanisms; regularized H3 comparison with H4 constants and varying horizons; finite-lifespan upper bound; energy cancellation; conditional logarithmic/BKM implication; transport support and endpoint maximality contradiction; viscous frequency warning with its quantifier limitation.

**Review status:** author source inspection and calculations only. A read-only author check found all relative file links resolving and all eleven explicit EUL anchors unique; this is not independent Gate 4 signoff. HEAD remained at the stated baseline and the tracked diff was empty after authoring. Separate technical mathematics review, independent source/hypothesis checking, worked-calculation review, link/ID validation, and pedagogical cold reading remain required by [PLAN.md](PLAN.md). No external manuscript correspondence, fresh kernel validity, Comparator verification, or completed human-proof validation is claimed. No Lean edits, builds, dependency operations, commits, or pushes were performed for this chapter.
