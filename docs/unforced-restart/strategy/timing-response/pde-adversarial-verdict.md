# Final PDE/source adversarial verdict

## Executive summary

**Verdict: qualified acceptance of the exact mathematics and negative evidence boundary; partial algebraic success, failure to establish the intended timing/persistence result. This is not an unqualified draft pass.**

The amplitude–time cancellation, deletion sign, restart seed, finite-horizon adjoint, and inhomogeneous derivative equation withstand independent derivation. The new identity is useful bookkeeping for the same selected source, but supplies no signed selected-force correlation estimate, nonzero endpoint timing coefficient, or endpoint margin. Calling it an improvement is justified algebraically, not as demonstrated dynamical progress.

Exact pure-clock compatibility remains undecided by the inspected information. A scalar clock canceling the axial defect can be constructed near the endpoint; canceling the full spatial field is a separate, unproved condition. Neither an axial timing coordinate nor its growth proves nonlinear phase tracking, shifted breakdown, or destruction of growth.

The original source proves a forced candidate and uses uniqueness with the **same force** in its comparator argument. Its auxiliary modal energy and unweighted covariance do not control the force-deletion propagator. No internal existence witness, explicit-array threshold, toy example, or numerical observation may replace the selected record.

**No positive evidence for unforced breakdown emerged. Neither A nor B is resolved or made demonstrably easier.** The earlier exclusion of an unrestricted stability certificate is not a violation of the selected-source margin and is not evidence favoring either unforced outcome.

The audit accepts finite-slab identities under the stated selected-axis inputs, not an exhaustive reconstruction of their upstream production. It supplies two bounded mathematical clarifications below, not a successor investigation. This is human adversarial analysis, **not Lean validation or independent kernel checking**.

## 1. Source analysis — what was actually checked

Read both timing-response drafts, the earlier [FINAL-REPORT](../force-response/FINAL-REPORT.md), its historical [CALCULATION](../force-response/CALCULATION.md), and [CENTRAL-OBSTACLE](../CENTRAL-OBSTACLE.md). Historical (13)–(14) remain excluded, not available assumptions.

Targeted source-body inspection covered:

- `Research/UnforcedRestart/Round3/WitnessFeasibility/Main.lean`: `selected : Data` coherently contains one schedule, candidate, force, global smoothness and terminal jets. Consumers must project this record.
- `NavierStokes/ProblemStatement.lean`: viscosity exactly one, fixed unit periods, presingular velocity/pressure smoothness, projected residual sign, and forced candidate scope.
- `CorrectionInitialization.lean`, `ActualPrimary` near 2962; `EntranceAlignedBase.lean`, axis identities near 757; `BaseResidual.lean`, origin calculation 59–86; `MixedPeriodicAssembly.lean`, local germ transfer near 111–133; and `TimeLocalization.lean`, activation and late germ equality. `GermCandidateAssembly.lean` supplies the identified germ-transfer statements. These support the source identification; the entire initialization/direct-stage/gauge chain and mean cancellation were not exhaustively re-proved in this audit. The quantitative selected-axis transfer remains an explicitly inherited input.
- `ActualParticularControl.lean`, `selected_energy`: an auxiliary frame/modal quadratic-form bound, not an estimate for the full physical linearization. `ActualPrimaryCovariance.lean`, `viewSum_covariance_factor`: an unweighted fast-variable average, not a pairing against the axial PDE adjoint.
- `ComparatorTheorem.lean`: the original periodic conclusion concerns a forced candidate, viscosity rescaling, and uniqueness for matching datum **and force**. Deletion changes that problem. This source does not identify an autonomous sustaining mechanism.
- Companion `06-primitive-derivative-bounds.md` §1 explicitly leaves the enlarged-chart/actual-selected-label bridge conditional. No numerical constants from it were promoted to unconditional selected estimates here.

These checks do not identify a classical choice with an internally exhibited existence-history witness, increase its threshold, or reconstruct upstream profile production. Force jets at one spatial point are not projected-force jets: Leray is nonlocal and retains the constant mode. Pressure changes by periodic gradients leave the projected analysis unchanged.

## 2. Severity findings

### High — central dynamical deliverable not obtained

The new correlation is unestimated. There is no selected-source sign, certified nonzero timing excitation, endpoint asymptotic, linear margin or violation, or nonlinear persistence theorem. This is the decisive failure to report, even though the drafts candidly acknowledge it. A source-specific formula is not source-specific quantitative control.

### Medium — “new cancellation” must not imply improved endpoint control

The explicit quadratic source disappears, but its linearization remains in the propagator and the seed remains. The diffusion and differentiated-force correlations need not have a sign or individually bounded endpoint limits. No gain in integrability or tractability is demonstrated. The accepted result is necessary algebra specialized by an existing selected-axis identity, not new measured behavior of the force.

### Medium — timing terminology is coordinate-dependent

The axial coefficient \(\alpha\) is an observation, not a canonical phase. For a general normalized functional \(\psi\), \(a=\langle\psi,z\rangle\) changes with the gauge. Even in the displayed orthogonal gauge,
\[
\alpha=a+\kappa_T r(T).
\]
An axial coefficient cannot be substituted for the full-field gauge coefficient. Pure collinearity \(z=aY\), when it holds, is gauge-independent because \(Y\ne0\); the decomposition of a general response is not.

### Low — qualify the scope of “no bound/coefficient follows”

No **endpoint-uniform** bound or **nonzero asymptotic** coefficient follows. Ordinary finite-slab bounds and exact restart derivatives do follow. The drafts already mostly make this distinction; it must survive supervisor summaries.

No fatal sign, viscosity, pressure or seed error was found in the decisive draft identities.

## 3. New mathematical verification — accepted exact scope

All derivations in this section are human mathematics on a fixed slab \([t_0,T]\), \(T<1\), for the complete selected fields. Set \(Y=U_t\), \(N=\mathbb P(U\cdot\nabla U)\), and \(F=Y-\Delta U+N\). Expanding directly gives
\[
L_UU=F+N,\qquad L_UY=F_t,\qquad
L_U(U-v)=F+\mathbb P((U-v)\cdot\nabla(U-v)).
\]
Thus \(Y\) is not an automatic homogeneous phase mode. With \(d=t-t_0\),
\[
L_U(U+dY)=F+N+Y+dF_t=2F+\Delta U+dF_t.
\]
Because \((U+dY)(t_0)=U(t_0)\), Duhamel necessarily retains \(\Phi(T,t_0)U(t_0)\). Pairing with the specified terminal functional yields exactly
\[
2\alpha(T)=d_T+q_T/A-\mathcal C_T.
\]
At restart \(\mathcal C_{t_0}=\delta/A\), so \(\alpha(t_0)=0\). A positive displayed term cannot defeat cancellation. If \(\mathcal C_T\to C_*\), then \(\alpha\to(\delta-C_*)/2\); this premise is unproved. Even \(C_*=\delta\) does not give the required \(O(q_T)\) cancellation rate.

Independent ansatz check: for \(V_\lambda=\lambda U(t_0+\lambda d)\), pressure \(\lambda^2p(t_0+\lambda d)\), the time/convection/pressure terms scale by \(\lambda^2\), diffusion by \(\lambda\). Hence the residual is
\[
\lambda^2f(t_0+\lambda d)+\lambda(\lambda-1)\Delta U(t_0+\lambda d).
\]
Its derivative proves the cancellation again. This is not a fixed-viscosity symmetry or a same-datum family. Its sampled-time endpoint is \(t_0+\delta/\lambda\); parameter differentiation is legitimate on finite slabs, not uniformly to time one.

Smooth periodic finite-slab coefficients yield the parabolic evolution on divergence-free \(H^4\); the generator is unbounded. Point evaluation is a continuous functional there, so \(\beta_T=\Phi(T,s)^*\kappa_T\) exists in the distributional dual. Integration by parts gives
\[
G^*b=\Delta b+\mathbb P(U\cdot\nabla b)-\mathbb P((\nabla U)^Tb),
\quad \frac{d}{ds}\langle\beta_T,H\rangle=\langle\beta_T,L_UH\rangle.
\]
Consequently \(\langle\beta_T(s),Y(s)\rangle=1-\int_s^T\langle\beta_T,F_t\rangle\). Earlier normalization can vanish and would generally destroy the homogeneous adjoint equation. There is no endpoint adjoint, dominated-convergence justification, or permission to exchange the endpoint limit with these integrals.

For any scalar \(a(t)\), \(L_U(aY)=a'Y+aF_t\). The stated orthogonal-gauge equation and conditional axial ODE therefore have the correct signs. Bounded projected \(F,F_t\) and the inherited axis value give the conditional \(O(\delta^{A+2})\) bound, but only if the full remainder vanishes.

## 4. New review clarifications — not results claimed by the drafts

**Restart coefficient.** Since \(z(t_0)=0\), \(z_t(t_0)=F(t_0)\), and differentiation of \(\kappa_t\) multiplies zero at restart:
\[
\alpha'(t_0)=\frac{F_2(t_0,0)}{Y_2(t_0,0)}=O(\delta^{A+1}).
\]
This is genuine finite-time calibration, not a sign or nonzero coefficient: the selected numerator is unknown and may vanish. Small initial response does not control its later propagation.

**Scalar clock and shifted endpoint.** Put \(g(\tau)=F_2(\tau,0)/Y_2(\tau,0)\). The axial cancellation clock satisfies
\[
\theta'=1-g(\theta),\qquad \theta(t_0)=t_0.
\]
For sufficiently late fixed restart, \(|g|\le1/2\), so this scalar clock exists monotonically until it reaches one, with
\[
T_*=t_0+\int_{t_0}^1\frac{d\tau}{1-g(\tau)},\qquad
T_*-1=\int_{t_0}^1\frac{g(\tau)}{1-g(\tau)}d\tau
=O(\delta^{A+2}).
\]
This follows by inversion of the scalar ODE and the smooth-force bound. It is **not an unforced solution** unless the full field \(F-gY\) vanishes. It clarifies why a small possible endpoint displacement neither proves nor excludes exact clock absorption.

## 5. Hypothetical tests and rejected inferences

For \(W=U\circ\theta\), the exact projected defect is \(F(\theta)+(\theta'-1)Y(\theta)\). A changed comparison pressure absorbs only its gradient part before projection, not this defect. The total nonlinear pressure difference also includes quadratic-error pressure; the corrected draft distinction is valid.

A constant delay gives \(v\approx U(t-a)\) under the deletion sign, but changes the restart trace. Ramping from zero restores the trace and introduces the clock-rate defect. On the selected axis the shifted profile is \(j_*(q+a)^{-A}\): its Taylor expansion about \(a=0\) is not uniform when \(|a|/q\) is order one. A linear timing response therefore cannot settle the shifted nonlinear singularity. Actual persistence additionally requires a comparator lifespan and a norm controlling quadratic Duhamel feedback. Local existence alone does not supply either endpoint comparison interval or this norm.

**Counterexamples to generic sign inference, not models of the selected force.** On the same viscosity-one unit torus take \(E=\cos(2\pi x_0)e_2\), \(\mu=4\pi^2\), \(U=b(t)E\), and \(b'+\mu b=c\). Convection vanishes, \(F=cE\), and the zero-seed deletion response is exactly
\[
z(t)=\frac c\mu(1-e^{-\mu(t-t_0)})E.
\]
Choose \(b(t_0)\) sufficiently negative that \(b'(t)>0\). For \(c>0,c<0,c=0\), the timing observation normalized by \(Y_2(t,0)>0\) has respectively positive, negative, zero sign. The cancellation identity holds in all three cases. Thus its structure and derivative normalization alone cannot force excitation. These smooth shear examples have no selected singular-axis asymptotic and supply no finding about the actual source. No numerical evidence was used.

## 6. Unresolved question and disposition

The unresolved central question is whether removal of this **same selected** force from one fixed late datum produces a total response compatible with nonlinear growth, possibly at a shifted time and location. Neither timing excitation nor persistence nor destroyed growth is established. The older direct-source estimate remains useful inherited information; the new work supplies necessary algebra, not a new selected-source response estimate.

**At most one next diagnostic, not launched:** at one fixed admissible restart, certify a nonzero pairing of
\[
F(t_0)-\frac{F_2(t_0,0)}{Y_2(t_0,0)}Y(t_0)
\]
with one independent spatial functional, using the actual selected contracts. Nonzero excludes both exact linear pure timing from zero seed and a differentiable exact same-datum pure clock. Zero is inconclusive; neither outcome settles general modulation or A/B. This finite-time test is justified because it avoids unconstructed endpoint adjoints. No broader investigation is recommended by this verdict.

Only this new verdict file was written. No builds, installs, Lean/config edits, Git writes or successor work were performed. Historical snapshot/HEAD receipts are not independently recertified by this audit.
