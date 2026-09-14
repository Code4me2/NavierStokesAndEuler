# Final source-and-strategy adversarial verdict

## Executive summary

**Verdict: qualified acceptance of the identities and negative evidence boundary; partial algebraic success, failure to establish selected timing excitation or autonomous persistence.** This is not an unqualified strategic pass.

Independent differentiation confirms
\(L_U[U+(t-t_0)U_t]=2F+\Delta U+(t-t_0)F_t\), with the nonzero restart seed indispensable. The adjoint representation and nonlinear clock residual are correct on compact presingular slabs. No decisive sign or pressure error was found in the actual timing drafts.

The new correlation formula is a useful exact reorganization of the selected problem, but is universal residual algebra specialized using previously obtained axial data. It supplies no new estimate, nonvanishing result, or favorable asymptotic for the selected deletion response. Calling it “actual-source cancellation” must not suggest that convection has been controlled or that selected forcing excites a phase mode.

Accept “pure-clock compatibility remains undecided” as an evidentiary statement about the inspected contracts—not a proof of compatibility, impossibility of deciding it, or nonlinear shadowing. An additional necessary spatial-derivative test is given below as a review proposal, not an evaluated selected-source result.

**No positive evidence for unforced breakdown emerged. Neither A nor B is resolved or made demonstrably easier.** The prior obstruction concerns a different source and seed; a failed stability certificate does not establish destroyed growth or favor a counterexample.

The source audit is targeted and source-trusting upstream. Adversarial audit agreement is neither Lean validation nor independent kernel checking. Only this new verdict is written; there is no revision or successor phase.

## 1. Source analysis — what was actually inspected

Read both timing documents, the earlier [FINAL-REPORT](../force-response/FINAL-REPORT.md), its historical [CALCULATION](../force-response/CALCULATION.md), and [CENTRAL-OBSTACLE](../CENTRAL-OBSTACLE.md). Historical (13)–(14) are not usable hypotheses.

Decisive source inspection:

- [WitnessFeasibility/Main.lean](../../../../Research/UnforcedRestart/Round3/WitnessFeasibility/Main.lean), complete: `selected : Data` is one classical choice containing the schedule, force, candidate and global smoothness. `terminal_origin_jets` concerns that force at `(1,0)`. It does not identify this choice with an internal existence-proof witness or export force removal.
- [ProblemStatement.lean](../../../../NavierStokes/ProblemStatement.lean), complete: viscosity exactly one, periodic pressure/velocity/force, presingular smoothness, residual equation and prescribed blowup. Its comparison vocabulary does not export a restarted unforced stability theorem.
- [CorrectionInitialization.lean](../../../../NavierStokes/CorrectionInitialization.lean), `ActualPrimary` definitions around 2962: the nominal data belong to `FinalSlowBase.actualProfile`; no witness substitution is licensed.
- [EntranceAlignedBase.lean](../../../../NavierStokes/EntranceAlignedBase.lean), `modulated_leading_axis` and `modulated_positive_axis`; [BaseResidual.lean](../../../../NavierStokes/BaseResidual.lean), origin calculation; and targeted `FinalSlowBase` suppliers: these substantiate the base axial constants, positivity and smoothness.
- Targeted `ActualCandidateAssembly` stage definitions and `GermCandidateAssembly` germ contracts support the prior transfer mechanism. [TimeLocalization.lean](../../../../NavierStokes/TimeLocalization.lean): late activation is literal local spacetime equality, not merely value equality. I retain the earlier full germ-transfer and mean-cancellation audit as inputs; this is not a fresh exhaustive check of every localization/gauge dependency.
- [ActualParticularControl.lean](../../../../NavierStokes/ActualParticularControl.lean):43–54 bounds `PrimaryODE.State` under a selected frame, with harmonic damping. [ActualPrimaryCovariance.lean](../../../../NavierStokes/ActualPrimaryCovariance.lean):382–398 matches a native `doubleAverage` to partition factor times leading stress. Neither theorem contains this PDE propagator or its terminal adjoint weight.
- Companion `06-primitive-derivative-bounds.md` §1 explicitly leaves the enlarged-chart bridge conditional for every actual selected label. No numerical array or internally exhibited preparation can silently repair it. This review checked that qualification, not the whole companion derivation.

Thus the same selected trajectory/source is maintained. No toy computation, internal existence history, or modal estimate has been transferred as an actual-force response theorem. Global force smoothness on a compact time-window times the torus bounds every fixed spatial Sobolev seminorm of \(F=\mathbb Pf\) and \(F_t\). Terminal-origin flatness of \(f\) does **not** imply flatness of the nonlocal \(F\).

## 2. New mathematics — independently checked exact scope

All calculations first fix one late \(t_0\) and \(T<1\). Write \(Y=U_t\), \(N=\mathbb P(U\cdot\nabla U)\), \(F=Y-\Delta U+N\), and \(L_U=\partial_t-\Delta+\mathbb P(U\cdot\nabla\,\cdot+\,\cdot\,\cdot\nabla U)\).

### Signs, cancellation and adjoint

Bilinearity gives
\[
L_UU=F+N,\qquad L_UY=F_t,\qquad
L_U(U-v)=F+\mathbb P((U-v)\cdot\nabla(U-v)).
\]
For \(d=t-t_0\), the product rule adds \(Y\), so
\[
L_U(U+dY)=F+N+Y+dF_t=2F+\Delta U+dF_t.
\]
Duhamel for \(L_Uz=F,\ z(t_0)=0\) therefore gives exactly
\[
2z(T)=U(T)+d_TY(T)-\Phi(T,t_0)U(t_0)
-\int_{t_0}^T\Phi(T,s)(\Delta U+d_sF_t)\,ds.
\]
The seed is not optional and is not zero just because \(z(t_0)=0\).

Smooth compact-slab coefficients support parabolic evolution on divergence-free periodic \(H^4\). Point evaluation belongs to its distributional dual. With the drafts' \(\kappa_T\), \(\beta_T=\Phi(T,\cdot)^*\kappa_T\) obeys \(-\beta_T'=G^*\beta_T\), where integration by parts yields
\[
G^*b=\Delta b+\mathbb P(U\cdot\nabla b)-\mathbb P((\nabla U)^Tb).
\]
The generator is unbounded; this is distributional duality, not an \(H^4\) Riesz identification. Pairing smooth fields and integrating gives
\[
2\alpha(T)=T-t_0+q_T/A-\mathcal C_T,
\qquad \mathcal C_{t_0}=\delta/A.
\]
Consequently the draft's margin and conditional limit formulas are correct. A limit \(\mathcal C_T\to\delta\) alone permits errors much larger than \(q_T\); for example a formal correction \(q_T^{1/2}\) defeats the margin. This is an illustration of insufficient convergence rate, not an asymptotic assigned to the selected force.

Also
\[
\langle\beta_T(s),Y(s)\rangle
=1-\int_s^T\langle\beta_T(r),F_t(r)\rangle\,dr.
\]
There is no conserved phase normalization. Endpoint convergence of \(\beta_T\), dominated convergence in these integrals, and interchange of \(T\uparrow1\) with differentiation or modulation have not been justified.

### Modulation, gauge and nonlinear pressure

At fixed torus and viscosity, \(V_\lambda=\lambda U(t_0+\lambda d)\), \(p_\lambda=\lambda^2p(t_0+\lambda d)\) has residual
\[
\lambda^2f(t_0+\lambda d)+\lambda(\lambda-1)\Delta U(t_0+\lambda d).
\]
The defect and changed datum \(\lambda U(t_0)\) confirm that this is not a same-datum symmetry. Its sampled singular time is \(t_0+\delta/\lambda\); for \(\lambda>1\) it occurs before one. Differentiation near \(\lambda=1\) is legitimate for each fixed \(T<1\), not on a common interval through one.

For any smooth dual gauge \(\chi(t)\) satisfying \(\langle\chi,Y\rangle=1\), set \(a=\langle\chi,z\rangle\), \(r=z-aY\). Direct differentiation yields
\[
L_Ur=F-a'Y-aF_t,
\quad a'=\langle\chi,F-aF_t\rangle+
\langle\chi'+G^*\chi,r\rangle.
\]
Thus the inhomogeneity and remainder coupling are gauge-independent obligations; the scalar coordinate is not gauge-independent. The drafts' \(L^2\) gauge is well-defined at finite times because \(Y_2(t,0)\ne0\). It does not construct an invariant complement. Exact linear pure timing requires \(F=a'Y+aF_t\), including restart collinearity. The integrating-factor estimate \(|a|\le C\delta^{A+2}\) is valid **only under this extra full-field hypothesis**.

For \(W=U(\theta(t))\), the residual is \(f(\theta)+(\theta'-1)Y(\theta)\). Subtracting an unforced comparator and expanding convection yields the stated projected error equation with positive quadratic error. The total pressure difference includes nonlinear pressure; the displayed \(\pi_{\rm lin}\) represents only the projected linear convection correction. Pressure gauge additions do not alter any projected conclusion. Leray retains constants.

Matching the datum uses \(\theta(t_0)=t_0\). A constant shift generally fails that condition and samples only times below one. A delay \(\theta=t-\varepsilon\) moves the sampled singularity to \(1+\varepsilon\); it does not remove it. Ramping the delay preserves the datum but creates \(-a'Y\). Already on the axis, the second Taylor term relative to the first is of order \(|a|/q_t\). Linear timing is therefore not uniform when a fixed nonzero shift approaches the endpoint.

## 3. Severity findings and adversarial countertests

**High — central evidentiary shortfall, not a discovered algebra error.** No signed selected pairing is estimated. \(\mathcal C_T\) contains the full convection-dependent propagator, diffusion and propagated seed. Eliminating an explicit quadratic source does not simplify that operator by theorem. This is necessary algebraic information with a sharper bookkeeping target, not demonstrated timing excitation. Reject any stronger reading of “substantive new reduction.”

**High — nonlinear and A/B inference blocked.** A large linear observation neither establishes actual error growth nor rules out shifted singular growth. A small observation supplies no norm for quadratic feedback or lifespan. The conditional persistence criterion is a valid sufficient implication: if the clock reaches one and the weighted error stays strictly below \(j_*\), the comparator's axial velocity is unbounded. None of its existence/remainder hypotheses is established. A global comparator may be assumed for contradiction, not obtained from local existence on the required interval. Periodic B does not settle finite-energy whole-space A; existential versus universal quantifiers do not rank difficulty.

**Medium — universality defeats generic sign arguments.** A concrete PDE countertest is the smooth mean-zero shear
\(U=b(t)\cos(2\pi x_0)e_2\). Let \(\mu=4\pi^2\). Then \(N=0\), \(F=(b'+\mu b)\cos(2\pi x_0)e_2\), and exactly
\[
z=[b(t)-e^{-\mu d}b(t_0)]\cos(2\pi x_0)e_2.
\]
For \(b=e^{rd}\), \(b(t_0)=1\), the derivative-normalized axial response is
\((1-e^{-(\mu+r)d})/r\). It is positive for \(r>0\), negative for \(-\mu<r<0\), and zero for \(r=-\mu\), although \(Y\ne0\). These are genuine finite-slab NS examples testing the universal algebra, **not substitutes for the selected singular trajectory or its axial asymptotic**. In the unforced case the seed and integral cancel exactly. No positivity argument can arise solely from the amplitude–time identity.

**Medium — old obstruction remains source-specific in the wrong direction.** The prior test \(L_UY=F_t\), \(Y(t_0)\ne0\), excludes the advertised unrestricted growth bound by comparing \(q_T^{-A-1}\) with \(q_T^{-\gamma}\). It does not evaluate \(\int\Phi F\) with zero datum. A differentiated trajectory is not an automatic homogeneous phase mode.

**Qualification — “undecided” is local to the evidence.** Neither full-field collinearity nor its failure is supplied. This does not assert that every original source theorem has been exhausted or that the selected clock could actually be unforced.

## 4. Review proposal only — one bounded spatial diagnostic

A sharper necessary pure-clock test uses the already accepted axial derivative rather than an unspecified second observation. If \(F(t)=c(t)Y(t)\), then
\[
\mathscr D(t):=Y_2(t,0)\,\partial_2F_2(t,0)
-\partial_2Y_2(t,0)\,F_2(t,0)=0.
\]
Differentiate the accepted \(\partial_2U_2=4/q_t\) in time: \(\partial_2Y_2=4/q_t^2\). Hence
\[
\mathscr D(t)=Aj_*q_t^{-A-1}\partial_2F_2(t,0)
-4q_t^{-2}F_2(t,0).
\]
Smooth projected force bounds imply, conditionally on collinearity,
\(|c(t)|=q_t^2|\partial_2F_2(t,0)|/4=O(q_t^2)\), sharper than the value-only \(O(q_t^{A+1})\). This is an additional necessary restriction, not an exclusion or persistence result.

**At most one next diagnostic, not launched:** certify \(\mathscr D(t)\ne0\) at one actual selected time in the intended clock's sampled interval. This would exclude exact pure-clock absorption across that time, without endpoint adjoints. A zero value is inconclusive; the test does not exclude general modulation or even exact linear timing, whose condition also contains \(aF_t\). It requires the actual projected source, not unprojected terminal jets. No further investigation is authorized by this verdict.

## 5. Final disposition and preservation scope

Accepted: exact finite-slab identities, seed/sign bookkeeping, conditional bounds and the drafts' stated nonconclusions. Qualified: novelty is algebraic reorganization, and source verification remains targeted. Rejected: any report of established timing excitation, nonlinear persistence, destroyed growth, or positive evidence for unforced breakdown.

**Unresolved central question:** what is the same selected zero-seed deletion response, and does the corresponding nonlinear unforced evolution retain singular growth? This audit does not decide either part.

No builds, installs, Lean checks, Git commands/writes, commits or successor work were performed. The only write in this review is this new verdict. Prior snapshots and administrative HEAD/index/ref preservation claims were not independently reproduced here; they are not mathematical evidence. The supervisor can report **partial algebraic success and strategic nonclosure**, not that a persistence strategy passed.
