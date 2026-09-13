# Final report — deleting the selected force

## OVERVIEW

**Outcome (iii): the total response remains unknown.** Deleting the force starts a different fluid evolution from the same late velocity. The construction prescribes a growing velocity; it does not show that an unforced fluid will keep following it, or that the late force is necessary to sustain its growth.

We now control one concrete part of the deletion response: the force acting directly on the observed axial velocity, including its nonlocal forcing-pressure contribution. Exact axial damping makes that contribution uniformly small after one sufficiently late restart. **The complete response is not proved smaller than the prescribed growth.** Motion elsewhere, diffusion, transport and response pressure can still feed the observation. Their combined signed contribution is uncontrolled; naming it does not estimate it.

There is also a decisive negative result about the proposed method. A small time shift of the selected trajectory changes its axial velocity faster than the trajectory itself grows. This differentiated trajectory obeys the same linearized equation with a smooth differentiated force. Consequently, the proposed uniform estimate for all inputs cannot hold with the advertised growth exponent. Its proposed uniformly coercive energy form cannot hold either.

This excludes a particular stability certificate, **not** the selected force-deletion response: the obstruction uses a different source and a nonzero initial seed. Neither total margin nor total violation follows. No credible route to endpoint persistence emerged from the inspected proof tools. The supported next step is the derivative calibration established below; any later attempt must explain selected-source cancellation or rigorously handle the growing derivative directions, rather than seek the excluded unrestricted estimate.

## KEY ISSUES

- **Fresh gain:** the direct-source interface is closed, including forcing pressure. This is not control of the total propagator.
- **Substantive correction:** historical calculation (13)–(14) are impossible as stated, not merely unavailable.
- **Unknown:** the whole endpoint signed response, even at the single axial observation, and all nonlinear persistence claims.
- **Certified failure, human-analytic only:** the stated unrestricted Green/symmetrizer criterion fails. This is not a certified failure of the selected total-margin criterion.
- **Reusable tools:** selected germs, source smoothness and mean cancellation give exact identities and a useful calibration. No reusable original-proof tool controlling full-PDE endpoint stability has been identified.

## 1. Disposition and evidence boundary

This report supersedes the strategic claims in [CALCULATION.md §6](CALCULATION.md#6-exact-stopping-point-and-a-noncircular-sufficient-theorem) and the corresponding paragraph of [REPORT-DRAFT.md](REPORT-DRAFT.md). Both remain unchanged as historical evidence. In particular, “no such form … has been supplied” must now be read as **the stated form is excluded**. The conditional algebra (14) ⇒ (13) ⇒ margin is valid, but its hypotheses cannot hold for this selected velocity.

The prior [CENTRAL-OBSTACLE.md](../CENTRAL-OBSTACLE.md) also remains unchanged. Its stopping point is sharpened, not replaced by a persistence theorem.

All new PDE conclusions here are human analytic deductions, not new Lean theorems. This completion reread both documents and the central memo, and checked the decisive selection, smoothness/periodicity, nominal-profile and axial-coefficient contracts in the sources below. The wider germ, localization, residual, modal and covariance audit is the accepted prior review recorded in the calculation; this completion does not represent a new exhaustive source audit.

## 2. Same selected problem; genuine gains versus reconfirmations

Use only [WitnessFeasibility.selected](../../../../Research/UnforcedRestart/Round3/WitnessFeasibility/Main.lean). Its record ties the schedule, forcing, candidate and global forcing smoothness together. [ActualPrimary](../../../../NavierStokes/CorrectionInitialization.lean) abbreviates `FinalSlowBase.actualProfile` and its nominal witness. No classical choice is identified with a separately exhibited internal witness, and no threshold is silently increased.

Write \(q_t=1-t\), \(A=1/2+h\in(1/2,1)\), and \(j_*>0\) for that nominal witness's axial constant. The transferred selected germs give, on a fixed terminal window,
\[
 U_2(t,0)=j_*q_t^{-A},\qquad
 \partial_2U_2(t,0)=4/q_t,\qquad
 \partial_0U_2(t,0)=\partial_1U_2(t,0)=0.
\]
The [axial coefficient identities](../../../../NavierStokes/EntranceAlignedBase.lean) supply the leading affine axis profile and positive-order vanishing. The accepted transfer uses actual stage-zero initialization, positive-stage zero germs, local finiteness, gauge-curl equality, cutoff plateau, periodization and late activation. It requires no global axisymmetry.

**Gains over the central memo:** explicit observable transfer; actual mean cancellation; a signed full-PDE decomposition; exact axial damping; and control of the complete direct projected source. **New in this resolution:** using the time derivative to exclude the proposed operator route.

**Reconfirmations, not new stability results:** viscosity-one residual signs, Leray retaining constants, finite-horizon evolution and distributional duality, the fixed-restart quantifiers, and the need to retain early spatial seeds. The [candidate contract](../../../../NavierStokes/ProblemStatement.lean) gives the equation and force periodicity; selected global smoothness gives bounded spatial Sobolev seminorms of the force and its time derivative on a closed terminal window.

The selected-domain limitation remains: companion chapter 06's enlarged-chart threshold bridge for explicit arrays on every actual label is not exported merely by selecting a prepared record. Exported qualitative contracts remain usable; repairing that numerical/domain bridge would not establish full-PDE stability. Upstream profile production remains source-trusted, not independently reconstructed here.

## 3. What is controlled, and what is not

On the fixed unit torus let
\[
 F=\mathbb Pf=U_t-\Delta U+\mathbb P(U\cdot\nabla U),\quad
 L_Uz=z_t-\Delta z+\mathbb P(U\cdot\nabla z+z\cdot\nabla U).
\]
Fix **one** admissible \(t_0=1-\delta\); solve \(L_Uz=F\), \(z(t_0)=0\). The linear deletion observable is \(J(T)=q_T^Az_2(T,0)\). The sought margin is
\[
 \exists t_0<1\ \exists\rho\in(0,1)\ \forall T\in(t_0,1):
 |J(T)|\le\rho j_*.
\]
Finite-horizon \(H^4\) evolution supports point evaluation, the diffusion evaluation and an \(H^{-4}\) terminal adjoint. It supplies no endpoint-uniform constant.

The accepted calculation gives
\[
 J(T)=D_F(T)+R_U(T),\qquad
 \sup_T|D_F(T)|\le C_{\rm ev}M_4\delta^{A+1}/3,
\]
where \(M_4=\sup_{[1-\delta_*,1]}\|f(s)\|_{H^4}<\infty\). This controls forcing pressure without pretending that Leray preserves local flatness. The remaining term is
\[
 R_U(T)=q_T^{A+4}\int_{t_0}^Tq_s^{-4}\mathcal K_U(s)z(s)\,ds,
\]
\[
 \mathcal K_U(s)v=\Delta v_2(0)-j_*q_s^{-A}\partial_2v_2(0)
 +\partial_2\Delta^{-1}\operatorname{div}
 (U\cdot\nabla v+v\cdot\nabla U)(0).
\]
This contains the complete unknown response, not a newly controlled remainder. Core-scale dimensional comparisons neither establish the response's spatial scales nor preclude signed cancellations. The heat-source estimate already has the same \(\delta^{A+1}\) power; the advance is exact decomposition and pressure accounting, not demonstrated favorable total-response dynamics.

The positive heat-parametrix contraction majorant diverges at least as \(c j_*q_T^{-h}\). Only that majorant fails: it is not a lower bound for the actual operator or response. An early state \(z(\tau)\) still feeds the later evolution; terminal force flatness cannot erase it.

## 4. Why the unrestricted replacement is excluded

Let \(Y=U_t\). Differentiation on the same fixed torus gives
\[
 L_UY=F_t,\qquad Y_2(T,0)=Aj_*q_T^{-A-1}.
\]
The established zero means of \(U,F\) imply zero means of \(Y,F_t\). Smoothness gives a fixed finite \(M_{t,4}=\sup\|F_t(s)\|_{H^4}\).

Historical (13) would bound every mean-zero input's unweighted axial observation by \(C(q_s/q_T)^\gamma\) times its \(H^4\) norm. Duhamel applied to \(Y\), retaining its fixed initial seed, would then bound its observed growth by \(O(q_T^{-\gamma})\). This contradicts its exact \(q_T^{-A-1}\) growth for every \(0\le\gamma<A+1\), including the entire advertised range \(0\le\gamma\le A\). Appendix A gives the constants and calibration. The energy inequality (14) implies that same forbidden bound, so it too is excluded in its stated range.

This is not growth or smallness of \(z\): \(Y\) has initial datum \(Y(s_0)\) and source \(F_t\), whereas \(z\) has zero restart datum and source \(F\). No continuous dilation, changed schedule or substituted witness is used.

## 5. Next step and stopping rule

The smallest supported analytic step is now completed: the differentiated-trajectory calibration rules out overly broad estimates. Beyond it, any viable continuation must exploit selected-source structure, or justify a restricted/modulated evolution that accounts for growing derivative directions. Simply projecting away \(U_t\) introduces unproved dual construction, invariance, source compatibility, observation and remainder obligations. No inspected certificate meets them; **no credible positive closure route emerged**.

The original modal-energy estimate controls a moving-frame auxiliary ODE. Native covariance uses an unweighted fast-variable average, not the axial adjoint's weight. Neither supplies the full pressure-coupled propagator or its cross-mode strain control. There are reusable original identities for source/observable reduction, but no identified original-proof stability tool that closes the remaining pairing. Further peripheral residual inventories or primitive bounds are not the supported next task.

Even a scalar linear margin would not control the nonlinear error:
\[
 w=U-v:\qquad L_Uw=F+\mathbb P(w\cdot\nabla w).
\]
Periodic B may assume comparator global smoothness for contradiction, not stability. Whole-space A additionally needs a justified whole-space construction and comparison; a periodic field is not finite-energy whole-space data. **No result for A or B, and no nonlinear shadowing or endpoint persistence, is claimed.**

## 6. File and check scope

Only `docs/unforced-restart/strategy/force-response/FINAL-REPORT.md` is new. No prior calculation, report, source or historical receipt is edited. Main HEAD remains `1d16509bec4609ae418e64842e81b8b0ac07dcc7`. The historical companion HEAD `6da0731071d900b7a1cf3fb9c009aa7cf6bc6c7f` is retained as a prior receipt, not asserted freshly audited here. Central memo SHA-256 remains `f991919951bee0dd2d0b7568091b90c5babc447c41df43c518ad7163e2c511c2`.

Completion checks are limited to this new report's local link targets/anchor, length limits, and preservation against a pre-write snapshot of tracked files and existing restart documentation, HEAD and refs. These are documentation/preservation checks, **not mathematical certification**. No Lean edits, builds, proof checks, installations, commits, pushes, ref changes or automatic successor work are performed.

## Appendix A — concise correction calculation

The unchanged [calculation §§1–5](CALCULATION.md) supplies the accepted detailed derivation; its §6 proposed route is superseded above.

Since spatial Leray commutes with time differentiation, differentiating
\(F=U_t-\Delta U+\mathbb P(U\cdot\nabla U)\) gives \(L_UU_t=F_t\). On any compact presingular slab, \(Y=U_t\) is smooth and Duhamel applies. Fix admissible \(s_0<1\). If historical (13) held, then
\[
 Aj_*q_T^{-A-1}
 \le Cq_T^{-\gamma}\left[
 q_{s_0}^{\gamma}\|Y(s_0)\|_{H^4}
 +M_{t,4}\int_{s_0}^Tq_s^\gamma\,ds\right].
\]
For \(\gamma\ge0\), the bracket is at most
\[
 B=q_{s_0}^{\gamma}\|Y(s_0)\|_{H^4}
 +\frac{M_{t,4}q_{s_0}^{\gamma+1}}{\gamma+1}<\infty.
\]
Multiplication by \(q_T^{A+1}\) gives \(Aj_*\le CBq_T^{A+1-\gamma}\), impossible as \(T\uparrow1\) if \(\gamma<A+1\). No claim is made at or above that threshold.

With \(\ell_Tv=q_T^Av_2(0)\) and the historical distributional adjoint \(a_T\), the exact signed calibration is
\[
 \boxed{\ell_T\Phi_U(T,s_0)U_t(s_0)
 +\int_{s_0}^T\langle a_T(s),F_t(s)\rangle\,ds
 =Aj_*/q_T.}
\]
The seed is essential. Independently, spatial differentiation gives
\(L_U\partial_2U=\partial_2F\) and \(\partial_2U_2(T,0)=4/q_T\), excluding \(0\le\gamma<1\) by the same argument. Both inputs are periodic, divergence-free and mean-zero.

Finally, a uniformly coercive (14) yields homogeneous \(H^4\) growth at most \(\sqrt{C_0/c}(q_s/q_T)^\gamma\) by differentiating its energy and integrating \(2\gamma/q_t\). Bounded evaluation yields (13), contradicting the preceding test. Thus (14) is impossible with its stated exponent, not an outstanding symmetrizer search.
