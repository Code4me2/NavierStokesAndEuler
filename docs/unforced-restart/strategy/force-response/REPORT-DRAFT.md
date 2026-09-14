# Report draft — selected force response

**Decision: outcome (iii), after a completed bounded calculation.** Neither the requested total margin nor its violation is established. [CALCULATION.md](CALCULATION.md) combines the two supplied analyses, independently checks decisive source formulas, and isolates one remaining full-PDE pairing rather than proposing another source-inventory campaign.

## Established in the human calculation

1. **Same selected observable.** The actual stage germs, exported selected schedule, base coefficient identities, localization and activation give, on one fixed terminal interval,
   \[
   U(t,0)=j_*(1-t)^{-A}e_2,\qquad \partial_2U_2(t,0)=4/(1-t),
   \quad\partial_0U_2(t,0)=\partial_1U_2(t,0)=0.
   \]
   Here \(j_*\) belongs to the actual nominal witness, not a newly selected profile.
2. **Complete source and cancellation.** All residual terms survive in \(F=\mathbb Pf=U_t-\Delta U+\mathbb P(U\cdot\nabla U)\). Periodic curl integration and the literal direct-angular half-turn prove zero mean; the observation's constant mode contributes zero. Leray itself still retains constants.
3. **Full finite-horizon identity.** On divergence-free periodic \(H^4\), including constants, the smooth-coefficient evolution and distributional adjoint justify
   \[
   J(T)=\int\langle a_T,F\rangle
   =j_*-\ell_T\Phi_U(T,t_0)U(t_0)
     +\int\!\int S(a_T):(U\otimes U).
   \]
   The adjoint terminal datum is in \(H^{-4}\), not \(L^2\). No endpoint-uniform propagator estimate follows from finite-horizon existence.
4. **Concrete improvement over generic energy.** Exact axial stretching is damping. Splitting pressure into forcing and response parts gives \(J=D_F+R_U\), where
   \[
   \sup_{t_0<T<1}|D_F(T)|\le C_{\rm ev}M_4(1-t_0)^{A+1}/3.
   \]
   This controls the **entire direct projected source**, including its nonlocal forcing-pressure part; no flatness of \(\mathbb Pf\) is assumed. The stronger local Taylor bound for unprojected \(f_2(t,0)\) is retained but not mistaken for whole-source control.

## Exact obstruction, not a claim of instability

The remaining signed term is
\[
 R_U(T)=q_T^{A+4}\int_{t_0}^Tq_s^{-4}\mathcal K_U(s)z(s)\,ds,
\]
\[
 \mathcal K_U(s)v=\Delta v_2(0)-j_*q_s^{-A}\partial_2v_2(0)
 +\partial_2\Delta^{-1}\operatorname{div}
   (U\cdot\nabla v+v\cdot\nabla U)(0).
\]
It includes diffusion, axial transport and complete response-pressure coupling. Restart-seeded spatial modes continue feeding it. Native modal damping and unweighted covariance do not control the adjoint-weighted total stress or its cross-mode strain interactions.

A full heat-parametrix test proves that its particular positive \(H^4\) contraction majorant grows at least like \(c j_*q_T^{-h}\). This rules out uniform smallness of **that majorant only**. It proves no lower bound for the actual response and does not exclude cancellation.

The quantifier target remains one \(t_0\) and one \(\rho<1\) for **every** later \(T<1\). The calculation states a sufficient axial Green estimate and derives it conditionally from a uniformly coercive coefficient-level symmetrizer inequality. Neither is claimed available. The germ, mean and damping tools can be extracted now; a bound for the remaining pairing requires genuinely new full-PDE analysis beyond the inspected native machinery. Repairing chapter 06's selected-domain threshold bridge alone does not supply it.

## Scope and preservation

**Source interpretation:** decisive bodies checked at main HEAD `1d16509bec4609ae418e64842e81b8b0ac07dcc7`, companion HEAD `6da0731071d900b7a1cf3fb9c009aa7cf6bc6c7f`; source links are in the calculation. Central report and companion 05/06 read fully.

**Human analytic derivation:** finite-horizon evolution/duality, signed identities, mean integration, axial damping and estimates above. **New formal results: none.** No builds, installations, Lean implementation, commits, refs or pushes. Only these two new documentation files were written. Existing `CENTRAL-OBSTACLE.md` and all prior files remain untouched; its SHA-256 is `f991919951bee0dd2d0b7568091b90c5babc447c41df43c518ad7163e2c511c2`.

Even scalar linear success would require nonlinear closure for \(L_Uw=F+\mathbb P(w\cdot\nabla w)\). Under periodic B, global comparator smoothness may be assumed for contradiction, not stability. Whole-space A was not attempted.
