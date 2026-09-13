# 07 — Shear-driven pulses in a forced singular construction

**Qualified v2 — paper/source clarification, not an autonomous breakdown theorem.** This supplement reads the new paper against upstream `f9e8bc5…`; it does not change the older baselines of chapters 01–06. [The separate ledger](physical-mechanism-validation.md) identifies revisions, inspected suppliers, assumptions and the bounded approximation/pressure map.

## Executive overview

The construction does more than prescribe growth without regard to the equation. A concentrating background has a singular momentum imbalance in an annulus. Tiny externally seeded oscillatory pulses extract energy from its shear. The oscillatory waves have zero angular means in cylindrical components, but their quadratic velocity products transport momentum. Two pulse families are chosen so that this covariance cancels the background's leading stress divergence. Shearing also shortens radial wavelengths: amplification weakens while viscous damping strengthens, giving small tails that can be cut off. Further corrections and localization leave a residual extending as a smooth external force.

The tiny seed contribution is **not the entire external force**. The pulse equation is a principal, pressure-constrained amplitude equation within a designed background, not an autonomous solution of the full nonlinear initial-value problem. Its homogeneous growth after seeding does not prove that every later part of the physical evolution is force-free.

This is a versioned correction to an overly literal reading of “installed growth.” The profile and correction schedule are engineered, but their compatibility with viscous momentum balance is substantive. What remains unknown is whether an unforced evolution from one late velocity supplies the requisite future seeds, stress and concentration, or tracks them after deleting the complete force. Neither the physical explanation nor the independently useful whole-space pressure results demonstrate such leverage. B remains paused.

## 1. What needs to be canceled

At viscosity one put
\[
R(u,p)=u_t+(u\cdot\nabla)u-\Delta u+\nabla p.
\]
The background satisfies
\[
R(u_B,p_B)=-(\partial_r+2/r)T_{\mathrm{phys},\theta}e_\theta
 -(\partial_r+1/r)T_{\mathrm{phys},z}e_z+E_B.
\]
Here \(T_{\mathrm{phys}}\) is the full summed annular stress, with leading term \(T\); only that leading target is matched by the primary waves. All joint derivatives of the remainder are flat at the singular point in the specified approach domains. This is not zero residual on a terminal time interval. Paper §3.2, pp.9–11, and Proposition 5.5 express this decomposition; [FinalSlowBase](https://github.com/openai/NavierStokesAndEuler/blob/f9e8bc5b38b6e212696e8a30e3e91517af887bbd/NavierStokes/FinalSlowBase.lean) supplies `residual_identity` and `error_jetRate` with profile, approach and radius hypotheses.

The exact increment algebra is
\[
R(u_B+w,p_B+\pi)=R(u_B,p_B)+L_{u_B}(w,\pi)+\nabla\cdot(w\otimes w),
\]
where \(L_{u_B}(w,\pi)=w_t+u_B\cdot\nabla w+w\cdot\nabla u_B-\Delta w+\nabla\pi\), and \(\operatorname{div}w=0\). Thus a quadratic stress can cancel a background residual even when the wave's angular mean is zero (§3.3, pp.11–12).

| Step | Physical role | Qualification |
|---|---|---|
| Singular background → annular stress | Identifies missing momentum transport | Not yet sustainable by smooth forcing alone |
| External seed → shear amplification | Small perturbations draw energy from background | Designed pulse, not spontaneous creation from zero |
| Two covariances → stress cancellation | Nonlinear internal momentum transport | Averaged leading identity; other interactions remain |
| Shearing → viscous decay | Increasing radial wavenumber suppresses tails | Viscosity is essential, not negligible |
| Corrections → localization → smooth force | Removes remaining singular residual terms | Smooth force need not vanish |

The paper's rotational example (§2.2, pp.5–6) explains reinforcing radial/azimuthal perturbations when angular velocity decreases sufficiently rapidly. Axial shear supplies another amplification channel. Slight axial asymmetry separates the layers where rotational amplification is weak and axial shear vanishes. This illustrates the chosen profile geometry, not a necessary instability mechanism for every vortex or every possible singularity.

## 2. Which scales and which time?

Write \(\tau=1-t\), \(A=1/2+h\), \(D=1/2-h\), with fixed paper parameter \(0<h<1/100\). The similarity relation is
\[
q-z^2q^{2h}=\tau,\qquad X=r^2/(2q),\qquad \eta=z/q^D.
\]
On compact similarity sets away from \(\eta=\pm1\), \(q\asymp\tau\). Core radial/axial lengths are \(q^{1/2},q^{1/2-h}\); tangential speeds scale like \(q^{-1/2-h}\), radial speed is \(O(q^{-1/2})\). Radial diffusion and radial/axial transport have rate \(q^{-1}\); axial diffusion is smaller by \(q^{2h}\) (§3.1, pp.7–8). A large angular Reynolds number does not remove radial viscosity from the balance.

For a fixed dyadic band (§6.1–6.2, pp.62–65),
\[
Q=2^{-\ell},\quad \epsilon=Q^h,\quad S_*=\ell^2,\quad
(R,Z,T)=(r/Q^{1/2},z/Q^D,\tau/Q).
\]
Slow boxes have mesh \(S_*^{-3}\): physical widths \(Q^{1/2}S_*^{-3},Q^DS_*^{-3},QS_*^{-3}\). Carrier frequency \(k\asymp\epsilon^{-1/2}\) gives wavelength \(Q^{1/2}/k\asymp Q^{1/2+h/2}\), while leading wave amplitude is \(Q^{-A}\sqrt\epsilon=Q^{-1/2-h/2}\), **up to logarithmic factors and vanishing edge weights**. Its square has stress scale \(q^{-1-h}\); radial divergence has scale \(q^{-3/2-h}\).

The slot variable \(v\) runs over \([0,L_s]\), with \(L_s=2r_0/c_i\asymp S_*\). Here \(r_0\) is an auxiliary rectangle radius, not physical cylindrical radius. The normalized fast time derivative is \(Q^{1+h}\partial_t\), with the evaluated operator \(-\epsilon\partial_T+c_iN_i\). Along the frozen slow-coordinate pulse model, the physical duration corresponding to a slot is \(Q^{1+h}L_s\); its Gaussian central width corresponds to \(Q^{1+h}\sqrt{L_s}\). Slow coordinates also move along the evaluated physical trajectory: the ODE is not an exact reparametrization of that whole trajectory.

The band index \(\ell\) labels shrinking scales. The correction index \(J\) labels improved residual accuracy, not successive physical times or an autonomous cascade. Increasing \(J\) changes finite-prefix accuracy and constants; one diagonal selects the final field.

## 3. The pulse equation and a worked energy identity

Use \(a(v)=(a_r,a_\theta,a_z)\) for the real amplitude, avoiding the paper's use of \(t\) for both a vector and physical time. With phase normal \(n\ne0\), the principal equation is
\[
a'=-Ka+\frac{n\cdot Ka-n'\cdot a}{|n|^2}n-da-\operatorname{proj}_{n^\perp}b,
\qquad n\cdot a=0,\qquad d=\epsilon k^2|n|^2.
\]
For harmonic \(m\ne0\), damping is \(m^2d\). The source \(b\) is the harmonic residual to cancel; it is **not** the complete external force. Pressure cancels the normal component, including normal components of \(b\) (§7.2, pp.77–80, (7.13)). Leading pulses instead use \(b=0\) and a small nonzero initial amplitude. Curl reconstruction, variable cutoffs, phase defects and nonlinear interactions still require correction.

Write the chart background velocity as \(b_r e_r+Ve_\theta+Ge_z\): \(V\) and \(G\) are its azimuthal and axial profiles, and \(F=V/R\) is angular velocity, not external force. For \(g=(RF_R,G_R)\), the actual cylindrical matrix acts as
\[
Ka=(-2Fa_\theta,(2F+g_\theta)a_r,g_za_r).
\]
Consequently the rotation terms cancel in its quadratic form:
\[
a\cdot Ka=-2Fa_ra_\theta+2Fa_ra_\theta
 +g_\theta a_ra_\theta+g_za_ra_z=g\cdot[a_r(a_\theta,a_z)].
\]
Dot the homogeneous equation with \(a\). Tangency kills its normal term, yielding
\[
\boxed{\frac12\frac{d}{dv}|a|^2
=-g\cdot[a_r(a_\theta,a_z)]-\epsilon k^2|n|^2|a|^2.}
\]
This reconstructs paper (7.22), p.81: the same flux vector controls shear-energy extraction and momentum transport. Extraction requires \(g\cdot[a_r(a_\theta,a_z)]<0\); it does not hold for every tangent vector. At the representative point choose tangential orthonormal directions \(N,K\) with
\[
g_0=|g_0|N,\qquad T=T_NN+T_KK,\qquad
-g_0\cdot T=-|g_0|T_N.
\]
The selected cone has \(T_N<0\), selecting the extraction direction. Its transverse restriction makes both squared pulse amplitudes positive (§4). The component \(T_K\) controls transverse momentum transport, not another independent energy scalar; growth alone cannot establish stress matching.

For a frozen real wave \(a\cos(k\Phi)\), mean kinetic energy is \(|a|^2/4\), and radial/tangential momentum flux is \(a_r(a_\theta,a_z)/2\). The boxed identity concerns amplitude energy \(|a|^2/2\), not that averaged physical energy.

Source support is deliberately narrower than “new Lean energy theorem”: [MovingFrameODE.baseAction](https://github.com/openai/NavierStokesAndEuler/blob/f9e8bc5b38b6e212696e8a30e3e91517af887bbd/NavierStokes/MovingFrameODE.lean) defines that matrix; [TangentProjection](https://github.com/openai/NavierStokesAndEuler/blob/f9e8bc5b38b6e212696e8a30e3e91517af887bbd/NavierStokes/TangentProjection.lean) proves normal/pressure cancellation; [PrimaryODE.ambientSolution_hasDerivAt](https://github.com/openai/NavierStokesAndEuler/blob/f9e8bc5b38b6e212696e8a30e3e91517af887bbd/NavierStokes/PrimaryODE.lean) reconstructs the equation from the constructed modal solution under continuity and frame-kinematics hypotheses. The displayed dot-product derivation is human algebra from these suppliers.

## 4. Why growth turns into decay, and how stress is matched

The reference net rate is
\[
\gamma(s)=\frac{\lambda_0}{\sqrt{1+s^2}}
 -\frac{\lambda_0(1+s^2)}{(1+u_*^2)^{3/2}},\qquad
s(v)=\pm(u_*/2+u_*v/L_s).
\]
For \(\lambda_0,u_*,L_s>0\), it is positive before the midpoint, zero there, negative afterwards. [PulseGrowth.netGrowth_sign](https://github.com/openai/NavierStokesAndEuler/blob/f9e8bc5b38b6e212696e8a30e3e91517af887bbd/NavierStokes/PulseGrowth.lean) and the slot sign theorems prove this reference classification. The actual variable-coefficient solution is comparable to
\[
P(v)=\exp\!\left(\int_{L_s/2}^{v}\gamma(s(w))\,dw\right)
\asymp \exp[-c(v-L_s/2)^2/L_s]
\]
in the **two-sided Gaussian-bound sense**, not with one identical Gaussian constant. Frame errors perturb the dynamics; no exact midpoint maximum for every actual component is asserted. Paper Lemma 7.4, pp.80–81, gives \(cP\le a_r\le CP\), using a growing-coordinate seed \(P(0)\) and a controlled decaying/growing-coordinate ratio.

Shear increases radial phase slope. The first term of \(\gamma\) weakens while its damping term strengthens; \(\epsilon k^2\asymp1\). Temporal cutoff derivatives act in tails bounded by \(e^{-cL_s}\). With \(L_s\asymp\ell^2\), these beat any fixed power of \(Q=2^{-\ell}\), including fixed derivative losses. This explains tiny external seeding and smooth cutoff errors, not a global small-force bound.

For frozen amplitudes, angular averaging gives \(\langle\cos^2(k\Phi)\rangle_\theta=1/2\), since the angular frequency is a nonzero integer. Average also over the independent auxiliary torus **before** evaluating its physical phase map. Angular means can still depend on the auxiliary torus. Double averaging is performed before physical evaluation and is not a pointwise physical stress identity. Surviving auxiliary-dependent angular means, evaluated at the physical phase map, and same-label interactions require later correction (§3.3, p.12).

Define \(C(w)=\langle\langle w_r(w_\theta,w_z)\rangle_\theta\rangle_Y\), using normalized angular and auxiliary Haar measures. Here \(b_\sigma\) is a homogeneous cosine pulse with auxiliary and slot cutoffs, extended by zero off its sign's rectangle, before the slow cutoff or scalar amplitude. Disjoint auxiliary supports eliminate cross-label products. Put \(H=[C(b_+)\mid C(b_-)]\) and \(T_{0,*}=(Q/q)^{A+1/2}T_0\), the chart's order-zero target from the leading profile stress \(T_0\), not the entire \(T_{\mathrm{phys}}\). Choose squared amplitudes \(y=H^{-1}T_{0,*}\). Then
\[
W_0=\sqrt\epsilon\sum_{\sigma=\pm}\sqrt{y_\sigma}\,b_\sigma,
\qquad C(W_0)=\epsilon Hy=\epsilon T_{0,*}.
\]
For the reference columns \(h_\sigma(-A_cN-\sigma u_*K)\), with \(h_\sigma,A_c>0\),
\[
h_\pm y_\pm=\tfrac12(-T_N/A_c\mp T_K/u_*).
\]
Thus \(T_N<0\) and \(|T_K|<(u_*/A_c)(-T_N)\) ensure positivity; the paper's strict margin tolerates the actual column errors (§7.3, pp.81–84). Gaussian mass concentration supplies the actual columns, not an assumed stress identity. [PulseCovariance](https://github.com/openai/NavierStokesAndEuler/blob/f9e8bc5b38b6e212696e8a30e3e91517af887bbd/NavierStokes/PulseCovariance.lean) proves mass bounds and `actualColumn_factorization`; [ActualPrimaryCovariance.viewSum_covariance_factor](https://github.com/openai/NavierStokesAndEuler/blob/f9e8bc5b38b6e212696e8a30e3e91517af887bbd/NavierStokes/ActualPrimaryCovariance.lean) retains an explicit partition factor on the native domain. Do not silently replace that factor by one on arbitrary selected enlarged cells. Physical curls add smaller terms, not exact equality of the entire corrected covariance with the target.

## 5. Full forcing and the autonomous gap

The correction cycle removes remaining singular interactions; summation and spatial localization preserve the core while allowing smooth residual extension (§3, pp.13–15; §9, pp.100–115; §10, pp.116–125). The heat exterior solves its local equation exactly, but localization creates additional smooth force. Activation to zero datum also creates force. [CandidateFromLimits.force](https://github.com/openai/NavierStokesAndEuler/blob/f9e8bc5b38b6e212696e8a30e3e91517af887bbd/NavierStokes/CandidateFromLimits.lean) glues actual residual jets; `force_smooth` consumes their locally uniform limits. Neither this nor seeding estimates imply that all forcing is exponentially small, confined to seeds, or zero near terminal time.

Taking the divergence of the localized equation gives (10.5)
\[
-\Delta p=\partial_i\partial_j(u_i u_j)-\operatorname{div}f,
\]
with repeated spatial indices summed. The residual includes **every** cutoff derivative in (10.4)–(10.5). Principal normal-pressure cancellation does not remove the full pressure/localization residual or the force-divergence contribution.

**Versioned clarification v2:** the historical research heading “Installed growth, not an autonomous cascade” remains valid as a distinction about construction and selection. Read literally as “PDE-independent growth” or “no physical shear mechanism,” it is superseded here. Historical calculations and their negative stability-certificate verdicts are not rewritten or recertified.

Autonomous seeding would require one unforced evolution to generate the future pulses and required stress from its own admissible datum, including all nonlinear/pressure errors. Force deletion instead asks whether the unforced IVP from one fixed late \(U(t_0)\) retains concentration after removing **all** raw force \(f\). Work on a presingular classical slab \([t_0,t_1]\), \(t_1<1\), where both solutions exist smoothly. On the unit torus use periodic pressure, normalized to zero spatial mean, and the Leray projection \(\mathbb P\) retaining constant vector fields. Put \(F=\mathbb Pf\) (distinct from §3's angular velocity). Same-velocity pressure absorption requires \(F=0\) throughout the slab. Flat raw origin jets do not prove that condition. Unlike the earlier pressure-inclusive \(L_{u_B}(w,\pi)\), define the projected operator on divergence-free fields by
\[
\mathcal L_Uw=w_t-\Delta w+
\mathbb P(U\cdot\nabla w+w\cdot\nabla U).
\]
With deletion error \(w=U-v\),
\[
\mathcal L_Uw=F+\mathbb P(w\cdot\nabla w),\qquad w(t_0)=0.
\]
Native pulse bounds are not estimates for this full operator. Also \(\mathcal L_UU_t=F_t\): no homogeneous neutral clock direction or equation-level clock invariance follows. Selected response, endpoint nonlinear control and comparison lifespan remain unsupplied. The independent approximation/pressure mapping in the ledger changes none of these conclusions or chapter 06's selected-array/domain qualification.
