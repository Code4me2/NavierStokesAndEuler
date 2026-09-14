# One primary pulse: seed size, backward cost, and autonomous supply

**Final bounded human mathematical/source analysis; accepted with qualifications by two independent reviews, not kernel certification.** This is a corrected copy of the preserved `CALCULATION.md`; review resolutions and finalization checks are in [REVIEW-DISPOSITIONS.md](REVIEW-DISPOSITIONS.md). Owned root: `/home/velvet/pulse-seeding-analysis-nM8ujEl7`. All input locations and byte hashes are in [INPUTS.json](INPUTS.json). No source, historical receipt, repository or Git reference was changed. No build, Lean implementation, numerical selected-field model, or Comparator recovery was attempted.

## 1. Representative and evidence boundary

Choose **the positive-sign, first-harmonic primary pulse of paper Lemma 7.4 and Proposition 7.5**, in one sufficiently large existing band and one active slow box, at a slow point in the open stress annulus where the slow mask is nonzero. Freeze that point and a transverse point where its cutoff is nonzero. This is a member of the actual construction's family, **not a replacement constant-shear example**. The negative-sign companion enters only to determine the positive pulse's share of the two-component target. No numerical representative, value of the selected profile, slope parameter, or rounded frequency is fabricated.

In literal upstream notation, fix the existing `ActualPrimary.choice Bbud N0`, one of its `Label Bbud N0`, and `j = 0 : Fin 2` (the positive sign). Use its `phases`, `covariance`, and `rawVelocity`. The selected point must belong to that preparation's native carrier and its positive stress region. Where a sufficiently-large-band condition is used below, it restricts the **one label inspected**; it does not replace the selected preparation or silently increase its stored threshold. Constants are finite symbolic constants of this same preparation, not effective selected numbers.

Primary paper locators refer to [the controlling text][P]: §6.1–6.2, text lines 3298–3522, printed pp.62–66; §7.1–7.4, lines 3825–4597, pp.73–87; §9.1, lines 5282–5382, pp.101–103. These sections and the controlling companion/historical reports were read; this is not an independent audit of all 166 paper pages or the whole construction.

**Three objects must remain separate.**

1. **Modal pulse:** an actual variable-coefficient ODE with the slow point fixed; the reference diagonal system below estimates it.
2. **Exact localized field:** cutoff potential, physical evaluation, and full curl. It is divergence-free, but has additional linear and nonlinear residuals.
3. **Full unforced periodic NS solution:** not supplied by either of the above. Neither the background alone nor the initialized wave sum is such a solution.

## 2. Exact conventions, source and stress share

### Coordinates, clock and carrier

Use viscosity **one**, the normalization of the construction. A counterexample at this positive viscosity would suffice to refute universal B, but none is obtained here. Fix paper `0<h<1/100`, `A=1/2+h`, `D_h=1/2-h`; the Lean interfaces often state the weaker `0<h<1/2`. Nothing below substitutes a numerical value of `h` into a selected Lean object.

Physical time is `t`, backward time is `τ=1−t`, and

\[
q-z^2q^{2h}=\tau,\quad X=r^2/(2q),\quad
Q=2^{-\ell},\quad \epsilon=Q^h,\quad S=\ell^2,
\qquad (R,Z,T)=(r/Q^{1/2},z/Q^{D_h},\tau/Q).
\]

Here `R` is the **band** radius, not the profile radius `r/√q`. Physical velocity, pressure, residual and potential equal their normalized representatives times, respectively,

\[
Q^{-A},\quad Q^{-2A},\quad Q^{-2A-1/2},\quad Q^{1/2-A}.
\]

The auxiliary geometry is also literal: `Jg=[[3,1],[1,5]]`, `Tg=4+√2`, `Λg=4−√2`, `bg=√2−1`, `vr=(1,−bg)`, `vt=(bg,1)`, `ρg=log Λg/log Tg`, `κs=10⁻⁵`, `dr=2(1+h)ρg−hκs`. Evaluate `Y=vr r^dr+vt t mod Z²`; take `Yi=Jg^iY`, with `i=floor(log_Tg(Q^(−1−h)/S))`. On one lifted rectangle,

\[
Y_i-c_\gamma-k_{\rm copy}=\xi_gv_r+\eta_gv_t,
\quad c_i=T_g^iQ^{1+h},\quad v=(\eta_g+r_0)/c_i,
\quad L=2r_0/c_i\asymp S.
\]

The auxiliary radius `r0` is not a cylindrical radius. The evaluated derivatives are

\[
t_*=Q^{1+h}\partial_t^{\rm phys}=-\epsilon\partial_T+c_iN_i,
\quad D_r=\partial_R+M_i d_rR^{d_r-1}L_i,
\quad D_z=\epsilon\partial_Z,\quad D_\theta=R^{-1}\partial_\theta,
\]

where `Mi=Λg^i Q^(dr/2)`, `Ni=vt·∂Yi`, `Li=vr·∂Yi`. Thus `t_*v=1`, `Dr v=Dz v=0`. A slot has clock duration `Q^(1+h)L`, its central Gaussian width `Q^(1+h)√L`. Physical slow coordinates also change: the modal derivative is **not** the whole physical trajectory derivative. Slow-box time width is `QS^(−3)`; the slot/box ratio `εS⁴→0` explains local freezing, not validity across a fixed macroscopic restart gap. Auxiliary periodicity itself does not periodize physical space.

Let the chart base be `b er+V eθ+G ez`, `F=V/R`, `g=(R F_R,G_R)`. At the box representative write

\[
N=g_0/|g_0|,\quad K=(-N_z,N_\theta),\quad
\lambda_0^2=-2F_0N_\theta(2F_0N_\theta+|g_0|)>0,
\quad c_0=\lambda_0/(2F_0N_\theta)<0.
\]

These are profile-derived, not free unstable coefficients. The strict stress cone fixes one positive slope parameter `u=u_*`. For the chosen positive pulse,

\[
k=\lceil\epsilon^{-1/2}\rceil,\quad
B_s^2=\frac{\lambda_0}{\epsilon k^2(1+u^2)^{3/2}},\quad
s(v)=u/2+uv/L.
\]

Before rounding, `(p̃/R0,pz)=Bs(K−u g0/(L|g0|²))`; `kp` is a nearest **nonzero** integer to `kp̃`, with the fixed tie rule, and `pz` is unchanged. Put `x0=Bs u/2`. The phase, with no additional chosen offset, is

\[
\Phi=p\theta+p_zZ/\epsilon+x_0R-v(pF+p_zG),
\quad n=\nabla_*\Phi=
(x_0-v(pF_R+p_zG_R),p/R,p_z-\epsilon v(pF_Z+p_zG_Z)).
\]

The physical carrier covector is `k Q^(−1/2)n` in the cylindrical orthonormal frame. On the valid slot `n=Bs(s,K)+O(S⁻¹)`, so carrier wavelength is comparable to `Q^(1/2)/k`. In particular `1≤εk²≤4`: diffusion cannot be discarded.

### Polarization and the actual seed source

Write the real homogeneous amplitude as `a_h(v)=B(v)z(v)`, where the paper frame is

\[
B=[e_r-s_aK_a,\ N_a]
\begin{pmatrix}1&1\\c_0\sqrt{1+s^2}&-c_0\sqrt{1+s^2}\end{pmatrix},
\quad K_a=n_{\tan}/|n_{\tan}|,\quad
N_a=((K_a)_z,-(K_a)_\theta),\quad s_a=n_r/|n_{\tan}|.
\]

The prescribed initial value is **exactly** `z(0)=(P(0),0)`; it is not zero. Here

\[
P(v)=\exp\int_{L/2}^{v}(\lambda-d_{\rm ref})\,dw,
\quad \lambda=\lambda_0/\sqrt{1+s^2},
\quad d_{\rm ref}=\lambda_0(1+s^2)/(1+u^2)^{3/2}.
\]

The actual modal system, paper (7.17), is

\[
z'=[\operatorname{diag}(\lambda,-\lambda)+E-dI]z,
\quad d=\epsilon k^2|n|^2,
\quad |E_{ij}|\le C_E/S,\quad |d-d_{\rm ref}|\le C_d/S.
\tag{1}
\]

In ambient coordinates the pressure-constrained equation is

\[
a_h'+\mathcal K a_h+d a_h+ikn\pi_h=0,\quad n\cdot a_h=0,
\qquad \mathcal K a=(-2Fa_\theta,(2F+g_\theta)a_r,g_za_r).
\]

The homogeneous pressure is `πh=i(n·𝒦ah−n′·ah)/(k|n|²)`. The energy identity is

\[
\tfrac12(|a_h|^2)'=-g\cdot[a_{h,r}a_{h,\tan}]-d|a_h|^2.
\]

The growing direction has negative flux along `N` and extracts shear energy. It is not autonomous creation of a perturbation.

The cutoff is `ψ(v)=profile(v/L)`, the literal smooth `ContDiffBump` centered at `1/2`, plateau radius `1/5`, outer radius `1/3` in [GaussianTailFlat][GT]:27–110. Thus the primary field is zero near entry despite the nonzero **uncut** seed. At fixed slow/transverse coordinates set

\[
b_+=\chi_g(\xi_g)\psi(v)a_h(v)\cos(k\Phi),
\quad A_+=\sqrt\epsilon\,a_+\eta_\beta\chi_g(\xi_g).
\]

The **principal** forcing needed to activate this wave is

\[
F_{\rm seed,*}=A_+\psi'(v)a_h(v)\cos(k\Phi).
\tag{2}
\]

Its physical residual factor is `Q^(−2A−1/2)`. The entry part lies in `[L/6,3L/10]`, the exit part in `[7L/10,5L/6]`. It is tangent; pressure is multiplied by the same cutoff. In the paper convention `L_m t=−f_m`, the compensating prescribed source would have the **opposite** sign. For the homogeneous pulse, the actual cutoff residual is the positive expression (2). Real harmonic coefficients are half the cosine coefficient at `m=±1`, with conjugate imaginary pressures. Formula (2) is **not the full external force**: slow-mask derivatives, curl repairs, phase defects, interactions and final localization remain.

### What this pulse must supply

Let `T=T0,*=(Q/q)^(A+1/2) T0`, not the full summed background stress. Double averages are taken in angle and independent auxiliary variables **before physical evaluation**. Put `H=[C(b+) | C(b−)]`, `y=H^(−1)T`, `a±=√y±`. The companion pulse has disjoint auxiliary support, so it supplies the second column without cross-products.

Paper (7.27)–(7.29) gives, with `Ac=−c0√(1+u²)>0`,

\[
H_\sigma=h_\sigma(-A_cN-\sigma uK+e_\sigma),
\quad h_\sigma\asymp L^{-1/2},\quad |e_\sigma|\lesssim S^{-1/2}.
\]

Ignoring only these quantified column errors, the positive pulse's required share is

\[
h_+y_+=\tfrac12(-T_N/A_c-T_K/u).
\]

The strict margin `|TK|/u≤(1−ηc)(−TN/Ac)` yields for the actual columns

\[
c\sqrt L|T|\le y_+\le C\sqrt L|T|.
\tag{3}
\]

The scalar coefficient is therefore of order `L^(1/4)√|T|`, not order one. The uncut physical amplitude scale at our fixed point is

\[
\mathcal A=Q^{-A}|A_+|
\asymp Q^{-1/2-h/2}L^{1/4}\sqrt{|T|}\,|\eta_\beta\chi_g|.
\tag{4}
\]

This is the scale of one pulse; only the **pair**, followed by the squared partition, supplies `q^(−1−h)T0`. Zero angular velocity mean does not imply zero quadratic transport. The native Lean identity retains a `partitionFactor`; do not set it to one outside a justified coverage domain.

## 3. Discriminating calculation: cheap intended seed, expensive wrong polarization

All estimates in this section concern **the actual finite-slot ODE (1)**. Define the two explicitly evaluable integrals on the growing half-slot:

\[
\begin{split}
\Lambda&=\int_0^{L/2}\lambda\,dv
=\frac{\lambda_0L}{u}[\operatorname{arsinh}u-\operatorname{arsinh}(u/2)],\\
\mathcal D&=\int_0^{L/2}d_{\rm ref}\,dv
=\frac{\lambda_0L}{u(1+u^2)^{3/2}}
\left(\frac u2+\frac{7u^3}{24}\right),\\
G_*&=\Lambda-\mathcal D>0,\qquad P(0)=e^{-G_*}.
\end{split}
\tag{5}
\]

These retain the actual coefficient regime without assigning selected numbers. For explicit positive bounds, let

\[
\begin{split}
a_u&=\lambda_0u(u/2)\big[(1+9u^2/4)^{-3/2}+2(1+u^2)^{-3/2}\big],\\
b_u&=\lambda_0u(3u/2)\big[(1+u^2/4)^{-3/2}+2(1+u^2)^{-3/2}\big].
\end{split}
\]

Differentiating the actual reference rate `g(v)=λ−dref` gives `a_u/L≤−g′≤b_u/L` on `[0,L]`. Since `g(L/2)=0`,

\[
a_uL/8\le G_*\le b_uL/8,
\quad e^{-b_u(v-L/2)^2/(2L)}\le P(v)
\le e^{-a_u(v-L/2)^2/(2L)}.
\tag{6}
\]

Thus the covariance-normalized **uncut entry amplitude** has physical norm (not the oscillating velocity's pointwise norm)

\[
\boxed{\ \|a_{\rm seed,physical}\|\asymp\mathcal A e^{-G_*}
=Q^{-1/2-h/2}L^{1/4}\sqrt{|T|}|\eta_\beta\chi_g|e^{-G_*}.\ }
\tag{7}
\]

Here `a_seed,physical=Q^(−A)A_+ B(0)e_+ P(0)` is the physical uncut amplitude coefficient. It excludes the cosine, which has zeros, and the slot cutoff, whose entry trace is zero. In the stated uniform coefficient regime it is super-polynomially small as the band grows, despite the target stress's singular physical scale.

**Why the actual coefficient errors do not destroy this conclusion.** Let `V(v,0)` be the fundamental matrix of (1). Put `e=CE/S`, and choose the inspected band with `e≤λmin/8`, where `λmin` is a positive lower bound for `λ` on its slot. For the solution from `(1,0)`, `r=z−/z+` solves

`r′=E21+(−2λ+E22−E11)r−E12 r²`.

For `e>0`, at the upper barrier `r=2e/λmin≤1/4`, the derivative is at most `e−4e+2e(1/4)+e(1/4)²=−39e/16`; at the lower barrier it is at least `39e/16`. Thus the vector field points inward. If `e=0`, the diagonal equation preserves `r=0` directly. Consequently `|r|≤2e/λmin≤1/4`, and

`(log z+)′=λ−d+E11+E12r=λ−dref+O(1/S)`.

Since `L/S` is bounded, `|V(L/2,0)e+|=exp(G_*+O(1))`. The upper energy estimate gives `||V(L/2,0)||≤exp(G_*+O(1))`. This proves the midpoint amplification of the seed (7), as well as the seed scale's necessity up to constants for reaching a prescribed midpoint amplitude of size `𝒜` in this ODE: no smaller-norm seed reaches that size. It is not a lower bound for every field realizing an averaged stress by other timings or polarizations. Bounded frame maps convert modal and ambient norms.

There is also a **second, very different backward cost**. Liouville's determinant formula gives

\[
\det V(L/2,0)=\exp[-2\mathcal D+O(1)].
\]

If `σ1≥σ2>0` are its singular values, the preceding growth estimate and `σ1σ2=|det V|` give

\[
\boxed{\ \sigma_1=e^{G_*+O(1)},\qquad
\sigma_2=e^{-\Lambda-\mathcal D+O(1)},\qquad
\sigma_2/\sigma_1=e^{-2\Lambda+O(1)}.\ }
\tag{8}
\]

For output left singular vectors `l1,l2` and desired modal midpoint vector `q`, the **exact finite-dimensional** seed cost is

\[
|V^{-1}q|^2=|q\cdot l_1|^2/\sigma_1^2+|q\cdot l_2|^2/\sigma_2^2.
\tag{9}
\]

In particular, a budget `C𝒜 e^(−G_*)` permits only

\[
|q\cdot l_2|\lesssim\mathcal A e^{-2\Lambda},
\qquad
2\Lambda\ge\lambda_0L/\sqrt{1+u^2}.
\tag{10}
\]

An order-one relative component in the other output polarization instead requires `𝒜 exp(Λ+𝒟+O(1))`. This is an exponential discrimination, **not merely invertibility or an unsigned upper bound**. The actual pulse from `e+` lies in the admissible narrow output strip; the source deliberately chooses it.

**Do not overinterpret (10).** It is a condition for backward realization of an arbitrarily prescribed **full midpoint vector at the tiny budget**, not a claim that all stress-producing seeds require exponentially accurate initial alignment. Forward evolution of many small seeds with a nonzero growing projection automatically filters the decaying component. The strict stress cone tolerates small direction errors. Absolute cosine phase offsets leave an individual column's averaged covariance unchanged; exact phase locking is necessary for reproducing the selected field, not for that one averaged column. Thus (8) is a constraint on a proposed inverse construction, not an obstruction to all autonomous stress production.

The cutoff source itself obeys the concrete bound

\[
|F_{\rm seed,*}|\le C|A_+|L^{-1}e^{-a_uL/50}
\tag{11}
\]

on its two transition regions, by (6). Fixed derivatives cost powers of `Q⁻¹` and `S`; `exp(−cℓ²)` beats these. That is the paper's legitimate smooth tail mechanism, not a smallness theorem for the complete projected force.

## 4. Can all injections be moved to one fixed restart?

### What the actual finite-pulse result says

Within this one slot, initializing the **uncut** ODE at `v=0` with (7) gives the required growing pulse without a modal source. At any other fixed point of this same finite slot there is also a finite-dimensional initial vector producing its future portion. These statements neither give an exact divergence-free NS solution nor remove the localized cutoff residual. Equation (9) is necessary and sufficient only for the two-dimensional endpoint problem with its background and phase prescribed. An NS datum cannot prescribe each modal trajectory independently: the background evolves too, pressure couples space, curl repairs interact, and one periodic solenoidal trace must serve every band. Backward parabolic evolution on the full function space need not have the bounded inverse of a finite matrix.

For any fixed physical `t0<1`, `q(z,t0)≥1−t0`. Hence sufficiently small bands `Q<(1−t0)/2` have **no physical dyadic support at that time** (`q/Q≤2` is necessary). Their constructed localized primary fields have zero restart trace. Merely copying the source's finite-late-band traces at `t0` does not install the nonzero modal seeds for those bands. This is a support observation about the construction, **not proof that late force is necessary**: an unforced field could transport information from larger scales or generate different local oscillations.

No one fixed `t0` belongs to the valid frozen slot of every later band. The interval on which (1), its small frame error, and its coordinate comparison have been established cannot be extended to `v≈−(1−t0)Q^(−1−h)` by assertion.

### A quantified test of the naive fixed-carrier preload, not an NS theorem

There is a precise bad cost if “put every future seed in the initial datum” means **hold its tiny physical carrier fixed and let it wait diffusively**. This is explicitly a frozen plane-wave heat surrogate, not a numerical model of the selected field. Its wavevector size at a valid slot point is

`|ξℓ|²=k² Q⁻¹ |n|² ≍ Q^(−1−h)`.

For waiting time `Δ>0` at viscosity one, recovering the entry seed (7) requires a preload of size

\[
\mathcal A\exp[\Delta|\xi_\ell|^2-G_*].
\tag{12}
\]

Since `G_*=O(ℓ²)` but `|ξℓ|²≍2^((1+h)ℓ)`, a fixed positive waiting time overwhelms the favorable seed exponent. To conclude divergence of the preload along an infinite sequence, additionally require `𝒜ℓ>0` and `max(0,−log 𝒜ℓ)=o(Q^(−1−h))`, with uniform carrier and growth constants. Quantitatively interior target/mask lower bounds suffice. Merely nonzero target/mask values do not: values near flat edges can decay arbitrarily fast. No such evaluated selected-point sequence is extracted here; sequence-level divergence remains conditional. In a genuine periodic **fixed-Fourier-mode** version of this test, such coefficients cannot be Fourier coefficients of a smooth datum (indeed they do not tend to zero). Distinct localized annular carriers are not automatically such a Fourier sequence, so that last conclusion is not transplanted to the exact construction.

This rejects the cheap **unchanged high-frequency heat-storage argument**. It does not reject storage at a larger spatial scale, shearing to the final covector later, nonlinear transfer, or a different unforced trajectory. Those possibilities change the hypothesis behind (12). The original source gives no estimate for their earlier wavevector history or full linearized propagator. Keeping only the prescribed shear while discarding its evolving geometry and nonlinear/pressure errors would also be an unsupported extension.

A time displacement `δv` of the reference pulse changes its envelope at the nominal center by factors bounded as `exp(−cδv²/L)` and `exp(−Cδv²/L)`. Thus a fixed fraction of peak envelope requires `|δv|=O(√L)`, a physical clock tolerance of order `Q^(1+h)√L` in the frozen interpretation. Moving a pulse center is not the same as multiplying its carrier by a harmless constant phase: the former changes overlap with the target and the shear/damping balance. The source does not prove an autonomous timing law meeting these shrinking windows.

**Smoothness distinction:** the local entry seeds (7), taken as coefficients, decay faster than any fixed inverse scale and could pay fixed derivative losses. Therefore local seed size alone does **not** rule out smooth all-stage initial data. For each fixed derivative order, `Q^(−M)S^p exp(−cℓ²)` is summable, also after polynomial label-count losses with controlled overlap. Constants may depend on the derivative order and finite correction stage; no uniform-in-stage theorem follows. This is C-infinity flatness, not analyticity: no factorial derivative bound or analytic Fourier decay is supplied, and nonzero compact cutoffs are not real analytic. Positive-time analyticity of a hypothetical unforced solution would require a separate argument. Conversely, the seeds are specified at different physical times, spatial supports and frames; no common-time trace, compatible tails, or all-stage PDE is thereby constructed. Removing the exit cutoff also leaves a nonzero homogeneous tail; its behavior outside the supported slot is not covered by (1). A nonzero homogeneous finite ODE cannot vanish on an open entry/exit interval by uniqueness, but that does not prove that an NS solution needs external force there.

## 5. Can the known nonlinear products autonomously supply this seed?

### Actual mode bookkeeping, not just wavevector addition

At a frozen point the projected quadratic NS evolution source (minus transport, not the nonlinear residual) of two divergence-free plane waves with covectors `ξ,η` and polarizations `a,b` has the symbol

\[
-i\mathbb P_{\xi+\eta}\big[(a\cdot\eta)b+(b\cdot\xi)a\big].
\tag{13}
\]

The projection and contractions matter as much as `ξ+η`. For two harmonics of our **same label**, `ξ=mk n`, `η=m′k n`, and their leading polarizations are both tangent to `n`. Both contractions vanish, regardless of which tangent polarizations are used. In particular, the apparently resonant route `2kn+(−kn)=kn` has **zero leading fast-derivative symbol**, not an order-`k` seed. This is the actual cancellation behind Lemma 9.2, not a chosen failing triad unrelated to the source.

For the **exact localized curl fields**, derivatives of amplitudes and cylindrical frames remain. Their quadratic products need not vanish. Paper (7.39) and (9.2)–Lemma 9.2 show that the full amplitude's small longitudinal component cancels the apparent `ε^(−1/2)` derivative loss. Two same-label waves in `Wα,Wβ` produce nonzero harmonics in `W(α+β−κs)`, rather than the naive `W(α+β−1/2)`. These are bounds for actual product coefficients, not a lower bound on a projected growing response.

There are two independent selection facts:

* The real primary has only `m=±1`; its quadratic self-products have only `m=0,±2`, **not `m=1`**, including amplitude derivatives and cylindrical connections. Thus there is no quadratic self-injection of its own fundamental.
* The positive and negative primary pulses, and other distinct constructed labels with overlapping slow supports, have disjoint enlarged auxiliary supports. Their products and derivative products vanish even after physical evaluation. They cannot serve as the proposed overlapping parent pair in this construction.

The background is angularly independent. Its linear action preserves the angular carrier and supplies amplification **of a seed already present**, not inhomogeneous creation of that carrier from zero. Interactions with a mean preserve the wave harmonic and depend on that wave. Mean corrections may have enlarged auxiliary supports; pressure is nonlocal, so this is not an invariant independent-label decomposition of arbitrary NS solutions.

### Order test for the first same-label return channel

There is a bounded additional discrimination. At any **fixed finite correction stage**, use the paper coefficient classes and its modal inverse only:

1. A primary amplitude is in `W1/2`, with the logarithmic and edge factors retained in that class.
2. Its quadratic nonzero source is in `W(1−κs)` and initially has `m=±2`. The zero-initial-data modal inverse preserves this exponent, costing only powers of `S`. Precisely, `V₂(v,w)=exp(−3∫_w^v d(a)da)V₁(v,w)` by (7.18). This damping stays inside the Duhamel integral: it is not a uniform `exp(−cL)` gain for sources arbitrarily near `v`.
3. Apply the slot cutoff to the response potential and pressure, then take the full curl as in Lemma 7.7. The repaired second-harmonic amplitude remains in `W(1−κs)`, with curl correction in `W(3/2−2κs)`. Raw modal tangency alone would not justify exact solenoidality of the localized wave. The cutoff tails and uncompensated sources remain additive residuals, not zero force.
4. Pairing this complete response with the complete primary can return to `m=±1`, with source in `W(3/2−2κs)`; the further modal inverse preserves that exponent. Relative to the primary's **natural upper amplitude scale**, the available bound gains `ε^(1−2κs)` up to fixed-stage powers of `S`. An actual small ratio to the primary amplitude additionally requires quantitative interior lower bounds; it is not a ratio at cosine nodes or arbitrarily small masks.

For completeness, the exact localized return coefficient can be calculated without dropping curl repairs. Let `a=a₂`, `b=a₋₁` be complete amplitude coefficients, and define

`𝔇a=(D_r+R⁻¹)a_r+D_z a_z`, `Ja=(−a_θ,a_r,0)`,

`𝔗(a,b)=a_rD_r b+a_zD_z b+(a_θ/R)Jb`.

Exact solenoidality gives `2ik n·a=−𝔇a` and `−ik n·b=−𝔇b`. Hence the coefficient of `exp(ikΦ)` in symmetrized cylindrical transport is

\[
C_1=\mathfrak T(a,b)+\mathfrak T(b,a)
       +\tfrac12(\mathfrak D a)b+2(\mathfrak D b)a.
\tag{14}
\]

Indeed the fast terms are `−ik(n·a)b+2ik(n·b)a`, giving **plus** coefficients `1/2` and `2`. Each term in (14) lies in `W(3/2−2κs)` by the actual amplitude-derivative bounds. Its physical residual factor is `Q^(−2A−1/2)`; it enters an evolution source with the opposite sign, and pressure elimination remains. No nonzero projected growing component or lower response bound follows from (14). This uses paper (7.39), Lemma 9.2, and the literal `orderedKernel` with cylindrical connections, not a frozen projection substituted for the localized PDE.

Since `ε=2^(−hℓ)` and `1−2κs>0`, this factor tends to zero at fixed stage/order. This is a response estimate within the modal hierarchy, not a comparison of an instantaneous source with the exponentially smaller entry seed: the source class includes `P(v)`, and (7.19) cancels that weight during forward propagation, leaving only polynomial slot losses. The matched wavevector therefore does not supply a leading-order pulse by this perturbative return mechanism. More basically, this chain already uses the primary to create its `m=2` parent: it is feedback, not an independent origin for the first fundamental. The `m=0` quadratic flux is precisely the useful order-`ε` stress, but it too arises from an existing primary. No sign or nonzero growing projection of the returned source is proved. These class estimates cannot be extrapolated to infinitely many interacting stages with uniform constants or reinterpreted as full-PDE response estimates.

A hypothetical pair of **different, overlapping autonomous parent waves** could evade both the same-label cancellation and the source's support separation. It would have to supply the required covector, a nonzero projected polarization along the amplifying direction, sufficient integrated amplitude, and the correct slow/temporal overlap. Other integer combinations (for example existing harmonics 3 and −2) also evade the simple `±1` quadratic selection rule. They are not ruled out by one absent channel, and wavevector matching alone establishes none of the other requirements. No such independently supplied parent pair is identified in the inspected NS construction.

**Inference:** the source's known products explain stress transport and perturbative repairs, but do not exhibit an autonomous seed supplier. This is not a theorem that nonlinear NS cannot seed such a pulse.

## 6. Literal producer map and selection audit

All upstream links below are local files in the supplied `f9e8bc5…` export; hashes and the historical pin association are recorded in `INPUTS.json`. Old source comments cite earlier paper numbering; the mapping here uses formula bodies.

| Paper item | Literal producer/contract and inspected location | Evidence limit |
|---|---|---|
| Profile-derived phase and spectral cone, (7.1)–(7.11) | [PrimaryGeometryAssembly][PG]:244–362, `Prepared`, `family`, `construction`; 391–463, `exists_prepared`, `prepared` | `exists_prepared` really assembles base/representative inputs. A consumer of a classical choice gets its exported fields, not every intermediate threshold in that existence proof. |
| Same selected primary | [CorrectionInitialization][CI]:3890–4017, `ActualPrimary.Choice`, `choice_nonempty`, `choice`, `phases`, `covariance_eq_integral`, `rawVelocity`, `gaussian`, `cutVelocity` | `choice_nonempty` calls `PrimaryTargetBounds.exists_constructed_bounds`; `choice` is `Classical.choice`. The literal fields use **that** preparation, target, covariance and frame. |
| Nonzero growing seed, (7.12), Lemma 7.4 | [PrimaryPulseBounds][PP]:549–658, `positiveSeed`, `referenceP`, `fundamental`, `fundamental_eq_primary`; [PrimaryODE][PO]:402–405, `primarySeed`, `primary` | `fundamental` is `JointODE.reparamSolution` with seed `P(0)•(1,0)` and zero forcing. It is not an arbitrary solution supplied as a premise. |
| Actual versus reference coefficient bounds | [BasePhaseGeometry][BG]:842–965, `FamilyData.modal_errors`, `damping_error`, `coefficientControl`, `energy_bound` | The **absolute** damping error needed for (8) is a theorem of the literal family. `PhaseConstruction.damping_error` alone, [PP]:1610, exports only a one-sided bound and would not suffice for the determinant estimate. `FamilyData.construction_frame`, [BG]:1061–1065, identifies the exported frame with this same family frame by `rfl`. Instantiate `family` using the same selected `Prepared` fields; do not strengthen an arbitrary record by borrowing a hidden witness. |
| Actual pulse equation | [PP]:1965–2000, `normalizedPulse_hasDerivAt`; [ActualPrimaryDynamics][AD]:57–122, `rawVelocity_hasDerivAt`, `frame_viscosity` | Native carrier and slot hypotheses remain. `v/L` in `normalizedPulse` is not physical time. |
| Covariance belongs to that solution | [PP]:1828–1960, `canonicalPrimaryPath`, `canonicalPrimaryPulse`, `primaryCovariance_eq_canonicalPairMatrix`; [CI]:3945–3949, `covariance_eq_integral`; [PulseCovariance][PC]:229,292,570,747, mass/factorization/positive inverse | Explicit equalities bridge the continuously extended pulse/integral to the same ODE. Existence of some covariance-producing pulse would not identify it with this one. |
| Cutoff and primary localization | [GT]:27–128, `profileBump`, `slotCutoff`, derivative support; [PP]:2010 onward, `uncutPrimaryWave`, `primaryWave_eq_cutoff` | Exactly one slot cutoff; it leaves derivative residual, not zero force. Full curl and remainder supplied in paper Lemma 7.7. |
| Native leading stress | [ActualPrimaryCovariance][AC]:376–399, `physicalLeading`, `partitionFactor`, `viewSum_covariance_factor` | Double average equals factor times leading stress on native strip, not an arbitrary physical pointwise stress identity or adjoint pairing. |
| Nonlinear harmonics | [HarmonicWaveInteraction][HI]:192–233, `orderedKernel`, `orderedKernel_eq_fullCoefficient`; 336–360, `convolution_apply_finset`, `transport_convolution` | Body includes cylindrical rotation and amplitude derivatives, with harmonic `m−j`; not a bare wavevector match. Class refinements retain solenoidal hypotheses. |

Targeted original-refactor cross-checks: [original PrimaryPulseBounds][OPP]:547–585 has the same explicit seed/reparameterized fundamental formula; [original CorrectionInitialization][OCI]:2962 onward ties `ActualPrimary.profile` to `FinalSlowBase.actualProfile` and begins the selected geometry record. These are lineage checks, **not** a claim that the complete original/upstream fields or classical choices are definitionally identical across revisions. The original `26e896e…` repository was not modified or built.

The chapter-06 enlarged-chart numerical-array bridge remains qualified. Sections 3 and 5 use the paper's finite-slot estimates and exported native-family bounds, not those untransferred arrays. The Riccati/singular-value deduction is new human mathematics, not a located Lean theorem. Absolute effective numerical values of `u,λ0,CE,Cd` and a numbered active label have not been extracted from the existential suppliers; the valid output is symbolic, uniform in the stated coefficient regime.

## 7. Strongest inference, unclosed obligations, and disposition

**Obtained:** a stress-calibrated entry size (7), an actual finite-slot exponential inverse-polarization constraint (8)–(10), and source-specific exclusions of the immediate self/paired-label seed channels. The frozen-carrier storage test (12) shows precisely why one tempting fixed-time preload argument fails **under its storage hypothesis**. It is not evidence that the selected force is dynamically necessary.

**Not obtained:** an actual fixed-restart propagation estimate to all later seed windows, a source-supported independent nonlinear parent pair, a common smooth solenoidal all-stage datum, or any unforced PDE construction or breakdown evidence. For a successful alternative, exact selected-pulse matching could be relaxed, but replacement pulses would still need two-component stress, energy extraction, pressure/divergence, localization and tail compatibility, and a sustainable background. A proof must close the nonlinear equation with `f=0`, not assume a small error after deleting the force. Local classical existence at each finite horizon does not supply one comparator lifespan or uniform endpoint control; global regularity may instead be assumed for a contradiction.

B quantifies over every smooth periodic divergence-free datum and positive viscosity. To refute it requires **one fixed datum/restart evolution**, not a new `t0` per horizon. The original zero datum evolves identically zero when unforced. Mean-zero forcing is neither force-small nor a periodic gradient. Auxiliary homogeneous growth is not homogeneous NS evolution.

Preserved exclusions: [CENTRAL-OBSTACLE][CO], [force-response final][FR], [timing overview][TO], and both [PDE][PV] and [source/strategy][SV] adversarial verdicts. The excluded unrestricted stability/symmetrizer certificate stays excluded. `L_U U_t=F_t` and timing identities do not estimate the selected deletion response or prove positive unforced breakdown. No claim of late-force necessity follows from the residual convention. Software status is separated below and is not a mathematical premise.

**Recommendation — stop the all-stage preload/force-deletion campaign on these inputs.** A further human investigation would need one independently specified autonomous parent mechanism or a controlled earlier covector history before another response estimate is a justified task. The present calculation is a finite-pulse diagnostic, not a credible construction plan for B. No implementation or algebra-only successor is recommended.

**Final review disposition:** both independent reports accept this conditional finite-pulse diagnostic with qualifications; those qualifications are incorporated here and itemized in [REVIEW-DISPOSITIONS.md](REVIEW-DISPOSITIONS.md). Equations (5)–(10) retain their native-slot, modal-coordinate and same-selected-family hypotheses. Equation (12) has an explicit nondegenerate-sequence condition; §5 now includes cutoff/curl repair, the exact return coefficient and the time-dependent damping kernel. No active numerical witness or all-stage estimate has been extracted. A failure of any proposed channel excludes that channel only. No automatic successor is authorized.

### Separate short software note

The inherited [software handoff][SH] leaves both authenticComparator gates **infrastructure-blocked** by resource errors. Regression/axiom checks and the library do not certify this human mathematics or establish B progress. No repair or retry was undertaken; none of this status is a premise of the mathematical conclusion.

[P]: /home/velvet/upstream-strategy-f9e8bc5-9d96jtuy/papers/navier-stokes.txt
[PG]: /home/velvet/upstream-strategy-f9e8bc5-9d96jtuy/upstream/NavierStokes/PrimaryGeometryAssembly.lean
[CI]: /home/velvet/upstream-strategy-f9e8bc5-9d96jtuy/upstream/NavierStokes/CorrectionInitialization.lean
[PP]: /home/velvet/upstream-strategy-f9e8bc5-9d96jtuy/upstream/NavierStokes/PrimaryPulseBounds.lean
[PO]: /home/velvet/upstream-strategy-f9e8bc5-9d96jtuy/upstream/NavierStokes/PrimaryODE.lean
[BG]: /home/velvet/upstream-strategy-f9e8bc5-9d96jtuy/upstream/NavierStokes/BasePhaseGeometry.lean
[AD]: /home/velvet/upstream-strategy-f9e8bc5-9d96jtuy/upstream/NavierStokes/ActualPrimaryDynamics.lean
[PC]: /home/velvet/upstream-strategy-f9e8bc5-9d96jtuy/upstream/NavierStokes/PulseCovariance.lean
[AC]: /home/velvet/upstream-strategy-f9e8bc5-9d96jtuy/upstream/NavierStokes/ActualPrimaryCovariance.lean
[GT]: /home/velvet/upstream-strategy-f9e8bc5-9d96jtuy/upstream/NavierStokes/GaussianTailFlat.lean
[HI]: /home/velvet/upstream-strategy-f9e8bc5-9d96jtuy/upstream/NavierStokes/HarmonicWaveInteraction.lean
[OPP]: /home/velvet/Desktop/NavierStokesAndEuler/NavierStokes/PrimaryPulseBounds.lean
[OCI]: /home/velvet/Desktop/NavierStokesAndEuler/NavierStokes/CorrectionInitialization.lean
[CO]: /home/velvet/worktrees/unforced-restart-20260909T202951Z/docs/unforced-restart/strategy/CENTRAL-OBSTACLE.md
[FR]: /home/velvet/worktrees/unforced-restart-20260909T202951Z/docs/unforced-restart/strategy/force-response/FINAL-REPORT.md
[TO]: /home/velvet/worktrees/unforced-restart-20260909T202951Z/docs/unforced-restart/strategy/timing-response/OVERVIEW.md
[PV]: /home/velvet/worktrees/unforced-restart-20260909T202951Z/docs/unforced-restart/strategy/timing-response/pde-adversarial-verdict.md
[SV]: /home/velvet/worktrees/unforced-restart-20260909T202951Z/docs/unforced-restart/strategy/timing-response/source-and-strategy-adversarial-verdict.md
[SH]: /home/velvet/h3-pressure-pilot-z7lj1we_/broader-validation/final-narrow-integration-SiMI7HBH/HANDOFF.md
