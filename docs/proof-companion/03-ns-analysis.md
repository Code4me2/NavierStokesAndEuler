# 03 — Navier–Stokes: from coherent approximations to forced nonextension

**Author scope:** NS analysis only. **Source baseline:** `597692fa5d55e07d810b2d96ead1a67972585425`. Model reported by the harness: `gpt-6-astra`. This chapter follows [PLAN.md](PLAN.md). The preceding construction chapter must supply the *same* physical fields throughout the argument below.

**Evidence convention.** **Source-established** means that the named declaration and relevant hypotheses were inspected in the baseline source, not that its entire dependency closure was independently verified. **Conditional exposition** is an ordinary mathematical argument from displayed inputs. **Unexpanded lemma** marks a substantive source input whose analytic proof is not reconstructed here. **New deduction** is proved here but is not claimed to be a packaged Lean theorem. **New research** is a missing mathematical improvement, not a theorem of the repository. No build, kernel check, independent-challenge run, external-manuscript verification, or independent reviewer signoff was performed for this chapter.

The route is this: one sequence of corrected physical fields gives a diagonal velocity with a singular core; its residual has arbitrarily small terminal jets; actual extensions away from the core turn those limits into compatible force jets; localization and activation produce a compact, zero-data forced solution before time one. Periodization comes **after** compact force construction. Slab uniqueness then identifies any admissible competitor with this solution, contradicting continuity on a compact set through the terminal time. This is a forced nonextension argument, not a proof that the force is zero.

## Conventions and imported construction contract

Write `x=(x₀,x₁,x₂)∈R³`, with `x₂` the axial coordinate; `e₂=(0,0,1)`. Fields are written `u(t,x)` although comparator sources use `v x t`. Let
\[
 \mathcal R_\nu(u,p)=\partial_tu+(u\cdot\nabla)u-\nu\Delta u+\nabla p,
 \qquad \Delta=\sum_{i=0}^2\partial_{x_i}^2.
\]
Until NSA-009, viscosity is one and the singular time is one. The equation is `R₁(u,p)=f`, with `div u=0`, before time one. A total function's assigned value at time one is not a classical terminal solution.

`D^m` means the actual full spacetime Fréchet derivative, with its multilinear operator norm; `D^{≤M}` means the maximum of these norms for `0≤m≤M` at the stated point. `D_x` denotes spatial differentiation. Euclidean coordinate mixed derivatives and these tensor norms differ only by constants depending on the order and dimension: evaluation on unit coordinate vectors gives one direction, while multilinear expansion in a coordinate basis gives the other. Constants below absorb these finite-dimensional factors; no constant is claimed independent of derivative order. `||u||₂²=∫|u|² dx`; physical kinetic energy is half this number. Spatial integrals are over `R³`, except when a unit periodic cell is specified.

The construction interface is deliberately a quantified input, not “there exists a witness.” Fix once and for all admissible `0<h<1/2`, the small correction parameter `κ`, geometry, band floors and the profile certificate. Import:

1. Physical increments `A_j,B_j,P_j` from **one coherent run**. `A_j` are vector potentials, `B_j` direct angular velocities, and `P_j` pressures. In particular
   \[
   A_0=A_{\rm base,gauged}+A_{\rm init},\qquad
   P_0=P_{\rm base}+P_{\rm init},
   \]
   and `B₀` is the actual initialization's direct angular field. Stage zero is not a small positive correction.
2. Raw joint-derivative estimates, finite-prefix background estimates and finite-prefix residual estimates, with losses independent of prefix index. NSA-001–003 state their quantitative use.
3. Genuine local endpoint models, common shrinking outer support for the positive stages, and axis-zero *germs* of potential corrections, not merely zero potential values on the axis. NSA-004–005 state their use.

The source interface is [MixedCandidateAssembly.lean](../../NavierStokes/MixedCandidateAssembly.lean) — `NavierStokes.MixedCandidateAssembly.StageEstimates`; the same-field consumer is [GermCandidateAssembly.lean](../../NavierStokes/GermCandidateAssembly.lean) — `NavierStokes.GermCandidateAssembly.exists_candidate_witness_of_finite_stages`. The physical derivation of these inputs belongs to chapter 02. **OBL-NSA-001 remains open:** the interface is now linked to [NSC-003](02-ns-construction.md#nsc-003) (axis and gauge), [NSC-007](02-ns-construction.md#nsc-007) (literal increments), [NSC-008](02-ns-construction.md#nsc-008) (physical estimates), and [NSC-009](02-ns-construction.md#nsc-009) (one schedule). Attaching IDs does not independently verify actual instantiation, including stage zero; OBL-NSC-001–006 propagate into these applications.

<a id="nsa-001"></a>
### NSA-001 — The physical scale and one diagonal schedule

**Statement and status: conditional exposition, matching source-established schedule consumers.** Put `τ=1-t>0`, `z=x₂`. The physical scale `q=q(t,x)` is the unique positive root
\[
 \tau=q-z^2q^{2h}.                                      \tag{1}
\]
It is independent of radius and angle. It is smooth for `t<1` and positive there. It tends jointly to zero as `(t,x)→(1,0)` from the past; indeed the same zero limit holds at every terminal point with `x₂=0`. It is not Euclidean distance to `(1,0)`.

For orientation, writing `a=2h∈(0,1)` and `w=q^{1-a}`, equation (1) is `τ=w^{a/(1-a)}(w-z²)`. Its positive branch has `w>z²` and is strictly increasing from zero to infinity. The derivative of the original scalar map there is
\[
 1-a z^2q^{a-1}>1-a>0,
\]
so the implicit-function theorem applies. The zero-limit assertion can also be seen from `q=τ+z²q^a`: at least one of `τ≥q/2` and `z²q^a≥q/2` holds, hence
\[
 q\le\max\{2\tau,(2z^2)^{1/(1-a)}\}.
\]
For `z≠0`, the terminal positive-branch limit is `|z|^{2/(1-2h)}`, not zero.

Sources: [SimilarityCoordinates.lean](../../NavierStokes/SimilarityCoordinates.lean) — `NavierStokes.SimilarityCoordinates.coordinateQ_spec`, `NavierStokes.SimilarityCoordinates.positive_solution_unique`; [SimilarityProfile.lean](../../NavierStokes/SimilarityProfile.lean) — `NavierStokes.SimilarityProfile.q`; [PhysicalWaveSum.lean](../../NavierStokes/PhysicalWaveSum.lean) — `NavierStokes.PhysicalWaveSum.physicalQ`, `NavierStokes.PhysicalWaveSum.physicalQ_pos`, `NavierStokes.PhysicalWaveSum.physicalQ_smoothAt`; [AnnularEndpoint.lean](../../NavierStokes/AnnularEndpoint.lean) — `NavierStokes.AnnularEndpoint.physicalQ_tendsto_zero`.

Let `q_big>0` be the domain threshold where raw fields are smooth. For each of the three families `F=A,B,P`, assume on the actual positive-scale domain, with `q≤1`,
\[
 \|D^m F_j\|\le C^F_{j,m}(1+|\log q|)^{p^F_{j,m}}
                      q^{g_j-L_F(m)},\qquad j\ge1.       \tag{2}
\]
The constants and logarithmic exponents may depend on `j,m`; `L_F` may not depend on `j`. Assume `g₀≥0`, `g_j>0` for `j≥1`, monotonicity, and `g_j→∞`. The construction ledger uses `g_j=hj/10` before cutoff losses; fixed `h>0` is indispensable. The accuracy after `J` cycles is `σ_J=1/5+J/10`, whereas positive increment `j` is built from the input state after `j−1` cycles. Source: [ActualIterationLedger.lean](../../NavierStokes/ActualIterationLedger.lean) — `NavierStokes.ActualIterationLedger.gain`, `NavierStokes.ActualIterationLedger.sigma_formula`, `NavierStokes.ActualIterationLedger.inputSigma_succ`. Also assume the physical scale derivative bounds `||D^kq||≤Q_k q^{1-k}` on `0<q≤1`, as supplied by the physical cutoff theorem. These are joint, not axial-only, estimates.

Choose a smooth scalar cutoff `χ` equal to one for `|s|≤1/2` and zero for `|s|≥1`. A single positive integer schedule `a_j`, common to **all three** components, can be chosen with
\[
 a_{j+1}\ge2a_j,\qquad 1/a_j<q_{\rm big},
\]
and any specified lower bound on `a₀`, such that
\[
 \|D^m[\chi(a_jq)F_j]\|\le2^{-j}q^{\gamma_j-\ell_F(m)},
 \qquad j\ge1,\quad m\le j+2,\quad \gamma_j=g_j/2.        \tag{3}
\]
Here `ℓ_F(m)=finiteBound(L_F,m)+m`, or a common larger loss for the three families; `finiteBound` is a finite maximum including `1`. The extra `m` pays derivatives falling on the cutoff. The gain in (3) is **post-cutoff** gain, not the raw gain.

**Why one schedule suffices.** On the support of a derivative of `χ(aq)`, `aq≤1` and the chain rule, together with `D^kq=O(q^{1-k})`, gives `D^k[χ(aq)]=O(q^{-k})`, with constants independent of `a≥0`. Leibniz then gives, for each fixed `j,m`,
\[
 \|D^m[\chi(aq)F_j]\|
 \le K_{j,m}(1+|\log q|)^{\widehat p_{j,m}}
                q^{g_j-\ell_F(m)}.                     \tag{4}
\]
For `ε=g_j/2>0`, `q^ε(1+|log q|)^P→0` as `q↓0`: substitute `s=-log q`, obtaining an exponential times a power of `1+s`. Thus choose `a_j` so large that the remaining factor is at most `2^{-j}` whenever `0<q≤1/a_j`, simultaneously for the finite list `m≤j+2` and the three components. Where `q≥1/a_j`, the cut field and all its jets vanish, including the boundary by smoothness of `χ`. Increase `a_j` further to enforce doubling and the strict raw-domain gap. This recursive construction never changes the underlying raw fields.

Define
\[
 \mathbb A=\sum_{j\ge0}\chi(a_jq)A_j,\quad
 \mathbb B=\sum_{j\ge0}\chi(a_jq)B_j,\quad
 \mathbb P=\sum_{j\ge0}\chi(a_jq)P_j,\qquad
 U=\nabla\times\mathbb A+\mathbb B.                      \tag{5}
\]
At any point with `q>0`, all sufficiently large summands vanish on a neighborhood; consequently these are smooth presingular sums. Above the raw-domain threshold all summands vanish on one common neighborhood because `1/a₀<q_big`. Arbitrary totalizations of the raw fields outside their valid domain are never differentiated as analytic data.

**Sources for (2)–(5):** [CutStageEstimates.lean](../../NavierStokes/CutStageEstimates.lean) — `NavierStokes.CutStageEstimates.RawStageBounds`, `NavierStokes.CutStageEstimates.cut_product_bound`, `NavierStokes.CutStageEstimates.cut_product_bound_of_threshold`, `NavierStokes.CutStageEstimates.physicalQ_jet_bound`; [MixedDiagonalResidual.lean](../../NavierStokes/MixedDiagonalResidual.lean) — `NavierStokes.MixedDiagonalResidual.exists_physical_schedule_residual_zero`; [MixedCandidateAssembly.lean](../../NavierStokes/MixedCandidateAssembly.lean) — `NavierStokes.MixedCandidateAssembly.StageEstimates.exists_schedule`.

**Dependencies/obligations:** imported physical estimates; OBL-NSA-001. The scale derivative bounds and physical estimates are source inputs, not derived in full from the correction construction here.

<a id="nsa-002"></a>
### NSA-002 — The finite head must reach its plateau

**Statement: conditional exposition, source-established tail bridge.** For `J≥0` define the *uncut* prefixes
\[
 A^{[J]}=\sum_{j=0}^J A_j,\quad B^{[J]}=\sum_{j=0}^J B_j,
 \quad p_J=\sum_{j=0}^J P_j,\quad
 u_J=\nabla\times A^{[J]}+B^{[J]}.
\]
Under NSA-001, near `(1,0)` from the past,
\[
 \|D^m(\mathbb A-A^{[J]})\|
 \le2^{-J}q^{\gamma_{J+1}-\ell_A(m)},\quad m\le J+3,     \tag{6}
\]
and similarly for `B,P`. This is a fixed-prefix rate, **not** all-order flatness of one fixed tail.

To prove (6), first split exactly
\[
 \mathbb A-A^{[J]}
 =\sum_{j\le J}(\chi(a_jq)-1)A_j
   +\sum_{j>J}\chi(a_jq)A_j.                            \tag{7}
\]
The second sum alone is not the difference from the uncut physical approximation. Since the head is finite, choose `δ_J>0` with `a_j δ_J<1/2` for every `j≤J`. On the **open** region `0<q<δ_J`, every head cutoff is identically one locally. The first sum in (7) and all its derivatives vanish there. The terminal limit `q→0` supplies this region eventually, including for `j=0`.

For `j≥J+1`, the requirement `m≤J+3` implies `m≤j+2`. Monotonicity of `γ`, the direction of the power inequality for `0<q≤1`, and the geometric series give
\[
 \sum_{j>J}2^{-j}q^{\gamma_j-\ell_A(m)}
 \le q^{\gamma_{J+1}-\ell_A(m)}\sum_{j=J+1}^\infty2^{-j}
 =2^{-J}q^{\gamma_{J+1}-\ell_A(m)}.
\]
Local finiteness justifies differentiating at the point; no unjustified infinite derivative interchange is needed.

A curl costs one full derivative. Thus
\[
 \|D^m(U-u_J)\|\le C_J q^{\gamma_{J+1}-L_v(m)},\qquad
 L_v(m)=\max\{\ell_A(m+1),\ell_B(m)\},\quad m+1\le J+3. \tag{8}
\]
The pressure loss is `ℓ_P(m)`. For the next lemma we may weaken `γ_{J+1}` to `γ_J` and use the common loss
`L_tail(m)=max{L_v(m),ℓ_P(m)}`. This avoids a hidden index shift.

**Sources:** [DiagonalJetBounds.lean](../../NavierStokes/DiagonalJetBounds.lean) — `NavierStokes.DiagonalJetBounds.CutStageBounds`, `NavierStokes.DiagonalJetBounds.partialPotential_eventuallyEq_uncut`, `NavierStokes.DiagonalJetBounds.potential_tail_jet_bound`; [DiagonalResidual.lean](../../NavierStokes/DiagonalResidual.lean) — `NavierStokes.DiagonalResidual.jetRate_diagonal_tail`, `NavierStokes.DiagonalResidual.JetRate.spatialCurl`; [MixedDiagonalResidual.lean](../../NavierStokes/MixedDiagonalResidual.lean) — `NavierStokes.MixedDiagonalResidual.velocity_tail_jetRate`, `NavierStokes.MixedDiagonalResidual.velocityLoss`.

**Dependencies:** NSA-001. **Obligations:** OBL-NSA-001 and OBL-NSA-006 (independent calculation review). The finite-head algebra is expanded here; the actual physical-prefix identification still requires the construction handoff.

<a id="nsa-003"></a>
### NSA-003 — Fully quantified residual flatness

**Statement: conditional exposition of a source-established theorem.** Suppose the fields in NSA-001–002 are smooth on one open presingular domain approaching `(1,0)`. In addition, for every `J,k`, on some past neighborhood of `(1,0)`, assume
\[
 \|D^k u_J\|\le C_{J,k}q^{-L_{\rm bg}(k)},\qquad
 \|D^k\mathcal R_1(u_J,p_J)\|
       \le C'_{J,k}q^{\gamma_J-L_{\rm res}(k)},            \tag{9}
\]
with losses `L_bg,L_res` independent of `J`. The raw finite-residual bound may have the stronger exponent `g_J-L_res(k)`; `g_J≥γ_J` allows (9). Then
\[
 \forall m\in\mathbb N\ \forall N\ge0\quad
 \exists J,C,\mathcal U:\quad
 \|D^m\mathcal R_1(U,\mathbb P)(t,x)\|\le Cq(t,x)^N
 \quad ((t,x)\in\mathcal U,\ t<1).                     \tag{10}
\]
The neighborhood is small enough to lie in the common domain and to have `0<q≤1`. Constants may depend on fixed construction parameters, `m,N,J` and the schedule, but not on `(t,x)` there. Neither one stage nor one neighborhood is asserted for all orders.

**Worked calculation.** Fix `m,N`. Let
\[
 b=\max\bigl(0,\max_{k\le m+1}L_{\rm bg}(k)\bigr),\qquad
 \ell=\max\bigl(0,\max_{k\le m+2}L_{\rm tail}(k)\bigr).
\]
Because `γ_J→∞`, choose the **same** `J≥m+2` with
\[
 \gamma_J\ge\max\{N+b+\ell,\ N+L_{\rm res}(m)\}.       \tag{11}
\]
No monotonicity of the stage constants is needed. Intersect the finitely many neighborhoods used by (8)–(9), the finite-head plateau, and `q≤1`. Set `w=U-u_J`, `r=𝔓-p_J`; by weakening powers and enlarging constants,
\[
 \|D^{\le m+1}u_J\|\le A q^{-b},\quad
 \|D^{\le m+2}w\|\le Wq^{N+b},\quad
 \|D^{\le m+1}r\|\le Pq^{N+b}.                         \tag{12}
\]
The exact residual difference is
\[
\begin{aligned}
 \mathcal R_1(u_J+w,p_J+r)-\mathcal R_1(u_J,p_J)
 ={}&\partial_tw-\Delta w+\nabla r\\
 &+(u_J\cdot\nabla)w+(w\cdot\nabla)u_J
   +(w\cdot\nabla)w.                                  \tag{13}
\end{aligned}
\]
There is no background-pressure factor in the nonlinear terms. A differentiated time term needs `m+1` velocity derivatives, a Laplacian needs `m+2`, and a pressure gradient needs `m+1` pressure derivatives. Therefore their norms are bounded by
`(c_tW+c_ΔW+c_pP)q^{N+b}≤(c_tW+c_ΔW+c_pP)q^N`.

For example, a coordinate multi-index `α` of joint order `m` gives
\[
 D^\alpha[(u_J\cdot\nabla)w]
 =\sum_{\beta\le\alpha}\binom\alpha\beta
          (D^\beta u_J\cdot\nabla)D^{\alpha-\beta}w.
\]
Each product is at most `AW q^{-b}q^{N+b}=AWq^N`. The sum of binomial coefficients is `2^m`; coordinate contractions only add a fixed dimension factor. The other cross term is identical in derivative count. The quadratic term is bounded by
\[
 c_mW^2q^{2N+2b}\le c_mW^2q^N,
\]
because `N,b≥0`. Thus (13) has `m`th derivative norm at most
\[
 [c_tW+c_\Delta W+c_pP+c_m(2AW+W^2)]q^N.                \tag{14}
\]
The second inequality in (11) makes the residual of the *same* prefix `O(q^N)`. Adding gives (10). Choosing a tail stage first and a different residual stage afterwards would not prove this assertion.

For each fixed `m`, take `N=1`; `q→0` implies `D^m R₁(U,𝔓)→0` jointly at `(1,0)` from the past. This is the terminal zero-jet conclusion. It is not the claim `R₁(U,𝔓)=0` at each presingular point: the neighborhoods in (10) shrink as `N` increases and the constants change.

**Sources:** [DiagonalResidual.lean](../../NavierStokes/DiagonalResidual.lean) — `NavierStokes.DiagonalResidual.JetRate`, `NavierStokes.DiagonalResidual.FiniteJetRate`, `NavierStokes.DiagonalResidual.residualDifference_jetRate`, `NavierStokes.DiagonalResidual.residual_jetRate_of_stages`; [MixedDiagonalResidual.lean](../../NavierStokes/MixedDiagonalResidual.lean) — `NavierStokes.MixedDiagonalResidual.residual_jetRate`, `NavierStokes.MixedDiagonalResidual.physical_vanishingJointJets`.

**Dependencies:** NSA-001–002 and (9). **Obligations:** OBL-NSA-001, OBL-NSA-006. The six-term calculation is supplied; derivation of (9) for the coherent physical run is not supplied by this calculation.

<a id="nsa-004"></a>
### NSA-004 — Genuine exterior models and compatible endpoint jets

**Statement: conditional exposition; anchored-model and extension inputs remain unexpanded.** A genuine one-sided extension of a field `F` at `(1,x*)` is a smooth field `E` on an open spacetime neighborhood `V` of that point such that `E=F` on `V∩{t<1}`. Equality only along a single time line would not suffice. Suppose the three sums `𝔄,𝔅,𝔓` have such extensions for every `x*≠0`. Their localized residual then has genuine away extensions, and NSA-003 supplies its zero jets at the origin once localization preserves the core.

Here is how the source obtains the component extensions; it is important not to replace this by a formal assignment of boundary tensors.

* **Off the central plane**, `x*₂≠0`, `q` tends to the positive root `Q*=|x*₂|^{2/(1-2h)}`. If `Q*<q_big`, assume each raw stage has a genuine endpoint model there. A locally positive scale and `a_j→∞` leave only finitely many cut summands in a common neighborhood; smooth extension of the scale and those finitely many models extends the sum. If `Q*≥q_big`, the strict gap `1/a₀<q_big` makes **every** cutoff vanish on one common past neighborhood, so the zero field extends the sum. Raw models outside `q<q_big` are not needed.
* **On the central plane away from zero**, `x*₂=0`, the radial distance `r*=sqrt(x*₀²+x*₁²)` is positive while `q→0`. Assume for every positive stage, wherever the raw field is used and nonzero,
  \[
  \sqrt{x_0^2+x_1^2}\le C_{\rm supp}\sqrt q,             \tag{15}
  \]
  with **one** `C_supp` for all stages. Choose a common neighborhood where the left side exceeds `r*/2` and the right side is smaller than `r*/2`. All positive stages vanish there simultaneously. The zeroth cutoff is on its plateau; the sum equals its actual zeroth stage as a germ. The initialization changes also satisfy shrinking support, leaving the anchored base model locally. Separate neighborhoods depending on `j` would not justify this argument.

Sources: [MixedDiagonalExtensions.lean](../../NavierStokes/MixedDiagonalExtensions.lean) — `NavierStokes.MixedDiagonalExtensions.SublevelShrinkingSupport`, `NavierStokes.MixedDiagonalExtensions.offplane_extension_local`, `NavierStokes.MixedDiagonalExtensions.sum_eventually_eq_initial`, `NavierStokes.MixedDiagonalExtensions.initial_add_extension`, `NavierStokes.MixedDiagonalExtensions.diagonal_awayExtensions_local`; [AnnularEndpoint.lean](../../NavierStokes/AnnularEndpoint.lean) — `NavierStokes.AnnularEndpoint.outerRadius`.

> **Unexpanded anchored-base lemma — OBL-NSA-002.** With a strictly increasing base scale sequence, `0<h<1/2`, smooth slow coefficients, an exterior coefficient certificate with radius `R≥0`, and equality of the leading exterior angular coefficient to the specified heat coefficient, the radially normalized base potential has a genuine one-sided extension at every nonzero point of the terminal slice. At central-plane points its extension is the anchored heat potential. The normalization is `K(t,s,z)−K(t,1,z)`, where `s=(x₀²+x₁²)/2`; the physical anchor is `s=1`.
>
> Source: [TailGaugePotential.lean](../../NavierStokes/TailGaugePotential.lean) — `NavierStokes.TailGaugePotential.radialNormalize`, `NavierStokes.TailGaugePotential.central_oneSidedExtension`, `NavierStokes.TailGaugePotential.awayExtensions`. For the actual profile certificate `H`, modulation witness `v`, entrance parameter `upper` and band floor `B`, the instantiated statements are `NavierStokes.TailGaugePotential.finalPotential_sameCurl` and `NavierStokes.TailGaugePotential.finalPotential_awayExtensions` in that same file. Their proof bodies pass through realized exterior coefficients and a radial heat primitive. This chapter does not reconstruct those coefficient and heat-primitive estimates, or the raw off-plane models. They remain construction/exterior analytic debt.

**From actual limits to compatibility.** Let `F` now denote the localized residual, smooth on `t<1`, with zero joint jets at `(1,0)` and actual away extensions. Define
\[
 L_m(0)=0,\qquad L_m(x)=D^mE_x(1,x)\quad(x\ne0).
\]
Different local choices give the same tensor because both are limits of the same past derivative. For every `x`,
\[
 D^mF(t,y)\longrightarrow L_m(x)
       \quad\text{as }t\uparrow1,\ y\to x.              \tag{16}
\]
This is stronger than pointwise convergence in `t`.

To see why `L_m` is continuous, choose a neighborhood where `D^mF(t,y)` is within `ε/2` of `L_m(x)` for all sufficiently late `t`. For fixed nearby `y`, pass `t↑1`; this bounds `|L_m(y)−L_m(x)|` by `ε/2`. With continuity of `L_m`, the triangle inequality then yields locally uniform convergence of `D^mF(t,·)` to `L_m`. On each compact spatial set, a finite cover gives one terminal time for the chosen order and tolerance.

Compatibility is not an extra freely prescribed axiom. On the open past the derivatives satisfy the actual recurrence `D(D^mF)=D^{m+1}F` (with the usual tensor identification). Passing in the fundamental theorem of calculus along short spatial segments, using the locally uniform limits, gives the spatial derivative recurrence of `L_m`. Along the normal direction, the same theorem and continuity of the next jet give the one-sided derivative at the boundary. Induction gives closed-past smoothness of the traced field `F(1,x)=L₀(x)` with all boundary derivatives `L_m(x)`.

**Source-established compatibility consumers:** [JointResidualLimits.lean](../../NavierStokes/JointResidualLimits.lean) — `NavierStokes.JointResidualLimits.OneSidedExtension`, `NavierStokes.JointResidualLimits.boundaryLimits_joint`, `NavierStokes.JointResidualLimits.continuous_of_joint_limits`, `NavierStokes.JointResidualLimits.locallyUniform_of_joint_limits`; [CandidateFromLimits.lean](../../NavierStokes/CandidateFromLimits.lean) — `NavierStokes.CandidateFromLimits.ResidualLimits`, `NavierStokes.CandidateFromLimits.tracedResidual_smooth`, `NavierStokes.CandidateFromLimits.tracedResidual_boundary_jets`.

> **Unexpanded extension operator — OBL-NSA-003.** Given presingular smooth velocity and pressure and locally uniform limits of every *actual full residual derivative*, the traced past residual has a smooth extension to all spacetime, agreeing with the activated residual for `0≤t<1`, with boundary jets `L_m`, and zero for `t≥2`. If both incoming fields vanish outside one closed spatial set at all times, so does this force extension. Source: [CandidateFromLimits.lean](../../NavierStokes/CandidateFromLimits.lean) — `NavierStokes.CandidateFromLimits.force`, `NavierStokes.CandidateFromLimits.force_smooth`, `NavierStokes.CandidateFromLimits.force_eq_activated_residual`, `NavierStokes.CandidateFromLimits.force_boundary_jets`, `NavierStokes.CandidateFromLimits.force_zero_from`, `NavierStokes.CandidateFromLimits.force_zero_outside`.
>
> The source uses a spatially local Taylor–Borel construction on the **actual normal jets**, after past activation and tracing. Schematically it sums `ψ(b_n s)s^n L_{n,normal}(x)/n!` for `s=t−1≥0`, choosing thresholds on compact spatial exhaustions, and glues to the past. Proving all-order convergence, compatibility and spatial locality of that operator is not replaced here by this schematic formula. An arbitrary formal series would not meet the hypotheses. Only the force is extended; the singular velocity is not.

**Dependencies:** NSA-001–003, genuine raw models and support inputs; localization in NSA-005. **Obligations:** OBL-NSA-001–003, OBL-NSA-006. This ordering is not circular: NSA-005's algebra is independent of the force extension, then this lemma applies to its localized residual.

<a id="nsa-005"></a>
### NSA-005 — Gauge-sensitive localization, activation, and compact-first periodization

**Statement: conditional exposition with source-established assembly.** For the localization and activation algebra, assume only NSA-001–003 for the same `𝔄,𝔅,𝔓`, together with the component exterior models described in NSA-004; do not assume its force-extension conclusion. The order is: component models → localization/activation algebra below → boundary compatibility in NSA-004 → force extension → candidate and periodization below. Let
\[
 \rho(x)=\chi(16(x_0^2+x_1^2))\chi(4x_2),\quad
 U_c=\nabla\times(\rho\mathbb A)+\rho\mathbb B,
 \quad P_c=\rho\mathbb P.                              \tag{17}
\]
Here `ρ=1` on `x₀²+x₁²<1/32, |x₂|<1/8`, and its closed support lies in
\[
 K=\{x:x_0^2+x_1^2\le1/16,\ |x_2|\le1/4\}
       \subset[-1/4,1/4]^3.
\]
It is smooth because it depends on squared radius, not a nonsmooth radial norm at the axis.

**Curl and gauge calculation.** The product rule is
\[
 U_c=\rho U+\nabla\rho\times\mathbb A.                 \tag{18}
\]
If `curl G=0`, replacing `𝔄` by `𝔄+G` changes `U_c` by `∇ρ×G`, despite preserving the uncut velocity. Thus the anchored potential in NSA-004 is essential for extending the localized residual on the cutoff annulus. It is not an arbitrary gauge choice after localization.

The curl part of (17) is divergence-free. The direct part requires geometry: away from the axis each direct angular field has the form `β(t,r,z)(−x₁,x₀,0)`, where `r=sqrt(x₀²+x₁²)` and `β=b(t,r,z)/r` for the source's tangential-magnitude coefficient `b`. The source's local angular data require a continuous, strictly positive inner support radius at each presingular slow point and vanishing of `b` below it. Thus the field is locally zero at the axis; no division by `r=0` is used analytically. Away from the axis its divergence is zero by cancellation of the two radial derivatives, and `∇ρ·𝔅=0` because `ρ` is axisymmetric. Multiplication by `χ(a_jq)` also preserves this structure, since `q` depends only on `t,z`. Consequently
\[
 \operatorname{div}(\rho\mathbb B)
    =\nabla\rho\cdot\mathbb B+\rho\operatorname{div}\mathbb B=0.
\]
Above the raw domain all summands are locally zero as in NSA-001; this argument does not assume raw scalar smoothness there.

Near the origin (17) agrees with the uncut fields on an open spacetime cylinder. Hence its residual has the same terminal zero jets as in NSA-003. Away from zero, apply the differential expression in (17) and then the residual operator to the three actual local models in NSA-004. This gives genuine extensions of the **localized residual**, even though localization generally changes its value.

Sources: [DirectAngularDiagonal.lean](../../NavierStokes/DirectAngularDiagonal.lean) — `NavierStokes.DirectAngularDiagonal.angularField`, `NavierStokes.DirectAngularDiagonal.AngularData`; [SpatialLocalization.lean](../../NavierStokes/SpatialLocalization.lean) — `NavierStokes.SpatialLocalization.spatialCutoff`, `NavierStokes.SpatialLocalization.supportCylinder`, `NavierStokes.SpatialLocalization.plateau`; [LocalAngularDiagonal.lean](../../NavierStokes/LocalAngularDiagonal.lean) — `NavierStokes.LocalAngularDiagonal.spatialCut_angularSum_divergence`; [MixedPeriodicAssembly.lean](../../NavierStokes/MixedPeriodicAssembly.lean) — `NavierStokes.MixedPeriodicAssembly.cutVelocity_divergence_free`, `NavierStokes.MixedPeriodicAssembly.cutResidualExtension`, `NavierStokes.MixedPeriodicAssembly.cutResidual_awayExtensions`, `NavierStokes.MixedPeriodicAssembly.cutResidual_vanishingJointJets`.

**Activation calculation.** Let `θ(t)` be the source switch, zero for `|t|≤3/8` and one for `t≥3/4`. Put `u=θU_c`, `p=θP_c`. Then `u(0,x)=0`, divergence remains zero, and
\[
\begin{aligned}
 \partial_t(\theta U_c)&=\theta\partial_tU_c+\theta'U_c,\\
 ((\theta U_c)\cdot\nabla)(\theta U_c)&=\theta^2(U_c\cdot\nabla)U_c,\\
 \mathcal R_1(\theta U_c,\theta P_c)
 &=\theta\mathcal R_1(U_c,P_c)+\theta'U_c
        +(\theta^2-\theta)(U_c\cdot\nabla)U_c.          \tag{19}
\end{aligned}
\]
This displayed identity is an ordinary product-rule derivation, not an assertion that activation produces no force. Near time one `θ=1` on a neighborhood, so all residual endpoint jets are unchanged. NSA-004 now constructs a global smooth `f` equal to (19) before one, supported in `K` and zero for `t≥2`. Every fixed derivative is bounded on `[0,2]×K`; multiplying by any spatial and temporal polynomial weight preserves a finite bound. This explains rapid decay on the future half-space. There is no analogous compact spatial support for its periodic lift.

Sources: [TimeLocalization.lean](../../NavierStokes/TimeLocalization.lean) — `NavierStokes.TimeLocalization.activatedVelocity_zero_early`, `NavierStokes.TimeLocalization.activatedVelocity_zero_initial`, `NavierStokes.TimeLocalization.activatedVelocity_eq_late`; [MixedPeriodicAssembly.lean](../../NavierStokes/MixedPeriodicAssembly.lean) — `NavierStokes.MixedPeriodicAssembly.exists_compact_candidate`; [R3CompactCandidate.lean](../../NavierStokes/R3CompactCandidate.lean) — `NavierStokes.R3CompactCandidate.Properties`, `NavierStokes.R3CompactCandidate.of_limits`. The precise external-prose decay/norm bridge remains chapter 01's responsibility.

**Same-field singularity.** The imported potential corrections must vanish as germs near each relevant axis point, so their curls vanish there as well. Zero values alone would not control curls. Direct angular fields vanish on the axis. The source then proves that the *unlocalized mixed diagonal* eventually equals the constructed base at the origin. After (17) and activation, this yields, for all sufficiently late `t<1`,
\[
 u(t,0)=u_{\rm base}(t,0)
       =j_*(1-t)^{-(1/2+h)}e_2,\qquad j_*>0.           \tag{20}
\]
The exact base formula is an imported construction assertion: [BaseResidual.lean](../../NavierStokes/BaseResidual.lean) — `NavierStokes.BaseResidual.baseVelocity_at_origin` assumes smooth coefficients, a strictly increasing base scale sequence and vanishing positive-order axial coefficients at the origin; the construction must also supply positivity of the leading coefficient `j_*`. The transfer is an eventual identity, not one throughout `[0,1)`. It is stronger than an abstract unbounded-speed predicate and fixes the singular points at `x=0`.

Source transfer: [GermCandidateAssembly.lean](../../NavierStokes/GermCandidateAssembly.lean) — `NavierStokes.GermCandidateAssembly.origin_eventually_base`, `NavierStokes.GermCandidateAssembly.origin_blowup`; [MixedPeriodicAssembly.lean](../../NavierStokes/MixedPeriodicAssembly.lean) — `NavierStokes.MixedPeriodicAssembly.cutVelocity_origin`, `NavierStokes.MixedPeriodicAssembly.periodicVelocity_origin`. The theorem `origin_eventually_base` explicitly takes the actual profile certificate, modulation witness, initialization and stage axis-zero germs, local angular data and a scale sequence tending to infinity. OBL-NSA-001 includes matching these inputs with (2) and (9).

**Why nonlinear periodization works.** First construct this compact `(u,p,f)`. Then form lattice sums, for example
\[
 u_{\rm per}(t,x)=\sum_{k\in\mathbb Z^3}u(t,x-k),\qquad
 f_{\rm per}(t,x)=\sum_{k\in\mathbb Z^3}f(t,x-k),        \tag{21}
\]
with the analogous pressure, or the source's equivalent curl-of-periodized-potential formulation. The supports lie in separated translates of `[-1/4,1/4]^3`. Locally at most one translate can contribute; elsewhere all are zero locally. Therefore the joint derivatives and the residual locally equal those of one translated compact field. In particular the apparently dangerous cross terms
`(u(·−k)·∇)u(·−l)` with `k≠l` vanish. This is locality, **not nonlinear superposition**. The strict support gap also handles the boundaries of representative cells.

Both pressure and velocity are unit-periodic; periodic pressure is not replaced by periodic pressure gradient. The force remains smooth and time-supported in `[0,2]` on the future half-space, with terminal jets obtained from the compact jets at representatives. They vanish at lattice copies of the origin, not necessarily at every terminal spatial point. Sources: [MixedPeriodicAssembly.lean](../../NavierStokes/MixedPeriodicAssembly.lean) — `NavierStokes.MixedPeriodicAssembly.periodized_navier_stokes`, `NavierStokes.MixedPeriodicAssembly.periodize_jets`, `NavierStokes.MixedPeriodicAssembly.candidate_of_periodization`.

**Dependencies:** NSA-001–004 and the imported base/axis assertion. **Obligations:** OBL-NSA-001–003, OBL-NSA-006. The local periodization proof and product-rule identities are expanded; no separate schedule is selected for the periodic candidate.

<a id="nsa-006"></a>
### NSA-006 — Compact-candidate energy, including zeros of the norm

**New deduction, conditional on the candidate hypotheses; not a located packaged candidate-energy theorem.** Let `ν>0`, `T* >0`. Suppose `(u,p)` is jointly smooth on every closed slab `[0,T]×R³`, `T<T*`, solves `Rν(u,p)=f` at interior times, is divergence-free, and `u(0)=0`. Assume one compact set contains the velocity support for **all** `0≤t<T*`. Pressure need only be smooth on each slab; it need not decay. Suppose `f` is smooth through `T*` and has common compact spatial support there. Define
\[
 H(T)=\int_0^T\|f(s)\|_2\,ds.
\]
Then for every `T<T*`,
\[
 \|u(T)\|_2\le H(T),\qquad
 \frac12\|u(T)\|_2^2+\nu\int_0^T\|\nabla u\|_2^2\,ds
       \le\frac12H(T)^2.                              \tag{22}
\]
Here `||∇u||₂²=Σ_{i,k}∫|∂ᵢu_k|²`, the Hilbert–Schmidt derivative norm, not an unidentified tensor operator norm.

**Proof.** Work on one fixed `T<T*`. Compact support and smoothness justify time differentiation under the integral and integration by parts in one large fixed ball. The transport term is `∫u·∇(|u|²/2)=0`. The pressure term is `∫div(pu)−p div u=0` because `pu` is compactly supported. The diffusion term gives `−∫u·Δu=||∇u||₂²`. Integrating the resulting identity yields
\[
 \frac12\|u(T)\|_2^2+\nu\int_0^T\|\nabla u(s)\|_2^2ds
      =\int_0^T\langle f(s),u(s)\rangle ds.             \tag{23}
\]
Let `Y(t)=||u(t)||₂²`, `a(t)=||f(t)||₂`. Then `Y'/2≤a√Y`. Dividing by `√Y` at its zeros would be invalid. Instead set `y_ε=√(Y+ε²)`. For `ε>0`,
\[
 y_\varepsilon'=\frac{Y'}{2\sqrt{Y+\varepsilon^2}}
 \le a\frac{\sqrt Y}{\sqrt{Y+\varepsilon^2}}\le a.
\]
As `y_ε(0)=ε`, integration and `ε↓0` give `√Y(t)≤H(t)`. Substitute this back into (23):
\[
 \int_0^T\langle f,u\rangle ds
 \le\int_0^Ta(s)H(s)ds=\tfrac12H(T)^2,
\]
proving (22). Smoothness through `T*` and compact force support imply `H(T*)<∞`. Taking a supremum in the first estimate and monotone limits in the dissipation integral gives bounded presingular energy and finite total presingular dissipation, even if (20) holds.

For a nonzero initial datum the same regularization gives `||u(t)||₂≤||u(0)||₂+H(t)`; the zero-data assumption is what gives the displayed sharp form (22). For smooth periodic fields the same argument uses cancellation on opposite faces, including **periodic pressure**, and the cell `L²` norm.

**Source inputs:** [R3CompactCandidate.lean](../../NavierStokes/R3CompactCandidate.lean) — `NavierStokes.R3CompactCandidate.Properties`, `NavierStokes.R3CompactCandidate.of_limits`; force properties from NSA-004–005. This proof does **not** yield a classical terminal velocity, strong `L²` convergence at `T*`, or an energy identity across the singularity. Bounded energy alone does not imply any of them.

**Dependencies:** NSA-005 for candidate instantiation; otherwise the displayed hypotheses suffice. **Obligations:** inherited OBL-NSA-001–003, and OBL-NSA-006 for independent mathematical review of this new deduction.

<a id="nsa-007"></a>
### NSA-007 — Slab-local uniqueness and why whole-space pressure is not automatic

**Source-established comparison statement, with conditional derivations below.** Fix `0<T<1` and viscosity one. Let reference `(u,p)` and competitor `(v,π)` be jointly smooth on the closed slab `[0,T]×R³`, divergence-free at interior times, with equal residuals there and identical initial velocities. For whole-space uniqueness assume:

* one compact set `K_T` contains the reference velocity support for every time in the slab;
* the competitor belongs to `L²` at every time and `sup_{0≤t≤T}||v(t)||₂²<∞`.

No compact support, spatial derivative bound, or spatial decay is imposed on the competitor. Neither pressure is assumed to decay. Then `u=v` throughout the closed slab. For the periodic version instead assume unit periodicity of **both velocities and both pressures**; no separately imposed energy bound is needed on a compact cell.

Exact source statements: [R3/WholeSpaceUniqueness.lean](../../NavierStokes/R3/WholeSpaceUniqueness.lean) — `NavierStokesR3.WholeSpaceUniqueness.classical_uniqueness_on_Icc`; [PeriodicUniqueness.lean](../../NavierStokes/PeriodicUniqueness.lean) — `NavierStokes.PeriodicUniqueness.classical_uniqueness_on_Icc`. These signatures were inspected, including their pressure, support and interior-time equation hypotheses.

**The easy periodic energy calculation.** Set `w=u−v`, `r_p=p−π`. Equal forcing cancels and
\[
 \partial_tw-\Delta w+(v\cdot\nabla)w+(w\cdot\nabla)u+\nabla r_p=0.
\]
On a periodic cell, the transport and pressure integrals vanish. Therefore
\[
 \tfrac12\frac d{dt}\|w\|_2^2+\|\nabla w\|_2^2
   =-\int w\cdot(w\cdot\nabla)u
   \le\|D_xu\|_\infty\|w\|_2^2.                        \tag{24}
\]
The reference gradient is bounded on the fixed compact slab-cell. Zero initial difference and Gronwall yield equality. Pressure periodicity cancels boundary terms; allowing an affine spatial pressure would not be this theorem. Source: [PeriodicUniqueness.lean](../../NavierStokes/PeriodicUniqueness.lean) — `NavierStokes.PeriodicUniqueness.energy_balance`, `NavierStokes.PeriodicUniqueness.energy_rate_le`.

**Why copying (24) to `R³` is insufficient.** Finite `L²` velocity does not itself justify a global integral of `w·∇r_p`, or say that the pressure is the canonical Riesz pressure plus a harmless constant. Taking divergence gives a Poisson equation, but that leaves a harmonic ambiguity. The inspected whole-space theorem discharges this issue from the actual equation and slab energy, not by silently adding pressure decay.

> **Unexpanded pressure-recovery/flux lemma — OBL-NSA-004.** Assume `T>0`, both velocities and pressures smooth on `[0,T]×R³`, both velocities divergence-free and having equal residuals on `(0,T)×R³`, and both velocities uniformly finite-energy on `[0,T]`. For every compact smooth scalar test `ψ`, spatial index `k`, and interior time, the pairing of `∂ₖr_p` equals the distributional gradient pairing of the canonical pressure associated to
> `G_ij=u_i u_j−v_i v_j∈L¹`.
>
> More explicitly, if `P_can=Σᵢⱼ RᵢRⱼG_ij` with Fourier multiplier `RᵢRⱼ=−ξᵢξⱼ/|ξ|²`, the conclusion is `⟨∂ₖr_p,ψ⟩=−⟨P_can,∂ₖψ⟩`, interpreted through Riesz operators on tests, not an unproved `L¹` boundedness of Riesz transforms. This identifies the actual compact-cutoff pressure flux with its canonical pairing.
>
> Source: [R3/PressureRecovery.lean](../../NavierStokes/R3/PressureRecovery.lean) — `NavierStokesR3.PressureRecovery.Hypotheses`, `NavierStokesR3.PressureRecovery.averaged_value_zero`, `NavierStokesR3.PressureRecovery.gradient_recovery`; [R3/ActualPressureFlux.lean](../../NavierStokes/R3/ActualPressureFlux.lean) — `NavierStokesR3.ActualPressureFlux.pressure_flux_eq_canonical`.
>
> The inspected proof averages in time against a compact smooth test, obtains a harmonic functional with a genuine `H³`-test-norm bound, eliminates it by a harmonic Sobolev-dual vanishing theorem, then removes temporal averaging using continuity and temporal test uniqueness. The physical pressure is only tested compactly; no unproved action on all Schwartz tests is assumed. The harmonic-functional and Riesz/commutator estimates are not fully reconstructed here. This is unresolved analytic exposition/audit, not evidence of a source flaw.

**The remaining flux terms can be absorbed; they are not already `O(1/R)`.** Let `χ_R` be the source smooth spatial cutoff at scale `R≥1`, and use weight `ζ_R=χ_R^8`. Write
\[
 E_R=\int\zeta_R|w|^2,\quad
 A_R=\Bigl(\int\zeta_R|\nabla w|^2\Bigr)^{1/2},\quad
 B_R=\|\chi_R^4w\|_6.
\]
The whole-space source obtains constants `M,U,G₀` before choosing radius or time, bounding respectively `||w||₂`, `||u||₃`, and the nine `||G_ij||₁`. Uniform energy gives `M,G₀`; compact smooth reference support gives `U` and a uniform gradient bound `G`. With these bounds, its actual pressure flux estimate is
\[
 \left|\int r_p\,\nabla\zeta_R\cdot w\right|
 \le C_P\left[(B_R^{1/2}+1)(A_R/R+R^{-2})
                +R^{-7/4}B_R^{3/4}\right].             \tag{25}
\]
The constant `C_P` is uniform in `R` and interior time. This is the precise output whose harmonic-analysis proof remains boxed above. Source: [R3/PressureFlux.lean](../../NavierStokes/R3/PressureFlux.lean) — `NavierStokesR3.PressureFlux.exists_uniform_actual_pressure_flux_bound`, including its explicit uniform `L²`, reference `L³`, and tensor `L¹` hypotheses.

Once `R` is large enough to enclose the reference support in the cutoff plateau, `∇ζ_R·u=0`. Localized energy integration, the transport estimate and (25) give
\[
 \tfrac12 E_R'+A_R^2\le GE_R+C_0R^{-2}
 +C_1R^{-1}B_R^{3/2}
 +C_P[(B_R^{1/2}+1)(A_R/R+R^{-2})+R^{-7/4}B_R^{3/4}]. \tag{26}
\]
Weighted Sobolev gives `B_R≤S(A_R+C M/R)`. All these constants precede `R,t`. The exact source closure is [R3/WholeSpaceComparisonClosure.lean](../../NavierStokes/R3/WholeSpaceComparisonClosure.lean) — `NavierStokesR3.WholeSpaceComparisonClosure.eq_of_pressure_flux_bound`.

Here is the power absorption behind that closure. Absorb fixed constants into `Q≥1`, so `B_R≤Q(A_R+R^{-1})`. Expanding the powers with `(a+b)^α≤C_α(a^α+b^α)` bounds the flux part of (26) by a constant times a sum of
\[
 R^{-1}A_R^{3/2},\quad R^{-1}A_R,\quad
 R^{-2}A_R^{1/2},\quad R^{-7/4}A_R^{3/4},
\]
and pure radius powers at most `C/R` for `R≥1`. For each term `cR^{-β}A^α` with `0<α<2`, Young's inequality gives
\[
 cR^{-\beta}A^\alpha
 \le\varepsilon A^2+C_{\varepsilon,c,\alpha}R^{-2\beta/(2-\alpha)}.
\]
The four displayed pairs give radius exponents `4,2,8/3,14/5`, all greater than one. Choose the finitely many `ε` with total at most `1/2`. The full right-hand error is at most `A_R²/2+D/R`. Consequently
\[
 E_R'\le2GE_R+D'/R,\qquad E_R(0)=0.
\]
Gronwall yields `E_R(t)≤(D'T/R)e^{2GT}` uniformly on this fixed slab. Let `R→∞`; since `0≤ζ_R≤1` and `ζ_R→1` pointwise, timewise `w(t)∈L²` permits dominated convergence. Thus `||w(t)||₂²=0`; continuity in space upgrades almost-everywhere equality to equality everywhere. This explicitly explains why the remaining `L⁶` and dissipation quantities in (25) do not prevent closure.

Source arithmetic: [R3/ComparisonRateBound.lean](../../NavierStokes/R3/ComparisonRateBound.lean) — `NavierStokesR3.ComparisonRateBound.exists_uniform_flux_absorption`, `NavierStokesR3.ComparisonRateBound.exists_uniform_rate_bound`. The foregoing Young calculation is conditional on the localized Sobolev/flux bounds; it does not prove the boxed pressure estimate itself.

**Dependencies:** comparison is independent of the diagonal construction; NSA-005 supplies its reference when applied. **Obligations:** OBL-NSA-004 (pressure and localized analytic inputs), OBL-NSA-006, plus inherited construction obligations for candidate instantiation.

<a id="nsa-008"></a>
### NSA-008 — Compact-set nonextension uses only presingular slabs

**New deduction/repackaging of source-established comparison and nonagreement results.** Suppose the candidate of NSA-005 exists. There is no competitor smooth through time one with matching initial datum and residual on `0<t<1`, divergence-free there, and either:

* periodic velocity and periodic pressure; or
* in the whole space, for **each** `T<1`, timewise `L²` velocity and a finite uniform energy bound on `[0,T]`.

The bounds may depend on `T` and may diverge as `T↑1`. No competitor energy bound at time one is used in the final contradiction. This is a slab-local formulation, not the literal delivered theorem signature with its global-energy requirement.

**Proof.** For each fixed `T<1`, all comparison hypotheses in NSA-007 hold: candidate smoothness restricts to the closed slab, its support is contained in `K`, pressures are smooth, residuals coincide with the same force, and both data are zero. Hence equality holds for every `t<1`, choosing `T` with `t≤T<1` (time zero follows from the datum). A competitor continuous through one is bounded on the compact set `[0,1]×K`; equality and (20) contradict this already at `x=0`.

Even if only the abstract speed-unbounded predicate is retained, compactness is sufficient: outside `K` the reference is zero, so every positive large-speed witness lies in `K`. In the periodic case move each witness into one fixed compact fundamental cell using periodicity. Unbounded speed on noncompact space **without** either a fixed origin or such a compact localization would not contradict smoothness through time one; witnessing points could escape to infinity.

Source: [R3CompactCandidate.lean](../../NavierStokes/R3CompactCandidate.lean) — `NavierStokes.R3CompactCandidate.Properties.not_global_agreement`, whose literal statement uses a globally future-smooth competitor; its proof uses only continuity on `[0,1]×K`. The presingular identification is the theorem cited in NSA-007. Our local-through-one formulation follows by the displayed compact-set argument and is not attributed to the literal global signature.

**Dependencies:** NSA-005 and NSA-007; NSA-006 is a consistency result, not needed to add an energy hypothesis to the compact reference, since compact slab smoothness already gives that. **Obligations:** OBL-NSA-001–004, OBL-NSA-005 (class/adapter handoff), OBL-NSA-006. Nonexistence in the excluded source class and equivalence with an external prose class remain separate questions.

<a id="nsa-009"></a>
### NSA-009 — Viscosity normalization and what it does not prove

**New displayed calculation of a source-established normalization.** Given viscosity-one fields, for a fixed `ν>0` define
\[
 u_\nu(t,x)=\nu u(\nu t,x),\quad
 p_\nu(t,x)=\nu^2p(\nu t,x),\quad
 f_\nu(t,x)=\nu^2f(\nu t,x).                            \tag{27}
\]
Then
\[
 \partial_tu_\nu=\nu^2u_t(\nu t,x),\quad
 (u_\nu\cdot\nabla)u_\nu=\nu^2(u\cdot\nabla)u(\nu t,x),
 \quad\nu\Delta u_\nu=\nu^2\Delta u(\nu t,x),
\]
and `∇pν=ν²∇p(νt,x)`. Thus `Rν(uν,pν)=ν²R₁(u,p)(νt,x)=fν` and divergence remains zero. Initial velocity remains zero; spatial support and unit periods are unchanged. The singular time is `1/ν`, and force shutdown is at `2/ν`.

For fixed `ν`, every derivative `∂_t^kD_x^α fν` gains the finite factor `ν^{2+k}`. Smoothness and future rapid decay are preserved; constants may depend on `ν`. The energy relation is `||uν(t)||₂²=ν²||u(νt)||₂²`. Conversely a hypothetical viscosity-`ν` competitor pulls back by time factor `ν⁻¹`, velocity factor `ν⁻¹` and pressure factor `ν⁻²`. Smoothness, periods, and slab-local finite energy persist; whole-space comparator energy membership must be translated as in chapter 01.

Sources: [ComparatorBridge.lean](../../NavierStokes/ComparatorBridge.lean) — `NavierStokes.ComparatorBridge.rescale`, `NavierStokes.ComparatorBridge.rescaledForce`, `NavierStokes.ComparatorBridge.normalized_solution_core`, `NavierStokes.ComparatorBridge.normalized_solution`. The latter is the periodic add-on; the core theorem does not itself assert a whole-space energy adapter.

**Dependencies:** NSA-008 for exclusion. **Obligations:** inherited OBL-NSA-001–005, OBL-NSA-006. Sending `ν↓0` in (27) is not a fixed-viscosity small-force theorem, nor a proof of convergence to a singular Euler solution.

<a id="nsa-010"></a>
### NSA-010 — Flat force is not zero force; conditional terminal restart

**Logical distinction and new conditional deduction.** Even zero jets of every order at a point do not force a smooth function to vanish nearby. For example
\[
 b(t)=\begin{cases}\exp[-1/(1-t)^2],&t<1,\\0,&t\ge1\end{cases}
\]
is smooth and infinitely flat at one but positive for every `t<1`. Taking `b(t)g(x)` with a nonzero smooth compactly supported vector field gives the same distinction for forcing. In this construction the force's zero jets are at `(1,0)` (and its periodic copies), not asserted on the entire terminal slice. Neither (10) nor smooth extension removes the activation terms in (19) or localization errors.

The forced conclusion has the quantifier form `∃u₀,f: no global solution for (u₀,f)`. Unforced failure requires `∃u₀: no global solution for (u₀,0)`. The former does not imply the latter by logic. In particular zero **constructed initial datum** is not zero constructed forcing.

Here is a valid but additional route to an unforced result. Suppose one could prove, for some `0≤t₀<1`, either `f=0` on `[t₀,1)` or `f=∇φ` there for a scalar `φ` smooth in the required presingular pressure class. In the second case set `p̃=p−φ`, so `R₁(u,p̃)=0`. In the periodic case `φ` must be periodic (up to an admissible time-only gauge); an affine spatial potential cannot simply be subtracted while retaining the stated pressure class. Restart at `t₀` with datum `u(t₀)`. Smooth compact support supplies rapidly decreasing whole-space data; periodic smoothness supplies periodic data. Divergence remains zero. If an unforced global competitor in the required class existed for this restarted datum, translate time, apply NSA-007 on each restarted presingular slab (the same argument permits a shifted initial time), and contradict NSA-008 at time `1−t₀`.

This deduction additionally requires the precise shifted-data admissibility and competitor-class bridge; it is not supplied merely by (27). The delivered force's shutdown at time two occurs **after** the singularity and gives no such restart. Nor would pressure absorbability on the whole interval from the original zero datum be compatible with the nonzero compact candidate: under the smoothness assumptions of NSA-006, gradient forcing does no work against divergence-free compact `u`, and (23) would force `u=0` throughout the presingular evolution.

**Evidence:** conditional deduction from NSA-006–008; no cited Lean theorem asserts the terminal force-removal premise. **New research / OBL-NSA-007:** prove effective force vanishing or admissible pressure absorbability on a terminal interval while preserving the singularity. This is not required for a forced exclusion, but is required for this proposed connection to unforced A/B. Official statement/prose fidelity and prize certification are outside this chapter; no prize conclusion is asserted.

## Local source-declaration index

Every link is relative to this chapter; all declarations refer to the baseline at the top. This index records precise interfaces rather than pretending that each row is one complete human proof. The expanded citations in NSA-001–010 identify additional helper declarations.

| Human lemma | Precise source declarations | What is imported or checked |
|---|---|---|
| NSA-001 | [MixedCandidateAssembly.lean](../../NavierStokes/MixedCandidateAssembly.lean) — `NavierStokes.MixedCandidateAssembly.StageEstimates`, `NavierStokes.MixedCandidateAssembly.StageEstimates.exists_schedule` | Raw-field smoothness on sublevels, gain and fixed-loss quantifiers, same three-family schedule. |
| NSA-001 | [CutStageEstimates.lean](../../NavierStokes/CutStageEstimates.lean) — `NavierStokes.CutStageEstimates.RawStageBounds`, `NavierStokes.CutStageEstimates.cut_product_bound_of_threshold` | Positive stages only; finite derivative list; logarithmic absorption halves gain. |
| NSA-002 | [DiagonalJetBounds.lean](../../NavierStokes/DiagonalJetBounds.lean) — `NavierStokes.DiagonalJetBounds.CutStageBounds`, `NavierStokes.DiagonalJetBounds.partialPotential_eventuallyEq_uncut` | Stage-zero exemption and local finite-head equality, including derivatives. |
| NSA-002–003 | [MixedDiagonalResidual.lean](../../NavierStokes/MixedDiagonalResidual.lean) — `NavierStokes.MixedDiagonalResidual.velocity_tail_jetRate`, `NavierStokes.MixedDiagonalResidual.physical_vanishingJointJets` | Curl loss, direct component, same physical scale and joint endpoint filter. |
| NSA-003 | [DiagonalResidual.lean](../../NavierStokes/DiagonalResidual.lean) — `NavierStokes.DiagonalResidual.residualDifference_jetRate`, `NavierStokes.DiagonalResidual.residual_jetRate_of_stages` | Actual joint derivatives, finite losses, one sufficiently advanced stage. |
| NSA-004 | [MixedDiagonalExtensions.lean](../../NavierStokes/MixedDiagonalExtensions.lean) — `NavierStokes.MixedDiagonalExtensions.diagonal_awayExtensions_local` | Shared support constant, central zeroth models, off-plane sublevel models and strict cutoff gap. |
| NSA-004–005 | [TailGaugePotential.lean](../../NavierStokes/TailGaugePotential.lean) — `NavierStokes.TailGaugePotential.finalPotential_sameCurl`, `NavierStokes.TailGaugePotential.finalPotential_awayExtensions` | Same anchored actual base, with certificate/modulation section variables retained. |
| NSA-004 | [JointResidualLimits.lean](../../NavierStokes/JointResidualLimits.lean) — `NavierStokes.JointResidualLimits.boundaryLimits_joint`, `NavierStokes.JointResidualLimits.locallyUniform_of_joint_limits` | Actual extensions plus joint zero jets, not free boundary tensors. |
| NSA-004–005 | [CandidateFromLimits.lean](../../NavierStokes/CandidateFromLimits.lean) — `NavierStokes.CandidateFromLimits.tracedResidual_smooth`, `NavierStokes.CandidateFromLimits.force_boundary_jets`, `NavierStokes.CandidateFromLimits.force_zero_outside` | Closed-side compatibility and local force extension; velocity is not extended. |
| NSA-005 | [GermCandidateAssembly.lean](../../NavierStokes/GermCandidateAssembly.lean) — `NavierStokes.GermCandidateAssembly.origin_eventually_base` | Unlocalized origin transfer under axis-germ and local angular hypotheses. |
| NSA-005 | [MixedPeriodicAssembly.lean](../../NavierStokes/MixedPeriodicAssembly.lean) — `NavierStokes.MixedPeriodicAssembly.exists_compact_candidate`, `NavierStokes.MixedPeriodicAssembly.candidate_of_periodization` | Compact force first; periodic pressure and local residual agreement afterwards. |
| NSA-006, NSA-008 | [R3CompactCandidate.lean](../../NavierStokes/R3CompactCandidate.lean) — `NavierStokes.R3CompactCandidate.Properties`, `NavierStokes.R3CompactCandidate.Properties.not_global_agreement` | Candidate support/smoothness and compact-set contradiction; (22) is a new deduction. |
| NSA-007 | [PeriodicUniqueness.lean](../../NavierStokes/PeriodicUniqueness.lean) — `NavierStokes.PeriodicUniqueness.classical_uniqueness_on_Icc` | Smooth periodic velocities **and pressures**, common forcing/data. |
| NSA-007 | [R3/PressureRecovery.lean](../../NavierStokes/R3/PressureRecovery.lean) — `NavierStokesR3.PressureRecovery.Hypotheses`, `NavierStokesR3.PressureRecovery.gradient_recovery` | Actual pressure recovered from both slab energy bounds and the equation. |
| NSA-007 | [R3/PressureFlux.lean](../../NavierStokes/R3/PressureFlux.lean) — `NavierStokesR3.PressureFlux.exists_uniform_actual_pressure_flux_bound` | Uniform constants plus remaining localized `L⁶` and dissipation terms. |
| NSA-007 | [R3/ComparisonRateBound.lean](../../NavierStokes/R3/ComparisonRateBound.lean) — `NavierStokesR3.ComparisonRateBound.exists_uniform_flux_absorption` | All flux terms absorbed uniformly in cutoff radius. |
| NSA-007–008 | [R3/WholeSpaceUniqueness.lean](../../NavierStokes/R3/WholeSpaceUniqueness.lean) — `NavierStokesR3.WholeSpaceUniqueness.classical_uniqueness_on_Icc` | Compact reference, unrestricted smooth pressures, slab-local competitor energy. |
| NSA-009 | [ComparatorBridge.lean](../../NavierStokes/ComparatorBridge.lean) — `NavierStokes.ComparatorBridge.normalized_solution_core`, `NavierStokes.ComparatorBridge.normalized_solution` | Inverse viscosity normalization; periodic add-on separate from whole-space energy. |

## Local obligation and handoff ledger

All entries below are **open**. History for each: opened in this chapter after baseline source inspection; no independent reviewer or closure evidence yet. “Open” is not a demonstrated failure of a Lean theorem.

| ID / owner | Precise missing work and evidence needed | Affected claims |
|---|---|---|
| **OBL-NSA-001 — NS analysis + NS construction/integrator interface** | NSC-003,007–009 are now attached; still derive/verify (2), (9), uniform support (15), anchored stage zero and axis-zero germs for one fixed-parameter physical run and the schedule actually selected. Source leads: `StageEstimates`, `exists_candidate_witness_of_finite_stages`. Need physical identities and estimates, not independent existential choices. | Candidate instantiation of NSA-001–010; all unconditional construction claims. |
| **OBL-NSA-002 — NS analysis, with construction owner** | Expand the anchored heat-primitive/exterior-coefficient proof and raw off-plane one-sided models under the exact coefficient/certificate hypotheses stated at NSA-004. Confirm common support constants for actual initialization and positive stages. Source leads: `TailGaugePotential.awayExtensions`, `MixedDiagonalExtensions.diagonal_awayExtensions_local`. | NSA-004–005 and all candidate consequences. |
| **OBL-NSA-003 — NS analysis** | Expand and independently check the actual normal-jet Taylor–Borel extension: compact-exhaustion thresholds, all-order convergence, boundary compatibility, and preservation of spatial zero regions for the activated past residual. Source lead: `CandidateFromLimits.force` and its imported gluing/endpoint proofs. | Smooth admissible force in NSA-004–005, then NSA-006–009. |
| **OBL-NSA-004 — NS analysis / PDE reviewer** | Reconstruct the harmonic Sobolev-dual vanishing, Riesz test pairings and commutator estimate giving (25), together with localized Sobolev/transport bounds in (26), from the precise slab hypotheses. The Young absorption is worked here but still needs independent checking. Source leads: `PressureRecovery.averaged_value_zero`, `PressureFlux.exists_uniform_actual_pressure_flux_bound`, `WholeSpaceComparisonClosure.eq_of_pressure_flux_bound`. | Whole-space NSA-007–009; periodic argument does not depend on this pressure route. |
| **OBL-NSA-005 — scope owner + integrator, NS analysis handoff** | Verify the direction from each prose-admissible competitor to the compared source class, including endpoint smoothness, pressure periodicity, whole-space `L²`/energy conventions and inverse scaling; separately establish constructed data/force admissibility. Attach SCOPE IDs without conflating challenge agreement with external prose equivalence. | Interpretation of NSA-008–010 as delivered/external statements. |
| **OBL-NSA-006 — independent reviewers/integrator** | Run all five PLAN gates. Recompute cutoff powers, finite-head locality, (13), curl/gauge term, (19), energy regularization, pressure-flux absorption and (27); independently check declarations, links, IDs and cold-read pedagogy. Author inspection is not independent review; no new kernel/Comparator run is claimed. | All chapter review status. |
| **OBL-NSA-007 — future research, not required for forced theorem** | Prove a terminal force-free or admissibly pressure-absorbable interval while preserving singularity, then verify shifted datum and comparison class. No source theorem supplying the premise was located. | Only the proposed unforced restart in NSA-010; not forced exclusion. |

**Exported IDs:** NSA-001 (schedule), NSA-002 (finite-head/tail bridge), NSA-003 (residual flatness), NSA-004 (endpoint compatibility and explicit unexpanded inputs), NSA-005 (localized activated compact/periodic assembly and origin transfer), NSA-006 (energy deduction), NSA-007 (slab comparison), NSA-008 (compact nonextension), NSA-009 (viscosity scaling), NSA-010 (forcing/restart distinction).

**Imported IDs:** NSC-003, NSC-007–009, linked in the construction contract above. The [scope chapter](01-scope.md) gives the internal class translation; external competitor inclusion remains OBL-NSA-005, not a completed scope signoff. See the [integrated scope summary](README.md#scope) and [validation ledger](VALIDATION.md).

**Local read-only checks:** all 62 relative links resolved, all ten `nsa-*` anchors were unique, and 96 fully qualified citation spellings had declaration-name matches in local source. These lexical checks do not establish namespaces, hypotheses, elaboration or mathematical validity; those require the source/reviewer gates. HEAD remained at the baseline and the tracked diff was empty. Only this assigned chapter was written by this author.

**Review status:** author source inspection and displayed derivations only. Technical independent review, independent source/hypothesis review, independent calculation review, integrated links/IDs review and pedagogical cold reading have not passed. The remaining boxed analytic inputs prevent calling this a complete self-contained human proof.
