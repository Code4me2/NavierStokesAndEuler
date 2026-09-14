# RC-EU-FINITE-01 — finite inviscid correction, after viscous production

## Result and evidence ceiling

**The selected local boundary is reconstructed, conditional on the accepted viscous-family and foundational inputs listed below.** For the fixed coherent `A,B,q` of `EulerAllOrderDriftCorrection.finite_exists`, the actual family at viscosities `ν_n=1/(n+1)` is globally Cauchy in continuous cylinder L². A derivative-word argument gives whole-sequence convergence in `C([0,T],H^(q+1))`, retains precisely the permitted finite energies, and attaches the literal signed-pressure equation to that same limit. No spatial compact embedding or new spatial-tail hypothesis enters.

The decisive estimate is

\[
 \|u_n-u_m\|_{C_tL^2}\le C_*|\nu_n-\nu_m|,
 \qquad C_*={\sqrt{(4K_bM)^2T e^{aT}}\over c},
\]

with `a` derived in §4, not supplied as a stability premise. The equation passes first in L²; a continuous H^q right-hand side and an integral identity then give the H^q derivative.

This is a **human reconstruction, not a new Lean/kernel verification**. Existing global validation does not certify this argument. The contract, atlas and all three branchmap Markdown files were read; their descriptions were checked against actual local source bodies, not treated as mathematical premises. Source root is `/home/velvet/Desktop/NavierStokesAndEuler`, pin `5fdcfe346d399f68f19a820526b59b5326f28939`. `exact-check.py` / `exact-check.log` verify HEAD, live-versus-pinned bytes, blobs, range hashes and first anchors for C01–C36, plus pinned bytes of selected helpers. These checks establish provenance only. No builds, Lean probes, installations, repository/source/Git mutations, or other reconstruction targets were undertaken.

C-number citations below resolve to the inclusive body ranges in the contract/atlas. Other citations give literal files and declaration names. Inspection of a caller is not an audit of its imported closure.

## 1. Freeze the objects before viscosity varies

Fix `L>0`, `T>0`, coherent all-order `A : Data L T`, actual `B : Budget L hT A`, and **then** a fixed natural `q≥6`. Write

- `D₂=A.atOrder(q+2)`;
- `D₁=lowerData D₂=A.atOrder(q+1)`;
- `D₀=lowerData D₁=A.atOrder(q)`;
- `N=q−4`, hence `N+6=q+2`;
- `ρ=B.radius`, `C=B.growthCoefficient`, `Δ=B.delta`, `ρ₀=B.initialRadius`;
- `S=(B.spatial q).full`, `r=S.residual`;
- `K=A.metricBudget(B.metric,q+1)`, including its actual inverse-metric operator path;
- `M=metricAmplification(K.c)(Δ/2)/weight(min(ρ₀/2,1),N)`.

Here `M` is the solution path bound, **not** `S.M`, the fixed-base pressure-inverse bound. `GevreyMetricEstimate.lean:27–28` defines `metricAmplification(c)=1+sqrt(5461)/c`; 5461 is the number `Σ_(j=0)^6 4^j` of base words. Likewise inverse-metric coercivity is `c²` with `c=K.c>0`; the positive forward pressure-coefficient coercivity `A.coercivity` is a different constant.

The scalar guards are retained literally:

\[
 C\ge\mathrm{combinedConstant},\quad 0<\Delta\le1,\quad \rho_0>0,
\]
\[
 2C(\mathrm{drift}+\Delta)T\le\rho_0/2,
 \quad\rho_0 S.R_c\le1,
 \quad 2r e^{3CT}\le\Delta/2,
 \quad\rho(t)=\rho_0-2C(\mathrm{drift}+\Delta)t.
\]

`combinedConstant_pos`, used in C07's body, gives `C>0`. Nonnegative drift and `t∈[0,T]` give `ρ(t)≥ρ₀/2>0`; also `2r exp(3Ct)≤2r exp(3CT)≤Δ/2`. These facts are fixed before `n,m`. Nothing here chooses a new radius or frequency threshold depending on `q`.

### Actual initialized suppliers, without substituting data

C28 (`PacketInitializedCorrectionData.lean`) defines the normalized approximation as `k·initializedPacketField(Npacket,k⁻¹)`, with the actual time change `Mparent.T=Dparent.T`; its residual is `k` times the joined inverse coefficient applied to the **initialized residual**, with that same time change. `correctionDataOfFields` receives these two literal fields and `κ=k⁻¹`. `PacketCorrectionSourceData.correctionData` sets the direction literally to `Dparent.m₀`, with `Dparent.m₀_unit.le` as its bound; `correctionDataOfFields` passes the two fields' actual towers. No new favorable vector is chosen.

C27 (`initializedUniformBudget`) forms joined/primary/normal/mean budgets on the initialized common radius, uses `Scales.ofTimeProfile`, sets `Kc=Lparent.correctionCoefficients NB period`, and supplies the five existing cost guards to C26 (`initializedAllOrderBudget`). C26 fixes the packet truncation `truncation k`, `ρ₀`, `Δ`, `C` and `ρ` once; only its `spatial q` realizations and cutoff vary with correction order. Its inverse metric is `initializedMetricBudget ... 0`. `PacketInitializedSpatialBudget.lean:26–33,57–122` verifies the literal supplier: `sourceMetricBudgetOfFields` receives the same two normalized fields, and the spatial fields come from `Kc` and the initialized background/derivative/residual/drift estimates. Those analytic productions remain upstream debt.

C29 does not select new coefficient fields at each order: `atOrder s` copies κ, direction, coercivity and the common coefficient towers, takes approximation realization `s+1` and residual realization `s`. Thus D₂ has approximation H^(q+3), residual H^(q+2); D₁ has approximation H^(q+2), residual H^(q+1); D₀ has approximation H^(q+1), residual H^q. `FieldTower.value_eq` and derivative uniqueness prove `FieldTower.truncate`. C30 applies these truncation identities twice to obtain equality of the **whole lower Data**, not just its scalars. `Data.metricBudget` copies every inverse-metric field unchanged. In particular K, G, κ, direction, approximation and residual retain their same-object lineage under both lowerings.

### Accepted family, exactly the C06 output

C06 invokes C07 separately at the historical `ν_n=1/(n+1)` and chooses the solutions furnished there. Accept one resulting family

\[
 u_n\in C([0,T],H^{q+2}),\qquad 0<\nu_n\le1,
\]

with, for every `n` and closed-interval `t`:

1. `u_n(0)=0` and `value(u_n(t))` in the same lifted divergence-free space;
2. the literal zero-data `quadraticDuhamel` identity with `D₁.coefficients` and `ν_n`;
3. `E_(N,ρ(t),K(t))(u_n(t))≤2r exp(3Ct)` and `≤Δ/2`;
4. `‖u_n‖_(C_tH^(q+2))≤M`.

**Upstream debt:** C07's actual construction goes through `partial_correction_bootstrap`, `norm_le_of_energy_bound`, and `exists_global_correction_of_bound`. Its energy/bootstrap, local existence and continuation proofs are not reconstructed here. This is not concealing the selected target: these inputs say nothing about two different viscosities or convergence, and furnish no inviscid equation. C03's body even discards the exported defect convergence before producing the Cauchy limit; that defect is not nonlinear compactness.

## 2. Native domains, norms and accepted foundations

All spaces in this proof are on the full noncompact cylinder

\[
 X_L=\mathbb R^3\times(\mathbb R/L\mathbb Z),
 \qquad d\lambda_L=d x\,d\theta
\]

with the source's product Lebesgue/angle Haar measure (`EulerProof/LiftedTransport.lean:48–63`). Values are three-component vectors. There are **four** standard derivative directions: angle first, then three spatial directions. For fixed κ,m the lifted transport is

\[
 T(z,f)=\sum_{i=0}^3\ell_i(z)D_i f,
 \quad \ell_0(z)=m\cdot z,\quad\ell_{j+1}(z)=\kappa z_j.
\]

Its actual cylinder tangent is `(κz,m·z)`; each `‖ℓ_i‖≤1` by `|κ|≤1`, `‖m‖≤1` (`LiftedTransportComponents.lean:13–55`). Lifted gradients correspond to `κ∇_x+m∂θ`; the divergence-free space is the orthogonal complement of the closed lifted gradient space in cylinder L². This is not a physical R³ scalar-pressure formulation. `Δ_cyl=Σ_(i<4)D_i²` is artificial cylinder heat, not physical three-coordinate NS viscosity.

`H^s` here denotes the **native** `SobolevSpace L s`: a closed subspace of the finite array `(D_w f)_(|w|≤s)` in L², with genuine strong translation-derivative edges. Its inherited norm is

\[
 \|f\|_{H^s}=\max_{|w|\le s}\|D_w f\|_2,
\]

not a sum or a root-of-squares convention. `CylinderSobolevSpace.lean` constructs the closed graphs/subspace and proves derivative/value uniqueness. The space and its continuous paths on the compact time interval are complete. Value, word, derivative and restriction operators are bounded; word extraction and restriction are contractive. No equivalence to an external Sobolev class is asserted.

The following are imported **foundational contracts**, not desired comparison conclusions:

| Input and literal supplier | Hypotheses matched here; what is not reconstructed |
|---|---|
| `CylinderSobolevSpace.sobolevSubspace`, `word_hasDerivAt`, `value_injective`; `CylinderSobolevOperators` / `SobolevRestriction` | Closed strong-translation graphs in global cylinder L²; compatible finite derivative arrays, contractive coordinate/restriction maps. General closed-graph and completeness theory is accepted. |
| `CylinderSobolevEmbedding.value_ae_bound`, `SobolevL2Product.scalarProduct_norm`; `SobolevTransport.transportBilinear`; `CorrectionOperators.coordinateProduct` | On this cylinder, `H^s→L∞` for `s≥3` with `Cemb(L,s)=3·cylinderEmbeddingConstant(L)·card(SobolevWord s)`; products are literal a.e. products. For `s≥6`, the actual products/transport give bounded maps `H^(s+1)×H^(s+1)→H^s`. Their general embedding/product construction is accepted; the lower difference bounds are derived below. |
| `EulerProof/LiftedTransport.lean:1442–1463`, `translation_derivative_pairing` | If both indicated translation orbits have strong L² derivatives, `⟨D_i f,g⟩=−⟨f,D_i g⟩`. Follows by differentiating translation invariance of the pairing. Applies globally; no compact-support or tail premise. |
| `SobolevMetricTransport.metric_transport_bound` and its literal supplier `EulerRepresentativeMetricEvolution.metric_transport_inner_bound` | Symmetric smooth bounded K with first-derivative bound; advector z in H^s, `s≥3`, lifted divergence-free and a.e. bounded; energy field in H¹. Source extends the smooth representative identity by actual Sobolev mollification. The general weak-divergence integration by parts/density theorem is accepted, not a solution comparison estimate. |
| `SobolevCoefficientPressure.pressureL2Operator`, `pressureSobolevOperator`, `projectedSourceOperator`; `SpatialJet.solvePressure` / `solvePressure_norm_le` | Same fixed gradient space, bounded coercive forward coefficient G, actual coefficient jet at the required order. Lax–Milgram gives a bounded gradient-valued inverse and its Sobolev jet lift at each finite order. Full inverse regularity theory is upstream debt. `SobolevPressureTime.pressureSobolev_continuousAt` uses the pressure resolvent with multiplier continuity; no separate pressure continuity assumption is added. |
| `MildEquationBridge.viscous_mild_hasDerivAt`, via `truncate_heatConvolution` and `ordinary_mild_hasDerivAt` | Positive viscosity, actual continuous `H^(s+1)` mild path, continuous source into H^s, `s≥2`. Truncating the gained-derivative kernel gives the ordinary heat Duhamel formula; heat differentiation gives the L² PDE on `(0,T)`. The general heat kernel/differentiation theory is accepted. Here `s=q+1≥7`. |
| `IntegralPathLimit` / `InjectivePathDerivative` | Complete real Banach spaces, continuous closed-interval paths, bounded linear integration and interior FTC. The relevant integral estimates and upgrade are worked in §7. |

For the transport foundational input the local mechanism is still explicit: testing lifted divergence against the scalar metric energy gives

\[
 \langle Kd,T(z,d)\rangle
 =-\tfrac12\int\langle (b_z\cdot\nabla K)d,d\rangle\,d\lambda_L,
 \qquad b_z=(\kappa z,m\cdot z).
\]

Symmetry is what combines the two differentiated factors of d. The advector's lifted divergence is exactly the cylinder divergence of `b_z`. The cited theorem supplies this identity/bound at the Sobolev regularity just specified, rather than assuming a smooth compactly supported d. On the unbounded spatial factor, its density/weak-divergence foundation removes boundary terms; it is not an additional uniform tail condition on the family.

## 3. Construct the comparison budget from the supplied coefficients

At local order `s=q+1`, C08 constructs `stabilityBudgetLower D₂ ... S K` for D₁. It copies K's actual coefficient, L² continuity, time derivative and derivative identity, c, symmetry, coercivity, inverse identity, and bound/first/time fields. The L² operator bound follows from the coefficient multiplier bound and `K.bound_le`.

It does **not** copy a stability inequality. Let A₀=S.A0 and A₂=S.A2. For any supplied coefficient jet J and positive radius,

\[
 \mathrm{bound}(J)\le\mathrm{coefficientBlock}(J,6,0)
 \le\sum_{j=0}^N w_j(\rho)\mathrm{coefficientBlock}(J,6,j).
\]

The first inequality uses the nonnegative zeroth derivative term of the block (C08 first proves `coefficient_bound_le_block`); the second selects j=0, where `w_0=1`, from a nonnegative finite weighted sum. Therefore

\[
 \|D_1.\mathrm{linear}(t)\|_{\text{pointwise witness}}\le A_0,
 \qquad \sum_{i<3}\|D_1.\mathrm{quadratic}_i(t)\|_{\text{witness}}\le A_2.
\]

The equality of lower coefficient fields is essential here: the weighted input is at D₂'s order, while the bound is used for D₁. Put

\[
 Z_b=\|D_1.\mathrm{approximation}\|_{C_tH^{q+2}},
 \quad V=C_{emb}(L,q+1)(Z_b+M),
\]
\[
 L_{rem}=A_0+(4+2A_2)C_{emb}(L,q+1)(Z_b+M).
\]

These are nonnegative finite numbers depending on fixed data and fixed q, not on viscosity indices. The actual whole-path norm `Z_b`, not an invented q-uniform background bound, is what C12/C14 use.

## 4. Literal subtraction and the decisive cancellation/estimate

Take **any two members of the accepted family**, `u=u_n`, `v=u_m`, with `ν=ν_n`, `μ=ν_m`; let d=u−v. At each fixed time set Z=D₁.approximation. Let `A(t)` be the linear multiplier and `Q_t(a,b)=Σ_(i<3) C_i(t)(a_i b)` the algebraic quadratic term. The full bilinear map is `B_t=T+Q_t`. Before projection the raw source is

\[
 F_t(e)=r_t+A(t)e+B_t(Z,e)+B_t(e,Z)+B_t(e,e).
\]

Here `r_t` denotes the actual residual field, not its scalar bound r. Bilinearity gives

\[
 B_t(u,u)-B_t(v,v)=B_t(u,d)+B_t(d,v).
\]

Consequently (C11)

\[
 F_t(u)-F_t(v)=T(Z+u,d)+R_t(u,v),
\]
\[
 R_t(u,v)=T(d,Z+v)+A(t)d+Q_t(Z+u,d)+Q_t(d,Z+v).
\]

These are exactly the **four** remainder terms, with d in opposite slots in the last two. The same residual cancels; `Q_t` need not be symmetric. Restriction in the linear term is understood as the actual contractive truncation.

### Pressure sign and same inverse

Let `P_G` denote the **unsigned** coercive inverse: `P_G f` is in the lifted gradient space and satisfies `Π_grad G P_G f=Π_grad f`. Thus the projected-source operator is `Π_G=I−G P_G`. The actual signed pressure in `EulerCorrectionEquation.lean:27–31` is

\[
 p(e)=-P_G F_t(e),
 \qquad S_t(e)=-\Pi_G F_t(e)=-F_t(e)-G p(e).
\]

This sign distinction matters: the source is not `−F+G p` for this signed p. The mild bridge and C09 now give, in L² at interior times,

\[
 d_t+T(Z+u,d)+G(p(u)-p(v))
 =\nu\Delta_{cyl}d-R_t(u,v)+(\nu-\mu)\Delta_{cyl}v. \tag{4.1}
\]

C09's `differenceRhs_eq_sub` is precisely the identity `νΔu−μΔv=νΔd+(ν−μ)Δv` plus this bilinear subtraction. It is not a new approximate equation.

### Four local inequalities

Write `K_b=K.bound`, `K_x=K.first`, `K_t=K.time`, and `x=‖d‖₂` at the time under consideration.

**(i) Pressure vanishes exactly.** Both p-values use the same G and same inverse on the same gradient space. Their difference lies in that space. The difference d is divergence-free. Using symmetry of K and the supplied pointwise `KG=I`,

\[
 \langle Kd,G(p(u)-p(v))\rangle
 =\langle d,KG(p(u)-p(v))\rangle
 =\langle d,p(u)-p(v)\rangle=0.
\]

Bounded coefficient multipliers justify these equalities on L² (`EulerProof/LiftedTransport.lean:457–472`). No estimate of a pressure difference and no derivative of the pressure is needed for comparison.

**(ii) Top transport costs only a coefficient derivative.** Z+u is lifted divergence-free. Its H^(q+1) restriction has a.e. norm ≤V, and d has H¹ regularity. The identity in §2 and the tangent bound give

\[
 |\langle Kd,T(Z+u,d)\rangle|
 \le\tfrac12 K_x(|\kappa|+\|m\|)V x^2
 \le K_x V x^2. \tag{4.2}
\]

This is C13's `difference_transport_bound`; C10 explicitly uses Z's and u's divergence. A naive product bound on this term would introduce `‖∇d‖₂` and would not yield the required viscosity-independent L² comparison.

**(iii) Heat is dissipative up to a fixed K-derivative error.** For each of the four unit directions, translation integration by parts and the coefficient product rule yield

\[
 \langle Kd,D_i^2d\rangle
 =-\langle KD_i d,D_i d\rangle-\langle (D_iK)d,D_i d\rangle.
\]

Coercivity and Young give

\[
 K_x x\|D_i d\|_2
 \le\tfrac{c^2}{2}\|D_i d\|_2^2+\tfrac{K_x^2}{2c^2}x^2.
\]

Summing four directions proves

\[
 \langle Kd,\Delta_{cyl}d\rangle
 \le-\tfrac{c^2}{2}\sum_i\|D_i d\|_2^2
       +\tfrac{2K_x^2}{c^2}x^2
 \le\tfrac{2K_x^2}{c^2}x^2. \tag{4.3}
\]

`MetricHeatEnergy.metric_product_hasDerivAt`, `metric_second_derivative_identity`, `metric_cross_young`, and `metric_heat_bound` supply exactly these steps; C13 specializes them to d's actual second-order jet. There is **no division by ν**. Two spatial derivatives of d suffice for this calculation.

**(iv) Remainder and viscosity mismatch.** Each term of `T(d,Z+v)` is `ℓ_i(d)D_i(Z+v)`. Put the latter factor in L∞ using H^(q+1) of its derivative, and the former in L². Derivative extraction from H^(q+2) is contractive and `‖ℓ_i‖≤1`. Four directions give

\[
 \|T(d,Z+v)\|_2\le4C_{emb}(L,q+1)(Z_b+M)x.
\]

Multiplication by A gives `A₀x`. In `Q(Z+u,d)` put Z+u in L∞; in `Q(d,Z+v)` put Z+v in L∞. The scalar coordinate functionals have norm ≤1 and the three multiplier bounds sum to A₂, giving `A₂ Cemb(Z_b+M)x` for each. Hence

\[
 \|R_t(u,v)\|_2\le L_{rem}x. \tag{4.4}
\]

This expands C11/C12 through `SobolevL2Stability.transport_reverse_norm` and `coordinate_coefficient_norm` / `coordinate_coefficient_reverse_norm`; it does not assume L² Lipschitzness of the full transport map. Finally, the native max-word norm gives

\[
 \|\Delta_{cyl}v(t)\|_2\le\sum_{i<4}\|D_i^2v(t)\|_2\le4M. \tag{4.5}
\]

### Differentiate the squared metric energy

Set `E_d(t)=⟨K(t)d(t),d(t)⟩`. It is continuous on [0,T], differentiable in the interior by the mild bridge and K's actual time derivative. Symmetry gives

\[
 E_d'=\langle K'd,d\rangle+2\langle Kd,d_t\rangle.
\]

Insert (4.1), cancel pressure, and use (4.2)–(4.5), with `ε=|ν−μ|`:

\[
 E_d'\le
 (K_t+2K_xV+4\nu K_x^2/c^2+2K_bL_{rem})x^2
 +2(4K_bM)\varepsilon x.
\]

The last Young inequality is just `(x−4K_bM ε)²≥0`, so the last term is at most `x²+(4K_bM)² ε²`. Since `ν≤1` and `c²x²≤E_d`,

\[
 E_d'\le aE_d+b\varepsilon^2,\qquad
 a={K_t+2K_xV+4K_x^2/c^2+2K_bL_{rem}+1\over c^2},
 \qquad b=(4K_bM)^2. \tag{4.6}
\]

All numerator terms are nonnegative. This reproduces C10's calculation and `SquaredMetricStability.metric_derivative_bound` below its interface. Squared energy avoids differentiating a square root at zero.

The common zero trace gives E_d(0)=0. For clarity, the source's coarser Gronwall bound needs no endpoint derivative: `e^(−at)E_d(t)−bε²t` has nonpositive interior derivative and is continuous on the closed interval. It is therefore nonincreasing. Thus

\[
 0\le E_d(t)\le b\varepsilon^2 t e^{at}\le b\varepsilon^2 T e^{aT}.
\]

Coercivity and c>0 yield `x≤sqrt(bT exp(aT)) ε/c`. Take the time supremum to obtain C14/C31's path estimate stated at the start. Since ν_n is Cauchy, `valuePath(u_n)` is Cauchy in **global** `C_tL²`. Every constant was fixed before n,m; no q-uniform comparison constant is claimed.

## 5. Whole-sequence strong convergence by words, not compact embedding

Let h=u_n−u_m. For an ordered word w of length j and a direction i with `j+2≤q+2`, the actual derivative edges and translation pairing give

\[
 \|D_iD_w h(t)\|_2^2
 =-\langle D_w h(t),D_i^2D_w h(t)\rangle
 \le\|D_w h(t)\|_2\,\|h(t)\|_{H^{q+2}}.
\]

The triangle inequality supplies `‖h‖_(C_tH^(q+2))≤2M`. Taking time suprema (or bounding the child norm by the square root of the fixed right-hand side) proves

\[
 \|D_iD_w(u_n-u_m)\|_{C_tL^2}^2
 \le2M\|D_w(u_n-u_m)\|_{C_tL^2}. \tag{5.1}
\]

This is the actual C15 derivation, not a presumed interpolation inequality. The parent word need not commute with any other word: the child is obtained by **prepending** i; the second derivative has two prepended i's.

The empty word is already Cauchy by §4. If a parent is Cauchy, (5.1) makes each child Cauchy: use parent tolerance `ε²/(2M+1)`. Induction reaches every word of length at most q+1; the last step takes j=q and uses exactly q+2 derivatives. It does not reach q+2.

For a continuous H^(q+1) path f,

\[
 \|f\|_{C_tH^{q+1}}
 =\sup_t\max_{|w|\le q+1}\|D_w f(t)\|_2
 =\max_{|w|\le q+1}\|D_w f\|_{C_tL^2}.
\]

There are finitely many words, so all coordinate Cauchy conditions can be satisfied after a single index. C16's `pathCoordinates_norm` is exactly this isometry; completeness now gives one

\[
 v_n:=\mathrm{truncate}_{q+1}u_n\longrightarrow e
 \quad\text{in }C([0,T],H^{q+1}). \tag{5.2}
\]

C32/C33 route the derived Cauchy estimate through precisely this argument. This is **whole-sequence** convergence. Neither spatial tightness, compact support, Rellich, time equicontinuity extraction, nor a subsequence of viscous solutions has been used. The Sobolev embedding foundation may itself use an a.e. convergent mollifier subsequence; that is not a subsequence selection in (5.2).

Contractive restriction gives `‖v_n‖≤M`, and norm continuity gives `‖e‖≤M`. Continuous evaluation at 0 gives e(0)=0. At any fixed t, continuous evaluation followed by `valueOperator` gives L² convergence, and the closed orthogonal-complement definition of lifted divergence freedom gives `value(e(t))∈DivFree_(κ,m)`. These are C17's three limit passages; they hold at **all** closed-interval times, including T.

## 6. Retain exactly the available metric blocks

The energy is not a physical H^P norm. With `w_j(ρ)=ρ^j/(j!)²`, its literal form is

\[
 E_{P,\rho,K}(f)=
 \sum_{j=0}^{P}\ \sum_{w\in\{0,1,2,3\}^{j}}
 w_j(\rho)
 \sqrt{\sum_{\ell=0}^{6}\ \sum_{a\in\{0,1,2,3\}^{\ell}}
 \langle K D_{a\mathbin{+}w}f,D_{a\mathbin{+}w}f\rangle}.
\]

Here `a+w` means base-then-external word concatenation, not a commutative multi-index. The square root is taken **inside** the external-word sum. `FiniteMetricEnergy.familyEnergy/familyMetricNorm` and `EnergyWordCoordinates.energyValues_eq_word` identify the precise coordinates.

Fix any P satisfying **both** `P≤N` and `P+6≤q+1`, and any t∈[0,T]. Positivity of ρ makes each weighted root nonnegative. The inclusion of external words for P into those for N preserves the identical base blocks, hence

\[
 E_{P,\rho(t),K(t)}(v_n(t))
 =E_{P,\rho(t),K(t)}(u_n(t))
 \le E_{N,\rho(t),K(t)}(u_n(t)).
\]

The equality uses preservation of every retained derivative word by restriction; the inequality is C36's literal finite-sum inclusion. For each surviving coordinate `D_(a+w)v_n(t)→D_(a+w)e(t)` in L². Boundedness of the **same** K(t), continuity of inner products and of the real square root, then finite sums, give convergence of E_P. This is `GevreyEnergyLimit.energyNorm_continuous`/`energyNorm_restrict`, used by C18. It includes zero energy, requires no smooth representative and no top-order lower-semicontinuity assertion.

Pass each of the two family bounds separately to get

\[
 E_{P,\rho(t),K(t)}(e(t))\le 2r e^{3Ct}\le\Delta/2.
\]

With N=q−4, the strongest allowed integer P is **q−5=N−1**, not N. In particular q=6 gives P≤1 although N=2. Top energy requires q+2 derivatives and is not an output here. C03's surviving-cutoff quantifiers and C02's energy fields match this restriction exactly.

## 7. Pass the nonlinear projected equation on the same e

### Restriction is an identity, including pressure

The coefficient operators at the two orders have the same L² values; product realizations are the same a.e. products; derivative restriction preserves the words. `SobolevNonlinearCompatibility.restrict_productHq`, `restrict_asymmetricTransport`, `restrict_coefficient` and `SobolevCorrectionCompatibility.restrict_orderZeroSource` yield C19's

\[
 \mathrm{truncate}_q F^{D_1}_t(u_n(t))=F^{D_0}_t(v_n(t)).
\]

For pressure, `pressureSobolevOperator` is a jet lift of a single `pressureL2Operator`, not a newly solved inverse problem at each order. Restricting it and applying the lower lift to the restricted source produce the same L² value; `value_injective` identifies their H^q arrays. This proves `restrict_pressure` and `restrict_projectedSource` in `SobolevNonlinearCompatibility.lean:55–79`. The actual coefficients κ,m,G and its coercivity are unchanged. Thus C19 proves

\[
 \mathrm{truncate}_q S^{D_1}_t(u_n(t))=S^{D_0}_t(v_n(t)). \tag{7.1}
\]

There is no later independent pressure selection. The general coercive inverse/jet regularity is the foundational debt from §2; (7.1) is an identity on that same inverse, not an assumption that all pressures are continuous.

### Continuous quadratic source, with its actual Lipschitz constant

Let `\mathcal C=D₀.coefficients`, a continuous coefficient record with input H^(q+1) and output H^q. `CorrectionTime.correctionCoefficients` constructs its projection as `I−G P_G`, forcing as the actual residual, linear term as the full linearization about D₀.approximation, and quadratic term as transport plus algebraic product. Thus `‖\mathcal C.linear‖` below is **not just A₀**. Multiplier continuity at q and coercivity imply pressure inverse continuity by `SobolevPressureTime.pressureSobolev_continuousAt` (resolvent); composition then makes the projection continuous. Compactness of the **time** interval makes these continuous operator-path norms finite.

For x,y in the H^(q+1) ball of radius M, bilinearity gives

\[
 B(x,x)-B(y,y)=B(x,x-y)+B(x-y,y).
\]

The common forcing cancels, so the actual projected source satisfies

\[
 \|S_t(x)-S_t(y)\|_{H^q}
 \le\underbrace{\|\mathcal C.projection\|
 (\|\mathcal C.linear\|+2\|\mathcal C.quadratic\|M)}_{Lip_M}
 \|x-y\|_{H^{q+1}}.
\]

All norms on coefficients are uniform continuous-path operator norms. Both v_n and e lie in that ball by §5. Taking suprema proves C20/C35's estimate and

\[
 S^{D_0}(v_n)\longrightarrow S^{D_0}(e)
 \quad\text{in }C_tH^q. \tag{7.2}
\]

### Recompute the defect and pass only where justified

The four-coordinate Laplacian extraction in (4.5) gives independently

\[
 \|\nu_n\Delta_{cyl}u_n\|_{C_tL^2}
 \le4\nu_n\|u_n\|_{C_tH^{q+2}}
 \le4\nu_n M\longrightarrow0. \tag{7.3}
\]

This is C21 and the quantitative defect proof exported by C06. This reconstruction uses only its **L²** target; it does not claim convergence of the entire viscous right-hand side in H^q from this bound.

Define L² paths

\[
 U_n=\mathrm{value}(u_n),\qquad
 f_n=\nu_n\Delta_{cyl}u_n+\mathrm{value}(S^{D_0}(v_n)),
 \quad U=\mathrm{value}(e),\quad g=\mathrm{value}(S^{D_0}(e)).
\]

Then U_n→U by (5.2) and value compatibility; f_n→g in `C_tL²` by (7.2),(7.3) and boundedness of value. C22 is exactly this sum of convergences. The actual mild derivative, rewritten using (7.1), says U_n′=f_n at every interior time (C25, via `lower_mild_value_derivative`). Each f_n is a continuous **closed-interval** L² path.

For a continuous Banach-valued f, define `I_t f=∫_0^t f(s) ds`; the source's clamped `pathIntegralOperator T hT 0 t` has norm ≤t≤T. Interior FTC plus continuous endpoint traces give

\[
 U_n(t)=U_n(0)+I_t f_n \quad (0\le t\le T).
\]

No endpoint derivative is used. Indeed, the convergence error of the integral is bounded by `T‖f_n−g‖_(C_tL²)`. Continuous evaluation of U_n at t and 0 therefore gives

\[
 U(t)=U(0)+\int_0^t g(s)\,ds. \tag{7.4}
\]

The L² FTC differentiates this in the interior. C23 and C04 implement precisely these bounded-integration/evaluation passages. `extendPath` is a continuous clamping device; locally in `(0,T)` it equals the original path. Its totalization does not prove an endpoint derivative.

### Upgrade by the strong integral equation, not by injectivity alone

Set `w=truncate_q e∈C_tH^q` and `F=S^{D₀}(e)∈C_tH^q`. Let `J=valueOperator L q : H^q→L²`. It is bounded and injective, and `Jw=U`, `JF=g`. Bounded linear maps commute with Bochner integrals of continuous paths. Thus (7.4) implies

\[
 J\left(w(t)-w(0)-\int_0^t F(s)\,ds\right)=0.
\]

Injectivity now gives the H^q **integral equation**. Since F is continuous in H^q, the Banach-valued FTC gives w′(t)=F(t) for `0<t<T`. This is C24/C05's argument. Injectivity of an embedding alone would not lift differentiability; the continuous stronger RHS and the commuting integral are essential.

Finally C05's `CorrectionData.source_sobolev` identifies F itself, not a new weak representative, with

\[
 \frac{d}{dt}\mathrm{truncate}_q e(t)
 =-D_0.\mathrm{rawSource}(t,e(t))
  -G_0(t)D_0.\mathrm{pressure}(t,e(t))
 \quad\text{in }H^q. \tag{7.5}
\]

`G₀` here is the actual coefficient Sobolev multiplier of D₀.metric. The pressure is the signed lifted-gradient solve described in §4, not yet a scalar physical pressure.

## 8. Producer → consumer, without witness substitution

The local source spine is:

1. **C07→C06:** upstream viscous existence/energy/bootstrap supplies each u_n with its own actual mild law, common norm and energy bounds. C06 uses the fixed reciprocal viscosity sequence, not a new schedule.
2. **C06→C03:** `stabilityBudgetLower`→C33→C32→C31 derives the comparison/Cauchy mechanism of §§3–5; C18/C36 attach the surviving energies. C03 returns the **same u and e** together with convergence, trace, divergence, norm and energies.
3. **C03→C01:** C01 obtains `⟨u,e,hu,hconv,hi,hd,hM,hE⟩` and immediately starts its output with `⟨e,hi,hd,hM,hE,...⟩`. It passes **that u,e,hconv** and the mild/norm fields of hu into C04, then uses C05 for (7.5). No new solve occurs after taking the limit.
4. **C01→C02:** `finite_exists` invokes C01 on `A.atOrder(q+2)` with `N=q−4`, B's original fields and `A.metricBudget ... (q+1)`. It rewrites `A.lower_twice`. The body takes `⟨e,hi,hd,_,he,hp⟩`: the norm certificate is not exported by this particular consumer, but e is unchanged. It rewrites hp by `←CorrectionData.source_sobolev`, then composes the derivative with `valueOperator L q` to obtain **exactly**

   `HasDerivAt (fun r => value (extendPath T hT.le e r))`

   `(value (((A.atOrder q).coefficients).apply t (e t))) t`

   for interior t. Trace, divergence and both retained-energy fields are the same certificates.
5. **C02's actual selection:** `Budget.solution q` remains `Classical.choose(finite_exists ... q)`; `Budget.family` uses that solution and its `choose_spec` trace/divergence/equation fields. No claim identifies this chosen witness definitionally with an internal existential exhibit of a proof. The local derivation constructs an admissible witness for `finite_exists`; the selected witness is used with exactly its exported specification. All-order compatibility/representatives lie outside this contract.

**Separately marked all-admissible deduction (human, not a replacement selection).** The two-solution estimate in §4 applies to any two admissible positive-viscosity mild paths with these same D₁,K and common bound M, not merely their numerical indices. Thus two admissible families on the same reciprocal schedule and same bound coincide at each n by setting ν=μ, and their strong limits coincide. This observation neither changes the historical schedule nor identifies an arbitrary selected inviscid witness with a particular hidden family. No such stronger selection attribution is needed here.

In particular this report attaches no canonical initialized Δ/ρ formulas to an arbitrary selected `GeometryJoinedChoice.Q`. That later record retains physical errors and coefficient identity, not equality to the internal initialized exhibit. The earlier NS diagonal/schedule and Euler packet hierarchy are untouched.

## 9. Field-use and derivative ledger

This ledger distinguishes actual local use from fields whose analytic production is accepted upstream. Passing a record is not a claim of minimal dependence.

| Supplied fields | Post-family use / upstream role |
|---|---|
| Data κ,direction, `scale_bound`, `direction_bound` | Same lifted gradient/divergence spaces and transport under all lowerings; norm ≤1 for four functionals and `(|κ|+‖m‖)/2≤1`. |
| Data metric coefficient, jets, continuous multiplier action; forward coercivity/positivity and L² continuity | Coercive pressure solve on the actual raw source, bounded H^(q+1)/H^q lifts, same-value restriction, continuous projection. Jets at q+2 also belong to C07's accepted energy production. |
| Data linear and three quadratic coefficient towers, jets and continuity | Four-term remainder, A₀/A₂ extraction, genuine continuous bilinear maps, source restriction and `Lip_M`. |
| Actual approximation/residual towers and `value_eq` | Approximation's fixed high norm Z_b, its lifted divergence, same nonlinear linearization and residual cancellation; residual's identity is needed for restriction even though its size is absent from the difference estimate. |
| MetricBudget metric, continuous, derivative, hasDeriv, c/c_pos, symmetric, coercive, inverse | Differentiate E_d in interior; use c² coercivity, pressure cancellation, heat and transport structure. All copied unchanged from B.metric. |
| MetricBudget bound/first/time, their signs and bound_le/first_le/time_le | K_b,K_x,K_t and hence a,b,C_*. Multiplier operator bound obtained from pointwise coefficient witness. |
| SpatialBudget radius_pos, A0/A2, linear/quadratic and signs | Nonnegative zeroth-term extraction of comparison coefficients. |
| SpatialBudget residual/residual_pos, retained family E_N bounds | Retained residual/target bound in §6. The value r is not used to estimate R(u,v) after subtraction. |
| SpatialBudget Rc,M,B,B0,B1 and signs; inverse_five/inverse_six; radius_small; metric_derivatives/metric_base; background/background_derivative; residual_bound | Accepted C07 existence/energy input. Post-family comparison does not reopen these estimates or use them as assumed stability. Z_b instead comes from the given continuous approximation path. |
| DriftBudget full, drift, drift_nonneg, drift_bound; all-order growth_bound, delta guards, radius_pos, decay, scale, small, radius_eq | Upstream family/energy and common positive radius; after family production only the already obtained radius positivity, M and target/residual bounds are required in the corresponding local steps. No global unused-field claim. |
| B.divergence; u_n trace/divergence/mild law/norm | Top-transport and pressure cancellations, zero difference energy, actual time derivatives, uniform interpolation, trace/divergence passage. Neither energy bounds alone nor mild laws for unrelated paths would suffice. |

Order ledger:

- D₂: coefficient/residual order q+2; approximation q+3; accepted energy cutoff N+6=q+2.
- D₁: source order q+1, viscous states q+2; comparison uses value in L², H¹ for transport energy, H² for heat, and H^(q+2) to place one derivative of Z+v in L∞ through H^(q+1).
- Word interpolation: parent j, child j+1, available second child j+2; reaches q+1 but not the top q+2.
- Limit: continuous H^(q+1); retained energy P+6≤q+1 and P≤N.
- D₀: continuous quadratic source H^(q+1)→H^q, equation in H^q after integral upgrade. Defect and initial equation passage only asserted in L².
- No physical graph evaluation, x/ell rescaling, frequency-k differentiated error, or physical pressure potential is an output.

## 10. What could be simpler, and what still needs review

**Mathematical simplifications, not implementations:**

- Call this step “uniform viscosity stability plus word interpolation,” rather than spatial compactness. The existing proof already avoids the substantial tail/Rellich machinery suggested by the earlier target description.
- Present one reusable two-solution lemma on the actual coefficient/inverse metric and bounded mild paths, followed by a separate energy-retention lemma. This separates comparison's low-order structural requirements from the much larger Gevrey existence budget without deleting that upstream budget.
- State the stronger integral equation directly once the L² integral equation and continuous H^q source are available. C04's derivative, C05's reintegration through C24, and final differentiation are mathematically sound but can be expositorily compressed into the single commuting-integral argument in §7.
- Expose source restriction as an identity of maps generated from the same coefficient/pressure inverse; keep signed pressure distinct from the unsigned solver. This would shorten repeated order adapters without erasing their object-identity obligations.
- Make `P≤min(N,q−5)` explicit at this application. The current two hypotheses are more reusable, but easy to misread as top-energy retention.

These are explanatory/interface candidates only. No alternate norm convention, optimized constants, minimal derivative theorem, witness replacement, or external-class equivalence is claimed. The source's coarse `Cemb`, factor 4, and Gronwall bound are kept; sharpening them is unnecessary for the selected consumer.

### Unresolved-input ledger and review hotspots

1. **Largest accepted debt — viscous production:** C07's nonlinear Gevrey energy/bootstrap and actual continuation are not proved here. The report starts at C06's complete same-path output, as contracted. RI-05/OBL-EUL-003 is narrowed, not globally closed.
2. **Foundational analytic debt:** the full cylinder Sobolev embedding/product/density, closed strong-derivative graphs, weak-divergence metric transport integration by parts, coercive inverse with Sobolev jets/resolvent, and heat-Duhamel differentiation remain imported with the matched domains/orders in §2. Their general proofs are not re-certified by local-body inspection or byte checks.
3. **Review the decisive constants:** the transport factor is `(1/2)(|κ|+‖m‖)≤1`; heat has four coordinate errors `K_x²/(2c²)`; energy differentiation doubles heat; Young contributes `+1` to the numerator of a and `(4K_bM)²` to b. No inverse viscosity occurs. Forward coercivity must not be confused with c².
4. **Review signs and identity:** `p=−P_G raw`, `source=−raw−Gp`; symmetry moves K to the Gp factor and `KG=I` cancels it. Both lowerings preserve the same actual G, inverse, gradient space and raw-source constituents.
5. **Review the two distinct losses:** interpolation discards the top state derivative and hence P=N energy; nonlinear source loses one more derivative, but the available defect estimate is only L². The stronger derivative comes from a continuous H^q integral, not convergence of full viscous RHS in H^q or injectivity alone.
6. **Review quantifiers/witnesses:** all constants are fixed before n,m for fixed q; energies/traces are on [0,T], derivatives only on `(0,T)`; the original reciprocal viscosity schedule and downstream `Classical.choose` definitions are retained. The norm bound from C01 is deliberately absent from C02's exported finite specification. Do not infer extra properties of its chosen witness merely from one existential exhibit.

No missing tail/domain/pressure hypothesis was found at this selected boundary under the stated foundational contracts. The deepest verified local step is the complete supplier→family→Cauchy limit→retained blocks→same signed-pressure equation→C02 derivative chain above. This is not a reconstruction of physical Euler, the all-order tower, packet renewal, broad-class exclusion, or any NS mechanism. Those deferred analytic and selected-witness debts, including NC/PM numerical-domain questions, remain untouched.
