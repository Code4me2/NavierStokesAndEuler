# Primitive derivatives upstream of native control — bounded derivation plan

## 1. Authorization, preservation, and deliverables

**Status: planning and selected source-body inspection only.** This is not chapter 06, a completed derivation, independent review, or formal validation. Audience: a graduate PDE reader without Lean knowledge. Produce one continuous worked chain, not a record inventory, full singularity textbook, or proposed refactor.

Frozen Lean/config baseline: `26e896edbdbe1215c0d50ddba24b2b6453646f5f`; observed HEAD agrees. Work only in `/home/velvet/worktrees/proof-native-control-20260912T185404Z`. Read repository README, Comparator instructions, repository validation plan, companion authoring plan, native plan, [chapter 05](05-native-weighted-control.md), and its [validation ledger](native-control-validation.md), including NC-D1 and NC-D3–D5. No `AGENTS.md` was found in the worktree/searched parent tree or checked ancestors. Build instructions are not authorization to execute builds.

The reviewed companion is preserved at:

```text
/home/velvet/research-snapshots/research-and-companion-20260912T192848Z/
  companion.tar
  companion-manifest.json
```

Manifest archive SHA-256: `1e6ecd4453daf1b6cbc9cd10abd1d8f3ddd4404076713cb2802422616e9b8158`. Historical source baselines and review claims remain historical. Entry status already contained changes to companion `02-ns-construction.md`, `README.md`, `SOURCE-MAP.md`, and untracked chapter 05, native plan, and native validation ledger; none is an output of this pass.

**Owned now:** this new `primitive-derivative-plan.md` only. **Reserved for the later single author:** `06-primitive-derivative-estimates.md` and `primitive-derivative-validation.md` (filenames, not links to nonexistent files). Minimal companion README/SOURCE-MAP links may be added when those files exist. Do not edit chapter 05, chapter 02, `PLAN.md`, `native-control-plan.md`, `VALIDATION.md`, `native-control-validation.md`, or `validate.py`. Do not overwrite any existing work silently.

No Lean, configuration, dependency, original-checkout, research-worktree, or snapshot writes. No builds, Lean probes, installations, dependency operations, commits, pushes, ref changes, reset/stash/clean, or source repair. Read-only reports are returned through the harness, not written by workers into any worktree. Delegation must follow the historical model requirement (`openai-codex/gpt-6-astra`); do not substitute silently. No delegation facility is available in this planning session, so the two assignments below are **pending, not launched or reviewed**.

## 2. Exact endpoint and permitted primitive boundary

Reconstruct these mathematical outputs for the **same selected profile and preparation** as chapter 05:

1. All-order actual normalized base bounds, and error bounds of size `Q_b^(2h)`, on the actual enlarged positive-time cells, with constants before band/label.
2. The concrete C1-error/C2-reference majorant used by preparation, and the route from the fixed profile's cone to the representative bounds. Explain why one prepared threshold works for both signs and every derivative order; do not choose a new threshold or schedule for each requested order.
3. Through order `N`, numerical normal, explicit normal-motion, shear, normalization, frame/coefficient/projection/synthesis witnesses from base orders through `N+1`.
4. Numerical inverse-square-normal and inverse-carrier witnesses, transported to the selected strip/copy, and a finite recurrence for the native pressure estimate using chapter 05's already displayed modal/ambient bound.

NC-D1 is addressed **relative to a declared fixed finite-profile input**, not by reconstructing the outgoing-profile ODE, every coefficient-solving step, or finite modulation existence. NC-D3 and the numerical part of NC-D4 are the main target. NC-D2 (incoming residual production) and NC-D5 (radial extension, cutoff defects, physical localization) stay open. Endpoint regularity of an auxiliary stable chart is not closure of NC-D5. No claim closes the whole OBL-NSC-004 cycle.

### Allowed primitive assumptions — state them mathematically at their first use

- The already selected outgoing/nominal profile, solved finite modulation, fixed `0<h<1/2`, nonzero axis normalization, and the literal aligned smooth coefficient family. Smoothness means ambient smoothness on a neighborhood of each compact set used, including the coefficient parameter endpoints. The smooth enlarged weighted bundle used to choose the actual schedule is included at this finite-coefficient boundary. Identify its quotient components and their smoothness supplier; do not assume bounds on a summed profile or a flat weighted residual.
- For an individual fixed coefficient or cutoff, compact derivative suprema may be named as primitive **numbers defined from that function**, with finiteness proved from smoothness. No universal analytic/Gevrey growth in derivative order is assumed. Display the compact set, norm, order, and which fixed coefficient each number depends on.
- The fixed finite-profile positivity and strict cone/edge-direction conditions may be inputs, explicitly translated from the actual profile certificate. For preparation, expand their transport to the leading frequency/shear, spectral eigenpair and compact representative bounds. If the endpoint direction/gluing conditions cannot be translated, keep that part of NC-D1 conditional rather than assuming `Prepared` exists.
- Elementary finite-dimensional product, chain, reciprocal and real-power calculus, compactness, the inverse function theorem with a displayed nonvanishing Jacobian, and local finiteness of a sum once proved. Reconstruct quantitative constants, not an assumed inverse-coordinate derivative theorem.
- For the final handoff only: chapter 05's reviewed order-zero comparison/transport and weighted ODE calculation, fixed slot geometry, incoming all-jet residual invariant and frequency coherence. They must be applied after their primitive base inputs have been supplied here.

**Forbidden primitive assumptions:** `AdmissibleScales.ordinary/blown`, `BaseChartJets.Estimates`, `Prepared.frequency_jets/axial_jets/base`, arbitrary polynomial jets of the base or normal, compact derivative constants of an unexplained normalization map, `normalInverse_unweighted`, solved pressure classes, or the derivative bounds being reconstructed. These are conclusions to produce. Source theorem names may locate the argument; they cannot replace it.

## 3. Keep the actual witness fixed

Use chapter 05's dictionary: budget `B_bud`, initializer threshold `N0`, preparation `a`, prepared majorant `M0=a.M`, slot radius `r0`, selector `e(q)=(ell,b)`, reference band `b_r`, arbitrary copy `k`, nonzero harmonic `j`. The phase sign in `ell` is not a real/imaginary component. Use `d` for derivative order, `r` for the Borel summation coordinate, `rho` for its normalized scalar coordinate, and `S0=S(b_r)`. Call chapter 05's growth majorant `mathcal G` here to distinguish it from the axial base field `G`.

The identity spine is:

- [FinalSlowBase](../../NavierStokes/FinalSlowBase.lean): `NavierStokes.FinalSlowBase.coefficients`, `NavierStokes.FinalSlowBase.scales`, `NavierStokes.FinalSlowBase.scales_admissible_on`.
- [PrimaryGeometryAssembly](../../NavierStokes/PrimaryGeometryAssembly.lean): `NavierStokes.PrimaryGeometryAssembly.frequency`, `NavierStokes.PrimaryGeometryAssembly.axial`, `NavierStokes.PrimaryGeometryAssembly.exists_prepared`, `NavierStokes.PrimaryGeometryAssembly.family`, `NavierStokes.PrimaryGeometryAssembly.Prepared.restrict`.
- [CorrectionInitialization](../../NavierStokes/CorrectionInitialization.lean): `NavierStokes.CorrectionInitialization.ActualPrimary.choice_nonempty`, `NavierStokes.CorrectionInitialization.ActualPrimary.choice`, `NavierStokes.CorrectionInitialization.ActualPrimary.phases`.
- [PrimaryTargetBounds](../../NavierStokes/PrimaryTargetBounds.lean): `NavierStokes.PrimaryTargetBounds.exists_constructed_bounds` must be inspected for the final cutoff restriction used by the literal choice; it is not permission to reprove covariance.
- [ActualParticularStageControls](../../NavierStokes/ActualParticularStageControls.lean): `NavierStokes.ActualParticularStageControls.selectedConstruction`, `NavierStokes.ActualParticularStageControls.selected_tangent_eq`, `NavierStokes.ActualParticularStageControls.selected_inverse_frequency`.

At the base layer, prove the actual formulas, not just equality of classes. With `A=1/2+h`, `p=(R,(Z,T))`, `c(p)=(rho,(X,eta))`, and the fixed coefficient sequence `d`, they are
\[
 F_b(p)=\frac{\rho^{-A}}R\frac{\sqrt{2X}}{C_{\rm axis}}
     \operatorname{slowSum}_{\mathbf a,h}(d_\phi)(Q_b\rho,X,\eta),\qquad
 G_b(p)=\rho^{-A}\operatorname{slowSum}_{\mathbf a,h}(d_{\rm axial})(Q_b\rho,X,\eta).
\]
The leading fields replace each sum by its order-zero coefficient. Retain `1/R`; it disappears only after using `X=R²/(2rho)` in the leading-frequency identity. The Borel schedule `mathbf a=FinalSlowBase.scales` is not the preparation record `a`.

[BaseChartJets](../../NavierStokes/BaseChartJets.lean): `NavierStokes.BaseChartJets.frequency`, `NavierStokes.BaseChartJets.axial`, `NavierStokes.BaseChartJets.leadingFrequency_eq`, `NavierStokes.BaseChartJets.frequency_eq_normalized_velocity`, `NavierStokes.BaseChartJets.axial_eq_normalized_velocity` bind these fields to the actual constructed curl base. Restriction of labels retains representatives, fields, phase modes and constants. No replacement profile or newly optimized Borel schedule is admissible.

All jets are full real Fréchet operator norms. Native products use max norms, real modal/ambient spaces Euclidean norms, complex ambient space the componentwise sup norm. A vector assembly may be bounded by the sum of coordinate bounds; do not identify these norms. Constants precede the labels/copies they control. Fixed-`j` jet constants may depend on `j`; inverse-frequency gain and energy are uniform over nonzero `j`.

## 4. Required producer calculations and source trail

### P1. Individual templates → one actual schedule → all-order summed errors

[SlowBorelBase](../../NavierStokes/SlowBorelBase.lean): `NavierStokes.SlowBorelBase.exists_template_jet_bound`, `NavierStokes.SlowBorelBase.powerStage_blown_bound`, `NavierStokes.SlowBorelBase.powerStage_jet_bound`, `NavierStokes.SlowBorelBase.exists_admissibleScales`, `NavierStokes.SlowBorelBase.normalized_correction_bound`, `NavierStokes.SlowBorelBase.normalized_tangential_bounds`.

Start with the actual positive stage
\[
 u_l(r,w)=\chi(\mathbf a_l r)r^{2hl}f_l(w),\quad l\ge1,
 \qquad \operatorname{slowSum}=f_0+\sum_{l\ge1}u_l.
\]
At fixed positive `r`, freeze the dilation `(s,w) -> (rs,w)` and define the blown derivative at `(1,w)`. On active cutoff support, `c=mathbf a_l r` lies in `[0,1]`. Define `T_{l,d}` by the smooth joint template on `[0,1] × {1} × K`; explain the local-power cutoff which makes the template globally smooth while agreeing with `s^(2hl)` near `1`. Derive
\[
 \|\mathfrak D^d u_l(r,w)\|\le T_{l,d}r^{2hl},\qquad
 \|D^d u_l(r,w)\|\le T_{l,d}r^{2hl-d}\quad(0<r\le1).
\]
Outside support all jets vanish by an open germ, not just a value identity. The coefficient and cutoff compact seminorms, product rule and real-power derivatives can give explicit majorants for `T_{l,d}`; a supremum of derivatives of the **explicit individual template** is acceptable if its finiteness is proved. A supremum of unknown summed-field derivatives is not.

[DiagonalScale](../../NavierStokes/DiagonalScale.lean): `NavierStokes.DiagonalScale.exists_diagonal_scales`, `NavierStokes.DiagonalScale.doublingEnvelope`, `NavierStokes.DiagonalScale.dyadic_tail_sum`. Expand its finite constraints: for each `l>=1`, choose one local integer scale enforcing `T_{l,d} r^(hl)<=2^(-l)` for all `d<=l+2` and `0<r<=1/b_l`, then take the doubling envelope. In this zero-log-power specialization a sufficient local number is
\[
 b_l\ge\max\left(1,\max_{d\le l+2}(2^lT_{l,d})^{1/(hl)}\right),\quad
 a_0=\max(1,b_0),\quad a_{l+1}=\max(b_{l+1},2a_l),
\]
with the initial budget included in `b_0`. This displays a sufficient numerical choice, **not a claim that a noncomputable source choice equals these ceilings**. Trace the source's chosen witnesses and properties instead of replacing the actual schedule.

Crucially [EntranceAlignedBase](../../NavierStokes/EntranceAlignedBase.lean), `NavierStokes.EntranceAlignedBase.scales`, chooses from the **enlarged weighted bundle**. Inspect `NavierStokes.EntranceAlignedBase.scales_spec` and `NavierStokes.EntranceAlignedBase.scales_admissible`; project/restrict that very choice via FinalSlowBase, rather than invoking a second existence theorem for just `F,G`. Explain any bounded-linear projection cost for its seven-component base bundle and components 6 (`phi`) and 5 (`axial`).

For requested order `d`, split at `J=max(d,1)`. Local finiteness for `r>0` justifies actual differentiation. The head retains exponent `2hl`, while the tail has `2^(-l)r^(hl)` and `d<=l+2`. Sum the geometric series to obtain the source witness
\[
 E_d=\sum_{l=0}^{J}T_{l,d}+2^{-J},\qquad
 \|\mathfrak D^d(\operatorname{slowSum}-f_0)\|\le E_dr^{2h}.
\]
Stage zero in that head is harmlessly zero. Show the exponent comparisons for `r<=1`. Multiply the `phi` error by `sqrt(2X)/C_axis` by Leibniz and combine with the axial bound. This is the actual all-order supplier, not an assumption of tail smallness or termwise differentiation at `r=0`.

### P2. Stable inverse chart → normalized-coordinate numerical jets

[PhysicalCoordinateBounds](../../NavierStokes/PhysicalCoordinateBounds.lean): `NavierStokes.PhysicalCoordinateBounds.inverseDifferential`, `NavierStokes.PhysicalCoordinateBounds.inverseJet`, `NavierStokes.PhysicalCoordinateBounds.iteratedFDeriv_comp_inverse`, `NavierStokes.PhysicalCoordinateBounds.homogeneous_derivative_bound`, `NavierStokes.PhysicalCoordinateBounds.physical_coordinate_derivative_bounds`.

Write the defining equation `rho-Z²rho^(2h)=T`, positive stable branch, and `X=R²/(2rho)`, `eta=Z/rho^(1/2-h)`. The inverse Jacobian denominator is `1-2h eta² >= 1-2h>0`. In forward coordinates `y=(r,s,z)` and `a_h=2h`, the inverse differential acts by
\[
 L(y)v=\left(\frac{v_T+2zr^{a_h}v_z}{1-a_hz^2r^{a_h-1}},v_s,v_z\right).
\]
On `{r=1} × [lo,hi] × [-1,1]`, derive every derivative from this formula; an inverse-chart bound is not an input. The exact recursive tensor producer is `J_0[g]=g`, `J_{n+1}[g]=D J_n[g] composed in the new slot with L`, with currying an isometry. A numerical two-index recurrence is
\[
 A_{0,t}=\sup_K\|D^tg\|,\qquad
 A_{n+1,t}=\sum_{i=0}^{t}\binom ti A_{n,t-i+1}L_i,
 \quad L_i\ge\sup_K\|D^iL\|.
\]
Compute `L_i` by the reciprocal/product recurrences in §5 and falling factorials for powers. For total inverse order `N`, only the finite triangle `n+t<=N` is needed. Apply to the source's power, `eta`, and `X` lifts. Work the first derivative explicitly as a sanity check. Use anisotropic homogeneity to rescale arbitrary positive `r` to `1`, with the actual dilation operator norm; recover the physical bound `C_d r^(-d)` on the prescribed bounded scalar range, paying the source's upper-range factors. Then compose with `physicalInput=(1-T,(R²/2,Z))`, whose derivatives vanish above order two. Do not confuse bounded normalized jets with uniformly bounded physical derivatives at singular time.

[BaseChartJets](../../NavierStokes/BaseChartJets.lean): `NavierStokes.BaseChartJets.scaled_jet_from_blown`, `NavierStokes.BaseChartJets.normalized_error_envelope`, `NavierStokes.BaseChartJets.normalizedCoordinates_polynomial`, `NavierStokes.BaseChartJets.geometry_factors_polynomial`, `NavierStokes.BaseChartJets.actual_estimates`.

Recenter at `r=Q_b rho`. For `qlo<rho<qhi`, the frozen inverse dilation costs `K_rho=max(1,1/qlo)`, not `Q_b^(-1)`. Thus the error witness before nonlinear chart composition is exactly
\[
 E_d qhi^{2h}K_{\rho}^{d}Q_b^{2h}.
\]
Compose with the recovered coordinate jets, multiply by `rho^(-A)/R` or `rho^(-A)`, and add the leading fields. Supply arrays of constants for every order; explain why their band degree is **zero** at this base layer. No differentiation of the error majorant `Q_b^(2h)` occurs: band is frozen.

### P3. The same preparation realizes the inputs

[PositiveRepresentatives](../../NavierStokes/PositiveRepresentatives.lean): `NavierStokes.PositiveRepresentatives.exists_positive_reference_charts` supplies actual three-mesh cells with `R>=sqrt(lo)/2`, bounded slow coordinates, `1/4<rho<4`, `lo/2<X<2hi`, `T>0`, `|eta|<1`. Reconstruct the compact stable-branch/enlarged-cell argument; these are pointwise geometry conclusions, not derivative premises. Retain the one-mesh support, two-mesh phase carrier, three-mesh convex base domain distinction.

`NavierStokes.BaseChartJets.exists_actual_positive_charts` chooses one band cutoff with `4Q_b<=1` and gives all orders on these cells. `NavierStokes.BaseChartJets.Estimates.localBaseBounds` extracts error jets through 1, leading jets through 2, and uses
\[
 K=C_{F,\mathrm{err},\le1}+C_{G,\mathrm{err},\le1}
   +C_{F,\mathrm{lead},\le2}+C_{G,\mathrm{lead},\le2}+1,
 \qquad B_{\mathrm{base}}=2K.
\]
Explain the doubling and `(Q_b^h)^2=Q_b^(2h)` rather than conflating this number with `M0` or the phase construction's larger `M_*`.

[AlignedProfileSpectralCone](../../NavierStokes/AlignedProfileSpectralCone.lean): `NavierStokes.AlignedProfileSpectralCone.referenceFrequency_eq_actual`, `NavierStokes.AlignedProfileSpectralCone.referenceShear_eq_actual`, `NavierStokes.AlignedProfileSpectralCone.reference_cone`, `NavierStokes.AlignedProfileSpectralCone.modulated_positive_reference_cone`, `NavierStokes.AlignedProfileSpectralCone.modulated_representative_bounds`.

Display `F_ref=rho^(-A-1/2) f(X,eta)>0` and `g_ref=F_ref(-shearA,-shearB)`. Translate `closed_shear_positive`/speed from the fixed finite profile to `(g_0)_0<0` and `2F_0 (g_0)_0+|g_0|²>0`, where the subscript outside parentheses selects the first shear component. Recover the negative eigenvector ratio as in chapter 05. On the stable compact reference set take maxima and positive minima of the explicit frequency, shear, eigenvalue, ratio and radius quantities. Explain how the continuous edge-glued target and uniform continuity give `u,eta_margin,N_target` for the same profile, or mark the untranslated finite edge premise explicitly pending.

Finally expand `NavierStokes.PrimaryGeometryAssembly.exists_prepared`: reference constants/target first; admissible same schedule and actual chart estimates; maximum majorant including `B_base`, `u`, `1/(2r0)`, `4r0 Tg`, cell radius and reciprocal radius; large-band threshold last, above the base/chart/target thresholds and `N0`. Read the inequalities of `BasePhaseGeometry.LargeBand` when exhibiting its cutoff. Subsequent covariance cutoff restriction changes only the admissible label set. No all-order bound is required to be uniform in derivative order, and the threshold does not depend on `N`.

### P4. Base order N+1 → frame order N, then numerical pressure normalization

[PhaseJetBounds](../../NavierStokes/PhaseJetBounds.lean): `NavierStokes.PhaseJetBounds.PolynomialJets.fderiv`, `NavierStokes.PhaseJetBounds.PolynomialJets.directional`, `NavierStokes.PhaseJetBounds.PhaseFamily.polynomial_jets`, `NavierStokes.PhaseJetBounds.normalGeometry_jets`, `NavierStokes.PhaseJetBounds.FrameJets.forcing`.

At each finite `N`, use P1–P3 through `N+1`. Work directly with the explicit normal from chapter 05:
\[
 N=(x_0-s(p_\theta F_R+p_zG_R),\ p_\theta/R,
        p_z-\epsilon_rs(p_\theta F_Z+p_zG_Z)),\quad
 \dot N=(-(p_\theta F_R+p_zG_R),0,-\epsilon_r(p_\theta F_Z+p_zG_Z)).
\]
Frozen coefficients have only order-zero jets; `s` has degree-one polynomial growth in `S0` and derivatives vanish above one. Unit directional derivatives of `F,G` cost their next full order. The explicit motion costs **no further** base-order shift. Work the order-one normal derivative to expose the Hessian terms. Normal/shear/motion through `N` require base through `N+1`; forcing source, solution and amplitude through `N` require no hidden `N+2` at this algebraic stage.

Propagate numerical arrays through `beta²=|tail N|²`, its square root and reciprocal, `rho=N_rad/beta`, unit transverse vectors, rotation, `(1+rho²)^(-1)`, eigenvector and inverse, modal matrix, projection and synthesis columns. Tail lower bound is required for frame normalization; total normal lower bound alone is insufficient. Obtain both from chapter 05's comparison after P3 supplies its primitive hypotheses. Do not differentiate a comparison inequality or invoke compact composition with unnamed derivative constants. The numerical outputs may be conservative upper bounds, not the exact noncomputable constants selected by Lean.

[ScaledParticularFrameJets](../../NavierStokes/ScaledParticularFrameJets.lean): `NavierStokes.ScaledParticularFrameJets.native_normal_bounds`; [CurlClassBounds](../../NavierStokes/CurlClassBounds.lean): `NavierStokes.CurlClassBounds.normalInverse_unweighted`; [UniformPrimaryWeights](../../NavierStokes/UniformPrimaryWeights.lean): `NavierStokes.UniformPrimaryWeights.harmonic_inverse_bandBound`.

Transport with the same frozen `phi,c_t,c_N`; a reference jet of order `d` costs at most `(|phi|_op+c_max)^d` times its field multiplier, and replace `S0` by `25 S_b` only in polynomial upper bounds. Keep lower normal bound `b_nat=normal.lower*F_*.b>0`. Recover the actual `1/|N_c|²` recurrence in §5, not just class membership.

For the selected epsilon and carrier, inspect [Scaling](../../NavierStokes/Scaling.lean), `NavierStokes.Scaling.carrier_frequency_sqrt_bounds` and the carrier definition. The ceiling gives
\[
 K\sqrt\epsilon\ge1,\qquad |j|\ge1,\qquad
 |(jK)^{-1}|\le K^{-1}\le\sqrt\epsilon=\epsilon^{1/2}.
\]
The source's band witness is **constant 1, degree 0**, even for varying nonzero integer harmonics. All positive-order point jets of this frozen band multiplier vanish. Verify `selected_inverse_frequency` uses the incoming frequency coherence and the selected strip epsilon, not reference-band epsilon.

Stop after combining this gain, inverse-normal jets and chapter 05's ambient estimate into the finite-order pressure recurrence. Explain both real solves and complex recombination; keep the existing cancellation sign `pi=i c_p/(jK)`. No localization or physical-pressure theorem follows from this native bound alone.

## 5. Numerical recurrence contract (not new Lean records)

Use nonnegative arrays `P_d(S)` of finite polynomials, where `S>=1`, as explicit upper bounds on derivatives. Introduce them only after deriving the underlying fields. This avoids arbitrary unnamed polynomial degrees and supports a reproducible finite calculation. The chapter must prove these elementary rules and then **apply them to the actual formulas above**:

- Sum: `(P+Q)_d=P_d+Q_d`. Bounded bilinear map of norm `L`: `(P star_L Q)_d=L sum_{i=0}^d binom(d,i)P_i Q_{d-i}`. Inner products have norm one in Euclidean spaces; coordinate assembly and operator-column conversion require their norm factors.
- Constant affine map with linear norm `L`: order `d` pullback costs `L^d`. For general composition, use the set partitions of the `d` directions:
  `Comp(P,Q)_d = sum_{pi partition of {1,...,d}} P_{|pi|} product_{B in pi} Q_{|B|}` for `d>=1`; order zero is a separate range bound. This is the full multilinear chain rule, not coordinate multiindices with missing combinatorial factors.
- For `|f|>=b>0`, let `R_0=b^(-1)` and
  `R_d=b^(-1) sum_{i=1}^d binom(d,i) P_i R_{d-i}`. Differentiate `f f^(-1)=1` and prove induction. Sign of `f` need not be positive for this rule.
- On `x in [l,u]`, `l>0`, real-power outer derivative constants are
  `H_{a,d}=|a(a-1)...(a-d+1)| max(l^(a-d),u^(a-d))`, including `H_{a,0}=max(l^a,u^a)`. Use with the composition rule for square roots/inverse square roots and all scalar powers. For inverse powers an upper endpoint is unnecessary once the power is negative.
- Specifically set `Q_d=sum_{i=0}^d binom(d,i)P_i P_{d-i}` for `|N_c|²`. Then `R_0=b_nat^(-2)` and
  `R_d=b_nat^(-2) sum_{i=1}^d binom(d,i) Q_i R_{d-i}`.
  In particular `R_1=b_nat^(-4)Q_1` and
  `R_2=b_nat^(-4)Q_2+2 b_nat^(-6)Q_1²`. Check these as an independent low-order test.
- Weighted propagation: if amplitude/source arrays `U_d,V_d` carry the **single** factor `w P_c`, while normal, motion and action arrays are `P_d,T_d,A_d`, pressure numerator bounds are
  `B = P star (A star U) + T star U + P star V`.
  Then real-source pressure constants are `(R star B)_d`, with weight `epsilon^(alpha+1/2) sqrt(zeta) P_c`. No square of the flat weight occurs; no majorant is differentiated. Use chapter 05's actual endpoint/affine costs consistently before forming these arrays. Real/imaginary extraction into real three-space costs at most `sqrt(3)`; final complex addition pays the sum.

For a uniform order-`N` pair `(C_N,m_N)`, take the maximum polynomial degree through `N` and `C_N=1+` the sum of all coefficients through `N`. Then every array entry is bounded by `C_N S^(m_N)`. List the finite inputs used by this algorithm; numbers depending on arbitrary smooth coefficient seminorms are **explicit relative witnesses**, not evaluated decimal constants. Infinite-order conclusions mean `for every N there exist constants`, not one bound for all orders.

## 6. Two read-only assignments

| Assigned role | Scope and required return | Prohibited shortcut |
|---|---|---|
| **PD-A — actual base and preparation producer** (pending) | P1–P3 and the identity spine. Return standalone derivations for the individual-template bounds, actual weighted-bundle schedule, head/tail sum, inverse-Jacobian numerical triangle, actual `F,G`/error constants, finite-profile cone translation and ordered preparation. Inspect final initializer restriction. List precise allowed finite-profile assumptions and any unresolved edge supplier. | Do not start from `AdmissibleScales`, `Estimates`, `Prepared`, or unproved inverse-coordinate jet bounds. Do not select a new schedule/profile to meet numerical ceilings. |
| **PD-B — quantitative jet/normalization reviewer and producer** (pending) | Independently check §5 and the P2 inverse recurrence, then derive P4. Return explicit finite arrays for normal/motion/shear/frame/projection, `N+1` table, selected pullback costs, inverse-square-normal and constant-1 frequency witnesses, and weighted pressure recurrence. Challenge the interface to PD-A and chapter 05, including norms, domains, lower bounds and circular assumptions. | Do not stop at polynomial-jet closure lemmas, compact smoothness, inverse classes, or a pressure exponent without constants. Do not infer jets from order-zero comparison. |

Both roles read this plan and chapter 05/ledger fully, inspect enclosing source hypotheses and proof bodies at the frozen baseline, and return mathematical reports only. No file ownership, writes, further agents, Lean execution, build or installation permissions. Each report must distinguish **derived**, **source identity**, **source-only finite-profile input**, and **unresolved**; give fully qualified declarations and relative source paths, quantifiers, domains, constants, low-order checks, and a short graduate-reader explanation. Neither a role assignment nor its eventual agent report counts as independent human review.

Later, one author integrates the reports into chapter 06, then a separate reviewer checks the integrated mathematics/source correspondence and cold-reads it without Lean. Do not concatenate reports or mark gates passed before they run.

## 7. Acceptance and separate validation ledger

The reserved new ledger uses explicit `primitive-*` anchors, not new historical NSC/NSA/EUL coverage. It records each chapter claim, supplier, computed recurrence, allowed input, outstanding debt, reviewer identity and disposition. NC-D1/NC-D3/NC-D4 progress is recorded **there**, by links back to the unchanged native ledger; NC-D5 remains open. The historical ledgers are not rewritten to make earlier review appear stronger.

Acceptance requires a reader to reproduce (i) actual head/tail `r^(2h)` recovery, (ii) the nondegenerate inverse-chart recurrence, (iii) the frozen-dilation cancellation of inverse `Q_b`, (iv) the C1/C2 prepared majorant and same-witness threshold order, (v) a first-order normal calculation showing base Hessians, and (vi) order-two inverse-normal and full pressure constants. All six must be worked, not just cited. The final chapter must state exactly which finite coefficient/profile inputs remain outside its proof boundary.

Planned mechanical checks: unchanged `validate.py` for links and historical coverage, `git diff --check`, direct trailing-whitespace/new-anchor checks, HEAD/status inspection, SHA-256 comparison of protected companion files with the supplied manifest, and byte comparison of tracked Lean/config files with the frozen baseline. These are read-only documentation/integrity checks, not kernel or mathematical validation. No missing dependency is to be installed to run them. Lexical declaration checks are not namespace/hypothesis checking.

This planning pass inspected selected actual bodies in BaseChartJets, SlowBorelBase, DiagonalScale, PhysicalCoordinateBounds, FinalSlowBase, PrimaryGeometryAssembly, AlignedProfileSpectralCone, PhaseJetBounds, initializer and inverse-bound suppliers. Further dependencies in the assigned trail are explicit worker tasks, not purportedly audited closure. No chapter, final validation ledger, integration links, independent review, new singularity result, source defect, or refactoring has been delivered by this plan.

**Executed planning checks:** existing validator PASS (mechanical scope only: 13 Markdown files, 513 relative links, unchanged 30 human IDs/30 mapped lemmas and 174 lexical targets); `git diff --check` and new-plan whitespace check passed. The supplied archive hash and all 13 protected companion file hashes matched the manifest. The tracked-diff allowlist contains only the three pre-existing companion changes; the only additional untracked path is this plan. HEAD remains the frozen baseline. The planned full baseline byte audit and mathematical/source-review gates have not been run. No protected file was edited and no formal validation was performed.
