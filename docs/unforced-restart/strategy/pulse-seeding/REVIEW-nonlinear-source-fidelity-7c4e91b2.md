# Independent adversarial review: nonlinear mechanism and source fidelity

## Verdict

**Accept as a conditional, construction-specific finite-pulse diagnostic, with the clarifications below. No positive evidence for unforced B, no common-time smooth datum, and no impossibility theorem for autonomous seeding.** The stop recommendation is justified on these inputs. No successor is launched.

I independently read literal `CALCULATION.md`, `OVERVIEW.md`, `INPUTS.json`, and `CHECKS.json`; the governing paper §§6.1–6.2, 7.1–7.4 and 9.1–9.2; and the source bodies listed below. I did not treat the producer’s checks or source labels as mathematical certification. All evidence was read-only. The only output written is this uniquely named review Markdown. No builds, simulations, Lean files, Comparator attempts, or Git operations were performed.

## 1. Independent interaction calculation

The candidate is the paper’s **same-label second-harmonic return**, not an unrelated Fourier triad. Use its positive-sign phase and actual moving normal

`n = (x0 − v(p F_R+pz G_R), p/R, pz − εv(p F_Z+pz G_Z))`,

with `kp` the construction’s rounded nonzero angular integer. Its physical covector is `k Q^(−1/2)n`, not `kn` in physical units. At the reference midpoint,

`n_ref = Bs(u,K)`,  `a_1,ref = x(er − uK − Ac N)`,

where `N=g0/|g0|`, `K=(-Nz,Nθ)`, `Ac=−c0 sqrt(1+u²)>0`. Thus

`n_ref · a_1,ref = Bs x(u−u−Ac K·N)=0`.

This is not just reference cancellation: in the actual frame the velocity is `x(er−s_a K_a)+y N_a`, and `n_r=s_a|n_tan|`, `K_a·N_a=0`, so `n·a_1=0` exactly before curl repair. The homogeneous radial flux at reference midpoint is `x²(−uK−Ac N)`; its negative N component gives positive shear extraction `|g0|Ac x²`, while diffusion remains present. Neither the normal nor the growing direction is a free choice.

For transverse principal amplitudes at harmonics 2 and −1, the quadratic coefficient at harmonic 1 has fast part

`ik[−(a_2·n)a_{−1}+2(a_{−1}·n)a_2]=0`.

Projection cannot turn this zero into a nonzero growing source. The RHS forcing convention introduces a minus sign on transport; the producer’s `−i P` symbol is consistent with that convention. It would have the opposite sign if called the nonlinear residual itself.

### Exact localized return coefficient

To check what the leading-symbol argument omits, let `a=a_2` and `b=a_{−1}` now be the **complete curl-generated amplitudes**, including cutoff and curl repairs. Write

`D a = (D_r+R^(−1))a_r + D_z a_z`,

`J a = (−a_θ,a_r,0)`,

`T(a,b) = a_r D_r b + a_z D_z b + (a_θ/R)Jb`.

Their exact divergence equations are `2ik n·a=−D a` and `−ik n·b=−D b`. Substituting into the two ordered transport terms gives the following exact coefficient of `exp(ikΦ)` in their symmetrized cylindrical transport:

**`C_1 = T(a,b)+T(b,a)+(D a)b/2+2(D b)a`.**

In particular, the final term has a **plus** sign. This formula follows directly from paper (7.39) and the actual ordered kernel, not a frozen Euclidean projection in place of the localized PDE. It retains cylindrical connections and the evaluated amplitude derivatives. The physical nonlinear residual coefficient is `Q^(−2A−1/2) C_1`. For an NS evolution source it enters with the opposite sign, with pressure elimination still to be handled.

This produces a discriminating estimate. For `a∈W_(1−κs)` and `b∈W_(1/2)`, every displayed term is bounded in `W_(3/2−2κs)`: `D_r` costs at most `κs`, `D_z` is better, connections cost none, and the products retain the paper’s envelope/edge weights. The naive fast bound would have been `W_(1−κs)`. Thus solenoidality really removes the half-power fast loss in this proposed return channel, even though its complete coefficient need not vanish.

Conversely, no inspected identity computes a nonzero growing projection of `C_1`, its sign, or a lower bound for its integrated response. Amplitude derivatives and connections may cancel further; such exceptional cancellations only strengthen this upper bound. The source does not exhibit an independently supplied second-harmonic parent.

### Temporal response and order

The primary’s only harmonics are ±1, including after curl. Its quadratic terms have 0 and ±2, never ±1. Angle-independent coefficients and cylindrical connections preserve that selection rule. For its nonzero quadratic source, Lemma 9.2 gives `W_(1−κs)`. The zero-entry modal inverse in Proposition 7.2 preserves that exponent because

`||V_m(v,w)|| ≤ C P(v)/P(w)`.

The source has `P(w)`; Duhamel integration therefore costs a polynomial in `S`, not `exp(G*)`. For `m=2`, the exact extra propagator factor is `exp(−3∫_w^v d)`. This is additional damping, but not a uniform exponentially small factor on the whole Duhamel integral: sources arbitrarily near `v` have arbitrarily short damping intervals. The producer does not need such a stronger claim.

After cutoff and curl, the second-harmonic response remains in `W_(1−κs)`; its curl correction is in `W_(3/2−2κs)`. Pairing the complete response with the complete primary gives the coefficient above and then a fundamental modal response in `W_(3/2−2κs)`. Relative to the primary’s **natural upper amplitude scale**, this gains `ε^(1−2κs)` times fixed powers of `S`. On a compact interior region with quantitative primary lower bounds, it is also a genuine small ratio to the primary. It is not a pointwise ratio at cosine nodes or arbitrarily small masks.

This is perturbative feedback from an existing primary. It cannot be its independent origin. At any fixed finite correction order it is too small at the natural peak scale to replace the primary by this route. It is not a theorem about an infinite autonomous cascade, a full-PDE response, or a comparison with the exponentially tiny entry coefficient.

Distinct constructed wave labels cannot provide the missing overlapping parents: paper Lemma 6.1 separates their enlarged **absolute-torus preimages** whenever slow supports intersect. The separation survives derivatives and physical evaluation. Merely separating rectangles on different band tori would not suffice; the actual paper establishes the stronger statement. This does not eliminate nonlocal pressure effects, mean-mediated coupling, or overlapping waves outside this selected construction.

## 2. Equations (5)–(10) and normalization

I find the finite-dimensional deduction sound under the stated actual coefficient bounds.

* With `s=u/2+uv/L`, direct integration gives the stated arsinh formula for Λ and `7u³/24` in D. Since `λ−d_ref>0` before `L/2`, `G*=Λ−D>0`.
* Differentiation gives `−g'=(λ0 u/L)s[(1+s²)^(−3/2)+2(1+u²)^(−3/2)]`. The producer’s `a_u,b_u` are valid lower/upper bounds on the whole slot. Integrating twice gives (6), including `G*` between `a_u L/8` and `b_u L/8`.
* The invariant Riccati strip is valid for `e≤λ_min/8`. The upper energy bound controls the **operator norm**, while the actual growing column supplies its matching lower bound. Neither direction is being inferred from an upper bound alone.
* The trace is `−2d+tr E`; absolute damping comparison and `L/S=O(1)` imply `det V=exp(−2D+O(1))`. Combining this with the largest singular value gives (8). The SVD inverse formula (9) and strip width (10) follow. Bounded frame maps preserve exponential scales, though the exact Euclidean SVD identity is in modal coordinates.
* (10) restricts an arbitrarily prescribed full endpoint vector at a tiny budget. It does not require exponential precision of the initial direction for every acceptable covariance. The draft correctly distinguishes forward filtering and covariance tolerance.

The paper’s physical residual normalization is `Q^(−2A−1/2)`; physical time differentiation corresponds to `Q^(1+h)∂t`. Native `rawVelocity_hasDerivAt` explicitly cancels the factors `L` and `1/L` from `normalizedPulse(p,v/L)`. Viscosity is `εk²|n|²`, not negligible, and no missing factor of L appears in the finite-slot equation.

The seed is literally `P(0)e_+`, not a zero-data homogeneous solution. Multiplying by the one slot cutoff gives principal residual `+ψ' a_h` with the displayed fixed amplitudes. Its physical sign and the paper’s compensating `−f_m` convention agree. This deletes neither the slow derivatives nor pressure/curl/localization residuals.

Covariance uses the cosine factor 1/2 and the auxiliary Jacobian `c_i dv`; Gaussian mass is of order `sqrt(L)`, but `c_i≈1/L`. Consequently each column has size `L^(−1/2)`, the positive squared amplitude has size `sqrt(L)|T|`, and the scalar amplitude has size `L^(1/4)sqrt(|T|)`. The producer’s seed calibration passes this check. It is an amplitude/envelope statement, not a lower bound for the oscillating physical velocity at every angle.

## 3. Storage, common-time smoothness, and limits

Section 4 is appropriately conditional. In the unchanged-carrier heat model, `|ξℓ|²≈Q^(−1−h)` and the backward cost `exp(Δ|ξℓ|²−G*)` does overwhelm the favorable `exp(−cℓ²)` seed for a fixed positive wait and a quantitatively nondegenerate sequence of targets/masks. Actual finite-slot estimates cannot be continued to a macroscopic earlier time by substituting a large negative v.

At one fixed `t0<1`, `q≥1−t0` excludes all sufficiently late constructed dyadic supports. Their zero traces are not preinstalled uncut seeds. Neither fact rules out earlier low-frequency storage, later shearing, transport, pressure coupling, or nonlinear creation along another unforced trajectory.

The local seeds and supported cutoff tails can pay every **fixed** derivative loss. This is compatible with local smooth zero extension; it is not a compatible infinite sequence at one common time. An all-stage construction would additionally need one periodic solenoidal trace, summability/derivative control after common-time propagation, compatible boundaries/tails and the full autonomous nonlinear equation. No such estimate appears here. No uniform-in-correction-stage bounds have been established. There is no initial-data obstruction to all possible B counterexamples in this calculation.

## 4. Selected-witness routing and source debt

The crucial source route survives literal inspection:

1. `CorrectionInitialization.lean:3906–3950` stores `prepared` in `ActualPrimary.Choice`, selected via `PrimaryTargetBounds.exists_constructed_bounds`; `phases`, `covariance`, and later `rawVelocity` use that same preparation.
2. `PrimaryGeometryAssembly.lean:244–362` exposes the needed `Prepared` fields and defines `family` from **any such stored preparation**. Its eigenpair is profile-derived, `theta=0`, and `phaseSign 0=1`. Reconstructing this family is not replacing the selected witness.
3. `BasePhaseGeometry.lean:842–965,1061–1065` proves both modal errors and **absolute** damping error for that family and identifies its construction frame by `rfl`. The one-sided field in general `PhaseConstruction` would not alone prove the determinant asymptotic. The producer correctly avoids that trap.
4. `PrimaryPulseBounds.lean:549–658,1828–2000` defines the nonzero-seed fundamental and bridges the canonical interval solution, cutoff covariance integral, and normalized pulse equation. `ActualPrimaryDynamics.lean:57–122` retains native carrier/slot hypotheses and gives the actual viscosity.
5. `ActualPrimaryCovariance.lean:355–399` gives double-average stress with `partitionFactor`. It is not an arbitrary pointwise physical covariance theorem.
6. `HarmonicWaveInteraction.lean:192–360` contains derivatives, cylindrical rotation, and convolution with `m−j`. Its class theorem requires actual mode solenoidality and a finite harmonic range; it does not assert nonzero projected response. The paper, not merely this generic interface, supplies the construction-specific curl and support hypotheses used above.

I independently rehashed all 26 entries in `INPUTS.json`: **zero mismatches**. I read the inherited `REVIEW-INPUTS.json`; its export/pin association agrees. This authenticates byte agreement with the supplied manifest, **not Git-object provenance**. No Git operation was used. Cross-revision identity of classical choices, the global paper proof, historical software certificates and numerical-array transfers were not independently certified by this review. The finite-slot SVD argument remains human mathematics, not a located or checked Lean theorem.

## 5. Concrete clarifications requested

These do not overturn the disposition:

1. **Make the cutoff-and-curl step explicit between §5 steps 2 and 3.** Tangency of a raw modal response is not exact solenoidality of its localized field. The improved class bound for the complete interaction uses the repaired fields. State separately that cutoff tails remain additive residuals.
2. **Qualify lower-bound language along band sequences.** “Nonvanishing target/masks” alone does not prevent values tending to zero arbitrarily fast. For the divergent storage preload or an actual relative-response estimate, specify a sequence in a quantitatively nondegenerate interior region (or an explicit lower bound). Otherwise state only the upper-scale comparison. Likewise (7) is a modal amplitude, not a pointwise cosine lower bound.
3. **Keep the harmonic-2 damping factor inside its propagator integral.** It is `exp(−3∫_w^v d)`, not a uniform extra `exp(−cL)` gain for every forced response.
4. **Do not promote symbolic selected-family analysis into an extracted active numerical witness.** The native carrier/positive-stress/mask assumptions are essential. A numbered label and effective constants were not extracted; the draft already acknowledges this debt.

## Strongest valid inference

The selected family has an exponentially cheap, stress-calibrated uncut finite-slot seed and an exponentially selective small-budget inverse endpoint problem. Its immediate self-interaction has no fundamental, its same-label return loses the fast leading coefficient and is perturbatively smaller at fixed order, and its separated constructed labels cannot supply overlapping parents. The unchanged-carrier heat preload fails under its stated storage hypothesis.

**None of these findings constructs autonomous all-stage production or proves late force necessary.** They support stopping this particular force-deletion/preload campaign, not declaring B impossible or refuted.

### Reviewed producer byte identifiers

* `CALCULATION.md`: `d45cd18665ac68a965bb145c37fe65120e334f31476ce94b074e6c50d23a299d`
* `OVERVIEW.md`: `bb1907fb8e778acb56bfc99767e7970b1bee162cd3b4bfb50834ba7df5e88ee6`
* `INPUTS.json`: `9555b00ba3744127ab68ece12b4d501da9f9d1d816ded0bffdd81de403a2a075`
* `CHECKS.json`: `568aaa427b926e96a64288f7e98d2565c86db32e428f34712da8318681154e01`

Paper and Lean paths above are under `/home/velvet/upstream-strategy-f9e8bc5-9d96jtuy/papers/navier-stokes.txt` and `/home/velvet/upstream-strategy-f9e8bc5-9d96jtuy/upstream/NavierStokes/`, respectively.
