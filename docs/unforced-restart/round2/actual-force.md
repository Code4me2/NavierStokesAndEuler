# Actual-force integration update — L² cell budget checked; strong threshold OPEN

The integrator added `Research/UnforcedRestart/Round2/ActualForce/Main.lean` after settled-worker handoff: `cubeIntegral_constant`, `cell_energy_le`, `candidate_shift_force_continuous`, and `candidate_cell_budget`. These pass strict cached-dependency elaboration and comprehensive standard-axiom audit. The last two consume actual `CandidateProperties`, not a separately closed selected-witness specialization. They prove shifted force continuity and a single C>0 uniform on fixed `[0,H]`, with actual squared cell norm g≤C², its time integrability, and `∫₀ˢ g≤C²S`. No spatial supremum/time-integral swap is assumed. This supplies the new periodic PDE theorem's actual forcing interface.

The stronger Sobolev, projected-trace, mean-zero and quantitative-threshold analysis below remains **ordinary analysis, not new Lean acceptance**. In particular no Bessel-H³ norm identity or strong stability threshold was kernel-checked. See [REPORT.md](REPORT.md) for the norm-convention reconciliation and growth comparison. Final evidence: `Research/UnforcedRestart/Round2/Integration/runs/20260909T224305Z/`; clean source provenance remains blocked at upstream tracked build traces, not snapshot approval. No A/B claim.

---

# Historical actual-force handoff — O8 quantified membership, threshold OPEN

Owner: **actual-force**. Fixed viscosity **1**. No A/B claim.

## Status and acceptance

Read Round2 PLAN, round-one PLAN, FINAL-REPORT, OBLIGATIONS, MANIFEST.md, frozen validator, force-budget source/report, and the snapshot handoff. The read-only/tamper-evident snapshot is **not filesystem-immutable**. Its gate has not been declared cleared here. No source build or Lean process was launched; no focused slot was assigned by the coordinator. No shared artifacts were written.

**Accepted new Lean manifest: empty (not a validation PASS). Axiom checks: not run.** No `.lean` draft, holes, conjectural theorem, or uncompiled mathematical export is submitted. The progress below consists of rigorous ordinary-analysis deductions from identified source contracts, with proofs and explicit constants, **not newly kernel-checked results**. A small exact-arithmetic/source-preservation script is delivered separately; it is not a proof oracle or PDE experiment. Formal finite-volume/Sobolev adapters remain a compilation-stage deliverable, blocked on the coordinated slot. This handoff does not claim completion of that requested formalization.

New files:

- `Research/UnforcedRestart/Round2/ActualForce/budget_checks.py`
- its `out/{preservation.log,budget_checks.json,budget_checks.stderr,budget_checks.exit}`
- this report.

## 1. Actual field, support, and quantifiers

Source route (all baseline):

- `ActualCandidateAssembly.lean:1016–1074`, `Witness`, `witness`, `selected_witness`: one selected schedule and the actual potential/direct/pressure sums. Periodic force and compact force are different existential components. The terminal periodic jets are exposed; the compact component of this public witness exposes only `R3CompactCandidate.Properties`.
- `MixedPeriodicAssembly.lean:371–415`, `exists_compact_candidate`: constructs the **specific** compact force `CandidateFromLimits.force` from `U = curl(η A) + η B`, `P = η PSum`; returns global force smoothness, cube support and terminal jets. Its proof uses the smaller actual cylinder support.
- `SpatialLocalization.lean:30–111`: `η(x)=cutoff(16(x₀²+x₁²)) cutoff(4x₂)`, fixed support
  `K={x : x₀²+x₁²≤1/16, |x₂|≤1/4}`. Its Euclidean volume is **V=π/32**, and the elementary containing-cube alternative is **V≤1/8**. The unit cell has volume 1. These are standard Lebesgue geometric calculations, not new Lean volume theorems.
- `CandidateFromLimits.lean:83–123,211`, `force`, `force_smooth`, `force_eq_activated_residual`, `force_boundary_jets`, `force_zero_outside`: force equals the activated viscosity-one residual at **every x and 0≤t<1**, is globally smooth, and keeps K at all times. Shutdown is only at `t≥2`.
- `MixedPeriodicAssembly.periodize_jets`, `periodized_navier_stokes`, `candidate_of_periodization`: actual periodic force is separated periodization. Translating K by the integer lattice gives disjoint supports, including derivative supports. Hence its cell spatial derivative integrals equal the compact ones. One may use a centered cell, or the repository cube by periodic translation/integration; this is not an integral over all R³ of a periodic function.
- `CompactSpatialForceDecay.jet_zero_outside`, `jet_decay`; `PeriodicForceDecay.futureJet_continuous`, `futureJet_decay`; round-one `ActualForcingBudget.compact_jet_bound`: all future full within-jets have bounds `||J_m(t,x)||≤C_m`, with C_m positive, independent of t,x.

**Quantifier boundary:** fix one selected witness, its schedule, and its h (0<h<1/2), then choose the finitely many C_m required. They do not depend on restart horizon S or on an index of a finite partial sum: they bound the final infinite-sum force. This does **not** bound every partial-sum force uniformly in stage, and does not give constants uniform over h, schedules or other witnesses. The witness contract by itself only gives an unspecified compact support set; the explicit π/32 improvement uses the stronger construction route, not arbitrary `Properties` with an invented support volume.

For presingular work improve the existential constants to

`C_m^* = sup_{(t,x)∈[t0,1]×K} ||D^m_(t,x) f(t,x)||`.

These are finite by actual smoothness and compactness, do not use any future Borel extension beyond its fixed boundary trace, and work simultaneously for every `0<S<H=1-t0`. The nonnegative maximum can be zero; add 1 only if a positive constant is needed. For periodic jets maximize on the compact cell instead. Below C_m denotes either such slab maxima or the coarser round-one global bounds. There is no extracted numerical value for any C_m.

## 2. Actual mixed norms and explicit strong norms

Take t0>0 so full derivatives and future within-jets agree; no new-zero derivative identification is hidden. A spatial derivative word I of length j is evaluation of the full j-tensor on unit spacetime vectors `(0,e_i)`. Thus

`|∂_I f(t,x)|≤C_j`, and `∂_I f(t,x)=0` off K.

The derivative-support statement follows from local vanishing off closed K, including its complement neighborhoods, not from pointwise vanishing alone. All these derivatives are continuous. For any measurable interval I⊂[t0,1] of length ℓ and 1≤p,q≤∞,

`||∂_Iword f||_(L^q_t L^p_x) ≤ C_j V^(1/p) ℓ^(1/q)`,

with the usual zero reciprocal for infinity. Finite p follows by integrating the pointwise bound on K; the essential supremum bound handles p=∞; scalar integration in time proves the q bound. Compact support/continuity supply measurability, including continuity in the L^p norms; the uniform time-derivative bound supplies L∞-norm continuity as well. For periodization the same sharper V holds by disjoint translates. Without the explicit support bridge use volume 1 and periodic C_j.

In particular these are **integrals of actual spatial norms**, not the round-one expression `∀x, ∫|J_m(t,x)|dt`. No interchange of supremum and integration is invoked.

### A specified Sobolev convention and exact derivative counts

Use the Bessel H^k norm with Fourier frequencies 2πξ on R³ or 2πn on the unit torus. For smooth supported/periodic vector fields, Parseval and the binomial identity give exactly

`||f||_Hk² = Σ_{j=0}^k binom(k,j) Σ_{Iword∈{0,1,2}^j} ||∂_Iword f||_2²`.

The vector norm includes its three components; do **not** add another factor 3 for output components after bounding the vector-valued full tensor. There are 3^j ordered input words. Consequently define

`B_k² = V Σ_{j=0}^k binom(k,j) 3^j C_j²`.

Then, on this fixed restart's entire presingular interval,

`||f(t)||_Hk ≤ B_k`,  `||f||_(L^q([t0,t0+S];H^k)) ≤ B_k S^(1/q)`.

Explicitly:

- `B_2² = V(C_0² + 6 C_1² + 9 C_2²)`;
- `B_3² = V(C_0² + 9 C_1² + 27 C_2² + 27 C_3²)`.

These are genuine evaluation-relevant force spaces, not just L². For example the Fourier Cauchy–Schwarz proof gives on R³

`||z||∞ ≤ (8π)^(-1/2) ||z||H²`,

since `∫_(R³)(1+4π²|ξ|²)^(-2)dξ=1/(8π)`. On the unit torus one valid explicit constant is

`||z||∞ ≤ [1+1/(4π²)+1/720]^(1/2) ||z||H²`.

Proof: Fourier inversion and Cauchy–Schwarz reduce to the sum of `(1+4π²|n|²)^(-2)`. The max-coordinate shell r≥1 has `24r²+2` points and |n|≥r, giving a bound `1+(24ζ(2)+2ζ(4))/(16π⁴)`. This proves the stated constant, including the zero mode. Smooth fields suffice; extension by density gives the continuous H² representative. These are conventional analysis proofs here, not assertions about a preexisting Lean H² definition. Velocity error H² evaluation is relevant to O9; it does **not** assert that the PDE error enjoys that norm bound. No R³ support is assigned to the viscous comparator.

## 3. New terminal trace estimate: what interval smallness really measures

One extra full derivative yields a uniform **strong-norm Lipschitz estimate**. Set

`D_k² = V Σ_{j=0}^k binom(k,j)3^j C_(j+1)²`.

The full (j+1)-tensor bounds `∂t ∂_Iword f`; integrate this derivative on the fixed segment between t and 1 and apply the same finite derivative sum (or Bochner FTC) to obtain

`||f(t)-f(1)||Hk ≤ D_k(1-t)`.

Let P be the Leray projector in the relevant Fourier H^k space. Its multiplier is an orthogonal projection at each nonzero frequency, so its H^k operator norm is at most **1**; on the torus retain the zero mode. Put `F_*=||P f(1)||Hk`. Then

`| ||P f(t)||Hk - F_* | ≤ D_k(1-t)`.

For 0<ℓ≤H this proves the two-sided **actual mixed-norm budget expansion**

`| ∫_(1-ℓ)^1 ||P f(t)||Hk dt - ℓ F_* | ≤ D_k ℓ²/2`.

If F_*>0, for ℓ≤F_*/D_k (when D_k>0), the integral is at least ℓF_*/2. If F_*=0, it is at most D_kℓ²/2. If D_k=0, the integrand is constant and the formula is exact. Higher powers require vanishing **whole spatial solenoidal time traces**, with corresponding higher-derivative bounds; flatness at a single spatial point does not supply them.

This separates an uncomputed but concrete terminal quantity F_* from unspecified smoothness maxima. Neither F_*=0 nor F_*>0 is established for the selected force. The smooth extension and `JointResidualLimits.boundaryLimits` identify the actual trace, not its solenoidal norm. These estimates apply on all of K/the whole periodic cell, including the localization annulus.

For one fixed restart the removed budget is `∫_t0^(t0+S)||P f||Hk`, bounded by B_k S, with a finite limit as S↑H. It is **not** a shrinking terminal tail and need not tend to zero. This distinction is essential when reusing short-interval estimates.

## 4. Solenoidal/gradient freedom: actual mean compatibility

A useful deduction beyond generic torus warnings: **the actual presingular periodic force has zero spatial mean.** Here is the complete ordinary-analysis proof, using construction hypotheses rather than assuming the conclusion.

The compact reference u is smooth, divergence-free, and supported in the same K on any closed presingular slab. For each i,

`∫u_i = ∫div(x_i u)=0`

by compact support and div u=0. Its time derivative has the same support on interior time slices, so differentiation under the integral is justified by slab compactness. For its compact pressure from the construction, integrate its viscosity-one PDE:

`∫f = ∂t ∫u + ∫div(u⊗u) - ∫Δu + ∫∇p = 0`.

Each boundary integral vanishes because the corresponding fields are smooth and compactly supported. Periodization preserves these integrals on a cell. Equivalently integrate the periodic PDE with both pressures/velocities periodic. Therefore the periodic f has mean zero for t0≤t<1; smoothness extends this to t=1. No claim is made for the arbitrary post-terminal extension at t>1. The argument needs the specific compact pressure or the periodic pressure contract, not an unsupported pressure-decay premise from `Properties` alone.

Thus the usual constant-vector harmonic obstruction is removed for **this** presingular periodic force. On each fixed closed slab, exact removability reduces to the still unproved condition `curl f=0` everywhere: Fourier modes then give a smooth periodic potential with f=∇φ, and the corrected pressure is **p−φ**. For nonzero n, solve `φ̂(n)=( (2π i n)·f̂(n) )/(-4π²|n|²)`; the mean is set to zero. Smooth slab dependence follows by rapidly decreasing Fourier coefficients and the bounded elliptic multiplier. This is not a constructed vanishing-curl result.

In fact on this mean-zero torus class, Fourier algebra gives for k≥1

`||P f||Hk ≤ sqrt(1+1/(4π²)) ||curl f||H^(k-1)`.

At frequency ξ=2πn, `|P f̂|=|ξ×f̂|/|ξ|`, and `(1+|ξ|²)/|ξ|²≤1+1/(4π²)`. This is a possible smaller forcing diagnostic; no actual curl smallness is known. Projection is not assumed bounded in L∞, nor support-preserving on R³. Its H^k contraction is why the prior strong-norm budgets are legitimate upper bounds despite pressure freedom.

At viscosity one the actual identity to inspect is

`curl f = ∂t ω + u·∇ω − ω·∇u − Δω`,  `ω=curl u`.

Viscosity remains present. Origin-flat f does not annihilate this identity on an entire domain. No compact-support transport argument for comparator vorticity is valid.

## 5. Activation, localization, and exterior trace

On 0<t<1 write u=θU, p=θP. Direct product calculus yields

`f=θ R_1(U,P)+θ' U+(θ²−θ) DU(U)`.

`TimeLocalization.activatedVelocity_eq_late` and the switch lemmas make θ=1 for t≥3/4. For a fixed earlier t0 the transition contribution is retained; choosing t0>3/4 once removes activation terms, not the spatial cut residual.

Write W=curl A+B and b=∇η×A, so U=ηW+b. The pressure term is `∇(ηP)=η∇P+P∇η`; the latter cannot alone be discarded as a gradient because P varies spatially. Expanding R(U,ηP) gives the explicit localization remainder relative to ηR(W,P):

`∂t b − 2Σ_i(∂iη)∂iW − (Δη)W − Δb + P∇η`

`+ (η²−η)DW(W) + η(W·∇η)W + η DW(b) + (b·∇η)W + Db(ηW+b)`.

This follows by expanding Δ(ηW), DU(U), and the pressure product. It vanishes on the plateau (η=1, b=0), and outside the support, but not by any cited identity on the intervening annulus. Estimating k spatial derivatives of this remainder requires, among other terms, k+2 derivatives of A from Δb, up to k+3 derivatives of η, and time derivatives of A from ∂t b. Estimating the uncut term ηR(W,P) separately can require k+3 derivatives of A through Δ(curl A). The actual residual-jet convergence is a better source of finite C_k than a triangle estimate of singular summands, which can destroy essential cancellation. No quantitative annular seminorm was extracted.

`JointResidualLimits.lean:126–148` defines terminal tensors as zero at the origin and as derivatives of an actual one-sided extension for x≠0. `CandidateFromLimits.force_boundary_jets` transfers these identities. Smooth infinite flatness controls local joint neighborhoods near (1,0), and lattice copies after periodization; it says nothing forcing the entire exterior trace or its curl to vanish. Both zero and nonzero exterior solenoidal trace remain possible on the evidence inspected.

## 6. Amplification comparison — exact scalar diagnostic, not an actual PDE estimate

The source-backed axis exponent is α=1/2+h with 0<h<1/2: see `BaseResidual.baseVelocity_at_origin`, `FinalSlowBase.leading_origin`, `axis_tendsto`, and the eventual assembled-field route in the growth worker's assignment. Keep h, t0 and H fixed. The reference target is speed `j_*(H-S)^(-α)` (j_*>0); this report does not newly formalize the assembled equality or estimate reference gradients from that speed alone.

Suppose a separately proved linear strong comparison had `N'≤K N+F`, N(0)=0. Only as a diagnostic, set K(s)=κ/(H-s), κ≥0, and use F≤M=B_k. Exact integration gives

`N(S) ≤ M [H^(κ+1)−(H−S)^(κ+1)] / [(κ+1)(H−S)^κ]`.

The evaluation upper bound divided by the reference speed is at most

`(C_eval M/j_*) [H^(κ+1)−(H−S)^(κ+1)]/(κ+1) · (H−S)^(α−κ)`.

For κ<α this sufficient bound tends to zero; for κ=α its limiting constant must beat the chosen relative tolerance; for κ>α the bound fails that test for M>0. No κ or linear strong comparison is established for the actual candidate; nonlinear bootstrap terms and existence coverage cannot be omitted. Failure of this sufficient upper bound is **not** proof of actual error divergence.

Even if F vanishes identically after H/2, accumulated forcing before H/2 is subsequently multiplied by `(H−S)^(-κ)` in this model. Thus high-order terminal trace vanishing alone does not erase earlier weighted work for a fixed restart. Short-tail powers from §3 are useful inputs, but not the needed horizon-wide weighted threshold. No variation of ν, h or t0 with S, rescaled-viscosity inference, or numerical estimate of actual construction constants is used.

## 7. Assessment and smallest missing inputs

- **GO (ordinary analysis, formal adapters pending):** actual L^q_t H^k membership, explicit finite-volume/derivative-count constants, projection contraction, strong terminal trace modulus and its two-sided integrated asymptotics. Uniform over S for one fixed selected force. This closes the *mathematical packaging* gap beyond fixed-point time integrals, not clean Lean acceptance.
- **OPEN exact route O3:** presingular periodic mean compatibility is derivable as above. Smallest remaining construction-specific target is actual `curl f=0` on one whole terminal slab (equivalently P f=0 here), not a pointwise jet condition. No evidence proves it or disproves it.
- **OPEN perturbative O8:** the candidate meets strong-norm **finiteness** and fixed-tolerance short-interval tests. It meets **no verified meaningful stability threshold** at fixed ν=1. Missing: quantified C_0,…,C_(k+1), actual projected terminal trace or curl seminorm, and the reference-dependent viscous H^k stability constants/weighted tolerance from O7, with one comparator and horizon coverage. Existence of finite constants cannot decide their numerical comparison.
- **NO-GO inference:** unweighted short budgets, origin flatness, late activation shutdown, or smooth force membership alone cannot imply the requested growth transfer. This is a limitation of those deductions, not a nonexistence/blowup theorem.

## 8. Commands, evidence, and preservation

All commands ran from `/home/velvet/worktrees/unforced-restart-20260909T202951Z` unless noted. No compile command succeeded or failed: **none was executed**. No attempted uncapped fallback, cache fetch, build, validator rerun, commit, push, dependency or protected-source change.

Executed preservation commands (recorded with statuses in `out/preservation.log`):

```sh
git rev-parse HEAD
git diff --exit-code 597692fa5d55e07d810b2d96ead1a67972585425 --
git diff --cached --exit-code
(cd /home/velvet/research-snapshots/unforced-round1-20260909T221339Z && sha256sum -c SHA256SUMS)
```

HEAD matches baseline; both diffs and the checksum check exit 0. This verifies the seal, not filesystem immutability or regenerated binary provenance.

Exact computation command, exit **0** (`out/budget_checks.exit`), empty stderr:

```sh
python3 Research/UnforcedRestart/Round2/ActualForce/budget_checks.py \
  > Research/UnforcedRestart/Round2/ActualForce/out/budget_checks.json \
  2> Research/UnforcedRestart/Round2/ActualForce/out/budget_checks.stderr
```

The script verifies the externally specified SHA256SUMS digest and byte-hash equality of every archived regular file against its present worktree counterpart (paths/count in JSON); it extracts nothing. It checks exact integer Sobolev word coefficients and rational volume/embedding coefficients. No floating-point experiment, residual sampling, unknown-constant substitution or heuristic candidate computation is presented. The Fourier and FTC arguments above are written mathematical proofs, not consequences certified by Python assertions. The full old generated-artifact inventory is not rehashed by this script. Source hashes for this deliverable and final tracked-diff evidence are retained separately in the owned `out/` directory.
