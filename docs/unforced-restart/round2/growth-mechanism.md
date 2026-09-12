# Round2 growth-mechanism — source-backed analysis, not Lean acceptance

**Assessment:** select periodic H³ velocity comparison as the most defensible *finite-slab analytic target*. The ordinary global-norm Gronwall envelope is not a credible endpoint growth-transfer certificate without a substantial refinement. Vorticity/strain gives a concrete reason to investigate that refinement, but no preserved viscous invariant or instability theorem has been obtained. **O7–O9 remain open; no A/B claim.**

Owned outputs:

- `docs/unforced-restart/round2/growth-mechanism.md` (this report).
- `Research/UnforcedRestart/Round2/GrowthMechanism/source_audit.py` (source-only evidence tool).
- `Research/UnforcedRestart/Round2/GrowthMechanism/out/source-evidence.json`.

New accepted Lean files/declarations: **none**. New axiom audits: **none**. No uncompiled Lean draft or proof with holes is submitted. The computations below are exact pencil-and-paper deductions with hypotheses stated, **not freshly kernel-checked results**. Existing declarations are source citations, not new acceptance or an independent audit of the baseline construction.

## 1. Fixed contract and source evidence

Fix one `0<t0<1`, `H=1-t0`, one comparator with datum `a=u(t0,·)`, and all restrictions `0<S<H`. Write `τ=H-s`, `U(s,x)=u(t0+s,x)`, `w=U-v`, `r=p(t0+s,·)-q`. Viscosity is exactly one:

```
∂s w + U·∇w + w·∇U − w·∇w + ∇r = Δw + f_r,
div U = div v = div w = 0,       w(0)=0.
```

This is equivalent to the PLAN's `−DU(w)−Dw(v)` decomposition. Both velocities and both pressures must be smooth and unit-periodic on each closed slab. A hypothetical global arbitrary-datum existence assumption can supply the same v on all slabs; this report does not construct it. No zero-datum solution wrapper is used.

Read round2 PLAN, round-one PLAN, FINAL-REPORT, OBLIGATIONS, manifest and complete frozen validator. Independently checked the supplied snapshot SHA256SUMS digest and its eight entries. The source-only script additionally compares 18 cited baseline sources with `git show` at `597692fa5d55e07d810b2d96ead1a67972585425`, and 37 archived source/document/tool files with their frozen copies. This is **not** a fresh inventory of 162277 artifacts or a rebuild.

Snapshot seal remains read-only/tamper-evident, **not filesystem-immutable**. No source build or focused Lean invocation was launched; no coordinator compile slot or explicit snapshot-gate clearance was available to this worker. No shared build writes, original-checkout access, commits, pushes or global changes.

## 2. Actual core: velocity growth is accompanied by an explicit saddle strain

Use `σ=(x0²+x1²)/2`, axial coordinate z=x2, and denote the stream factor by **B** (to avoid confusing it with the restart horizon H), swirl potential by K. `AxisymmetricFields.lean`, `velocity_zero/one/two`, proves the actual Cartesian curl formulas

```
u0 = −x0 B_z/2 + x1 K_σ,
u1 = −x1 B_z/2 − x0 K_σ,
u2 = B + σ B_σ.
```

For smooth B,K, differentiating at `(0,0,z)` gives, with derivative matrix `(∂j ui)`, the exact matrix

```
Du = [ −B_z/2    K_σ       0 ]
     [ −K_σ     −B_z/2     0 ]
     [    0        0      B_z].
```

Consequently `S=(Du+Duᵀ)/2=diag(−B_z/2,−B_z/2,B_z)` and `ω=curl u=(0,0,−2K_σ)` on the axis. Swirl contributes a skew rotation, **not** strain. These derivative identities require two profile derivatives in a neighborhood, not just equality of velocity at one point.

### Exact base specialization

Source chain:

- `CoordinateAlgebra.lean`: `A(h)=1/2+h`, `D(h)=1/2-h`; hence A+D=1.
- `SimilarityCoordinates.lean`: `τ=q−z²q^(2h)`, `η=z/q^D`; at z=0, `q=τ`, `q_z=0`, `η_z=τ^(−D)`.
- `NaturalCore.physicalQ_at_zero_z`, `physicalEta_at_zero_z` and `BaseResidual.physicalChart_origin` fix the physical normalization.
- `SlowBorelBase.lean:1006–1045`: B is the physical profile of weight −A with coefficient `average(d.axial j)`; K has weight −h with coefficient `−C⁻¹ primitive(d.phi j)`.
- `EntranceAlignedBase.modulated_leading_axis` gives `d.axial 0 (0,η)=4η+j_*`; `modulated_positive_axis` gives zero positive-order axial and phi axis values for |η|≤1.
- `BaseResidual.slowSum_eq_leading_of_positive_zero` removes every positive stage at these axis values, irrespective of the cutoff schedule. `ProfileHistories.average_at_axis` supplies the stream's axis value.

Thus for the **final slow base**, in a neighborhood along the axis at each presingular origin,

```
B(t,0,z)=q^(−A)(4η+j_*),
B(t,0,0)=j_* τ^(−A),       B_z(t,0,0)=4/τ,
S(t,0)=diag(−2/τ,−2/τ,4/τ).
```

The coefficient 4 is not an invented strain estimate: it is the actual leading-axis slope. This derivation is new Markdown analysis, not an exported Lean matrix lemma. `FinalSlowBase.leading_origin` and `axis_tendsto`, using `BaseResidual.baseVelocity_norm_at_origin`, already verify the positive j_* and the base speed law at the origin.

Similarly, `partialS_physicalProfile` and the radial primitive identity, followed by positive phi axis zeros, give

```
K_σ(t,0,0)=−C⁻¹ d.phi 0 (0,0) τ^(−1−h),
ω2(t,0)=c_phi τ^(−1−h),   c_phi=2 C⁻¹ d.phi 0 (0,0).
```

`modulated_zero_fields` identifies `d.phi 0=C*v.profiles.f`; with C≠0 this gives `c_phi=2*v.profiles.f(0,0)`. No independently established numerical value or nonzero lower bound for c_phi is used here. The strain result does not depend on c_phi being nonzero.

### Transfer boundary: base versus selected field

`GermCandidateAssembly.origin_eventually_base` identifies the actual mixed velocity's **value** at the origin eventually; `MixedPeriodicAssembly.cutVelocity_origin`, `periodicVelocity_origin`, and `TimeLocalization.activatedVelocity_eq_late` (t≥3/4) preserve it. `ActualCandidateAssembly.witness/selected_witness` consumes the actual stage support and axis-zero proofs and selects one schedule, not one schedule per time. This traces the eventual selected speed amplitude and exponent, but no new closed selected-axis wrapper is submitted here.

**Do not differentiate a point-value identity.** `MixedAxisPreservation.origin_eventually_base_germ` is a stronger germ theorem for its PotentialStage/AngularSupport inputs; `MixedPeriodicAssembly.periodicVelocity_eventuallyEq` and `cutVelocity_eventuallyEq` also preserve germs on the plateau. These are plausible ingredients for transferring all base axis jets. The full identification of that germ theorem's inputs with the selected witness has not been assembled here. In particular this report does **not** label the displayed strain matrix a newly verified selected-candidate jet identity.

### What the geometry does and does not suggest

There is axial extension and transverse compression at rate 1/τ, with potentially faster swirl rotation τ^(−1−h). In the velocity-error energy term `−w·DU(w)`, skew rotation cancels. At the base origin this term is

```
(2/τ)(w0²+w1²) − (4/τ)w2².
```

So transverse velocity error is amplified in this local linear term while axial error is damped. Axial vorticity, in contrast, is stretched by `4/τ`. This distinction is lost by replacing the matrix by its full operator norm. Neither sign is a global PDE growth conclusion: the origin is not a material point (`u(t,0)=j_*τ^(−A)e2`), pressure is nonlocal, and diffusion and off-axis derivatives remain.

## 3. Route I — actual evaluation norm and a derivative-counted viscous estimate

### A useful existing bridge overlooked by the scalar-only approach

`NavierStokes/PeriodicSobolev.lean:239–321` already supplies a **concrete periodic evaluation bound**, not a placeholder norm:

- `mixedEnergy`: eight actual iterated cube integrals, derivatives indexed by subsets of {0,1,2}.
- `norm_sq_le_eight_mixedEnergy`: `|w(x)|² ≤ 8*mixedEnergy(w)` for smooth unit-periodic w.
- `derivativeH3Energy/Norm`: actual derivative energy, all ordered derivatives through order three, with fixed extra mixed multiplicities.
- `norm_le_three_derivativeH3Norm`: `|w(x)| ≤ 3*derivativeH3Norm(w)`.

These are baseline proofs by successive coordinate FTC, not a Fourier-embedding assumption. Applying them to the smooth periodic difference requires no PDE. They remove the *periodic velocity evaluation* library gap; they do not remove the PDE stability gap. H² would suffice analytically in dimension three, but H³ is selected because this exact, explicit embedding is already available and H³ also supports the nonlinear Lipschitz estimates below. No claim that this H³ velocity theorem directly controls gradient evaluation with the same constant.

For transparent derivative counting, define on the unit cube

```
N² = Σ_|α|≤3 ||∂^α w||₂²,       D = Σ_|α|≤3 ||∇∂^α w||₂².
```

There are 20 multiindices. Smooth periodic mixed derivatives commute, so the baseline mixedEnergy is a subsum of N²; the existing square estimate implies `|w(x)|≤3N`. Also `N²≤derivativeH3Energy(w)≤7N²` (maximum ordered multiplicity is 6, with at most one extra mixed copy). These norm comparisons are elementary unformalized adapters. The baseline integrals are iterated product integrals; Fubini identifies them with the same unit-cube Lebesgue integrals for continuous integrands. No whole-space norm of a periodic field is used.

### Differential identity, pressure and commutators

Assume jointly smooth fields on each closed slab, the displayed PDE on its open interior, periodic pressures, and common datum. Classical smoothness justifies all following differentiations. At the top level this uses spatial velocity derivatives through **5** to differentiate Δw three times, pressure through **4**, and mixed `∂s∂x^α w` through |α|=3. The estimate itself measures w through H³ and dissipation through H⁴; u through H⁴ or W^{4,∞}. We make no weak-solution/trace extension claim.

Applying ∂^α and pairing with ∂^αw, the principal U transport cancels, the w self-transport cancels, and periodic integration gives

```
(1/2)(N²)' + D
 = −Σα <∂^αw,[∂^α,U·∇]w>
   −Σα <∂^αw,∂^α(w·∇U)>
   +Σα <∂^αw,[∂^α,w·∇]w>
   +Σα <∂^αw,∂^α f_r>.
```

Pressure cancels because `div ∂^αw=0` and all boundary faces pair periodically. Here

```
[∂^α,U·∇]w
 = Σ_j Σ_0<β≤α binom(α,β) (∂^β U_j) ∂j∂^(α−β)w.
```

In this commutator: reference derivatives 1–3 and error derivatives at most 3. In `∂^α(w·∇U)`: reference derivatives **1–4**, error derivatives 0–3. This explicitly exposes the extra reference derivative; an H³ reference alone is not the claimed bound.

A completely elementary, if very wasteful, reference majorant is

```
M(s)=max_{1≤|β|≤4} ||∂^β U(s)||_∞,
a(s)=45*sqrt(20)*M(s).
```

For each α, commutator coefficients sum to at most `3*(2³−1)=21`, and stretching coefficients to at most `3*2³=24`. Bound each reference component by M, each remaining L² error derivative by N, and sum `||∂^αw||₂≤sqrt(20)N`. The two linear contributions are therefore at most a N². No zeroth-order U supremum is needed for this calculation.

For the self-commutator the endpoint products use `||∇w||∞≤C N` (three-dimensional H³ embedding). The only middle top-order product has two second derivatives; Hölder L³×L⁶→L² and the H¹→L⁶ bound on D²w control it by C N². Interpolation controls D²w in L³. Summing the finitely many terms gives `C_N N³`. C_N is a fixed domain/embedding constant, **not evaluated or newly formalized here**. There is no unexplained derivative loss in the self-term.

With `F3(s)=||P f_r(s)||H³`, Leray P on the unit torus is the orthogonal Fourier projection, commutes with spatial derivatives, and is a contraction in this derivative norm. Equivalently keep f_r and cancel gradient work directly. The estimate is

```
(1/2)(N²)' + D ≤ a N² + C_N N³ + N F3.                 (I)
```

A sharper standard Sobolev-product version replaces the W^{4,∞} coefficient by `C||U||H⁴`: for the transport commutator use `||∇U||∞||w||H³ + ||U||H³||∇w||∞`; for stretching use `||w||∞||U||H⁴ + ||w||H³||∇U||∞`. This also requires an independently proved product/commutator theorem, with its constants; none is imported from Euler as an NS result.

For sqrt at N=0, use `Nε=sqrt(N²+ε²)`, derive the scalar inequality on each finite slab and pass ε↓0. Thus (I) yields `N'≤aN+C_N N²+F3` in the comparison sense, not by dividing by zero. All coefficients/forcing are integrable on each closed S-slab under the stated smoothness and periodicity. S-dependent boundedness is not endpoint integrability.

**Viscosity can save one force derivative:** in top-order forcing pairings integrate one spatial derivative onto ∂^αw, leaving at most two on f. Cauchy–Schwarz and Young absorb part of D. The lower orders pair directly and Young gives, with fixed constants,

```
(N²)' + D ≤ (2a+C)N² + 2C_N N³ + C ||P f_r||H²².     (II)
```

This requires time L²H² forcing rather than time L¹H³ forcing for (I). Both are conditional classical PDE estimates in Markdown; (II) is not a new accepted dissipation theorem. No L∞ bound for the Leray projector is presumed. Spatial curl of a force costs one derivative; neither formulation requires time derivatives of the force for its budget, although classical smoothness is assumed for the derivation.

On R³ the same calculation needs actual finite Sobolev error norms, appropriate force norms, and pressure/convection flux closure (for example a Sobolev/Leray formulation with justified cutoff limits). Compact support of the forced reference gives **no** compact support of v or w. This report selects the periodic route precisely to avoid silently discarding those whole-space obligations.

### Fixed-restart amplification and an explicit threshold

Let `A=1/2+h ∈ (1/2,1)`, fix `0<ρ<1`, and set

```
b(s)=(ρ j_*/3) τ^(−A),       K(s)=∫₀ˢ [a(r)+C_N b(r)] dr.
```

A sufficient **bootstrap certificate**, to be proved from the actual force rather than assumed, is

```
exp(K(s)) ∫₀ˢ exp(−K(r)) F3(r) dr < b(s)             (T)
```

for every 0<s<H (uniform strict margin is convenient). Starting from N(0)=0, a first-crossing argument on each closed slab derives N<b from (I) and (T). Eventually the actual axis law and `|w(0)|≤3N` would then transfer growth. The role of (T) is an *unmet numerical/analytic test*, not a new solution contract.

Required reference speed amplification is exactly `(H/τ)^A`, with logarithmic derivative A/τ. The nonlinear bootstrap coefficient itself has a finite integral:

```
∫₀ˢ C_N b(r)dr
 = C_N*(ρ j_*/3)*(H^(1−A)−τ^(1−A))/(1−A).
```

This uses fixed h<1/2; constants are not uniform as h↑1/2. The main obstruction in this test is the reference-dependent linear amplification, not automatically the quadratic error term.

For diagnostic comparison only, solve the specified scalar model `y'=c y/τ+F0 τ^p`, `y(0)=0`, c,p≥0. Exact solution:

```
y(s)=F0 τ^(−c) [H^(c+p+1)−τ^(c+p+1)]/(c+p+1).
```

Dividing by `b=B τ^(−A)` gives

```
y/b = F0/[B(c+p+1)] * [H^(c+p+1)τ^(A−c)−τ^(A+p+1)].
```

Thus c>A makes this sufficient envelope fail eventually whenever F0>0; c=A gives the limiting condition `F0 H^(A+p+1)<B(A+p+1)`; c<A gives ratio tending to zero but still requires checking earlier slabs/closing the bootstrap. These are exact symbolic formulas, **not fits to the actual forcing**. Even infinite terminal flatness does not erase a positive weighted integral accumulated earlier at this fixed restart. A coefficient cτ^(−γ), γ>1, produces `exp(c*(τ^(1−γ)−H^(1−γ))/(γ−1))`, worse than every power.

For the base, the explicit strain already forces M≥4/τ. Therefore the deliberately coarse choice `a=45sqrt(20)M` has a lower bound `180sqrt(20)/τ`, far exceeding A/τ. If F3 has a positive weighted budget on any earlier subinterval, this particular upper envelope cannot satisfy (T) arbitrarily near H. Transferring that observation to the selected field requires the axis-*jet* assembly noted above. This is a **no-go for that sufficient certificate**, not evidence that actual w diverges: a poor upper bound may diverge while the bounded quantity does not. If P f vanishes identically on the restart slab, this obstruction does not apply.

### Route-I verdict and smallest missing theorem

**GO** for proving a genuinely evaluation-controlling periodic finite-slab H³ estimate such as (I)/(II), with constants and pressure cancellation. **NO-GO** for promoting the coarse global norm coefficient to an endpoint proof. **OPEN** for a relative-core refinement.

Smallest substantive *formal-analysis* gap: a periodic three-derivative NS difference energy/commutator theorem for the actual cube norm, with H⁴ reference dependence, H³ (or dissipative H²) projected force and zero common-datum error. Smallest substantive *endpoint* gap: a spatially resolved propagator/weighted error estimate exploiting rotation cancellation and the axial/transverse strain split, whose actual forced budget satisfies a derived growth-relative bound for this fixed t0. Simply assuming that bound would restate O9.

## 4. Route II — viscous vorticity/strain geometry, not a transported invariant

For a smooth viscosity-one field,

```
(∂t+u·∇−Δ)ω = Sω + curl f,
(∂t+u·∇−Δ)S = −(S²+Ω²) − Hess p + sym ∇f,
Ω=(Du−Duᵀ)/2,             Δp=−tr((Du)²)+div f.
```

These follow by differentiating/curling the actual PDE. Pressure is eliminated from vorticity but reappears as a nonlocal Hessian in strain. A sign assertion about that Hessian needs a real Poisson/domain estimate; periodicity alone supplies no favorable sign. There is no automatic invariant cone for the smallest or largest strain eigenvalue.

Viscosity is leading-order relevant. The natural coordinates have transverse scale sqrt(q) and axial scale q^D. Near the origin q=τ: transverse Laplacian costs τ⁻¹, the same as time differentiation; axial Laplacian costs τ^(−2D)=τ^(−1+2h), smaller only when the profile derivatives have comparable coefficients. This is a coordinate-scaling diagnostic, not an estimate of the full mixed candidate: high-frequency stages and cutoffs can have additional derivative costs. It rules out just dropping Δ from a claimed core invariant argument at fixed ν=1.

If c_phi≠0, the base formulas at the fixed origin give

```
∂t ω2 = (1+h) ω2/τ,       (Sω)2 = 4 ω2/τ.
```

Consequently the exact vorticity PDE demands

```
(Δω − u·∇ω + curl f)2 = (h−3) ω2/τ
```

there. Transport, diffusion and forcing together offset most of the positive stretching. Which part does so is **not** identified by the axis values. Treating `4/τ` as the actual vorticity amplification rate would be quantitatively wrong even for the reference. The origin is not a stationary fluid trajectory.

For the error ζ=ωU−ωv, direct subtraction, with v transport, gives

```
(∂s+v·∇−Δ)ζ
 = ζ·∇U + ωv·∇w − w·∇ωU + curl f_r.
```

With periodic fields and Z=||ζ||₂ this gives the honest upper estimate

```
(1/2)(Z²)' + ||∇ζ||₂²
 ≤ ||∇U||∞ Z²
   + [ ||∇w||∞||ωv||₂
       + ||w||∞||∇ωU||₂
       + ||curl f_r||₂ ] Z.
```

No closure by Z alone: L² vorticity controls about H¹ velocity, not velocity evaluation in three dimensions. H² vorticity, together with velocity mean, is comparable to H³ velocity on the torus, returning to Route I. Spatial derivatives through **two of ζ** require three derivatives of w, up to four of U in the differentiated `w·∇ωU` term, and up to three of f in `∂²curl f`; viscosity again can trade one force derivative into dissipation. These are exact derivative counts, not a new lower-order escape route.

The missing mean is material: on the unit torus,

```
mean(w)(s)=∫₀ˢ mean(f_r)(r)dr
```

by integrating the difference PDE. Curl does not see this component; constant periodic force is not necessarily a periodic pressure gradient. A vorticity-only comparison that drops the mean is incomplete.

For orientation, the magnitude equation away from ω=0 is

```
(∂t+u·∇−Δ)|ω|
 = (ω/|ω|)·Sω + (ω/|ω|)·curl f
   − (|∇ω|²−|∇|ω||²)/|ω|.
```

The last term is nonpositive. Maximum principles give useful **upper** stretching estimates, not the needed positive lower bound through force removal. Viscous diffusion also destroys any inference that a compactly supported initial vorticity or an axis-zero correction germ remains supported in a transported compact set. No such transport premise is allowed for v.

Critical norms to watch are `∫||∇v||∞dt` for Lipschitz transport/strong estimates, and the scaling-critical vorticity quantity `∫||ωv||∞dt` (under parabolic scaling). The base strain norm 4/τ is nonintegrable and, if c_phi≠0, base axial vorticity τ^(−1−h) is also nonintegrable. These are reference diagnostics only. A continuation criterion is not a proof of amplification or a stability theorem. No L∞ boundedness of the Riesz/Leray transforms, or direct bound of strain by ||ω||∞ alone, is used.

### Route-II verdict and smallest missing theorem

**NO-GO** for inviscid support transport, frozen axis germs, or a scalar stretching ODE as a proof after force removal. **OPEN**, but currently weaker than Route I, for a genuinely viscous geometric instability mechanism.

The minimum new theorem would be an actual NS evolution law preserving a quantitatively coercive core region/orientation (or a suitable weighted vorticity quantity), with lower bounds that control diffusion leakage, advection away from the fixed origin and the pressure Hessian where strain is used. It must be proved for the comparator from its initial datum, not stipulated to retain the reference strain matrix. No such theorem was located or derived here. The raw strain's large positive eigenvalue by itself is insufficient.

## 5. Handoff to actual-force and integrator

Useful force inputs for the selected finite-slab target are **L¹_t H³_x of P f_r**, or **L²_t H²_x of P f_r** with dissipation, on the actual unit cell. Uniform future spacetime jets from the selected candidate can in principle bound spatial derivatives by restriction to unit spatial directions; finite cell volume then supplies finite Sobolev constants. Those constants and the weighted tests are not calculated by this worker. Flatness at `(1,0)` supplies neither a bound of the spatial supremum nor removal of previously accumulated projected work.

Do not vary t0 with S or vary h/ν to manufacture smallness. The relevant constants depend on the one selected schedule, fixed h, datum, localization and domain. Per-S smoothness proves finiteness, not a uniform threshold. Failure of (T) is not proof of actual error divergence and not proof that force removal regularizes the comparator.

Concrete progress beyond the round-one assumed-error lemmas:

1. Located an already-proved periodic evaluation norm with numerical constant 3, avoiding another scalar placeholder.
2. Derived the actual base saddle strain `diag(−2,−2,4)/τ`, its velocity-error signs, and the independent swirl/vorticity power, from the constructed axis coefficients.
3. Exhibited exactly where viscous transport/diffusion must offset stretching, and why a geometric lower bound is missing.
4. Derived the three-derivative commutator identity, reference/force derivative counts, explicit coarse linear constant, and a dissipative one-force-derivative saving.
5. Computed the fixed-restart reference amplification and force-envelope thresholds; identified why the coarse sufficient bound is unusable toward the endpoint, without claiming the error follows that envelope.

## 6. Commands, failures, classification and audit status

Executed successfully (all exit 0):

```sh
sha256sum /home/velvet/research-snapshots/unforced-round1-20260909T221339Z/SHA256SUMS
(cd /home/velvet/research-snapshots/unforced-round1-20260909T221339Z && sha256sum -c SHA256SUMS)
git diff --exit-code 597692fa5d55e07d810b2d96ead1a67972585425 --
git diff --cached --exit-code
git rev-parse HEAD
python3 Research/UnforcedRestart/Round2/GrowthMechanism/source_audit.py
```

The script records exact subprocess commands, stdout/stderr, exits, source hashes and frozen comparisons in `out/source-evidence.json`. Its additional baseline-byte commands are `git show BASE:path` for each enumerated source. It reads the archive without extraction or modification. Output: `SOURCE_CHECKS_ONLY: 18 baseline sources; 37 frozen files; no Lean acceptance`.

One unsuccessful source lookup: `grep` tool, pattern `def h|abbrev h|jStar|j₀|axial.*origin|axis`, path `NavierStokes/ActualNominalData.lean`, returned **Path not found** (tool diagnostic, not a compiler failure). Corrected inspection followed `ActualCandidateAssembly`'s `CorrectionInitialization.ActualPrimary` import/open and the actual FinalSlowBase/EntranceAlignedBase declarations. Several broad source reads/searches were truncated by the tool; only the cited sections/signatures are claimed inspected, not a full mathematical baseline review.

**Compile/build commands: none. Successful/failed Lean commands: none. Accepted theorem manifest: empty for this worker, intentionally not an acceptance PASS. Axiom/export checks: not run; there are no new Lean exports.** The source script's empty lists are explicit status fields, not a validator that can certify vacuous mathematical success. Mathematical sections 2–4 are source-backed classical derivations/research (round-one classification D), requiring formalization and independent analytic review. The baseline declarations cited retain their historical status; no new clean-source provenance, Nanoda/Comparator or A/B result is asserted.
