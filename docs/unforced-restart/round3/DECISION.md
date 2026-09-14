# Round3 integrated decision

## Verdict: (3) neither decided

**Go for symbolic germ and integration certificates. No-go for certified actual-candidate numerics with the presently supplied inputs.** Neither exact periodic pressure absorption on a full terminal slab nor a certified obstruction to it has been established. Controlled perturbative growth transfer is also unproved. Missing certificates do not imply force zero, nonzero effective force, or impossible transfer.

This integrates the four completed reports against their actual Lean sources and accepted run evidence. It supersedes the *initial-progress descriptions* in PLAN/REPORT, not their frozen preservation records. No earlier file is changed. See [accepted proof/source map](ACCEPTED-SOURCE-MAP.md) and [validation manifest](VALIDATION-MANIFEST.json). Validation here is evidence/hash/export reconciliation, **not a fresh Lean replay or aggregate imported/helper audit**.

## 1. One actual reference, not a surrogate

Throughout, `d = WitnessFeasibility.selected`, `a=d.schedule`, and A, B, P are `potentialSum a`, `directSum a`, `pressureSum a`. Let

- `U = curl(χ A) + χ B`, `P_c = χ P` (compact, unactivated fields);
- `V = β U`, `Q_c = β P_c` (compact activated fields; V is MeanTopology.compactVelocity);
- u,p be the selected activated periodic velocity and pressure;
- f=`d.forcing`, with `R₁(u,p)=f` for **every x and 0<t<1**.

Parameters remain ν=1, terminal T=1, unit periods, fixed restart t₀=1/2 and horizon H=1/2. Every 0<S<H restricts this same reference and the same restart datum. B above denotes the direct field, not the scalar budget, which is exactly zero. N₀ is the actual `startingThreshold 0`; h is the actual primary exponent, 0<h<1/2. Neither is replaced by a numerical sample. All three sums use the same outer schedule and actual `physicalQ h`; the inner slow-base/Borel schedules are distinct dependencies.

**Retained-contract audit.** `Data` retains the candidate, smooth force, away extensions, schedule contract and terminal jets. CandidateProperties retains `speed_unbounded`; this is the available reference growth predicate. Data discards the Witness's explicit H³ limit, derivative-decay and compact-forcing conjuncts. Those stronger conclusions require a separate derivation for this Data, not a fresh existential choice. In particular:

- The two existential forces in Witness are not equated by that proposition.
- The selected force cannot be unfolded to the particular `CandidateFromLimits.force` construction.
- The latter constructor shuts down at t≥2; Data supplies only **some** finite future support endpoint. Neither statement implies presingular removal.
- For a fixed schedule, any two Data forces agree on (0,1). Incoming jets fix their terminal trace by smoothness; no equality of future values follows. Future extension choices cannot tune away an incoming annular curl.

## 2. What is actually accepted

The five modules have 36 printed exports: eight frozen wrapper exports, plus **28 completed-role exports (26 theorems, two definitions)**. Only named-export axiom closures are accepted, all within `propext`, `Classical.choice`, `Quot.sound`.

| Result | Status and limits |
|---|---|
| Actual residual identity; same-schedule force equality | Checked, on (0,1), all space. |
| Any genuine cut-residual extension has the selected terminal jet | Checked at any nonzero representative, every order. This is a usable interface, not a produced annular jet formula. |
| Terminal spatial curl = antisymmetric spatial part of J₁ | Checked for every x; smooth force justifies spatial restriction. Origin curl vanishes; curl is jointly continuous. |
| Unequal tensor entries imply nonzero curl | Checked **conditional** interface; unequal entries have not been supplied. |
| Actual late-time cut-residual curl identity | Checked for 3/4<t<1 in `innerCube (1/4)`; uses germs, not differentiated point equality. |
| Compact velocity momentum and transport integrals vanish | Checked, each component, 0<t<1, over all R³. |
| Selected force cell mean is continuous | Checked on every finite closed time interval, including T=1. It is not a zero-mean theorem. |
| Cut residual vanishes off the closed cylinder, as a germ; terminal tensors there vanish | Checked universal construction lemmas. Selected-force specialization is a short **unformalized composition**. |
| Support-boundary terminal jets vanish | Analytical continuity consequence for the smooth selected force, **not** the strict-exterior theorem's conclusion. |
| Selected force mean zero on [0,1] | Source-backed analytical deduction; Lean composition remains missing. |
| Full localization/vorticity formulas; periodic-potential sufficiency | Analytical calculations/contracts, not new checked declarations. |

In particular the LocalizedForce handoff's phrase “terminal boundary jets” means the boundary-in-*time* tensors with a **strict spatial exterior** hypothesis. It does not mean a checked theorem on the spatial cylinder boundary. WitnessFeasibility's description of the curl adapter as unformalized is superseded by CurlGeometry's actual theorem. The initial REPORT's “no Lean files for other roles” describes the earlier pass only.

## 3. Spatial coverage and time quantifiers

At x use the pointwise representative y, with fixed lattice translation germs for derivatives. Never differentiate `round` or the representative map.

| Spatial region in representative coordinates | Terminal knowledge |
|---|---|
| y=0 (lattice origins) | Jₙ=0 by boundaryLimits and selected.jets; closed origin theorem checked. |
| Open plateau: r²<1/32 and |y₂|<1/8 | χ has a one-germ. Cut residual reduces to the **original mixed residual**, not automatically zero at nonzero points. |
| Transition region: K minus plateau, K={r²≤1/16, |y₂|≤1/4} | Radial transitions, axial caps, overlaps and plateau edges all count. Interior curl unresolved. This is not the iteration's shrinking active annulus. |
| Strict exterior of K | All terminal tensors vanish by the universal theorem and actual specialization. |
| Outer boundary of K | Selected force jets vanish by continuity from exterior in a separated cube; composition not checked. |
| Cell seams and translates | Separated-copy germs/periodicity cover them. No nonlinear superposition or differentiation of a discontinuous selector. |

Thus “annular curl unresolved” is the priority diagnostic, **not** a claim that every possible nonzero terminal mode has already been confined to the annulus: nonzero plateau representatives also lack a zero-jet certificate. Cylinder support alone does not imply annulus-only support. No arbitrary postterminal spatial support is exported by Data.

Define exact absorption on a terminal slab by

`∃ τ, 0<τ<1, ∃ φ, ∀ t∈[τ,1), ∀ x, f(t,x)=∇ₓφ(t,x)`,

with φ spatially unit-periodic and suitably jointly smooth on the slab. The spatial quantifier is the whole torus, and **one** τ works for all times and points. The fixed-restart version requires the identity on [1/2,1), not just after some later τ.

- Nonzero terminal curl at **one** x, with checked force-curl continuity, gives nonzero curl at that x for every sufficiently late preterminal t. It excludes **every** terminal absorption slab ending at 1, since each intersects that neighborhood. This interval-exclusion composition is not newly checked.
- Nonzero curl only at t₁<1 excludes slabs containing that time, not all later slabs.
- Even f(1,·)=0, or curl f(1,·)=0 and mean f(1,·)=0 throughout the cell, does not yield a slab identity. Smooth time-flat but nonzero incoming fields demonstrate the logical gap; they are not substitute candidates.
- Literal f=0 preserves p. Gradient absorption preserves u but changes pressure to **p−φ**.

## 4. Topology and the minimal exact route (conditional only)

On the unit torus, for smooth periodic f at each time, periodic-gradient sufficiency requires **both** curl f=0 everywhere and mean m(t)=∫[0,1]³ f(t,x)dx=0. This is a unit-volume integral, hence also the normalized mean. Curl alone misses constant harmonic fields; mean alone misses nonconstant solenoidal modes.

The analytical mean cancellation is well supported: compact incompressible V has zero momentum (checked); fixed compact support and local joint smoothness permit time differentiation; compact derivative integrals cancel ΔV and ∇Q_c; transport integral vanishes (checked). Separated-copy residual germs plus the PDE identify f as the periodized compact residual. Cell integral equals whole-space integral. Then force-mean continuity extends zero from (0,1) to [0,1]. Missing Lean compositions are time differentiation, derivative/pressure integrals, and the cell/whole-space measure adapter. No velocity trace at 1 is used.

If whole-slab curl vanishing is produced, the minimal potential task is the coherent gauge

`φ(t,x)=∫₀¹ x·f(t,sx) ds`.

Symmetric spatial Jacobian gives ∇φ=f; periodicity makes φ(x+eᵢ)−φ(x) constant in x, equal to the i-th cell mean. Zero mean makes φ periodic. Compact-parameter differentiation gives joint regularity; no unrelated choice of a potential for each t is needed. This is ordinary analysis, not yet a formal torus sufficiency theorem.

Then prove `(u,p−φ)` is an unforced solution on the same slab, and compare with an admissible unforced solution from the matching datum by the appropriate uniqueness theorem on every compact presingular subslab. Smooth periodic divergence-free restart data and pressure regularity must be explicit. Existence/lifespan through the desired horizon is a separate obligation, not provided by absorption. If τ>1/2, restarting at τ uses u(τ); it does **not** identify an unforced evolution started from u(1/2). The earlier mismatch must be controlled or absorption must cover [1/2,τ] too. No global-existence or A/B conclusion follows here.

## 5. Gauge, localization, activation and effective support

These are source-grounded **analytical** identities. Write u₀=curl A+B, b=∇χ×A, so U=χu₀+b. For smooth local fields,

```
R₁(U,χP) = χR₁(u₀,P) + b_t − Δb − (Δχ)u₀
 − 2Σᵢ(∂ᵢχ)∂ᵢu₀ + P∇χ + N,
N = (χ²−χ)(u₀·∇)u₀ + χ(u₀·∇χ)u₀ + χ(u₀·∇)b
  + (b·∇χ)u₀ + χ(b·∇)u₀ + (b·∇)b.
R₁(βU,βχP) = βR₁(U,χP) + β′U + (β²−β)(U·∇)U.
```

β has a one-germ only for t>3/4. Both activation defect terms matter at the fixed restart. Curl of the **total** pressure gradient is zero: the ∇χ×∇P and ∇P×∇χ pieces cancel. Dropping only P∇χ is invalid. The curl of the viscous residual retains Δ curl b and all cutoff derivatives; an unreduced evaluator needs spatial derivatives through order four of A and three of B.

The slow potential is radially anchored at physical radial energy s=1, retaining all slow orders and initial/correction/mean stages. Although adding a curl-free G preserves uncut velocity, it changes localized velocity by ∇χ×G. The gauge-only contribution and base-only velocity therefore cannot certify the total residual curl. A terminal calculation must use actual agreeing smooth germs, not subtract divergent ungauged endpoint expressions.

Even if f is supported away from a chosen core region at some times, its Leray projection need not be: pressure inversion is nonlocal and viscosity propagates influence. Localization does not prove dynamical independence or a small response.

## 6. Specified perturbative target, only if effective force persists

No persistence certificate is available. The following **conditional analytical problem**, not accepted PDE existence/stability or an experiment, fixes what route (2) would actually require.

Use the Leray projector Π onto all divergence-free torus fields, **including constants**. For Fourier convention exp(2πik·x), Π₀=I and Πₖ=I−kkᵀ/|k|² for k≠0. Set g=Πf for this actual f. It is zero exactly for periodic gradients; it is not known zero or nonzero here.

Let v be an unforced comparator with v(t₀)=u(t₀), and set w=v−u. On [t₀,t₀+S], S<H, subtraction and projection give

```
L_u w = −g − Π[(w·∇)w],   div w=0,   w(t₀)=0,
L_u z := ∂t z − Δz + Π[(u·∇)z + (z·∇)u].
```

The **spatially resolved viscous linearized response** is

`L_u z=−g, div z=0, z(t₀)=0`,

with periodic boundary conditions and the *actual activated u* as coefficient. If E_u(t,s) is the evolution operator on divergence-free fields, the target is

`z(t)=−∫[t₀,t] E_u(t,s)g(s) ds`.

For r=w−z, `L_u r=−Π[((z+r)·∇)(z+r)]`, r(t₀)=0. This keeps viscosity, advection, stretching, projection, activation and the full force. A scalar norm envelope or annulus-only source model is not this problem.

A usable transfer target must establish one comparator on all restrictions S<H (compatibility by uniqueness, not new data per S), with bounds uniform enough as S↑H. Let G(t)=sup_Q |u(t,x)|, finite for each t<1 and unbounded arbitrarily near 1 by d.candidate.speed_unbounded and periodicity. One concrete sufficient budget is

`||z(t)||∞ + ||r(t)||∞ ≤ θ G(t)+C`, with fixed 0≤θ<1 and C≥0.

Then `sup_Q |v(t)| ≥ (1−θ)G(t)−C`. An Hˢ estimate with s>3/2 may supply the L∞ bound only with an explicit embedding constant and valid nonlinear/evolution estimates. To use the existing pointwise `speed_transfer` theorem directly requires its stronger pointwise relative-error hypothesis, not merely this sup-norm budget. No axis-only or H³ rate is assigned to the frozen Data without a bridge. Uniform constants, the evolution operator bounds, nonlinear closure, comparator lifespan/admissibility and this growth-relative budget are all unknown. Finite smooth force norms alone prove none of them.

## 7. Missing producer and numerical gate

The missing *decision producer* is not extension uniqueness or a tensor-to-curl adapter; those are checked. It is an actual local residual-germ calculation with a decided antisymmetric first spatial jet. Concretely, at some nonzero representative y in the transition region, produce an expression E, a neighborhood of (1,y), smoothness and agreement with `cutResidual A B P` on its open-past part, and **derive**

`(D E(1,y)[(0,eᵢ)])ⱼ − (D E(1,y)[(0,eⱼ)])ᵢ ≠ 0`.

A structural identity or rigorously enclosing interval excluding zero suffices; assuming that inequality as an input does not. OneSidedExtension existence already follows from the sources, so another opaque existence proof is not the missing producer. The alternative producer is all-space curl vanishing on one entire terminal slab (plus the mean/potential compositions), not terminal-only vanishing. No preferred actual y or sign has been certified.

No numerical experiment is proposed. Required numerical inputs would include certified representations of the **actual** profile/h, threshold/geometry, actual active schedule integers, finite-stage functions and cutoff jets, plus inner Borel errors. Preterminal positive-q local finiteness yields an exact outer finite prefix; doubling gives a_j≥2^j, so `2^N q_min>1` suffices to kill the outer tail on a neighborhood with certified q≥q_min>0. That does not evaluate the retained finite stages or justify an endpoint cutoff. Terminal work instead needs the actual extension-germ producer and derivative bounds. A curl enclosure needs every contributing derivative error; a Fourier/test-pairing certificate needs full-cell integration and quadrature/truncation errors. Smoothness/existence supply no numerical modulus. Noncomputable choices obstruct the supplied evaluation interface, not symbolic mathematics or computability in principle.

## 8. One next-phase formal bridge

**Choose compact momentum time differentiation, not another conditional sign interface.** Proposed single substantive theorem (not implemented in this integration):

```
selected_compact_temporal_integral_zero:
  ∀ t∈(0,1), ∀ i : Fin 3,
    ∫ x : Space, (temporalDerivative MeanTopology.compactVelocity t x) i = 0.
```

This is a nontrivial, selection-uniform analytical integration step toward the actual harmonic cancellation. It has a known proof mechanism and does not require an annular sign, effective parameters, or terminal velocity bounds.

Acceptance criteria:

1. Use exactly the frozen selected schedule and activated compact velocity. No new witness or strengthened Data.
2. Derive local joint smoothness from selected candidate smoothness via compact/periodic germs on K and the zero germ outside K. Use one fixed compact support on a closed time neighborhood strictly inside (0,1).
3. Specialize `NavierStokesR3.CompactTimeIntegral.hasDerivAt_integral_of_contDiffOn` (`NavierStokes/R3/CompactTimeIntegral.lean:139`) on that closed interior slab, using `hasDerivAt_time_of_contDiffOn` to match the temporal derivative. Differentiate the checked identity `∫ V_i(t)=0` and use derivative uniqueness. These source interfaces were inspected; their common-support/C¹ hypotheses must be proved, not assumed as an interchange axiom or desired zero integral.
4. Strict pinned Lean check in new phase-owned output, printed closure within the three permitted axioms, complete command/source/log/output hashes; no baseline/dependency rebuild, proof suppression or imported moving output.

**Explicit unknowns after acceptance:** compact pressure/Laplacian cancellation adapters, coordinate-measure and separated-periodization cell integral transport, then force-mean zero including endpoints; torus potential sufficiency; the actual annular/plateau jet producer; full-slab curl identity or obstruction; projected-response and nonlinear growth-relative bounds; comparator lifespan. This bridge closes one real integration gap. It does not decide absorption or transfer.

## Validation receipt

`python3 Research/UnforcedRestart/Round3/Integration/reconcile.py` passed: 5 source modules, 36 distinct printed exports, all accepted source/log/output hashes and axiom lists matched. Sixteen directly cited baseline sources match the read-only source-built checkout. The read-only preservation verifier passed for 2,878 preexisting files, 16 frozen clean targets and external evidence; HEAD, index bytes and prior refs are unchanged. Tracked/index diffs are empty. No Lean compilation, dependency build, commit or push occurred in this integration. One initial Python output-path resolution failure was corrected and recorded separately; it was not a Lean failure and did not change accepted evidence. See [validation log](INTEGRATION-VALIDATION.log) and the manifest for commands, hashes, scope and trust roots.
