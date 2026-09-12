# Remaining obligations — no implicit bridges

All items below are **unproved applications/research**, not additional accepted Lean results. The accepted implications keep their premises explicit. Exact declarations/imports/axioms are in `Research/UnforcedRestart/MANIFEST.{json,md}`; fresh evidence is under `integration/validation/`.

Use one fixed restart `0<t₀<1`, `H=1−t₀`, datum `a(x)=u(t₀,x)`, and each closed slab `[0,S]` with `0<S<H`. Do not choose a new datum separately for each S and describe the resulting family as one solution.

## Obligation ledger

| ID | Required statement/input | What is available; what remains missing |
|---|---|---|
| **O1 — arbitrary-data class adapter** | Convert a space-first Comparator field with datum a to internal raw fields on `[0,S]`, with correct spatial operators, full derivative on `(0,S)`, smooth velocity/pressure, divergence and datum. For an actual restarted reference retain its checked new-zero within PDE. | Datum predicates are proved; reference translation is checked. `Solution`, `GlobalSolutionOne`, `MaximalLifespan.ClassicalSolution` are zero-datum wrappers, not arbitrary-data constructors. A complete finite-horizon nonzero-data Comparator adapter is not exported. Periodic pressure must be preserved; R³ conversion needs actual `MemLp`/slab energy bounds. |
| **O2 — existence, persistence, continuation** | For construction: an applicable NS local theorem at fixed ν>0 for the nonzero smooth datum, pressure recovery, one common positive lifespan for all smoothness orders, boundary regularity, uniqueness and an explicit continuation criterion. | No applicable general NS local theorem was located in the bounded search. An ODE Picard theorem and Euler stability are not substitutes. A lifetime depending on `‖a‖Hᵐ` need not exceed H. A hypothetical global A/B comparator legitimately discharges existence/coverage in a reductio, so O2 is not an unavoidable separate premise in that route. |
| **O3 — exact terminal force removal** | Prove, for an actual selected compact or periodic force, either `∀t∈[t₀,1), ∀x, f(t,x)=0`, or `f=∇φ` there with admissible φ. | `candidate_shift_unforced` and `absorb_on` consume precisely these kinds of identities, but do not supply them. Origin flatness, smooth extension, and shutdown at 2 do not suffice. Curl-free alone is inadequate for a periodic potential; zero circulation/mean compatibility matters. Global-from-zero absorbability obstruction does not refute terminal absorbability after energy injection. |
| **O4 — pressure correction and exact uniqueness assembly** | Smooth φ and corrected `p−φ` on each closed slab, periodic φ in the periodic class (or a separately verified admissible correction), endpoint within PDE if asserted, then equal-force raw uniqueness against the same-datum comparator and a terminal compact-region contradiction. | Correct sign and pressure-class preservation are checked. Raw periodic arbitrary-interval uniqueness is available; raw R³ uniqueness requires translating its `[0,S]` statement and supplying common reference support and competitor uniform finite energy. No competitor pressure decay follows from reference support. O3 remains the decisive construction-specific missing input. |
| **O5 — energy derivative/primitive assembly** | For actual differing-force periodic fields jointly smooth on a slab, combine the checked rate inequality with `energy_hasDerivAt`, endpoint continuity, zero initial integral, dissipation nonnegativity and FTC primitives, to instantiate `GronwallThreshold`. | Slice-wise `energyRate+2D≤(2B+1)E+∫Q|f|²` is checked. The slab derivative is available in baseline, but the new integrated/FTC wrapper is not exported. A finite slab gradient bound `B_S` does not imply a bound uniform as `S↑H`. This is mostly adapter/analysis formalization once a comparator is given, not the strong-norm or actual-smallness breakthrough. |
| **O6 — R³ inhomogeneous energy/pressure closure** | Justify differentiation and localized integration, pass spatial cutoffs to infinity, control convection and actual pressure-flux boundary terms for force difference f. | The new energy proof is periodic only. Baseline whole-space pressure recovery/uniqueness assumes equal residuals. Compact support of u does not imply support of v or w. Sufficient conditions include appropriate `C_t L²_x`, `L²_t H¹_x`, coupling/force integrability and vanishing integrated boundary flux; they must be derived for the intended Comparator, not inserted silently. |
| **O7 — fixed-viscosity strong-norm PDE stability** | Define an actual error norm (e.g. inhomogeneous Hᵐ) and prove a forced-vs-unforced estimate with pressure/projection control, derivative counts, nonlinear-error treatment, reference-dependent constants and lifespan coverage. | Difference algebra and L² estimates are real progress but insufficient. `StrongNormGrowthTransfer.evaluation_budget` takes a scalar N, not an Hᵐ object. Euler H³-difference/H⁴-reference results are not NS theorems. `sqrt E` differentiation at zeros requires regularization or another valid argument. |
| **O8 — actual quantitative forcing below the threshold** | Bound the actual removed solenoidal force in the exact norms from O7, and prove the weighted budget beats the required error tolerance for every sufficiently late time of one fixed restart. | New force estimates give uniform jets and `∀x, ∫aᵇ‖J_m(t,x)‖dt≤C_m(b−a)`. Spatial supremum/Lᵖ/Sobolev/mixed-norm packaging remains unproved here; quantitative constants and singular-reference amplification are unknown. Finite constants and fixed-ε short-interval smallness do not compare with a shrinking tolerance. Full spacetime derivatives of a width-d cutoff cost powers of d⁻¹. No Leray-projector L∞ bound is presumed. |
| **O9 — evaluation and actual growth connection** | Prove the chosen norm controls a continuous representative at the axis (H² for velocity, H³ for gradient are candidate integer orders in 3D), and establish `C_eval N(w(s))≤ρ|uᵣ(s,0)|+B`, with fixed ρ<1, B finite, toward H. Supply the actual assembled axis identity if using the axis criterion. | Relative-error transfer is checked **conditional on this decisive estimate**. Assuming it and calling it “stability” is circular. H²/H³ embedding claims are discussion, not new NS norm theorems. Alternatively all-space speed transfer requires a compact spatial reduction (periodic cube/reference compact support); unrestricted moving spatial witnesses do not contradict R³ smoothness. |
| **O10 — scaling/compactness alternative** | Formalize fixed-viscosity parabolic residual covariance; control velocity and pressure on fixed negative-time domains; obtain a topology passing `U⊗U`, eliminate defect stresses if needed, prove nontriviality, admissible regularity/class, and a singular/nonextension conclusion. | Force pointwise convergence and actual-base norm formula are checked. The assembled eventual identity/limit wrapper and compact-uniform force bounds are not. The base scale grows `r^(−2h)` at `(-1,0)`; source-supported assembled transfer obstructs locally uniform classical compactness in this normalization. Weak convergence/nontriviality is neither proved nor ruled out. Amplitude renormalization changes the convection coefficient; changing viscosity is not fixed-ν force removal. |

## Quantitative acceptance tests

For the checked scalar theorem, with continuous E,A,B on `[a,b]` and interior derivatives

```
E′ ≤ kE + g,   A′ = k,   B′ = exp(−A)g,
```

one obtains `exp(−A(t)) E(t) ≤ exp(−A(a)) E(a) + B(t) − B(a)`.
The normalized zero-error test is `B(t) ≤ exp(−A(t)) δ²`. A true PDE instantiation must prove all derivative identities and the interpretation of E; it cannot just rename E as a strong norm.

For the periodic energy inequality, η=1 gives candidate inputs `k=2L+1`, `g=∫Q|f|²` once a time-dependent gradient majorant L and the derivative/FTC bridge are proved. General η and ν formulas in the reports are unformalized extensions, not hidden parameters in the viscosity-one exports. An L² tolerance still does not discharge O9.

If amplification diverges toward H, an unweighted budget O(H) can fail to beat a vanishing weighted tolerance. Conversely failure of this sufficient upper-bound test **does not prove the actual error diverges** or that no sharper stability argument exists. Terminal infinite flatness at one spatial point does not control the spatial norm or its accumulated earlier work.

A sufficient actual axis target is, eventually,

```
|uᵣ(s,0) − v(s,0)| ≤ ρ |uᵣ(s,0)| + B,   ρ < 1,
|uᵣ(s,0)| = j_* (H−s)^(−(1/2+h)),   j_*>0, 0<h<1/2.
```

The triangle inequality would then force comparator axis growth. The quantitative first line is the missing conclusion of O7–O8, not a permissible unexplained success assumption. The exact selected-field eventual second-line wrapper is also not a new accepted declaration.

## Cutoff-specific obligations

* Immediate unforced restart has zero force from s=0 and the original snapshot datum. It need not glue smoothly to the entire old forced history.
* Smooth switch-off `g=ρf` is still forced during transition. Existence through switch-off, regularity and quantitative comparison must be supplied. Restarting at its end uses the **new** solution's datum, not automatically the old candidate's snapshot.
* Keeping the old fields gives the checked defect `(1−ρ)f`. Cutting velocity instead produces additional product-rule/convection terms; those formulas are discussion only here and do not preserve terminal growth when velocity is shut off before one.
* A global smooth-force admissibility predicate does not imply a globally smooth solution. Equal-force uniqueness cannot remove a nonzero force discrepancy.

## Priorities and stop conditions

1. Low-risk formal integration: O1 and O5; package mixed norms from the existing uniform force bounds; add selected-periodic/axis wrappers with their genuine witness hypotheses. These would reduce adapter gaps without solving the construction-specific problem.
2. Exact route: investigate O3 before claiming an exact unforced restart. Once an actual potential/vanishing interval is proved, O4 provides a concrete comparison plan.
3. Perturbative route: identify an actual fixed-viscosity strong-norm theorem and its constants before claiming O8 smallness. O7–O9 are substantive analytic work, not scalar bookkeeping.
4. Alternative route: O10 must address the explicit velocity normalization obstruction, not merely repeat vanishing force.

Stop any claimed A/B deduction that uses the wrong datum class, suppresses force discrepancy or pressure boundary work, treats a per-slab finite constant as horizon-uniform, substitutes L² for evaluation control, silently assumes continued existence, or equates a successful axiom audit with independent Comparator/Clay equivalence. None of these stronger claims is accepted in this integration.
