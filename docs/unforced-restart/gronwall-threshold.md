# gronwall-threshold — scalar budgets, not PDE stability

## Outcome and classification

**Unconditional formal result (class C: scalar infrastructure):** three checked theorems in `Research/UnforcedRestart/gronwall-threshold/Main.lean`, namespace `UnforcedRestart.GronwallThreshold`. They establish a variable-coefficient integrating-factor estimate with arbitrary initial error, and explicit threshold consequences, on any closed real interval using only interior derivatives.

**Explicitly conditional application:** identifying their scalar inputs with actual forced-versus-unforced Navier–Stokes energies requires the analytic bridges below. No unforced solution, local existence, strong-norm estimate, or A/B exclusion is constructed. No conjecture is promoted to a theorem.

Independently read `PLAN.md`, both prior Astra `final-report.md` and `skeptical-review.md` at the artifact directory specified there, and the source declarations listed below. The prior warning survives this inspection: equal-force uniqueness and smooth endpoint residuals do not imply unforced stability.

## 1. Exact checked scalar contract

All scalar variables are real; `E,E',A,k,B,g : ℝ → ℝ`. For `a ≤ b`, assume:

* `E,A,B` are continuous on `[a,b]`;
* on `(a,b)`, `HasDerivAt E (E' t) t`, `HasDerivAt A (k t) t`, and `HasDerivAt B (exp(-A t)*g t) t`;
* on `(a,b)`, `E' t ≤ k t * E t + g t`.

Then `weighted_budget` proves, for every `t ∈ [a,b]`,

\[
 e^{-A(t)}E(t)\le e^{-A(a)}E(a)+B(t)-B(a).                 \tag{1}
\]

The proof differentiates `exp(-A)*E-B` and uses the mean-value monotonicity theorem. No sign assumptions on `E,k,g,A,B` are necessary. Nonnegative energies/sources enter only in the intended application. Degenerate intervals `a=b` are allowed; no endpoint derivative is required.

`threshold` adds a real target `q` and the budget premise

\[
 e^{-A(a)}E(a)+B(t)-B(a)\le e^{-A(t)}q
\]

and concludes `E(t) ≤ q`. The initial error is not discarded.

`zero_initial_threshold` specializes to `E(a)=0`, `B(a)=0`, and

\[
 B(t)\le e^{-A(t)}\delta^2 \quad\Longrightarrow\quad E(t)\le\delta^2. \tag{2}
\]

Here `δ : ℝ` is unrestricted because only its square occurs. For an interpretation as a norm tolerance use `δ≥0` and separately establish `E=‖w‖²`.

**Primitive versus integral distinction:** Lean checks the displayed derivative contract for `A,B` as hypotheses, not a fundamental-theorem-of-calculus wrapper. In ordinary analysis, continuous `k,g` on a presingular slab give the normalized choices

\[
 A(t)=\int_a^t k(r)\,dr,\qquad
 B(t)=\int_a^t e^{-A(r)}g(r)\,dr.
\]

With these choices (1) becomes

\[
 E(t)\le e^{A(t)}\left[E(a)+\int_a^t e^{-A(r)}g(r)\,dr\right]. \tag{3}
\]

The FTC instantiation and (3)'s integral notation are **unformalized deductions here**, not extra accepted Lean declarations. The derivative contract avoids assuming global regularity of singular coefficients beyond the slab.

## 2. Where an actual PDE comparison would feed this contract

Fix `ν>0`, `0<t₀<1`, `H=1-t₀`, and `0<S<H`. Use restarted time `s∈[0,S]` and `Space = EuclideanSpace ℝ (Fin 3)`. The actual internal residual uses viscosity one; formulas with general `ν` below are ordinary mathematics with that parameter explicit, not a reinterpretation of the baseline definition.

Let `u` be the forced reference shifted from old time `t₀+s`, `v` an unforced solution at the **same** viscosity, `w=u-v`, `r=p-q`, and `f` the shifted original force. Equal restart data give `w(0)=0`. On the open time interior the intended equation is

\[
 \partial_s w=\nu\Delta w-Du(w)-Dw(v)-\nabla r+f.
\]

Take `E=∫|w|²`, `D=∫|∇w|²` (no factor one half in `E`). The domain is either R³ with Lebesgue volume or the unit periodic cube; do not integrate a nonzero periodic field over all R³. Under justified differentiation under the integral and integration by parts,

\[
 \tfrac12 E'+\nu D=-\int\langle w,Du(w)\rangle+\int\langle w,f\rangle
 \le L(s)E+F(s)\sqrt E,                                \tag{4}
\]

where `L(s)≥‖Du(s)‖∞` uses the operator norm, and `F(s)=‖f(s)‖₂` in the chosen domain. A nonnegative majorant `L` is convenient. Viscosity has the favorable sign; dropping `νD≥0` introduces no `1/ν` in this particular estimate.

For any fixed `η>0`, Young's inequality gives

\[
 E'\le(2L+\eta)E+F^2/\eta.                            \tag{5}
\]

Thus the scalar inputs are `k=2L+η`, `g=F²/η`, and zero initial energy. A sufficient energy-error threshold at each `s` is

\[
 \int_0^s e^{-\int_0^r(2L+\eta)} F(r)^2/\eta\,dr
 \le \delta(s)^2 e^{-\int_0^s(2L+\eta)}.              \tag{6}
\]

This is a sufficient bound, **not a necessary condition for actual closeness**: the estimate discarded dissipation and possible cancellations. To control the entire half-open horizon it must hold for every `s<H`, not merely each fixed slab with unrelated tolerances.

For slab bounds `L≤L_S`, `F≤M_S`, put `K=2L_S+η>0`. For initial error `E₀`, (3) yields

\[
 E(s)\le e^{Ks}E_0+\frac{M_S^2}{\eta K}(e^{Ks}-1)
 \le e^{KS}(E_0+M_S^2S/\eta).
\]

For `E₀=0`, a simple sufficient **uniform slab** threshold is

\[
 M_S\le \delta\sqrt{\eta/S}\,e^{-KS/2},\qquad\delta\ge0. \tag{7}
\]

These explicit constants quantify why a small unweighted force is not by itself a stability statement. The sharper first bound has no artificial division problem here since `K>0`.

An alternative, sharper L¹-time estimate is obtained by applying the energy inequality to `sqrt(E+ε²)` and sending `ε↓0` on a fixed slab:

\[
 \|w(s)\|_2\le e^{\int_0^s L}
 \left[\|w(0)\|_2+\int_0^s e^{-\int_0^r L}F(r)\,dr\right]. \tag{8}
\]

This avoids pretending `sqrt E` is differentiable at its zeros. It is an **unformalized analytic deduction conditional on (4)**; our Lean theorem does not supply the regularization/limit proof.

For a modified forcing `f_new=χ f` rather than zero forcing, the forcing difference in these formulas is `(1-χ)f`. Changing the force does not keep the original velocity a solution.

### Missing analytic hypotheses in (4)

Periodic: smooth velocity and pressure slices, periodic velocity **and pressure**, divergence freedom, actual differing-force equation, time regularity, and cube-integral differentiation/IBP. Whole space: sufficient integrability and differentiation control on each slab, velocity boundary terms, and an actual pressure-flux cancellation/recovery result. Compact support of `u` does not make `v` or `w` compactly supported. The baseline whole-space equal-force uniqueness theorem cannot simply be relabeled as (4).

## 3. Deterioration near the singular horizon

The following are **model-coefficient deductions**, not bounds established for the actual candidate. They quantify the stability obligation rather than inventing candidate constants.

If one has a nonnegative coefficient majorant `k(s)=c/(H-s)`, `c>0`, then

\[
 A(s)=c\log\frac H{H-s},\qquad
 B(s)=\int_0^s \left(\frac{H-r}{H}\right)^c g(r)\,dr.
\]

A fixed energy tolerance `δ²` requires the sufficient test

\[
 B(s)\le\delta^2((H-s)/H)^c.
\]

For nonnegative continuous `g` positive somewhere before `H`, the accumulated budget has a positive lower bound after that point, whereas the right side tends to zero. This test eventually fails even if `g` vanishes to infinite order at `H`. It does **not** prove the actual PDE error diverges: only this sufficient estimate ceases to certify a fixed error tolerance.

If `k(s)=c(H-s)^{-β}` with `β>1`, then

\[
 A(s)=\frac c{\beta-1}\big((H-s)^{1-\beta}-H^{1-\beta}\big).
\]

The allowed weighted budget for a polynomial target `q(s)=C(H-s)^{-γ}` is `q(s)e^{-A(s)}`, which tends to zero for every fixed `γ`. For `β=1` this budget is proportional to `(H-s)^{c-γ}` and tends to zero when `c>γ`. For `β<1` the coefficient's integral remains finite at `H`. These cases cannot be selected for the actual candidate without a quantitative reference-norm estimate. A diverging upper estimate for `L` is not a lower estimate for actual error amplification.

Taking `t₀` closer to one makes a bounded-force unweighted budget small, but also changes `H`, the datum norms, the growth coefficient, and the needed tolerance. No uniform balance is supplied by smoothness. Endpoint flatness at `(1,0)` alone controls neither the full spatial norm of the force nor its previously accumulated weighted budget.

## 4. Which norm threshold could transfer growth?

An L² threshold, even uniform through `H`, does not preserve an axis value or pointwise speed growth. Spatial concentration is the obstruction. Equations (6)–(8) therefore do not finish the desired argument.

For a genuine `H^m` error estimate in dimension three, velocity evaluation requires Sobolev embedding order `m>3/2` (integer `m≥2`); gradient evaluation requires `m>5/2` (integer `m≥3`). Constants depend on the domain and exact norm convention. A velocity target such as `C_emb‖w(s)‖_{H^m}≤θ|u(s,0)|`, `0<θ<1`, would preserve axis growth by the triangle inequality. Proving this target needs an actual viscous strong-norm comparison estimate and its forcing budget, not replacement of `E` by a new symbol in (4). Reference higher derivatives and nonlinear error terms may enter that estimate. Euler's H³-difference/H⁴-reference estimates are not a Navier–Stokes bridge.

The scalar threshold premise constrains coefficient/source primitives, not the existence of a blowup solution. There is no hidden blowup conclusion in these three theorems. Conversely assuming a strong-norm comparison already up to all `s<H` is a substantial unproved input; lifespan coverage cannot be read off finite-slab scalar estimates.

## 5. Exact source map and independent findings

* `NavierStokes/GronwallInterior.lean`: inspected complete file. `exp_neg_mul_le_of_deriv_le`, `le_exp_mul_of_deriv_le`, `le_uniform_exp_mul_of_deriv_le` assume constant nonnegative `K,ε` and nonpositive initial value. `eq_zero_of_deriv_le` is equal-force uniqueness infrastructure. New `weighted_budget` generalizes the scalar mechanism to variable coefficients and nonzero initial errors via primitives.
* `NavierStokes/PeriodicUniqueness.lean:237–335`: `energyRate`, `dissipation`, `coupling`, `energy_balance`, `neg_coupling_le_energy`, `energy_rate_le`. Inspected hypotheses include `hNS : ∀ x, residual u p = residual v q`. The existing rate is `2*B` times energy, not a differing-force budget.
* `NavierStokes/R3CompactCandidate.lean`: inspected complete file. `Properties` supplies one compact support set for reference velocity on `[0,1)`, one for force on future time, force smoothness and speed unboundedness. `of_limits` identifies the compact candidate's force through `CandidateFromLimits.force_eq_activated_residual`.
* `NavierStokes/CandidateFromLimits.lean:81–114`: `force` is the glued traced residual, `force_smooth` is global smoothness, `force_eq_activated_residual` holds at `0≤t<1`, `force_zero_from` only for `2≤t`. None is terminal force removal before one.
* `NavierStokes/ActualCandidateAssembly.lean:1021–1074`: `Witness` retains the three actual sums and gives periodic forcing and, separately, an existential `compactForcing` with `R3CompactCandidate.Properties` for the activated cut velocity and pressure. `selected_witness` fixes the selected budget/threshold and closes that witness. Thus the snapshot/reference path is to the actual cut sums, not an invented solution predicate.

Smooth force with fixed compact spatial support implies bounded `F(s)` on compact time intervals by ordinary compactness/integration reasoning; periodic smooth force gives the analogous unit-cube fact. This supplies finite constants, **not numerical bounds or comparison with (6)**. The actual `L(s)`, strong-norm constants, effective forcing size, and uniform lifespan remain unproved bridges. This report does not claim to have independently rechecked the full construction or challenge equivalence.

## 6. Validation and accepted declarations

Accepted file: `Research/UnforcedRestart/gronwall-threshold/Main.lean` only. Direct import: `NavierStokes.GronwallInterior`. No cross-task imports. The file contains inline axiom audits, so there is no separate research import-path setup.

Every exported declaration (all class C):

1. `UnforcedRestart.GronwallThreshold.weighted_budget`
2. `UnforcedRestart.GronwallThreshold.threshold`
3. `UnforcedRestart.GronwallThreshold.zero_initial_threshold`

Exact successful command, exit **0**:

```sh
env LEAN_NUM_THREADS=1 lake env lean -j1 \
  -DautoImplicit=false -DwarningAsError=true \
  -o Research/UnforcedRestart/gronwall-threshold/out/Main.olean \
  -i Research/UnforcedRestart/gronwall-threshold/out/Main.ilean \
  Research/UnforcedRestart/gronwall-threshold/Main.lean \
  > Research/UnforcedRestart/gronwall-threshold/out/Main.log 2>&1
```

`out/Main.exit` records `0`. `out/Main.log` prints, for **each** of the three declarations, exactly the allowed axiom set `[propext, Classical.choice, Quot.sound]`. No other substantive definitions are exported. This is fresh strict elaboration against prepared cached baseline dependencies, not a clean rebuild or independent Comparator run.

`git diff --exit-code` returned **0**, recorded in `out/tracked-diff.exit` with empty `out/tracked-diff.log`. Writes were confined to the owned research directory and this report. No broad build, dependency/config changes, commits, or pushes.

One initial rejected elaboration used the ambiguous name `mul_le_mul_left` while `Set` was open; it resolved to the wrong theorem. The cancellation step was replaced by `nlinarith` using strict positivity of the exponential. That failed draft is not accepted; the final file was recompiled successfully and all final axiom closures are clean.

## Acceptance boundary / remaining work

Scalar success: variable-coefficient budgets, arbitrary initial error, normalized zero-error threshold, and endpoint-safe proof are checked. PDE success would additionally require (i) actual differing-force energy identity with boundary/pressure control, (ii) FTC/norm regularity instantiation, (iii) quantitative candidate forcing and reference norms meeting a threshold, (iv) sufficiently strong norm-to-growth bridge, and (v) applicable unforced existence/uniqueness with horizon coverage. These are not discharged here. No A/B conclusion follows.
