# Pressure absorption: checked sign, missing potential

> Classification notice (agent 18): task-local research labels below are historical and superseded by [MANIFEST.md](../../Research/UnforcedRestart/MANIFEST.md). In particular, its generic conditional pressure lemmas are class **B**, not A. Research categories are unrelated to Clay problem alternatives A/B/C/D.

## Outcome and scope

Seven checked lemmas, namespace `UnforcedRestart.PressureAbsorption`, in `Research/UnforcedRestart/pressure-absorption/Main.lean`. They use the actual repository differential operators, not a surrogate solution predicate. **No terminal potential has been constructed, and no unforced A/B exclusion follows.**

Independently read `PLAN.md`, the prior Astra `final-report.md` and `skeptical-review.md` in the prescribed artifact directory, and the actual source signatures below. The prior claim that global gradient forcing cannot generate this zero-datum compact evolution is an energy deduction, not a new checked energy theorem here.

## Exact mathematics

All times are real, `Space = EuclideanSpace ℝ (Fin 3)`, fields have argument `(t,x)`, and the imported residual has viscosity **one**. For every velocity `u`, scalar pressures `p, φ`, real `t`, and `x : Space`, assuming smooth spatial slices of `p` and `φ`,

\[
R_1(u,p-\phi)=R_1(u,p)-\nabla\phi.
\]

Thus if `R₁(u,p)=f`, the corrected equation is `R₁(u,p−φ)=f−∇φ`. It is unforced **iff** `f=∇φ` at the point. The required sign is minus, not plus. This algebra does not need velocity differentiability: it leaves all velocity operator values unchanged. For an actual classical PDE interpretation, velocity regularity is still required separately.

For any set `I : Set ℝ`, `absorb_on` quantifies over **all** `t ∈ I` and **all** spatial points and assumes the pressure-slice smoothness, original equation, and gradient identity there. It supplies only the corrected equation on that same set. To use it at a restart, take `I = Ioo t₀ 1`, `0<t₀<1`; prove smoothness on each closed slab `[t₀,t₀+S]`, `0<S<1−t₀`, separately. It does not shift time, certify the new time-zero within derivative, or create a solution at time one.

The two pressure-contract lemmas say:

* for any `D : Set SpaceTime`, `ContDiffOn ℝ ∞ p D` and the same for `φ` imply it for `p−φ`;
* for any real time set `I`, `UnitSpatialPeriodsOn I p` and the same for `φ` imply it for `p−φ`.

There is no demand that the potential decay on R³ when the pressure class does not demand it. On the torus the potential must be periodic, or an alternative admissible correction must actually be exhibited. Smoothness merely before one does not supply smoothness through one. A time-only gauge `c(t)` has zero spatial gradient, as checked by `time_gauge_gradient`; temporal smoothness of `c` is unnecessary for this spatial statement but necessary if one wants a smooth corrected spacetime pressure.

## Solenoidal forcing and zero-datum obstruction

**Unformalized deductions, with analytic hypotheses explicit.** In L²(R³), Helmholtz projection onto divergence-free fields removes gradient components under the usual distributional/functional-domain hypotheses. On the unit torus its Fourier multiplier at nonzero frequency is `Id − k⊗k/|k|²`; the zero-frequency multiplier is `Id`. Consequently a nonzero constant vector force is divergence-free but cannot be the gradient of a periodic scalar: integrating its coordinate derivative over a period would give both zero and that nonzero component. Curl-free alone is not enough on the torus; zero circulation/mean constraints matter. No Helmholtz operator or decomposition theorem is constructed in the new Lean file. For arbitrary φ, `f−∇φ` is simply remaining force, **not automatically a solenoidal field**. Solenoidality would require `Δφ=div f` and appropriate global conditions.

On a smooth presingular slab, suppose the actual velocity is divergence-free and has a fixed compact spatial support (R³), or velocity and φ are smooth periodic fields (torus). Then

\[
\int u\cdot\nabla\phi= -\int\phi\,\operatorname{div}u=0.
\]

For R³ compact velocity, the product `φu` has compact support, so arbitrary pressure growth at infinity does not spoil this integration by parts. For a noncompact competitor, integrability and vanishing boundary flux cannot be omitted. On the torus opposite faces cancel only with the requisite periodic fields. Time integration and the kinetic-energy derivative require slab regularity and integrability; these follow for a smooth common-compact-support reference, not from pointwise finite energy alone.

Under these conditions at viscosity `ν>0`, if the **entire** forcing on `[0,T]` is an admissible gradient and `u(0)=0`,

\[
\tfrac12\|u(T)\|_2^2+\nu\int_0^T\|\nabla u\|_2^2\,dt=0.
\]

Nonnegativity and smoothness imply `u(T,x)=0` for every x. For every `T<1` this contradicts the candidate's speed growth. Hence effective nongradient forcing must occur somewhere during generation of the zero-datum reference. This does **not** imply nongradient forcing on every terminal interval. If absorbability holds only on `[t₀,1)`, the energy identity starts with `½‖u(t₀)‖₂²`, generally nonzero. Dissipating finite energy is not inconsistent with pointwise blowup. Terminal absorbability remains an open construction obligation, not something refuted by this global argument.

## Source map and actual candidate connection

* `NavierStokes/ProblemStatement.lean`: `pressureGradient`, `navierStokesResidual`, `UnitSpatialPeriodsOn`, `CandidateProperties`, `Solution`. `Solution` hardcodes zero datum even after restriction: it is not used as an arbitrary restart structure here.
* `NavierStokes/ResidualCalculus.lean`: `pressureGradient_add` assumes differentiability at the spatial point; confirms the genuine derivative calculus and sign convention.
* `NavierStokes/SolutionDifference.lean`: `pressureGradient_sub` supplies the actual smooth-slice subtraction rule used in the proofs.
* `NavierStokes/CandidateFromLimits.lean`: `force_eq_activated_residual` identifies the force with the activated residual for `0≤t<1`; `force_zero_from` only applies at `t≥2`. Neither provides a gradient representation before one.
* `NavierStokes/R3CompactCandidate.lean`: `Properties` extends the real `Solution (Ico 0 1)` with smooth force, common compact velocity support, compact force support, and speed growth; `of_limits` builds it from compact incoming fields and actual residual limits. This is the reference to which the compact energy discussion applies.
* `NavierStokes/ActualCandidateAssembly.lean`: `selected_witness` closes the construction and includes `compact_candidate`; `selected_candidate` extracts the periodic candidate. To instantiate `absorb_on`, restrict the selected candidate's equation to the terminal time set and supply a new potential and its smooth slices. The latter input is missing, not hidden in `selected_witness`.
* `NavierStokes/PeriodicUniqueness.lean`: `cubeIntegral_pressure_energy_zero` already formalizes the periodic spatial work cancellation for smooth periodic velocity/pressure slices and pointwise zero divergence (lines 213–225). It is source-inspected, not newly imported or independently rechecked here. No complete zero-datum energy obstruction theorem is claimed as a new Lean result.

## Accepted declarations and validation

Only accepted source: `Research/UnforcedRestart/pressure-absorption/Main.lean`. Imports: `NavierStokes.ResidualCalculus`, `NavierStokes.SolutionDifference` (the latter imports the baseline problem statement). Inline `#print axioms` is the complete audit; no separate research import mapping is required.

All names below carry prefix `UnforcedRestart.PressureAbsorption.`:

| Declaration | Classification / hypotheses |
|---|---|
| `residual_sub_pressure` | A, unconditional differential identity under two smooth pressure-slice hypotheses |
| `residual_after_correction` | A, additionally assumes actual residual equals f at the point |
| `unforced_iff_gradient` | A, same assumptions; necessary and sufficient gradient identity for this correction |
| `corrected_pressure_smooth` | A, pressure-class preservation under two stated `ContDiffOn` hypotheses |
| `corrected_pressure_periodic` | A, pressure-class preservation under two stated repository periodicity hypotheses |
| `absorb_on` | A, explicitly conditional PDE lemma under quantified smooth slices, residual equation and gradient identity |
| `time_gauge_gradient` | A, unconditional spatial identity for arbitrary `c : ℝ → ℝ` |

Exact final successful command (exit **0**, run serially):

```sh
env LEAN_NUM_THREADS=1 lake env lean -j1 \
  -DautoImplicit=false -DwarningAsError=true \
  -o Research/UnforcedRestart/pressure-absorption/out/Main.olean \
  -i Research/UnforcedRestart/pressure-absorption/out/Main.ilean \
  Research/UnforcedRestart/pressure-absorption/Main.lean \
  > Research/UnforcedRestart/pressure-absorption/out/Main.log 2>&1
```

`out/Main.exit` records 0. `out/Main.log` contains all seven axiom closures, each exactly `{propext, Classical.choice, Quot.sound}`. Fresh strict research elaboration against the prepared cached baseline is established; no clean dependency rebuild, independent Comparator check, or Clay-prose equivalence is claimed. No failed Lean attempts or auxiliary exported definitions remain.

## Success/failure criteria and remaining bridges

Achieved: actual residual sign, exact leftover force, periodic/smooth pressure contracts, and time-only gauge distinction. Failed as a forced-to-unforced reduction: there is no exhibited potential on an entire terminal spacetime neighborhood.

Required next inputs: (1) a terminal gradient identity, not just terminal jets or axial values; (2) smooth admissible potential with periodicity in the periodic case; (3) restart datum and time-translation boundary checks; (4) applicable same-positive-viscosity local existence/uniqueness and comparison-class membership. None is replaced by a theorem whose hypothesis says that the desired unforced solution already exists. No conjecture of terminal absorbability is endorsed by this report.
