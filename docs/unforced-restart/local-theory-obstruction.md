# Local theory and noncircularity audit (agent 13)

## Verdict and scope

**D — source audit / obstruction:** No applicable general Navier–Stokes local-existence or continuation declaration was located in the bounded source search. Existing NS uniqueness is useful and genuinely viscous, but the named lifespan module is not local theory. Three small diagnostic theorems were strictly checked; none supplies existence, lifespan coverage, terminal force removal, or A/B failure.

Independently read `PLAN.md`, prior Astra `final-report.md` and `skeptical-review.md` in the artifact directory identified by the plan, and the actual source declarations below. Their forced/unforced warning is confirmed at the signatures. This is not a full independent audit of the candidate construction or of whole-space pressure recovery.

**Important logical qualification:** Local existence is needed to *construct* an unforced restart evolution and discuss its maximal lifespan. It is not logically necessary for a contradiction against A/B: one may assume the asserted global unforced solution exists for an admissible snapshot. That legitimate contradiction hypothesis provides horizon coverage. The missing force-removal or quantitative comparison bridge remains; local existence alone would not supply it.

## Actual source map

All source paths in this section are baseline, read-only.

| Path / declaration | Actual content and applicability |
|---|---|
| `NavierStokes/ActualCandidateAssembly.lean`, `Witness`, `selected_witness` (lines 1016–1074) | One selected schedule and actual sums `ASum`, `BSum`, `PSum`; activated periodic velocity/pressure with `CandidateProperties`; separate `compactForcing` with `R3CompactCandidate.Properties` for activated `MixedPeriodicAssembly.cutVelocity ASum BSum` and `SpatialLocalization.cutPressure PSum`. The latter is the R³ snapshot source. These are constructed **forced** fields, not arbitrary-data existence. |
| `NavierStokes/R3CompactCandidate.lean`, `Properties`, `of_limits` | Smooth presingular solution, one compact velocity support for all `0≤t<1`, smooth supported force, speed unbounded at 1. No compact-support promise for a new unforced solution. |
| `NavierStokes/CandidateFromLimits.lean`, `force_eq_activated_residual`, `force_zero_from` | Actual residual identity for `0≤t<1`; shutdown only for `t≥2`. Neither gives a terminal unforced interval before 1. |
| `NavierStokes/ProblemStatement.lean:189–203`, `Solution`, `Solution.mono` | Viscosity one; full temporal derivative at positive times; `u(0,x)=0` independent of whether `0∈I`. Restriction retains the same time coordinate and zero datum. |
| `NavierStokes/MaximalLifespan.lean`, `ClassicalSolution`, `.restrict`, `.agree_on_overlap`, `candidate_no_solution_after_one` | Periodic velocity **and pressure**, zero datum, `[0,T)`, `T>0`. Uniqueness of existing solutions with the **same force**, and exclusion beyond 1 for the candidate's force. No local existence or continuation constructor. |
| `NavierStokes/CandidateConsequences.lean`, `candidate_admissible_lifespans`, `candidate_is_maximal` | Lifespans `(0,1]` for the particular constructed forced zero-datum problem, via candidate restriction and exclusion. Does not prove the general existence of maximal solutions. `zero_classical_solution_of_zero_force` and `candidate_force_nonzero_before_one` confirm the zero-datum obstruction. |
| `NavierStokes/PeriodicUniqueness.lean:390–429`, `classical_uniqueness_on_Icc` | Raw-field theorem on **arbitrary** `[a,b]`; equal datum at `a` need not be zero. All four fields smooth on the slab; both velocities and pressures unit-periodic; divergence and same forced PDE on `(a,b)`. Thus nonzero-data uniqueness is already available without using `ClassicalSolution`. |
| `NavierStokes/R3/WholeSpaceUniqueness.lean:29–49`, `classical_uniqueness_on_Icc` | Raw fields on `[0,T]`, `T>0`, equal (not necessarily zero) initial velocities, equal residuals, both smooth pressures, reference uniformly compact-supported, competitor uniformly finite-energy on that slab. No competitor pressure decay assumed; the proof invokes substantial pressure recovery. General noncompact-vs-noncompact strong uniqueness is not this signature. |
| `NavierStokes/R3FiniteEnergyComparison.lean`, `compact_candidate_agree_on_overlap` | Packages the preceding theorem for the original zero-datum forced candidate and `GlobalSolutionRn f v q`. Cannot substitute a different force or a nonzero restart into that wrapper. Translate the raw theorem instead. |
| `NavierStokes/TangentODE.lean`, `IntervalSystem`, `linear_solution_unique` | Globally Lipschitz state-space ODE and continuous bounded linear operators. NS diffusion is unbounded on a fixed Sobolev space; the nonlinearity loses derivatives. No direct Picard–Lindelöf application to the NS PDE is supplied. |
| `NavierStokes/ViscousPropagator.lean`, `norm_le_initial_add_integral` | Estimates conditional on a linear Hilbert-space ODE, used for a two-mode equation. Not nonlinear NS existence. |
| `Euler/OrdinaryEulerStability.lean`, `referenceNormPath`, `referenceWordBound`, `eventually_h3_bound` | Euler evolutions, with fourth-order reference control for third-order differences. Neither the viscous equation nor restart existence is obtained by substitution. |

Search evidence: `Research/UnforcedRestart/local-theory-obstruction/out/source-search.log`. Searches covered theorem/definition/structure names for local existence, continuation criteria, strong/mild solutions, ODE imports in `NavierStokes/**/*.lean`, and `Navier.?Stokes` in prepared mathlib sources. No mathlib NS-name matches; ODE imports led to the two modules above. This is a documented search, not a theorem that no differently named declaration could exist.

## Exact restart and external local-theory obligation

**Unformalized contract, not an assumed Lean solution predicate.** Let
`Space = EuclideanSpace ℝ (Fin 3)`, fix `ν : ℝ` with `ν>0`, `t₀ : ℝ` with `0<t₀<1`, and put `H=1-t₀>0`. Snapshot `a : Space → Space` is `a(x)=u(t₀,x)`. Internal fields have type `ℝ × Space → Space`, pressures `ℝ × Space → ℝ`; Comparator fields are curried space-first.

A standard strong local-theory route would take an integer `m≥3`, divergence-free `a∈H^m(Ω;ℝ³)`, and obtain **some** `T>0` and

\[
v\in C([0,T];H^m)\cap L^2(0,T;H^{m+1}),\qquad
\partial_s v\in L^2(0,T;H^{m-1}),
\]
\[
\partial_s v+(v\cdot\nabla)v=\nu\Delta v-\nabla q,
\quad\operatorname{div}v=0,\quad v(0)=a.
\]

Here `Ω` is R³ with Lebesgue measure, or the unit torus (equivalently unit-periodic lifts, with norms integrated on one cube). This is an external standard local-theory specification to import/prove, not a checked result in this task. Smooth data in all Sobolev orders require a persistence/bootstrapping theorem giving one common positive lifespan and jointly smooth velocity **and pressure up to the initial boundary**, not a separate possibly shrinking lifespan for each derivative order. Smoothness at `s=0` must justify Comparator's `derivWithin (Ici 0)`, not merely PDE validity for `s>0`.

A useful continuation theorem must state its criterion and class, e.g. for a maximal strong solution with finite endpoint `T*`, bounded `H^m` norm on `[0,T*)` allows extension. This is external analytic input, not supplied here. Its converse blowup alternative does **not** show a particular solution has finite `T*`. A local lifetime depending on `ν,m,‖a‖_{H^m}` need not exceed `H`; making `t₀` close to 1 simultaneously changes (potentially enlarges) the snapshot norm. Nor do separate local solutions automatically glue: uniqueness and regularity at each junction are needed.

### Matching A/B's actual classes

`NavierStokes/ComparatorDefinitions.lean` was read in full. Required global hypotheses are:

* A/R³: `InitialVelocityConditionDecay a` (all derivative orders and **real** decay exponents), then `NavierStokesExistenceAndSmoothnessRn ν a (fun _ _ => 0) v q`. This includes smooth velocity and pressure on `Space × [0,∞)`, PDE at every `s≥0` with the within derivative, divergence and initial datum, `MemLp (‖v · s‖) 2` at every nonnegative time, and one strict upper bound for energy at all future times. A standard unforced energy inequality would provide a non-strict bound; enlarge it to obtain the strict field. This class-conversion/energy proof is still required.
* B/periodic: `InitialVelocityConditionPeriodic a`, then `NavierStokesExistenceAndSmoothnessPeriodic ν a 0 v q`; unit-periodic **velocity and pressure**, and no separate energy field. Nonzero spatial mean of `a` is allowed; local theory must not silently require zero mean. Mean-zero pressure is an optional gauge normalization, not an imposed datum condition. An affine pressure correction is not periodic.
* Internal `navierStokesResidual` is viscosity **one**. Use it at `ν=1`, or prove an explicit operator/normalization bridge; no free viscosity parameter can be inferred from it.

For conditional terminal force removal, if `f=∇φ` on `[t₀,1)` with a suitably smooth scalar potential (periodic in the periodic case), then `q_ref=p-φ` has zero residual. Raw uniqueness on each `[t₀,t₀+S]`, `0<S<H`, can identify it with a hypothetical global unforced comparator with datum `a`. R³ requires the shift of the raw whole-space theorem and its slab energy assumptions. Smoothness through `H` plus equality approaching the singularity then gives the compact-region contradiction. **The terminal potential/force vanishing is unknown**, not a consequence of local theory. If force instead remains nonzero, uniqueness is inapplicable and a quantitatively strong inhomogeneous stability argument is required.

## Independent noncircularity stress tests

All examples/deductions in this section are **unformalized** unless tied to the checked declarations below.

1. **Changing the forcing does change the equation.** At fixed pressure, `Rν(u,p)=f` and `Rν(u,p)=χf` require `(1-χ)f=0`. The checked `unchanged_fields_force_rigidity` proves the underlying actual residual identity. Allowing changed pressure only helps if `(1-χ)f` is an admissible gradient, with the correct sign of the pressure correction.
2. **Concrete periodic cutoff counterexample:** take a nonzero constant vector `e`, `u(t,x)=t e`, `p=0`, `f=e`. This is a smooth forced NS solution at every positive viscosity, zero datum, periodic velocity and pressure. For a genuine smooth switch `χ`, the zero-datum solution of force `χ(t)e` is `v(t,x)=(∫₀ᵗχ(r)dr)e`, not the original `u` where the forces differ. This tests local cutoff reasoning; constant forcing here is not being offered as a globally decaying C/D force. A smooth compact-time bump in place of the constant acceleration gives the same test with admissible decaying force.
3. **Flatness is not vanishing:** a smooth function equal to `exp(-1/(1-t)^2)` for `t<1` and zero for `t≥1` is nonzero at every presingular time despite all terminal derivatives vanishing. Endpoint jets cannot establish terminal absorbability or the necessary norm budget over all space.
4. **Wrong zero-datum adapter:** a nonzero snapshot cannot satisfy the existing `Solution` after shifting, even when its time set omits zero. This is checked. Snapshot data need not always be nonzero (activation creates an early zero region), so the formal lemma explicitly assumes a nonzero snapshot point.
5. **Global absorbability vs terminal absorbability:** periodic zero-force zero-datum classical solutions are identically zero, checked below using energy uniqueness. With an admissible periodic potential, globally absorbable forcing would reduce to that situation. This does not rule out energy injected before a later force-free restart with nonzero datum. Whole-space versions need their energy/pressure hypotheses.
6. **No automatic invariant persistence:** divergence freedom follows from the equation/constraint in an appropriate local theory; fixed compact support and exact axial identities do not. Diffusion already destroys support persistence for generic compactly supported heat data. The viscous vorticity equation has `νΔω`; Euler's pure support transport is not transferable. Unforced compact-first periodization is not automatically compatible at positive times after evolving each copy, because their diffusive tails can overlap and NS is nonlinear.
7. **Avoid circular thresholds:** assuming `sup_{s<H}‖v(s)‖_{H^m}<∞` to obtain continuation is a criterion, not evidence it holds. Conversely, assuming a bound `|u(t₀+s,0)-v(s,0)|≤ε|u(t₀+s,0)|` with `ε<1` all the way to `H` already transfers the desired growth; it must be derived from a force budget and PDE stability, not described as local well-posedness. An L² difference bound alone does not control point evaluation in three dimensions.
8. **Legitimate reductio vs circular existence:** assuming a global smooth comparator to refute A/B is legitimate. Assuming actual solutions for every cutoff on horizons approaching `H`, or a uniform strong comparison estimate, without deriving those hypotheses is not local theory. A smooth cutoff is an admissible *force constructor*, not a solution constructor or invariant-preservation theorem.

## Checked Lean deliverables

**Accepted file:** `Research/UnforcedRestart/local-theory-obstruction/Main.lean`.
Only import: `NavierStokes.MaximalLifespan`. No research cross-imports, custom definitions, or auxiliary exported helpers. Inline `#print axioms` is the axiom audit.

All names below have prefix `UnforcedRestart.LocalTheoryObstruction.`:

| Declaration | Exact assumptions / conclusion | Classification |
|---|---|---|
| `nonzero_snapshot_not_solution` | Arbitrary actual fields `u,f,p`, set `I : Set ℝ`, `t₀ : ℝ`; `∃x, u(t₀,x)≠0` implies `¬Solution I f (fun z => u(t₀+z.1,z.2)) p`. No interior/positivity assumptions needed for this logical obstruction. | C, unconditional formal diagnostic |
| `unchanged_fields_force_rigidity` | At one real time and spatial point, two viscosity-one residual identities for the **same** `u,p` imply equal force values. No differentiability assumption needed for equality transitivity of the actual defined operator. | A, elementary actual-residual bridge, not analytic control |
| `zero_datum_unforced_periodic_is_zero` | `ClassicalSolution (fun _=>0) T u p` implies `u(t,x)=0` for all `t∈[0,T)`, all `x`. All smoothness, zero initial datum, periodic pressure/velocity and lifespan positivity come from that real repository structure. | B, specialization of imported viscous uniqueness; no new energy derivation |

These are unconditional formal results in the sense of having no unproved axiom/bridge; the explicitly quantified hypotheses above are not asserted for a newly constructed unforced restart.

### Exact successful validation

Run from the prepared worktree root; no build/install/update:

```sh
env LEAN_NUM_THREADS=1 lake env lean -j1 \
  -DautoImplicit=false -DwarningAsError=true \
  -o Research/UnforcedRestart/local-theory-obstruction/out/Main.olean \
  -i Research/UnforcedRestart/local-theory-obstruction/out/Main.ilean \
  Research/UnforcedRestart/local-theory-obstruction/Main.lean \
  > Research/UnforcedRestart/local-theory-obstruction/out/Main.log 2>&1
code=$?
printf '%s\n' "$code" > Research/UnforcedRestart/local-theory-obstruction/out/Main.exit
```

**Exit 0.** `Main.log` prints, for each of the three exported theorems, exactly `[propext, Classical.choice, Quot.sound]`. No warnings. `Main.exit` records `0`. This is fresh strict elaboration against cached prepared baseline dependencies, not a new clean baseline rebuild or independent Comparator run. The baseline includes untouched challenge placeholders, but the accepted theorem axiom closures contain no placeholder axiom.

Initial failed attempt: the zero-solution equation referred to nonexistent `NavierStokes.SolutionDifference.zero_residual`; the actual declaration is `NavierStokes.ProblemStatement.zero_residual`. First command exited 1 and its failed elaboration printed a `sorryAx` recovery dependency; it was **not accepted**. Correcting the namespace and rerunning the complete file yielded the clean successful closure above. No incomplete Lean attempt remains on the acceptance list.

`git diff --exit-code` returned 0; evidence `out/tracked-diff.log` is empty. Writes are confined to this owned report and owned research directory. No source/config changes, commits, pushes, global settings, shared outputs, or broad builds.

## Success / failure criteria and remaining bridges

**Achieved:** auditable distinction between raw nonzero-data uniqueness and zero-datum wrappers; actual candidate path; local-vs-global logical distinction; three checked noncircular diagnostics; named endpoint, pressure, energy, support and viscosity obligations.

**Not achieved / unproved:**

1. Applicable NS local existence, smoothing at the initial boundary, persistence and continuation in an explicit Sobolev class, with comparison-class conversion and energy control.
2. Formal snapshot admissibility and shifted derivative/PDE bridges (owned by the corresponding specialists; no unfrozen cross-task results consumed).
3. A smooth terminal force-free or admissibly pressure-absorbable interval of the actual candidate.
4. Alternatively, quantitative fixed-viscosity strong-norm stability and actual forcing below its horizon-dependent threshold; lifespan coverage must accompany any constructed solutions.
5. A proof that any axial/support invariant needed for growth survives the changed equation; no such persistence is inferred from local uniqueness.

Items 1–2 are standard-theory/adapter formalization obligations; items 3–5 require substantial construction-specific estimates or new mathematics, not a generic local-existence citation. No conjecture of A/B failure is endorsed by this audit.
