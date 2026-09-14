# Periodic restart datum: checked bounded result

## Result and exact scope

**Unconditional formal implication (actual-field regularity bridge, class A; not a PDE existence theorem):** for every `u f : SpaceTime → Space`, `p : SpaceTime → ℝ`, every `hc : CandidateProperties u p f`, and every real `t₀` with `0 < t₀ < 1`, the datum

\[
a:\operatorname{EuclideanSpace}\,\mathbb R\,(\mathrm{Fin}\,3)\to
\operatorname{EuclideanSpace}\,\mathbb R\,(\mathrm{Fin}\,3),\quad a(x)=u(t₀,x)
\]

satisfies the real repository predicate `Comparator.InitialVelocityConditionPeriodic`: ordinary spatial `ContDiff ℝ ∞`, Comparator divergence zero at every spatial point, and unit periods in all three coordinate directions. No extra analytic assumption is needed beyond the actual candidate contract. The general helper even permits `t₀=0`; no theorem permits `t₀=1`.

This does **not** say `a=0`, or `a≠0`, for every interior restart. The original activation actually leaves early snapshots zero; later snapshots need not be zero. `Solution` and `GlobalSolutionOne` hardcode zero original datum and cannot serve as arbitrary-data restart classes.

The pressure slice is separately proved smooth and unit-periodic. It is **not** prescribed as initial data in the Comparator problem.

## Accepted Lean file and declarations

`Research/UnforcedRestart/periodic-restart-data/Main.lean`, namespace `UnforcedRestart.PeriodicRestartData`:

* `snapshot_admissible`: assumes slice time in `Ico 0 1`, spacetime smoothness on `preSingularDomain`, zero internal divergence at that time, and unit spatial periods; concludes the actual Comparator initial-data predicate.
* `candidate_snapshot`: specializes the preceding implication to `CandidateProperties` and `0<t₀<1`.
* `candidate_pressure_snapshot`: same candidate/time assumptions; concludes scalar slice smoothness and `Comparator.IsOnePeriodic`.
* `periodize_snapshot`: for every normed additive commutative group `V`, every `g : SpaceTime → V`, and every real `t₀` and spatial `x`, unfolds the **actual** `PeriodicLocalization.periodize` to `∑' n, g (t₀,x-lattice n)`. Unconditional algebraic infrastructure (C), not convergence or nonlinear superposition.
* `pressure_gauge_periodic`: for every time set `I`, periodic pressure `p` on `I`, and arbitrary `c : ℝ → ℝ`, proves periodicity of `p(t,x)+c(t)`. Unconditional algebraic infrastructure (C). This lemma asserts neither smoothness nor a PDE gauge identity for nonsmooth `c`.

Imports: `NavierStokes.TimeLocalization`, `NavierStokes.ComparatorBridge`, `NavierStokes.PeriodicLocalization`. `ProblemStatement` and Comparator definitions are transitively imported. No challenge module or cross-task research import.

## Source path to the actual candidate

Independently inspected the source and both prior Astra `final-report.md` and `skeptical-review.md` in the planner-specified artifact directory. Their warning that C/D does not imply failure of A/B is retained.

* `ProblemStatement.lean:103–116`: actual `CandidateProperties` fields supplying smoothness, periods, divergence, and viscosity-one forced equation.
* `TimeLocalization.lean:91–99`: `spatial_smooth_including_initial` composes the smooth field with the spatial slice mapping into the relative domain. This avoids unjustified full time differentiability at a boundary.
* `ComparatorBridge.lean:34–38`: `divergence_eq` identifies the trace-based Comparator operator with internal coordinate divergence. Argument order is genuinely `(t,x)` internally; `toComparator u x t = u (t,x)`.
* `ComparatorDefinitions.lean:95–113,138–141`: precise datum predicate; no mean-zero or energy condition is added.
* `ActualCandidateAssembly.lean:1017–1051`: `Witness` fixes one schedule and the actual `ASum`, `BSum`, `PSum`. Its candidate velocity is `TimeLocalization.activatedVelocity (MixedPeriodicAssembly.periodicVelocity ASum BSum)`; pressure is `TimeLocalization.activatedPressure (SpatialLocalization.periodicPressure PSum)`. The same witness retains a compact forcing and compact candidate with velocity `activatedVelocity (MixedPeriodicAssembly.cutVelocity ASum BSum)` and pressure `activatedPressure (SpatialLocalization.cutPressure PSum)`.
* `ActualCandidateAssembly.selected_witness` and `.selected_candidate` (1070–1078) close that construction. Applying the checked `candidate_snapshot` to the witness's candidate field gives the claimed actual snapshots. This final existential specialization is source-mapped, not a new compiled import of the entire construction in this task.

## Compact-first compatibility and viscosity

`PeriodicLocalization.periodize` (lines 59–65) is the spatial lattice sum. The checked snapshot formula shows restriction in time commutes definitionally with that sum. For a fixed compact spatial support, only finitely many lattice translates contribute locally; periodization smoothness is not a consequence of a formal sum alone.

The nonlinear compatibility uses **separated copies**, not linear superposition of Navier–Stokes solutions. `MixedPeriodicAssembly.periodicVelocity_eventuallyEq_cut` (111–116) gives local equality on `innerCube (1/4)`. The compact-first theorem `candidate_of_periodization` (512–533) requires: compact candidate properties; uniform cube support of velocity and force; smooth periodic `U,P`; and local equality of both with compact `u,p` on the inner cube. It then invokes `periodized_navier_stokes` and returns `CandidateProperties U P (periodize f)`. The actual assembly discharges these requirements through `exists_candidate_force`. The pressure local-equality assumption must not be dropped.

**Unformalized deduction:** a smooth periodic slice has finite kinetic energy over a unit fundamental cube, by boundedness on its compact closure and finite volume. No whole-space `MemLp` claim for periodic fields is made. The delivered periodic Comparator class has no explicit energy field. This task does not provide a new integral theorem.

The actual residual is
\[
\partial_tu+Du(u)-\Delta u+\nabla p=f,
\]
so viscosity is **one**. A restart changes time origin, not viscosity. Its hypothetical unforced competitor must have `ν=1` as well. More generally one can state a separate restart problem for every fixed real `ν>0`, but the datum theorem itself has no viscosity parameter and does not turn the actual candidate into a solution at another viscosity. Comparator viscosity normalization also rescales velocity/time/force and is not used here.

## Pressure and the missing restart theorem

`Comparator.NavierStokesExistenceAndSmoothnessPeriodic ν a 0 v q` quantifies `v : Space → ℝ → Space`, `q : Space → ℝ → ℝ`; both are smooth on `Space × Ici 0`, satisfy the equation and divergence for all `s≥0`, obey `v x 0=a x`, and both are unit-periodic for every `s≥0`. The time derivative is `derivWithin (v x ·) (Ici 0) s`. No pressure initial-value constraint and no mean-zero normalization are imposed.

A smooth time-only pressure gauge is compatible with this class; periodicity alone is the checked part here. An affine spatial pressure is not generally admissible. Absorbing `f=∇φ` requires the sign `p-φ` and a smooth periodic admissible potential, not merely a terminal point jet identity.

**Explicitly conditional proposed PDE bridge, not formalized here:** let `H=1-t₀>0`, define `uᵣ(s,x)=u(t₀+s,x)` and `pᵣ(s,x)=p(t₀+s,x)`. On `0<s<H` the same-viscosity equation is forced by `f(t₀+s,x)`. It becomes unforced only if this force vanishes or an admissible pressure correction absorbs it on that whole interval. The closed-boundary derivative at `s=0` and smoothness on each `[0,S]`, `0<S<H`, require their own translation proof. There is no smoothness claim at `H`.

Remaining unproved bridges: terminal force removal/absorption for this candidate; arbitrary-data NS local existence and class-compatible uniqueness; shifted boundary PDE; quantitative stability preserving the singular mechanism when the force is changed. None is disguised as a datum hypothesis. No conjecture of successful force removal is asserted.

## Validation and acceptance evidence

Successful focused command (exit **0**), with inline axiom audit for every exported theorem:

```sh
env LEAN_NUM_THREADS=1 lake env lean -j1 \
  -DautoImplicit=false -DwarningAsError=true \
  -o Research/UnforcedRestart/periodic-restart-data/out/Main.olean \
  -i Research/UnforcedRestart/periodic-restart-data/out/Main.ilean \
  Research/UnforcedRestart/periodic-restart-data/Main.lean \
  > Research/UnforcedRestart/periodic-restart-data/out/Main.log 2>&1
```

`out/Main.exit` records 0. `out/Main.log` contains all five axiom closures; each is exactly `[propext, Classical.choice, Quot.sound]`. An initial failed elaboration lacked `open scoped ContDiff` and an explicit beta-reduced rewrite target; both were corrected before acceptance. Its error-recovery `sorryAx` output was not accepted as a theorem. No incomplete Lean attempt remains on the acceptance list.

`git diff --exit-code` passed after validation (tracked baseline unchanged). No build/install/configuration changes or commits. Fresh evidence is elaboration of this file against prepared baseline imports, not a clean kernel rebuild, independent Comparator challenge execution, or Clay-prose equivalence audit.

Success criterion met: actual periodic datum admissibility, pressure slice contract, and bounded lattice/gauge identities. Failure criterion for any stronger claim: absent PDE/existence/force-removal bridge. Accordingly no unforced counterexample or A/B resolution is claimed.
