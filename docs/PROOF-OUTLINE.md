# Proof outline

This document is a reader's map of the two developments in this repository. It says what
the initial data and the forcing are, which quantity diverges and why, how the modules are
layered, and where the load-bearing intermediate results live.

It is an orientation document, not a proof. The Lean sources are the statement of record;
where this text and a module disagree, the module is right. Every declaration and file name below
was re-checked against the tree by grep, but the repository is under active simplification, so
locate things by name (`grep -rn "theorem selected_candidate" NavierStokes/`) rather than by line
number. Two former monoliths, `Euler.EulerProof` and `NavierStokes.CorrectionStep`, are now
aggregator modules whose contents live in the like-named directories beside them (§1.3 E, §2.3 D);
a grep for a declaration will land in a part, not in the aggregator.

Both roadmaps were reconstructed from theorem statements, module docstrings and the import
graph. The source manuscripts are referred to in about 90 module docstrings, by numbered result and
equation, but are not included in the repository and carry no DOI or URL here, so the
correspondence between these files and their intended arguments cannot be checked from inside
the repository.

---

## 0. What is delivered

Four theorems, each stated in the vocabulary of an independent reference statement and checked
by the Comparator gate (see `ComparatorChallenges/README.md`):

| Theorem | Module | Content |
|---|---|---|
| `Euler.euler_breakdown_R3` | `Euler/Solution.lean` | smooth, rapidly decaying, divergence-free `u₀ : ℝ³ → ℝ³` with no global smooth finite-energy Euler solution |
| `Euler.exists_compact_smooth_euler_singularity` | `Euler/Solution.lean` | the full package: compactly supported nonzero `u₀`, a lifespan `0 < T* ≤ 1`, a Sobolev-class solution on `[0,T*)`, bounded energy, existence exactly for `T < T*`, `limsup ‖v‖_{C¹} = ⊤` at `T*`, and `∫⁻ ‖ω‖_∞ = ⊤` |
| `NavierStokes.Comparator.navier_stokes_breakdown_R3` | `NavierStokes/ComparatorSolution.lean` | Clay alternative (C): for every `ν > 0`, initial data and forcing with no global smooth solution of uniformly bounded kinetic energy on `ℝ³` |
| `NavierStokes.Comparator.navier_stokes_breakdown_periodic` | `NavierStokes/ComparatorSolution.lean` | Clay alternative (D): the same on `ℝ³/ℤ³` |

Both `Solution` modules end with `#print axioms`; the reported axioms are `propext`,
`Classical.choice`, `Quot.sound`.

The definitions used in these statements are re-declared inside the repository
(`Euler/SolutionDefinitions.lean`, `NavierStokes/ComparatorDefinitions.lean`) so that the
proof side never imports the challenge modules; the Comparator run is what checks that these
copies agree with the reference.

---

## 1. Euler

### 1.1 The data, and the quantity that diverges

The Euler result is **unforced**. Everything is in the initial velocity.

* **Initial datum.** `EulerPacketInduction.initialDatum` (`Euler/PacketFiniteLifespan.lean`),
  defined as `Stage.initialDataLimit packets` — the limit, in every Sobolev order `Hˢ`, of the
  initial velocities of a recursively constructed infinite family of *packet stages*. It is
  smooth, compactly supported, nonzero and divergence-free.
* **Divergent quantity.** `Stage.activationGradient` (`Euler/PacketStageGrowth.lean`), defined
  as `‖fderiv ℝ (fun x => P.state.evolution.velocity (P.time, x)) 0‖` — the operator norm of the
  velocity gradient at the origin, at stage `P`'s own activation time. The key estimate is

  ```
  gradient_lower : previousShear J X n / 2 ≤ P.activationGradient      (n ≠ 0)
  ```

  and `previousShear J X (n+1) = shear J X n = exp(scaleSequence J X n / (J+n)^5)` grows without
  bound, so
  `gradient_atTop : Tendsto (fun n => (P n).activationGradient) atTop atTop`.
* **What the divergence buys.** Each stage's gradient is attained on that stage's *own* short
  horizon, all of which sit inside one fixed base horizon
  (`baseHorizon J X = 6·J²·X^(-498)`, `Euler/PacketBaseGuardScales.lean`). A hypothetical smooth
  Euler evolution on the whole base horizon starting from `initialDatum` would be `H³`-close at
  time zero to every stage, and a no-gradient-escape lemma would then cap all the
  `activationGradient`s — contradicting `gradient_atTop`. This is
  `Stage.no_euler_evolution_of_initial_H3` (`Euler/PacketStageContradiction.lean`).

### 1.2 The scale hierarchy

`Euler/PacketSourceScaleSequence.lean` fixes the whole hierarchy in closed form, from one scalar
sequence and two parameters (an index offset `J : ℕ` and a base `X : ℝ`). The sequence itself is
`scaleSequence`, defined one module earlier in `Euler/PacketSourceScaleChoice.lean` by
`scaleSequence J X 0 = X` and `scaleSequence J X (n+1) = (J+n)² · scaleSequence J X n`:

```
shear        J X n = exp( scaleSequence J X n / (J+n)^5 )
frequency    J X n = exp( scaleSequence J X n / (J+n)^2 )
spike        J X n = exp(-scaleSequence J X n / (J+n)^3 )
supportScale J X n = exp(-scaleSequence J X n / (J+n)^(7/2) )
previousShear J X 0 = X^1000,   previousShear J X (n+1) = shear J X n
olderShear    J X 0 = 1,        olderShear    J X (n+1) = previousShear J X n
timeWidth    J X n = 3 · scaleSequence J X (n+1) · scaleSequence J X n / sqrt (previousShear J X n)
```

Reading the hierarchy: each stage adds an oscillation that is faster (`frequency`), more sheared
(`shear`), supported on a smaller set (`supportScale`) and active for a shorter time
(`timeWidth`) than its predecessor. The stage horizons shrink fast enough that all of them fit
inside `baseHorizon`, while the shear — and hence the gradient at the origin — diverges.

### 1.3 Layers

**A. Submission surface — `Euler/Solution.lean` (75 lines).**
`initialDatum_no_global_solution` is the hinge: one private theorem whose proof feeds the
vorticity confinement, the local upgrade and the identification of the canonical solution with
any Comparator-class solution into `finiteLifespan_contradiction_of_compact_vorticity`. The two
delivered theorems are then packaging.

**B. Comparator ↔ development bridge (namespace `Euler.ComparatorBridge`, plus its analytic support modules).**
This is analysis, not glue.
* `ComparatorLocalEvolution.compactCurlLocalUpgrade` (`Euler/ComparatorLocalEvolution.lean`)
  converts a solution in the reference's function class, with compact initial vorticity, into an
  ordinary `Evolution` of this development on a short interval: elliptic div/curl recovery
  (`Euler/DivCurlRecovery.lean`) for the spatial `L²` jets, and pairings against dense compact
  solenoidal test fields (`Euler/ProjectedEulerPairing.lean`, `Euler/CurlTimeDerivative.lean`,
  with the dense-test-to-strong-derivative upgrade isolated in `Euler/WeakHilbertODE.lean`) for
  the time derivative.
* `maximalVelocity_eq_of_compactCurlLocalUpgrade` (`Euler/ComparatorIdentification.lean`) uses
  ordinary uniqueness to identify the canonical maximal solution with every Comparator-class
  global solution below `T*`.
* `canonical_vorticity_hasCompactSupport` (`Euler/CanonicalVorticityConfinement.lean`): the
  canonical field's vorticity stays inside a fixed compact set `canonicalVorticityBall` for all
  `t < T*`, by `H³` stability against the packet horizons.
* `finiteLifespan_contradiction_of_compact_vorticity`
  (`Euler/CompactVorticityContradiction.lean`) is where `False` is actually produced: uniformly
  confined vorticity gives a uniform bound `M` on `‖ω‖_∞`, hence `∫₀^{T*} ‖ω‖_∞ ≤ M·T*`, which
  contradicts Beale–Kato–Majda.
* Supporting: `Euler/FiniteEnergyTruncation.lean`, `Euler/TruncatedBackwardFlow.lean` and
  `Euler/FlowEscapeBound.lean` (short-time compact-vorticity persistence, via global flows of
  compact solenoidal truncations rather than trajectories of the untruncated velocity), reaching
  the bridge through `Euler/ComparatorLocalCompactVorticity.lean`;
  `Euler/ComparatorMaximalSolution.lean` and
  `Euler/ComparatorMaximalFields.lean` (re-expression in the reference's Sobolev class and
  coordinate convention).

**C. Blowup criteria over a maximal lifespan (`EulerOrdinarySobolev`).**
* `Euler/OrdinaryEulerLifespan.lean` — `HasEulerEvolution A T`, and `FiniteLifespan` as
  `sSup {T | HasEulerEvolution A T}`. Membership of the endpoint is deliberately *not* asserted
  here.
* `Euler/OrdinaryEulerLocalExistence.lean` — `exists_local_evolution`: local well-posedness for
  any smooth solenoidal `L²` datum, as a strong Sobolev limit of regularized evolutions.
* `Euler/OrdinaryEulerContinuation.lean` — continuation past a closed endpoint (`no_endpoint`),
  hence `gradient_unbounded` at the finite maximal time.
* `Euler/OrdinaryLogarithmicGradient.lean` — the log-Sobolev gradient inequality
  `‖∇u‖_∞ ≲ 1 + ‖u‖_{L²} + ‖ω‖_∞ · log(e + ‖u‖_{H³})`, proved from a constructed Gaussian kernel
  and its heat equation.
* `Euler/OrdinaryBKMReduction.lean`, `Euler/OrdinaryEulerBKM.lean` — Beale–Kato–Majda:
  `vorticity_lintegral_eq_top`, `∫⁻_{[0,T*)} ‖ω(t)‖_∞ dt = ⊤`.
* `Euler/EulerC1Limsup.lean` — the filter-based `limsup ‖v(t)‖_{C¹} = ⊤` at `T*`, phrased through
  the pullback of the left-neighbourhood filter rather than a chosen sequence of times.

**D. The packet construction (the constructive core, and almost all of the code).**
* `Euler/PacketInductionStage.lean` — `structure Stage`, the ~30-field induction invariant: the
  parent map, the smooth state, low-frequency bounds (`low.Be`, `low.Bc`, `low.K`, `low.L`,
  `low.r`), the activation `time`, the horizon and support-scale identities, gradient and Hessian
  bounds against `previousShear`/`olderShear`, the geometric `frame` and its shear, error, tilt
  and compression conditions.
* `Euler/PacketInfiniteConstruction.lean` — the literal infinite family:
  `stages 0 = S.firstStage`, `stages (n+1) = (stages n).successor`, instantiated at
  `constructionScales` to give `packets`. `stages_initial_step` records that stage `n+1`'s initial
  velocity is stage `n`'s plus `high(frequency n) + mean(frequency n)`.
* `Euler/PacketForwardSuccessor.lean` (the time-zero step) and
  `Euler/PacketJoinedSuccessor.lean` (the positive-history step) build the successor, resting on
  the geometric packet choices `Euler/ParentGeometryForwardChoice.lean` /
  `Euler/ParentGeometryJoinedChoice.lean` and on the all-order correction field
  `Euler/AllOrderDriftCorrection.lean`.
* Below that sit the large analytic families consumed by the correction: `Gevrey*` (~46 modules),
  `Sobolev*` (~49), `Correction*` (~39), `AllOrder*` (~17), `Cylinder*` (~110),
  `Transverse*` (~119), `Mean*` (~147), with `Euler.EulerProof` — a foundational library of
  binomial/Gevrey majorants, Sobolev products, cylinder coordinates and pressure resolvents — at
  the base of the import DAG. Its name is historical: it is the foundation, not the Euler proof.

**E. `Euler.EulerProof`, the foundation.**
`Euler/EulerProof.lean` is now an aggregator: the 16k lines that used to sit in it were split,
along the top-level namespace blocks they already had, into eight parts under
`Euler/EulerProof/`, and the aggregator only re-exports them. The parts are strictly sequential —
each imports its predecessor — and only part 1 lists Mathlib imports, so a new Mathlib dependency
for the whole development belongs there. In dependency order:

1. `Euler/EulerProof/Foundations.lean` — Gevrey factorial majorants, smoothness of uniform limits,
   the geometric packet weights, and Lax–Milgram solvability for coercive operators with the
   regularity of the resulting inverse.
2. `Euler/EulerProof/LiftedTransport.lean` — the lifted `L²` and gradient space, the coercive
   pressure solve on it, metric transport and its derivatives, spatial regularity and the jet
   calculus, curl identities, and the metric energy evolution.
3. `Euler/EulerProof/CylinderSobolev.lean` — Bessel-weighted Fourier Sobolev norms on `Domain d`
   with their products and transport commutators, the chart identifying `Domain 4` with the lift
   tangent space, and the Sobolev algebra on the cylinder.
4. `Euler/EulerProof/Mollification.lean` — Sobolev norms and strong jet bounds for smooth tensor
   fields, the cylinder mollifier and its cover/Fubini identities, and the smooth representatives,
   tensors and pressures they produce.
5. `Euler/EulerProof/CutoffsAndEnergy.lean` — terminal energy and interval traces, the diagonal
   selection and Lagrangian formulations, vector calculus, the Gevrey cutoff family, the weighted
   energy and pressure bounds, and the graph pullback and breakdown criterion.
6. `Euler/EulerProof/PacketGrowth.lean` — the ODE core: the Riccati comparison driving one
   packet's growth, its stability under perturbation, and the ray system.
7. `Euler/EulerProof/PacketFrames.lean` — the bridge from ideal velocities to the ray system,
   stability and renewal of the moving frame, a global Picard–Lindelöf existence theorem, and the
   constants and coefficient control for a single stage.
8. `Euler/EulerProof/PacketScales.lean` — the scale vocabulary and its limits, the base and source
   scales and time widths, and the uniform, finite and activated scale choices that chain the
   stages into the cascade.

### 1.4 Key intermediate results (Euler)

| Declaration | Module | Role |
|---|---|---|
| `Stage.gradient_lower` | `Euler/PacketStageGrowth.lean` | `previousShear n / 2 ≤ activationGradient` |
| `Stage.gradient_atTop` | `Euler/PacketStageGrowth.lean` | the activation gradients diverge |
| `stages` / `packets` | `Euler/PacketInfiniteConstruction.lean` | the infinite packet family exists |
| `Stage.no_euler_evolution_of_initial_H3` | `Euler/PacketStageContradiction.lean` | no evolution on the base horizon from the limit datum |
| `initialDatum`, `lifespan` | `Euler/PacketFiniteLifespan.lean` | the datum and its finite maximal horizon |
| `exists_local_evolution` | `Euler/OrdinaryEulerLocalExistence.lean` | local well-posedness |
| `exists_finite_lifespan` | `Euler/OrdinaryEulerLifespan.lean` | maximal horizon as a supremum |
| `FiniteLifespan.gradient_unbounded` | `Euler/OrdinaryEulerContinuation.lean` | continuation ⇒ gradient blowup |
| `logarithmic_gradient_bound_solenoidal` | `Euler/OrdinaryLogarithmicGradient.lean` | log-Sobolev gradient inequality |
| `FiniteLifespan.vorticity_unbounded_of_logarithmic` | `Euler/OrdinaryBKMReduction.lean` | BKM reduction |
| `FiniteLifespan.vorticity_lintegral_eq_top` | `Euler/OrdinaryEulerBKM.lean` | `∫⁻ ‖ω‖_∞ = ⊤` |
| `FiniteLifespan.maximalC1Norm_limsup` | `Euler/EulerC1Limsup.lean` | `limsup ‖v‖_{C¹} = ⊤` |
| `compactCurlLocalUpgrade` | `Euler/ComparatorLocalEvolution.lean` | reference solution ⇒ ordinary evolution |
| `maximalVelocity_eq_of_compactCurlLocalUpgrade` | `Euler/ComparatorIdentification.lean` | identification with the canonical solution |
| `canonical_vorticity_hasCompactSupport` | `Euler/CanonicalVorticityConfinement.lean` | uniform vorticity confinement |
| `finiteLifespan_contradiction_of_compact_vorticity` | `Euler/CompactVorticityContradiction.lean` | the contradiction |

---

## 2. Navier–Stokes

### 2.1 Three facts to have up front

1. **Almost the whole development is one object.** The import closure of
   `NavierStokes.ComparatorSolution` is roughly 580 modules; the closure of
   `NavierStokes.ActualCandidateAssembly` — the construction of a single witness of
   `ProblemStatement.candidateStatement` — accounts for about 96% of those lines. Everything
   else is thin.
2. **There is one construction, not two.** Alternatives (C) and (D) share the same witness.
   `R3CompactCandidate.selected_compact_candidate` (`NavierStokes/R3ActualCandidate.lean`)
   extracts the whole-space candidate from the *same* `ActualCandidateAssembly.selected_witness`,
   by keeping the cut fields *before* periodization
   (`R3CompactCandidate.of_localized_fields`, `NavierStokes/R3CompactCandidate.lean`).
3. **The singularity does not come from the correction machinery.** It comes from a fixed slow
   base profile with an explicit closed form; see §2.2. The vast `Actual*` / `Cycle*` /
   `Correction*` apparatus exists to show that the infinite correction series converges to
   something smooth and divergence-free, that it solves the equation with a smooth force of
   compact future time support, and that it leaves the base undisturbed on the axis.

### 2.2 The data, and the quantity that diverges

* **Initial velocity: identically zero.** Both `NavierStokes/ComparatorTheorem.lean` and
  `NavierStokes/ComparatorR3Theorem.lean` instantiate the reference statement with
  `fun _ => 0`. The Clay statement permits a nonzero force, and `u° = 0` trivially satisfies its
  initial-data conditions; all of the construction lives in the forcing. A reader should not
  expect a nontrivial initial velocity anywhere in this development.
* **Forcing.** The exact `ν = 1` residual of the constructed velocity/pressure pair, which the
  construction arranges to be smooth, unit-periodic (whole space: compactly supported in space)
  and to vanish for all times beyond a fixed finite time
  (`ProblemStatement.CompactFutureTimeSupport`). For general viscosity the adapters use
  `fν(t,x) = ν² · f(ν t, x)` and rescale a hypothetical solution back to viscosity one
  (`ComparatorBridge.normalized_solution`).
* **Divergent quantity: the speed, near the spatial origin, as `t → 1⁻`.**
  `ProblemStatement.SpeedUnboundedAtOne u` says that for every `M > 0` and every `δ > 0` there
  are `t ∈ (1-δ, 1)` and `x` with `M < ‖u(t,x)‖`. It is proved from a closed-form identity for
  the slow base on the axis: `FinalSlowBase.origin` gives, for `t < 1`,

  ```
  velocity (t, 0) = ((1 - t)^(-CoordinateAlgebra.A h) * W.axis.j) • coordinateVector 2
  ```

  with `A h = 1/2 + h` and `0 < h < 1/2` (`NavierStokes/CoordinateAlgebra.lean`). Hence
  `FinalSlowBase.axis_tendsto` (`‖velocity (t,0)‖ → ∞` as `t → 1⁻`) and
  `FinalSlowBase.speedUnbounded`. The exponent `A` and its companions `D h = 1/2 - h`,
  `d η = 1 - η²`, `L h η = 1 - 2hη²` come from the self-similar change of variables
  `τ = q - z² q^{2h}` solved in `NavierStokes/SimilarityCoordinates.lean`
  (`forwardScalar a z q = q - z² q^a` with `a = 2h`).

* **Where the zero initial velocity comes from.** `TimeLocalization.activatedVelocity`
  (`NavierStokes/TimeLocalization.lean`) multiplies the singular fields by a smooth time switch.
  That is what makes the initial velocity identically zero without assuming it, and it is what
  moves the entire construction into the force.

### 2.3 Layers

**A. Statement adapters (~630 lines).**
`NavierStokes/ComparatorSolution.lean` — the two delivered theorems in the reference's exact
quantifiers, `∀ ν > 0`, with one-line bodies. `NavierStokes/ComparatorDefinitions.lean` — an
independent copy of the reference definitions, so that the adapters' import closure never
contains the challenge module. `NavierStokes/ComparatorBridge.lean` — the coordinate swap, the
operator identifications (`divergence_eq`, `gradient_eq`, `laplacian_eq`,
`temporalDerivative_eq`), the viscosity normalization `normalized_solution`, and
`forceConditionPeriodic_of_decay`, which upgrades jet decay to the reference's all-exponent
force condition.

**B. The two exclusion arguments.**
* Periodic (D): `ComparatorBridge.option_D_of_candidate` (`NavierStokes/ComparatorTheorem.lean`)
  → `MaximalLifespan.candidate_excludes_global_solution` (a global smooth periodic viscosity-one
  solution with the same zero datum and force would be classical past time one; periodic
  uniqueness forces agreement with the candidate on `[0,1)`, contradicting `SpeedUnboundedAtOne`)
  → `PeriodicUniqueness.classical_uniqueness_on_Icc`, classical `L²` energy uniqueness on the
  torus (closure: 4 modules — itself, `NavierStokes/PeriodicIntegration.lean`,
  `NavierStokes/ProblemStatement.lean` and the shared `NavierStokes/WithTopLemmas.lean`). Force
  conditions are discharged by `CandidateConsequences.futureJet_decay`.
* Whole space (C): `ComparatorBridge.option_C_of_compact_candidate`
  (`NavierStokes/ComparatorR3Theorem.lean`) →
  `ComparatorBridge.compact_candidate_excludes_global_solution`
  (`NavierStokes/R3FiniteEnergyComparison.lean`) →
  `NavierStokesR3.WholeSpaceUniqueness.classical_uniqueness_on_Icc`. That last theorem is the
  real analytic content of the C-branch: uniqueness on `ℝ³` where the reference velocity has
  compact spatial support but the competitor has only smoothness and a uniform finite-energy
  bound. Its closure is 66 modules, 62 of them the whole `NavierStokes/R3/` directory.

**C. The candidate assembly (almost everything else).**
* **Contract.** `ProblemStatement.CandidateProperties` / `candidateStatement`
  (`NavierStokes/ProblemStatement.lean`): smooth on `Ico 0 1 ×ˢ univ`, unit-periodic, zero
  initial velocity, divergence-free, exact `ν = 1` residual equal to a force with compact future
  time support, and `SpeedUnboundedAtOne`. Nothing is assumed or constructed in that module; it
  names `ActualCandidateAssembly.selected_candidate` as the proof and
  `NavierStokes/ComparatorTheorem.lean` as the consumer.
* **Top.** `ActualCandidateAssembly.selected_candidate` ← `selected_witness` ← `witness` ← the
  `Witness` predicate (`NavierStokes/ActualCandidateAssembly.lean`).
* **Hub.** `GermCandidateAssembly.exists_candidate_witness_of_finite_stages`
  (`NavierStokes/GermCandidateAssembly.lean`) takes the initial potential, the stage sequence,
  angular data, pressure stages, stage estimates, shrinking-support hypotheses, endpoint
  extensions and axis-zero germ conditions, and returns a diagonal schedule together with the
  periodic fields and the force. `origin_blowup` is its blowup half; `origin_eventually_base`
  is the statement that the corrections leave the base undisturbed near the axis.
* **Schedule.** `MixedCandidateAssembly.StageEstimates.exists_schedule`.
* **Field.** `SolenoidalDiagonal.potentialSum` — a `tsum` of cut potentials which is locally a
  finite prefix wherever the continuous scale is positive, hence smooth; terminal-slice
  regularity comes from `NavierStokes/JointResidualLimits.lean`.
* **Cycle.** `CorrectionState.State` (`NavierStokes/CorrectionState.lean`) →
  `CorrectionStep.CycleParameters` (`NavierStokes/CorrectionStep/CycleConstruction.lean`) and
  `CorrectionStep.CycleState` / `.step` / `.iterate`
  (`NavierStokes/CorrectionStep/WaveGains.lean`) → `CorrectionAnalyticStep.step`
  (`NavierStokes/CorrectionAnalyticStep.lean`, where the analytic invariant is shown to be
  preserved by every cycle) → `ActualCandidateConstruction.cycle`.
* **Localization.** `NavierStokes/SpatialLocalization.lean` (cut the potential *before* taking
  the curl, then periodize by a lattice sum), `NavierStokes/TimeLocalization.lean` (the smooth
  time switch), combined in `NavierStokes/MixedPeriodicAssembly.lean`.

**D. `NavierStokes.CorrectionStep`, the cycle bookkeeping.**
`NavierStokes/CorrectionStep.lean` is now an aggregator over six parts under
`NavierStokes/CorrectionStep/`, split along the original file's section boundaries, each part
depending only on the ones before it. Importing the aggregator gives exactly what importing the
former single file gave. In dependency order:

1. `NavierStokes/CorrectionStep/Fields.lean` — the shared vocabulary (`ScalarField`, `Tensor`,
   `TensorClass`, the covariance changes) and the full differential residual, `export`ed from
   `NavierStokes/SignedMeanGain.lean` and from the `HarmonicResidual.Actual` namespace of
   `NavierStokes/HarmonicResidual.lean`, plus the physical chart representation, the temporal
   construction and the gauge mean bookkeeping.
2. `NavierStokes/CorrectionStep/SignedStages.lean` — the physical residual decomposition, one
   stage's wave/mean residual, the signed stage parameters and their linear coefficient bridge,
   the gauge rank mean, and the moving-support, periodized and particular constructions.
3. `NavierStokes/CorrectionStep/CycleConstruction.lean` — the cycle parameters, the constructed
   temporal and rank stages, cycle mass preservation and mean completion, and the native equations
   satisfied by the periodized and particular families.
4. `NavierStokes/CorrectionStep/WaveGains.lean` — the linear wave theory of those families, the
   supported wave gain, the cycle recurrence (`CycleState`, `step`, `iterate`), the periodized curl
   identities, and the uniform and constructed wave gains.
5. `NavierStokes/CorrectionStep/MeanComposition.lean` — uniform periodized coefficients, the
   coherent reference particular family, the constructed mean stages and uniform gains, the
   four-stage mean composition, and the moving covariance and Gaussian means.
6. `NavierStokes/CorrectionStep/CycleInvariants.lean` — what one full cycle preserves: the cycle
   mean gain, regularity preservation, association transport and residual grouping, the real
   coefficient structure, the analytic invariant, and the wave cycle and derived request gains.

### 2.4 Key intermediate results (Navier–Stokes)

| Declaration | Module | Role |
|---|---|---|
| `ProblemStatement.candidateStatement` | `NavierStokes/ProblemStatement.lean` | the contract the whole construction meets |
| `ActualCandidateAssembly.selected_candidate` | `NavierStokes/ActualCandidateAssembly.lean` | the periodic witness exists |
| `R3CompactCandidate.selected_compact_candidate` | `NavierStokes/R3ActualCandidate.lean` | the same witness, before periodization |
| `R3CompactCandidate.of_localized_fields` | `NavierStokes/R3CompactCandidate.lean` | compact whole-space fields from the cut fields |
| `GermCandidateAssembly.exists_candidate_witness_of_finite_stages` | `NavierStokes/GermCandidateAssembly.lean` | finite-stage obligations ⇒ a witness |
| `MixedCandidateAssembly.StageEstimates.exists_schedule` | `NavierStokes/MixedCandidateAssembly.lean` | the diagonal schedule |
| `SolenoidalDiagonal.potentialSum` | `NavierStokes/SolenoidalDiagonal.lean` | the smooth divergence-free field |
| `CorrectionAnalyticStep.step` | `NavierStokes/CorrectionAnalyticStep.lean` | one correction cycle preserves the analytic invariant |
| `FinalSlowBase.origin` | `NavierStokes/FinalSlowBase.lean` | closed-form axis velocity `(1-t)^{-A}` |
| `FinalSlowBase.axis_tendsto` / `speedUnbounded` | `NavierStokes/FinalSlowBase.lean` | the speed diverges at time one |
| `CoordinateAlgebra.A`, `D`, `d`, `L` | `NavierStokes/CoordinateAlgebra.lean` | the self-similar exponents, `A = 1/2 + h` |
| `SimilarityCoordinates.forwardScalar` / `coordinateQ` | `NavierStokes/SimilarityCoordinates.lean` | `τ = q - z² q^{2h}`, and its positive inverse |
| `TimeLocalization.activatedVelocity` | `NavierStokes/TimeLocalization.lean` | the time switch that zeroes the initial velocity |
| `CandidateConsequences.futureJet_decay` | `NavierStokes/CandidateConsequences.lean` | force decay in every jet order |
| `ComparatorBridge.normalized_solution` | `NavierStokes/ComparatorBridge.lean` | viscosity `ν` ⇒ viscosity one |
| `MaximalLifespan.candidate_excludes_global_solution` | `NavierStokes/MaximalLifespan.lean` | the (D) exclusion |
| `PeriodicUniqueness.classical_uniqueness_on_Icc` | `NavierStokes/PeriodicUniqueness.lean` | energy uniqueness on the torus |
| `ComparatorBridge.compact_candidate_excludes_global_solution` | `NavierStokes/R3FiniteEnergyComparison.lean` | the (C) exclusion |
| `WholeSpaceUniqueness.classical_uniqueness_on_Icc` | `NavierStokes/R3/WholeSpaceUniqueness.lean` | finite-energy uniqueness on `ℝ³` |

---

## 3. Naming vocabulary

Module names in both libraries are built from a small set of prefixes. One line each, taken from
what the corresponding modules actually do.

| Term | Meaning |
|---|---|
| **Packet** | Euler. One localized, high-frequency, strongly sheared velocity increment, together with the induction stage (`structure Stage`) whose invariant it satisfies; the `Packet*` modules build stages, their bounds, and their successors. |
| **Parent** | Euler. The ambient particle map on whose deformation a packet is carried: `structure Parent` (`Euler/ParentPacketFrames.lean`) bundles a volume-preserving displacement with its velocity and acceleration, from which the frame, strain and curvature are derived. `Parent*` modules choose the next packet's geometry inside the current parent. |
| **Transverse** | Euler. The two-dimensional plane transverse to the packet's shear direction, and the forward solution operator acting on raw packet fields in that plane (`Euler/TransversePacketProvider.lean`). |
| **Cylinder** | Euler. The cylindrical coordinates in which a packet is posed: `Cylinder*` modules build the `L²` and Sobolev spaces on the cylinder, its angular averaging, and the invariance of mixed differential words under those coordinates. |
| **Mean** | Both. The angular (zero-frequency) part of a field, as opposed to its oscillatory part: `Mean*` modules build the mean coefficients, the mean inverse and its coercivity, and the classical divergence/pressure identities for the reconstructed mean fields. |
| **Gevrey** | Euler. Gevrey-class analytic control — factorial-growth bounds on all derivative orders — preserved under composition, products and flows; the majorant machinery behind the all-order corrections. |
| **Actual** | NavierStokes (prefix) and both (in prose). Marks the concrete, fully constructed object as opposed to an abstract or hypothetical one satisfying the same interface. The `Actual*` modules are the concrete instantiation of the correction cycle. In docstrings "actual", "genuine" and "literal" are emphasis of the same kind, not technical qualifiers. |
| **Signed** | NavierStokes. The signed wave update: the state increment whose sign is retained through the covariance computation, so that the removed physical bumps and the surviving squared term are tracked exactly (`NavierStokes/SignedMeanGain.lean`). |
| **Physical** | Both. The unscaled coordinates and fields, as opposed to the chart, lifted or normalized ones; `Physical*` modules convert between a scaled graph pullback and the actual Fréchet-derivative residual in physical variables. |
| **Particular** | NavierStokes. A particular solution of an inhomogeneous residual equation — the wave assembled to cancel a given residual block — as opposed to the homogeneous/primary field. |
| **Primary** | NavierStokes. The leading tangent field of a correction: the native vector pulse, its periodization and its complex harmonic, before the curl correction and before any signed or particular adjustment. |
| **Slow** | NavierStokes. The slow (self-similar, large-scale) variables and the slow base profile built from them; `Slow*` modules construct the asymptotic base series, its divergence, its residual matching and its stress support. |
| **Correction** | Both. One step of the iterative scheme that removes the current residual: in Euler the all-order drift correction added to each new packet; in NavierStokes the fields, residuals and bookkeeping of one correction cycle. |
| **Cycle** | NavierStokes. One full pass of the correction recurrence (`CorrectionStep.CycleState.step` / `iterate`, in `NavierStokes/CorrectionStep/WaveGains.lean`), and the coherence statements that hold across it. |

Two further conventions worth knowing: Euler module names concatenate their namespace path
(`EulerPacketSourceScaleSequence` lives in `Euler/PacketSourceScaleSequence.lean`), and the
whole-space uniqueness material in the `NavierStokes/R3/` directory uses the namespace root
`NavierStokesR3` — `NavierStokes/R3FiniteEnergyComparison.lean` describes it as ported from a
separate verified R³ development — whereas everything else in `NavierStokes/`, including the
flat `NavierStokes/R3*.lean` modules, lives under the `NavierStokes` root.

---

## 4. Caveats

* The two source manuscripts are cited throughout the docstrings by numbered result and equation
  but are not in the repository, and `formalization.yaml` gives no DOI or URL for them. Anything
  in a docstring of the form "the sequences in (37)" or "equations (3)--(5)" cannot be resolved
  from inside the repository.
* This outline was reconstructed from statements, docstrings and the import graph. It has not
  been checked against a proof term.
* Module counts and closure sizes quoted above are approximate and drift as the tree is
  simplified.
