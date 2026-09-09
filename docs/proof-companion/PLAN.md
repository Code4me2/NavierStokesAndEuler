# Proof companion: shared authoring plan

## Status, audience, and boundaries

This is a documentation-only plan for an auditable mathematical exposition, not a completed proof companion or an independent human verification of the construction. The audience is a **graduate PDE reader; no Lean knowledge is required**. Explain the mathematics continuously, with source citations as an audit layer rather than as substitutes for arguments.

**Exact source baseline:** `597692fa5d55e07d810b2d96ead1a67972585425`.

At initialization, `git status --short` contained only:

```text
?? REVIEW.md
?? SIMPLIFICATIONS.md
?? review-notes/
```

These existing untracked research files are protected. No tracked changes were present. `docs/proof-companion/` did not exist, so no pre-existing companion required backup. Before any later overwrite of an existing companion file, copy it outside the repository and record the backup path; do not overwrite another author's work silently.

No `AGENTS.md` was found in the repository, its searched parent tree, or the checked ancestor locations. Repository README and validation instructions were read. Existing instructions do not authorize executing their build recipes in this documentation task.

Allowed changes are confined to this new directory. Do not edit Lean source, proof targets, challenge statements, dependencies, build settings, existing documentation, or research. No reset, stash, clean, commit, or push. Do not run builds or dependency operations for this phase. Preserve unrelated concurrent changes, and stop to reconcile unexpected source drift rather than modifying it.

All participating author, reviewer, and integrator agents must use the selected **`openai-codex/gpt-6-astra`** model. No agents were launched for this planning step. Do not silently substitute models if delegation is unavailable.

## Ownership and interfaces

The coordinator owns this `PLAN.md`. Authors write only their assigned chapter; suggestions for other chapters go through handoff notes, not cross-file edits. File names below are reservations, not yet-created links.

| Owner | File | Required mathematical scope |
|---|---|---|
| `scope` | `01-scope.md` | Exact four delivered statements in mathematical language; admissible data, forces, velocity and pressure classes; quantifier order; boundary conventions; forced versus unforced logic; separate challenge fidelity and Clay-prose obligations. |
| `ns-construction` | `02-ns-construction.md` | Closed profile route; singular base; gauged potential; one explicit nonlinear correction cycle; coherent iteration with fixed parameters; physical finite-prefix and increment estimates; zeroth stage, band tails, finite heads, and one diagonal schedule. |
| `ns-analysis` | `03-ns-analysis.md` | Conditional diagonal-flatness calculation; compatible endpoint jets and force extension; spatial localization, activation and periodization; origin transfer; periodic and whole-space comparison including pressure recovery; energy deduction; viscosity rescaling and nonextension. |
| `euler` | `04-euler.md` | Separate unforced packet construction; scales and induction invariant; exact stage evolutions and initial-data limit; varying-horizon stability contradiction; finite lifespan, continuation, C1 and vorticity criteria; identification with delivered solution classes. |
| later `integrator` | `README.md`, `SOURCE-MAP.md`, `VALIDATION.md`; optional read-only validation script here | Reading route, glossary reconciliation, dependency/source index, obligation and review ledger, links, and evidence summary. Do not create placeholder claims of validation. |

Read in order: scope → NS construction → NS analysis; Euler is a separate branch after scope. Chapter 02 supplies a single coherent witness and precisely quantified physical estimates to chapter 03. Chapter 03 must not silently replace that witness with independently selected fields or schedules. Chapter 01 owns statement-class terminology used by both branches. Each author hands off a list of exported human lemma IDs, imported IDs, notation, exact source inputs, unresolved obligations, calculations, and review status. The integrator reconciles these interfaces before declaring the exposition complete.

## Notation contract

- Write fields as `u(t,x)`, `p(t,x)`, and `f(t,x)`, with `x ∈ R³`; torus fields are unit-periodic lifts on `R³`. Explicitly translate source argument order: comparator fields commonly use `v x t`, internal NS fields use `(t,x)`.
- Use the forward Laplacian `Δ = Σ_i ∂²_{x_i}` and
  `R_ν(u,p) = ∂_t u + (u·∇)u − νΔu + ∇p`; the equation is `R_ν(u,p)=f`, with `div u=0`. Euler has `ν=0` and zero external force. Distinguish pressure gradients from external forcing even when internal names say “force.”
- Normalize NS viscosity to one and singular time to `1` only when stated; reserve `T_*` for a general terminal time. Mark `[0,T]`, `[0,T)`, and interior-time equation requirements explicitly. A total-function value at the endpoint is not an endpoint solution.
- `D_x^m` denotes spatial derivatives; `D_{t,x}^m` joint derivatives. Define each norm and the exact meaning of `D^{≤m}` before using it. Explain finite-dimensional norm comparisons instead of silently identifying tensor conventions.
- Use `||u||_2²` for the source energy integral and `E_kin=½||u||_2²` for physical kinetic energy. Distinguish a bound on each fixed slab from one uniform over all future times.
- Define the Euler C1 quantity as the sum of the spatial supremum of speed and the spatial supremum of the derivative operator norm. Source suprema and nonnegative integrals may take `+∞`; do not silently replace pointwise suprema with essential suprema or limsup with a limit.
- Reserve `J` for correction-cycle/prefix index, `j` for increment index, and `n` for band index in NS discussion. Euler indices are chapter-local and must be introduced afresh. Fix admissible `h, κ` and geometry before sending `J` to infinity. Distinguish raw and post-cutoff gains.
- Define the positive terminal scale `q(t,x)` from its source before using power estimates. Avoid also calling pressure `q` in such sections. For `O(q^N)`, state the neighborhood, derivative orders, and all constant dependencies. Preserve `∀m,N ∃J,C,U`, not a single stage or neighborhood for every order.
- Never use “smooth,” “compact support,” “small,” or “uniform” without identifying the domain, supported field, parameter, and relevant time interval.

## Stable human lemma IDs and citations

Reserve these ID prefixes independently of section numbering:

- `SCOPE-001`, `SCOPE-002`, … — chapter 01.
- `NSC-001`, `NSC-002`, … — chapter 02.
- `NSA-001`, `NSA-002`, … — chapter 03.
- `EUL-001`, `EUL-002`, … — chapter 04.

Assign once, never renumber or recycle. Use an explicit lowercase HTML anchor such as `<a id="nsa-001"></a>` followed by `### NSA-001 — Residual perturbation`. Definitions and propositions may use the same prefix, with their kind stated. Splits get new IDs and retain the original as a redirect/summary. Cross-chapter citations use relative links to these explicit anchors after the target exists.

Every load-bearing human lemma must contain: mathematical statement with all hypotheses; proof or explicitly conditional argument; dependencies by human ID; source declarations; evidence status; unresolved obligation IDs. Source maps are many-to-many: list every needed declaration rather than implying one source theorem proves the entire human statement.

**Source citation format:** relative Markdown file link plus the **fully qualified declaration**, with the baseline SHA inherited from this plan. Example:

[NavierStokes/DiagonalResidual.lean](../../NavierStokes/DiagonalResidual.lean) — `NavierStokes.DiagonalResidual.residual_jetRate_of_stages`.

Another example illustrates that namespaces cannot be inferred from paths:

[NavierStokes/R3/WholeSpaceUniqueness.lean](../../NavierStokes/R3/WholeSpaceUniqueness.lean) — `NavierStokesR3.WholeSpaceUniqueness.classical_uniqueness_on_Icc`.

No line-number-only citations, invented declaration anchors, or unresolved manuscript equation numbers as evidence. Read namespaces, enclosing sections, implicit variables, structure fields, and relevant proof bodies. If a declaration is private, explain that limitation rather than inventing a public qualified name. Cite multiple declarations when an assertion is an assembly or a new prose deduction. A filename match alone is not hypothesis checking.

## Independently inspected starting points

The two prior reports were read completely under the external research directory:

```text
/home/velvet/.pi/agent/thread-phase/artifacts/astra-textbook-proof-investigation-codex-2026-09-09T20-00-53-927Z-e2c30812/
  final-report.md
  skeptical-review.md
```

They are research leads, not independent certification. Authors must read additional reports fully as needed for their chapter and then verify their claims against the baseline source. Do not copy stale citations or import prior build claims as newly executed validation.

This planning pass independently read the following declarations and selected local proof bodies; this is limited source inspection, not an audit of their full dependency closures:

| Source | Checked planning fact |
|---|---|
| [NS submission](../../NavierStokes/ComparatorSolution.lean) — `NavierStokes.Comparator.navier_stokes_breakdown_R3`, `NavierStokes.Comparator.navier_stokes_breakdown_periodic` | Both quantify over positive viscosity and existential admissible data and forcing. |
| [NS definitions](../../NavierStokes/ComparatorDefinitions.lean) — `NavierStokes.Comparator.NavierStokesExistenceAndSmoothnessRn`, `NavierStokes.Comparator.NavierStokesExistenceAndSmoothnessPeriodic` | Whole space includes timewise L2 membership and globally bounded energy. Periodic class has periodic velocity and pressure and no explicit energy field. |
| [Whole-space adapter](../../NavierStokes/ComparatorR3Theorem.lean) — `NavierStokes.ComparatorBridge.option_C_of_candidate`; [periodic adapter](../../NavierStokes/ComparatorTheorem.lean) — `NavierStokes.ComparatorBridge.option_D_of_candidate` | Proof bodies choose zero datum and a rescaled force; candidate existence is a separate input to these adapters. |
| [Iteration ledger](../../NavierStokes/ActualIterationLedger.lean) — `NavierStokes.ActualIterationLedger.sigma_formula`, `NavierStokes.ActualIterationLedger.gain_tendsto_atTop` | Accuracy is `1/5+J/10`; divergence of gain requires fixed positive `h`. Arithmetic does not construct correction cycles. |
| [Diagonal residual](../../NavierStokes/DiagonalResidual.lean) — `NavierStokes.DiagonalResidual.residualDifference_jetRate`, `NavierStokes.DiagonalResidual.residual_jetRate_of_stages` | Background/tail/residual hypotheses are explicit; velocity tail needs derivatives through `m+2`, pressure through `m+1`; one sufficiently large stage meets both requirements. |
| [Whole-space uniqueness](../../NavierStokes/R3/WholeSpaceUniqueness.lean) — `NavierStokesR3.WholeSpaceUniqueness.classical_uniqueness_on_Icc` | Smooth pressures, matching residuals and datum, reference compact support, and competitor energy on the comparison slab are inputs. Pressure decay is not an input. Imported pressure estimates still need review. |
| [Euler submission](../../Euler/Solution.lean) — `Euler.euler_breakdown_R3`, `Euler.exists_compact_smooth_euler_singularity`; [definitions](../../Euler/SolutionDefinitions.lean) — `Euler.EulerSobolevExistenceAndSmoothnessR3On`, `Euler.velocityC1Norm`, `Euler.vorticityNorm` | Quantitative lifespan is in a specified all-order Sobolev class; its equation is imposed at interior times. The delivered result distinguishes local finite bounds, terminal C1 limsup, and infinite vorticity integral. |
| [Euler stability](../../Euler/OrdinaryEulerStability.lean) — `EulerOrdinarySobolev.Evolution.referenceNormPath`, `EulerOrdinarySobolev.Evolution.eventually_h3_bound` | H3 comparison constants depend on a reference quantity using fourth-order spatial Sobolev control. |

The full correction construction, gauge route, endpoint extension, pressure closure, packet induction, and official-prose bridge have **not** been independently established by this planning pass.

## Validation contract

All five gates below are required for a reviewed companion. Record reviewer identity/role, baseline, exact scope, findings, revisions, and remaining limitations. A chapter author cannot be its sole final reviewer. Agent review must be described as agent review, not independent human review.

1. **Technical mathematics review.** A separate PDE-focused reviewer checks every load-bearing statement and logical implication, cancellations, sign conventions, derivative losses, quantifiers, uniformity, endpoint arguments, and dependency cycles. Trace construction estimates for the same fields that retain blowup. Do not replace an analytic step by “a suitable witness exists.”
2. **Source and hypothesis checking.** Independently resolve every cited declaration at the baseline. Expand structures and section variables, check assumptions and conclusion directions, and trace actual instantiation. Separate literal translation, proved prose deduction, proposed reformulation, source-only input, and new mathematics. For a Clay bridge, separately prove constructed-data admissibility and the direction from a prose-admissible competitor into the excluded formal class. Challenge agreement alone is insufficient.
3. **Worked calculations.** Require displayed derivations, not just resulting formulas: NS residual perturbation and derivative counts; one nonlinear correction cancellation including finite-head defect; curl localization/gauge term; time activation residual; diagonal power bookkeeping; viscosity scaling; compact-candidate energy with regularization at zero norm. Euler must work through the stage/reference H3 stability contradiction with H4-dependent constants, varying horizons, and the quantitative blowup-criterion implications. Label each calculation's assumed analytic inputs. Independently recompute coefficients, signs, and exponent inequalities.
4. **Links and IDs.** Check all relative files and anchors, uniqueness of human IDs, and existence/namespace of source declarations; ensure no required dependency points to a missing chapter. External references need retrieval status and exact version; inaccessible manuscripts remain unavailable, not validated. A script can check syntax and paths, not mathematical implication or fully elaborated hypotheses. Any optional script is read-only, local, and confined here; it must not invoke Lake or alter sources.
5. **Pedagogical cold reading.** A reviewer who did not author the chapter reads without Lean or the investigation reports. They must be able to state the theorem class, explain each main step and its inputs, reconstruct the worked calculations, distinguish force extension from velocity extension, and locate every unresolved step. Record confusing notation and hidden assumptions and resolve them before pedagogical signoff.

The integrator's `VALIDATION.md` will track these five gates per chapter and outstanding finding. “Passed with limitations” must name the limitations; no unchecked gate defaults to pass. The initial state is **not run**, except for the limited planning inspections explicitly recorded above.

Keep four outcomes separate: expository mathematics review, Lean/kernel validity, Comparator challenge fidelity, and equivalence with external mathematical prose. No new kernel or Comparator run was performed here. Future formal checking requires separate authorization and the unchanged [Comparator instructions](../../ComparatorChallenges/README.md) and [repository validation plan](../VALIDATION-PLAN.md); in particular, use an appropriate fresh unprivileged sandbox clone never precompiled with the solution. Do not execute those recipes as part of this documentation plan.

## Unresolved-obligation policy

Use stable IDs `OBL-SCOPE-001`, `OBL-NSC-001`, `OBL-NSA-001`, `OBL-EUL-001`, etc. Keep each obligation beside the affected lemma until the integrator collects it into `VALIDATION.md`. Each record needs: owner, precise missing assertion, hypotheses, source leads, affected human IDs/conclusions, evidence needed to close it, review status, and resolution history. States are `open`, `under review`, or `closed with evidence`; being present in Lean source does not close a human derivation obligation.

Initial required obligation families:

- **Scope:** external-prose/derivative/norm/boundary/energy translations and periodic pressure; inaccessible manuscript correspondence; any formal verification not newly performed.
- **NS construction:** unconditional prepared-profile route; gauged zeroth potential and initial direct field; one coherent physical correction run; tail-only signed matching versus finite bands; fixed-parameter estimates and stage-independent losses; positive stages versus the singular zeroth stage.
- **NS analysis:** finite-head plateau in diagonal-minus-prefix estimates; same-field origin transfer; genuine compatible endpoint jets and exterior extension; nonlinear separated-translate periodization; pressure recovery and absorption of remaining flux terms; all comparison hypotheses; candidate energy as a deduction rather than an already packaged source theorem.
- **Euler:** full packet induction and admissible scale choice; exact stage solutions and convergent initial data; eventual coverage of stage horizons; H4-dependent reference control; continuation/BKM and comparator identification in their precise classes.

An unresolved lemma is stated as conditional and propagates its obligation IDs to every dependent conclusion. An unresolved audit is not a demonstrated source flaw. Conflicting research claims are resolved from source or remain explicitly disputed; never resolve them by majority vote or reassuring terminology.

Do not claim an independently audited human proof, a completed textbook proof, or Clay equivalence while load-bearing obligations remain. In particular, forced NS exclusion does not logically imply unforced NS breakdown; smooth/flat forcing is not zero forcing; shutdown after the singularity is not a force-free restart; and the Euler mechanism is not automatically a positive-viscosity construction. New mathematics is recorded as future work, not filled in by exposition.

## Delivery sequence and preservation check

1. Agree on this shared contract; each owner allocates human and obligation IDs locally.
2. Authors draft their owned chapters, checking source rather than importing report conclusions.
3. Exchange interface inventories; run independent technical and source reviews, then worked-calculation review and cold reading.
4. Integrator writes only the reserved integration files, reconciles cross-chapter dependencies, checks links, and reports honest validation status.
5. Compare final HEAD and git status with the baseline; verify tracked diff is empty and only authorized companion files were added. Record unrelated concurrent differences without reverting them. Preserve all pre-existing research and leave the work uncommitted.
