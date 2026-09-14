# Unforced Navier–Stokes restart and stability: bounded research

**Status: setup ready; no unforced A/B result claimed.**

The authoritative [PLAN](../../Research/UnforcedRestart/PLAN.md) fixes notation, exclusive ownership, task contracts, existing declaration/import pointers, sequencing, and acceptance gates. Read it before writing research files. This README and PLAN are coordinator-owned; researchers write only their assigned subtree and task Markdown.

## Scope and notation in brief

Internal fields use `(t,x)∈ℝ×ℝ³`; Comparator fields use `x` then `t`. Default residual is viscosity one, `R(u,p)=∂t u+Du(u)-Δu+∇p`. Restart at `0<t₀<1`: `s=t-t₀`, new datum `a(x)=u(t₀,x)`, remaining horizon `1-t₀`. Compare on closed slabs strictly before that horizon, differentiating on their interiors. Smoothness at the singular endpoint is not available.

Periodic means unit coordinate periods; pressure periodicity is essential. R³ reference compact support does not impose competitor compact support or pressure decay. `ProblemStatement.Solution` hardcodes zero initial velocity and is **not** a general restart solution type.

For forced reference `u`, unforced comparator `v`, set `w=u-v`. The difference equation retains the actual force; energy normalization is `E=∫|w|²`. Force absorption uses `p-φ` when `f=∇φ`, with admissible smooth/periodic potential as appropriate. Merely cutting off a force constructs no solution of the modified PDE.

## Exclusive owners (agents 2–13)

Each owner writes only `Research/UnforcedRestart/<slug>/` and `docs/unforced-restart/<slug>.md`, with a separate `UnforcedRestart.<TaskName>` namespace, scratch area and output area. The task report links below are reserved destinations, not claims of completed reports.

| Agent | Task |
|---|---|
| 2 | [r3-restart-data](r3-restart-data.md) |
| 3 | [periodic-restart-data](periodic-restart-data.md) |
| 4 | [time-translation](time-translation.md) |
| 5 | [smooth-force-cutoff](smooth-force-cutoff.md) |
| 6 | [pressure-absorption](pressure-absorption.md) |
| 7 | [difference-equation](difference-equation.md) |
| 8 | [energy-comparison](energy-comparison.md) |
| 9 | [gronwall-threshold](gronwall-threshold.md) |
| 10 | [strong-norm-growth-transfer](strong-norm-growth-transfer.md) |
| 11 | [actual-forcing-budget](actual-forcing-budget.md) |
| 12 | [scaling-and-compactness](scaling-and-compactness.md) |
| 13 | [local-theory-obstruction](local-theory-obstruction.md) |

Agents 14–20 have read-only review roles specified in PLAN. No shared helper/log writes or concurrent broad Lake builds. Task owners correct their own files after review.

## Baseline evidence

Worktree `/home/velvet/worktrees/unforced-restart-20260909T202951Z`; branch `research/unforced-restart-20260909T202951Z`; unchanged baseline `597692fa5d55e07d810b2d96ead1a67972585425`.

* Toolchain: Lean `4.34.0-rc2`, compiler commit `6a10ac8c22beadecabdbb0919c2b50214762f91d`; Lake `5.0.0-src+6a10ac8`.
* All **11** pinned package revisions match `lake-manifest.json`, with clean tracked dependency source. This includes mathlib `85e3a25e006c35636f0e53b0e9296caca2685bc0` and Comparator `19e111e2141cf333c7daff0f64c5f24acc91dd2e`; all remaining exact pins are in the [dependency audit](../../Research/UnforcedRestart/setup/dependency-audit.txt).
* `.lake/packages` and `.lake/build` are worktree-local `cp -a --reflink=auto` snapshots of the existing checkout's artifacts. Copy-on-write reflinks, when supported, do not share mutable file contents. Every copied regular file was checked against its donor counterpart for identical inode/device: **none shared**. All copied symlinks resolve within this worktree. No source/config files were edited and no donor commands/builds were run.
* Single baseline invocation: `timeout 240s env LEAN_NUM_THREADS=2 lake --no-cache --rehash build`; **exit 0, 11087 jobs**, reported successful. See [status](../../Research/UnforcedRestart/setup/baseline-status.txt) and [full log](../../Research/UnforcedRestart/setup/baseline-build.log). `LEAN_NUM_THREADS` is recognized by the installed runtime; focused Lean additionally uses the supported `-j1`/`-j2` flag. Lake's help did not advertise a build `-j` flag, so none was invented.
* Baseline replay reports four `sorry` warnings in untouched `ComparatorChallenges.NavierStokes` (273, 280) and `ComparatorChallenges.Euler` (85, 170). These are pre-existing challenge placeholders, **not** acceptable research dependencies. Baseline success is not warning-free project certification.
* A fresh [strict import probe](../../Research/UnforcedRestart/setup/ImportProbe.lean) compiled with `autoImplicit=false`, `warningAsError=true`, `-j2` and unique output paths: **exit 0**. Its [log](../../Research/UnforcedRestart/setup/import-probe.log) checks key restart/operator/comparison signatures and prints axiom closures of difference algebra, periodic energy/uniqueness, whole-space uniqueness and perturbed Gronwall. Each printed closure is exactly `{propext, Classical.choice, Quot.sound}`.
* `git diff --exit-code` passed after setup/probe. This is a hash-revalidated cached baseline build, not a clean source rebuild of every theorem, an independent Comparator run, or an independent Clay-statement equivalence check. No dependency/tooling blocker currently prevents focused research elaboration.

## Validation contract in brief

Use focused `lake env lean -j1 -DautoImplicit=false -DwarningAsError=true` and task-unique `.olean`, `.ilean`, logs; see PLAN for a complete command. Never run broad `lake build`, `lake update`, cache/dependency preparation, or config changes from a researcher. Missing prerequisites go to the coordinator.

Every accepted file is rerun and every exported substantive declaration receives `#print axioms`. Allowed axioms are only a subset of `{propext, Classical.choice, Quot.sound}`. No `sorry`/`admit`, custom axioms, `unsafe`, native/oracle proof shortcuts, strictness disabling or max-heartbeat/resource bypasses. Conjectures/incomplete attempts are explicitly labeled Markdown, not accepted Lean.

Reports must distinguish actual-field PDE algebra, justified analytic PDE estimates, generic scalar infrastructure, and source-only obstruction findings. Every conditional premise remains explicit. A premise equivalent to the desired result is not progress. No invented NS local-existence declaration: `MaximalLifespan` supplies comparison/nonextension; an imported ODE Picard theorem is not NS local theory.

## Obstructions and realistic outcome

The prior Astra [final report](file:///home/velvet/.pi/agent/thread-phase/artifacts/astra-textbook-proof-investigation-codex-2026-09-09T20-00-53-927Z-e2c30812/final-report.md) and [skeptical review](file:///home/velvet/.pi/agent/thread-phase/artifacts/astra-textbook-proof-investigation-codex-2026-09-09T20-00-53-927Z-e2c30812/skeptical-review.md) were read in full. Their forced/unforced distinction remains decisive:

1. Force extension flat at the terminal core is not force vanishing on a terminal interval. Shutdown at time 2 is after the singular time 1.
2. Restart on a genuinely force-free or pressure-absorbable interval is conditional until that interval/potential is constructed for the actual candidate.
3. Equal-force uniqueness cannot compare the forced candidate with an unforced evolution. An inhomogeneous energy/strong-norm bridge is needed.
4. Small time-integrated force is not automatically below a threshold whose stability constants may diverge near the terminal time. L² closeness alone does not transfer pointwise blowup.
5. Vanishing rescaled force gives neither compactness nor a nontrivial limit. Viscosity normalization is not fixed-viscosity small forcing.
6. Existence and sufficient lifespan of a restarted unforced evolution need an applicable proved local theory, not a guessed import or circular assumption.

Likely useful bounded outputs are admissible slice data, translation/pressure/difference algebra, conditional comparison wrappers and explicit scalar thresholds. They would be genuine modest progress without establishing an unforced singularity. Setup itself adds **no new mathematical theorem**.
