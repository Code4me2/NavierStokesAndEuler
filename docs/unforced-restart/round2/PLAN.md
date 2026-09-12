# Round2 plan — authorized research, not an A/B solution

## Supervisor review of source-build preflight — corrective attempt authorized

The supervisor reviewed build-driver.log after the first driver exited BEFORE any Lean source build. The only reported artifacts were `proofwidgets/widget/package-lock.json.trace` and `proofwidgets/widget/js/lake.trace`. Independently checked: the proofwidgets tree is clean at pinned commit `a8acbfd87375ff4abe14ce09db5b7664d383bc7f`; both files are tracked upstream (blob IDs `b2c1f4c41b2937a0d65713b836769ddc66548469` and `03c13f137f036cf7439a6d979e0afa6d71d8c9d6`, respectively). The latter is a JSON JavaScript build log, not a Lean compiled object.

This is the required review of that failed preflight. Integrator/repair is authorized to correct artifact classification and perform a subsequent source-build attempt, preserving first-attempt logs with separately named new logs. Do not silently remove failure evidence or disable no-cache checks. Permit ONLY those exact pinned-source trace blobs in the initial inventory, with provenance recorded, or quarantine them in the external checkout with explicit source-diff accounting if the build would otherwise reuse them. Continue rejecting all preexisting non-core Lean objects/native compilation outputs and unaccounted build traces. Do not blanket-ignore `.trace` files or fetch compiled artifacts. Inspect dependency hooks so a tracked JavaScript trace cannot cause reuse of Lean dependency objects.

A bookkeeping rule requiring review must not permanently block the authorized build after that review is supplied. The correct outcome is a real source-build result or a concrete new failure, not repeated cached-only checks labeled final clean blockage for these two known source files.

## Supervisor clarification — execution gates resolved

The user has authorized this research and clean source build. The supervisor inspected the worker outputs and verified every entry in the external snapshot's SHA256SUMS successfully; its own digest matches the recorded value below. For this task, preserving an external read-only, hash-verified snapshot is sufficient. Filesystem `chattr +i`, WORM storage, sudo, or another user approval were NOT required. Do not claim filesystem immutability; preserve the snapshot without modifying it. The extra immutability approval gate introduced by this plan is withdrawn, not a security control to bypass.

Three workers returned before execution because of plan-created coordination gates: clean-provenance did not build; periodic-slab had no assigned compile slot. Those outputs are NOT completed implementation or provenance validation. When the fanout finishes, the integrator inherits ownership of the settled workers' Round2 files/reports and the designated external clean checkout, and must carry out the authorized source build and implement/check the periodic slab composition rather than merely summarize blocked reports. Do not edit a still-running worker's files. Final repair may use the same ownership after reviews. Baseline and round-one frozen files remain protected.

Focused compilation needs no human or unavailable coordinator approval: use a worktree-local `flock` file to serialize focused Lean calls. Hold the lock for the entire invocation, retain unique outputs and existing resource controls, and release it afterwards. This authorizes execution, not a mathematical success claim. Keep clean source builds separate and do not reuse dependency objects. If there is a real compiler, resource or mathematical failure, retain evidence and report it honestly.

Original planning status below is historical; this supervisor clarification takes precedence where it conflicts.

## Preservation and snapshot gate

Authorized worktree: `/home/velvet/worktrees/unforced-restart-20260909T202951Z`.
Baseline: `597692fa5d55e07d810b2d96ead1a67972585425`.
Original checkout `/home/velvet/Desktop/NavierStokesAndEuler` and remote companion at `26e896e` are off limits. No commits, merges, pushes, original proof/challenge/config edits, global configuration edits, dependency updates, or shared writable artifacts.

Before any Round2 writes, captured external snapshot:

`/home/velvet/research-snapshots/unforced-round1-20260909T221339Z`

`SHA256SUMS` itself has SHA-256:
`192e15dc0ff1cb79cae02a19941e0f816dc194e91123c205153ccf808322a488`.

Archive includes all new Research/ and docs/unforced-restart source/docs and nonbinary evidence (114 files). Inventory covers 162277 files, including individually hashed excluded generated binaries and .lake content. Metadata includes HEAD, full untracked status, tracked binary diff, staged diff and tracked index entries. Huge regenerated artifacts are inventoried, not archived. Verify with `sha256sum -c SHA256SUMS` in the snapshot directory. All files are mode 0444 and directory 0555. **Not filesystem-immutable:** unprivileged `chattr +i` failed with Operation not permitted. These permissions and external digest give a read-only, tamper-evident seal, not WORM protection. The supervisor has verified and accepted this read-only, tamper-evident snapshot for preservation. No immutable-store deposit or further approval is required; do not elevate privileges or change global configuration.

All pre-Round2 sources, docs, manifests, validator and historical evidence remain frozen. No rerun may overwrite their output directories. New repository writes only under `Research/UnforcedRestart/Round2/` and `docs/unforced-restart/round2/`. Read baseline instructions and round-one FINAL-REPORT, OBLIGATIONS, MANIFEST and validator before research. No AGENTS.md was found in the worktree/ancestor instruction search.

## Exclusive ownership (assignments, not claims of active agents)

| Owner | Exclusive writes | Assignment / acceptance target |
|---|---|---|
| clean-provenance | One external checkout `/home/velvet/research-builds/unforced-round2-clean-20260909T221339Z/` and its external evidence sibling; `docs/unforced-restart/round2/clean-provenance.md` | Fresh pinned source acquisition/build, complete no-cache provenance, resource logs and clean-build verdict. No research-tree writes. |
| periodic-slab | `Research/UnforcedRestart/Round2/PeriodicSlab/`; `docs/unforced-restart/round2/periodic-slab.md` | O1/O5: actual periodic common-datum fields; energy differentiation, endpoint continuity, zero error, force integrability, FTC and finite-slab Gronwall assembly. No strong-norm or existence claim. Namespace `UnforcedRestart.Round2.PeriodicSlab`. |
| growth-mechanism | `Research/UnforcedRestart/Round2/GrowthMechanism/`; `docs/unforced-restart/round2/growth-mechanism.md` | O7/O9: source-backed selected-field growth connection and genuine evaluation-controlling norm; distinguish embedding, PDE stability, amplification and derived relative error. If stability is missing, return the exact obstruction rather than another assumed-error success theorem. Namespace `UnforcedRestart.Round2.GrowthMechanism`. |
| actual-force | `Research/UnforcedRestart/Round2/ActualForce/`; `docs/unforced-restart/round2/actual-force.md` | O8, and O3 if feasible: identify actual selected compact/periodic force, package mixed/cell norms from uniform jets, expose constants and weighted-threshold gap. No fixed-point integral mislabeled as integral of supremum; no flat-origin-to-zero-slab inference. Namespace `UnforcedRestart.Round2.ActualForce`. |
| integrator | `Research/UnforcedRestart/Round2/MANIFEST.json`, `Research/UnforcedRestart/Round2/Integration/`, this PLAN, `docs/unforced-restart/round2/REPORT.md` and other integration-only docs | New manifest/validator/audit, source freeze, integration imports, semantic coverage, preservation checks and final report. No writes in worker-owned paths, including worker reports. |

Each researcher owns its own `out/` and `scratch/` below its directory; each compile uses a unique run directory and module-relative object paths. No shared logs, scratch files or output roots. Workers communicate proposals read-only; only integrator assembles validated/frozen dependencies. Cross-worker imports wait for explicit integration freeze. Ownership transfer requires a written handoff; reviewers are read-only.

## Fixed mathematical contract

Fix **one** `t0` with `0<t0<1`, `H=1-t0`, datum `a(x)=u(t0,x)`, and `0<S<H`. These are fixed parameters, not a new restart chosen separately for each S. A varying-horizon argument must restrict the same comparator v and same datum. Initial target is viscosity **ν=1**.

Internal fields take `(s,x)` with `Space = EuclideanSpace ℝ (Fin 3)`; Comparator fields take x then s through checked adapters. Let `ur(s,x)=u(t0+s,x)`, `pr(s,x)=p(t0+s,x)`, `fr(s,x)=f(t0+s,x)`. The reference remains forced:

`R1(ur,pr) = ∂s ur + Dur(ur) − Δur + ∇pr = fr`.

The comparator must be a real arbitrary-datum solution: `R1(v,q)=0`, `div v=0`, `v(0,x)=a(x)`. Supply joint smoothness of velocities and pressures on the closed slab, actual spatial operators, open-interior full temporal derivatives and explicit within-derivative PDE at zero whenever asserted. Do not use zero-datum `Solution`, `GlobalSolutionOne` or `ClassicalSolution` wrappers as arbitrary-data constructors. Both reference and comparator velocities are divergence-free.

On the torus both velocities **and both pressures** have unit coordinate periods; integrate over the actual unit cube Q, not R³. On R³ prove actual error integrability, competitor finite-energy contracts and pressure/convection boundary-flux closure; compact reference support is not competitor support. Existence and regularity are explicit inputs, not produced by translation or cutoff.

Set `w=ur−v`, `r=pr−q`. Signs are
`∂s w = Δw − Dur(w) − Dw(v) − ∇r + fr`.
For `E=∫Q |w|²` (no half), `D=∑i ∫Q |∂i w|²`, expect
`E′ = −2D − 2∫Q ⟨w,Dur(w)⟩ + 2∫Q ⟨w,fr⟩`.
Pressure absorption is **pr−φ** when `fr=∇φ`, with a genuinely admissible smooth periodic potential in the periodic case. Translation retains force; cutoff modifies force but constructs no solution.

Periodic-slab target is a genuine integrated energy estimate
`E(s) ≤ exp(A(s)) ∫₀ˢ exp(−A(r)) g(r) dr`,
where `A(s)=∫₀ˢ (2L(r)+1) dr`, `g(r)=∫Q |fr(r,x)|²`, `E(0)=0`, and L is a proved gradient operator-norm majorant. Prove differentiation, continuity, integrability and primitives rather than assume this inequality. S-dependent constants are not uniform as S approaches H. This target is L² only and does not control pointwise growth.

A conditional hypothetical global A/B existence hypothesis may provide an admissible comparator and coverage. It supplies neither strong stability nor growth transfer. O7–O9 require an actual norm, evaluation embedding, viscous PDE estimate and quantitative actual-force weighted threshold for this one restart. Do not conceal relative error, growth, amplification smallness or the desired conclusion in a solution contract and claim it derived. Label conditional tools and unresolved applications separately.

## Compute policy — mandatory before execution

Only clean-provenance may perform the **one** fresh source build campaign, in its own external checkout. No whole-project builds, cache fetches, dependency installs or updates in this isolated worktree. Researchers use existing cached dependencies solely for explicitly labeled focused elaboration.

Use cgroup-enforced limits (user systemd is available): fresh-build campaign `CPUQuota=200%`, `MemoryMax=16G`, `MemorySwapMax=0`, `TasksMax=128`; cap Lean threads at 2 and compiler/BLAS/OpenMP threads at 1. Verify actual cgroup limits before launching. If controls fail, stop, not an uncapped fallback. Lake scheduler settings must be checked against the installed version, not guessed; CPU/thread environment variables alone are not a memory/concurrency gate.

At most one focused Lean process active across all researchers, separate from the build campaign. Each focused invocation: `LEAN_NUM_THREADS=1`, `lean -j1 -DautoImplicit=false -DwarningAsError=true`, own outputs, enclosing `CPUQuota=100%`, `MemoryMax=6G`, `MemorySwapMax=0`, `TasksMax=32`, 10-minute wall timeout. Thus authorized aggregate is at most 3 CPU equivalents and 22 GiB. A worktree-local flock serializes the single focused slot; no separate coordinator approval is required. No independent background builds. Fresh campaign wall budget 8 hours; stop below 80 GiB free disk. Preserve timeout/OOM/failure evidence; no silent restarts or raised limits. A failed campaign requires review before a second campaign.

## Clean-build acceptance contract — all required

1. Create the sole fresh checkout only after the snapshot gate. Acquire baseline git sources from the authorized isolated repository using `git clone --no-local --no-hardlinks` into the new external path, detached at the full baseline SHA. No access to the original checkout or remote companion, and no shared object alternates. Verify every tracked baseline file/index and config hash. Export research source-only copies from the frozen snapshot; freeze and hash Round2 accepted additions before their compilation. No old .lake, out, cache, object or executable copies.
2. Acquire all eleven dependencies as source at the exact existing lake-manifest revisions, without updating the manifest. Verify package commits, clean tracked trees, source hashes and any nested requirements. Inspect acquisition/build hooks before execution. Do not use `lake exe cache get`, release archives of compiled code, Lake artifact caches, prebuilt dependency tools or old project/dependency oleans. Disable automatic mathlib cache hooks (including `MATHLIB_NO_CACHE_ON_UPDATE=1` where applicable) and Lake cache use; record the actual effective controls.
3. Before the first build, recursively inventory the checkout and packages: **zero preexisting project/dependency oleans**, including .olean variants, ileans, native outputs, build traces and cached Lake configuration objects. Include untracked/ignored paths and symlink resolution. Reject escaping links/paths. Any package configuration elaboration counts as a logged source build step, never a reused object. Package source acquisition must not execute unrecorded Lake hooks. No deletions outside this new checkout.
4. **Explicit trust boundary:** the installed official Lean 4.34.0-rc2 toolchain, its core/Lean/Lake oleans, compiler/runtime and host toolchain/OS/hardware are trusted inputs, NOT bootstrapped. Record Lean version, commit, executable/prefix realpaths and hashes. Every non-core imported module must resolve to an artifact produced from pinned source during this campaign. Sanitize and record LEAN_PATH, LEAN_SRC_PATH, LAKE_HOME/cache variables and actual resolver paths; no paths into the existing worktree's .lake, prior validation outputs or other checkouts. Use checkout-private writable HOME/cache locations without changing global config.
5. Build explicit proof libraries `Common NavierStokes Euler` and the complete dependency closure needed by accepted research/audits, from source under the resource cap. Do **not** use the default target, which includes intentional challenge placeholders. Preserve original strict library options. No `sorry`, `admit`, custom axioms, unsafe project constants, native/oracle proof shortcuts, option suppression or weakened checks. Trusted dependency metaprogramming is recorded, not misrepresented as a new mathematical axiom. Reject forbidden axioms in every accepted mathematical closure. Challenge modules must never enter this closure.
6. Compile every frozen accepted round-one source and audit into NEW external outputs, plus every accepted Round2 source and new aggregate audit. Strict flags and serial unique outputs remain mandatory. Record exact commands, timestamps, source/output hashes, exits, full logs, source-to-module-to-artifact map and process/resource evidence. Fresh source builds need not have byte-identical oleans to old cached builds; provenance is established by the clean initial state and recorded build/resolution chain, not merely two unrelated hashes.
7. New integration validator must preserve or strengthen the round-one gates: complete Lean-file classification (including excluded attempts), frozen source/tool hashes, prohibited-construct triage, exact imports, complete generated-helper/project constant semantic enumeration, unsafe checks, full axiom closures contained in `{propext, Classical.choice, Quot.sound}`, no challenge imports, all imported-module inventories, baseline/index/pin/path checks before and after. Missing evidence is failure; invalidate stale success markers before a rerun. Manifest acceptance may not be empty and vacuously PASS. Manual mathematical review is separate from compilation.
8. Frozen round-one validator is path-bound to the old worktree and rejects new Lean paths. **Do not patch it or loosen its classification.** Preserve it byte-for-byte. New Round2 tooling must implement explicit authorized-root checks for each environment, retain exact round-one accepted hashes and audit content, and account for Round2 files. Record the difference between this new validation and a literal frozen-validator rerun; never claim the latter happened in the external clone.
9. Acceptance report must show full baseline/source preservation, all source-built dependencies, no preexisting non-core object reuse, and all strict audit results. Compare round-one snapshot hashes after work without rewriting any old artifacts. A source build is not independent Comparator/nanoda certification or Clay-prose equivalence. This source-build checkout is not eligible for a later cold Comparator run; that would require separately authorized fresh setup, not repurposing it or modifying challenge configs.

## Deliverables / stop rules

Workers report exact declarations, hypotheses, classification, commands/exits/hashes, and remaining O1–O10 gaps in their exclusive Markdown paths. Integrator creates manifest and validator only once there are actual inputs to validate; no success marker or invented worker results now. Failed Lean attempts must be quarantined and classified, with diagnostics retained, never accepted with holes. Final report separates cached focused elaboration, clean source-build provenance, mathematical achievements, and unresolved strong stability/growth. No A/B claim follows from a successful build.
