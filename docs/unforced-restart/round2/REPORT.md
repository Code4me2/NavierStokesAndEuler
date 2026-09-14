# Round2 integration — finite-slab comparison checked; force removal BLOCKED

## Review-repair addendum

See [VALIDATION-LEDGER.md](VALIDATION-LEDGER.md) for the per-finding disposition and new evidence. No mathematical source or theorem hypothesis was changed. Historical run counts below retain their historical scope: their dependency inventory covered base objects only (core split objects but not IR). The repaired validator inventories split objects and IR, checks before/after artifact stability, and remains **cached-only**. Neither inventory repair nor cached replay supplies pinned-source build provenance.

## Decision

**Support the finite-slab comparison research, not the current endpoint force-removal claim.** Two new Lean sources now pass strict compilation and comprehensive standard-axiom audit, against cached dependencies. O5's raw periodic PDE/FTC composition is completed, and a candidate-contract actual time/cell L² force budget is checked. The strong-norm comparison and actual growth-relative threshold remain open. The coarse global-norm strategy needs a substantially sharper mechanism (or exact gradient-force removal), not merely another short-force-budget lemma.

This is **not** a proof that force removal is impossible, that the actual error diverges, or that the unforced comparator regularizes. No A/B, independent Comparator, Nanoda, clean-build acceptance, or publication claim.

**Clean acceptance remains BLOCKED, for a new concrete reason:** all eleven exact dependencies were acquired as source, but the mandatory zero-preexisting-build-trace preflight rejected two upstream tracked ProofWidgets trace files. No external Lake elaboration or dependency compilation followed. No cache substitution or second campaign was attempted. The historical immutability/slot gates are not the current blocker: PLAN's supervisor clarification accepted the read-only tamper-evident snapshot and transferred settled-worker ownership to the integrator.

## 1. Accepted-source manifest and actual checks

Canonical manifest: [`Research/UnforcedRestart/Round2/MANIFEST.json`](../../../Research/UnforcedRestart/Round2/MANIFEST.json). It embeds the exact twelve inherited entries/hashes/88 exports, adds the following two sources/eight exports, freezes the validator and tools, classifies all Lean paths, and specifies dependency order. Research categories below are unrelated to Clay alternatives.

| New source / namespace | Declarations and classification |
|---|---|
| `Round2/PeriodicSlab/Main.lean`, `UnforcedRestart.Round2.PeriodicSlab` | `force_energy_continuousOn`: actual cell norm continuity; `slab_energy_derivative_le`: genuine PDE derivative/rate bound; `primitive_on_slab`: generic closed-interval FTC; `periodic_slab_comparison`: genuine conditional periodic PDE integrated estimate. |
| `Round2/ActualForce/Main.lean`, `UnforcedRestart.Round2.ActualForce` | `cubeIntegral_constant`, `cell_energy_le`: generic real-cell integration tools; `candidate_shift_force_continuous`, `candidate_cell_budget`: actual **candidate-contract** forcing consequences. They assume `CandidateProperties`, not a new closed selection of `selected_witness`. |

Final independent Round2 validation: **exit 0; 16 strict compilations** (12 inherited mathematical sources, 2 new sources, unchanged frozen audit, new aggregate audit). **96 named exports; 42,939 project/research constants and full axiom closures; 11,110 imported modules.** Every checked mathematical closure is contained in `{propext, Classical.choice, Quot.sound}`. Generated helpers and unsafe checks are included. The eight new named exports account for ten newly covered constants, including generated helpers.

Final evidence root, relative to this worktree:

`Research/UnforcedRestart/Round2/Integration/runs/20260909T224305Z/`

- `CACHED_SUCCESS.json`: exact commands, timestamps, exits, source/object hashes and counts; explicitly not clean acceptance.
- `declarations.tsv`: complete semantic enumeration and axiom closures.
- `dependencies.json`: every imported module, source/object hashes, exact direct imports and inherited project options.
- `resolver.json`: new research output root, current cached project/dependency roots, no historical research output fallback.
- `toolchain.json`: installed trust root, resolved executable hashes, host identity, 7,571 core/toolchain artifact hashes.
- `preservation-before.json`, `preservation-after.json`: all **2,335 baseline tracked file bytes**, all **114 archived files**, eleven dependency pins, tracked/index checks and frozen-artifact preservation.
- Per-source logs/command JSON: actual cgroup values and compiler status, with outputs only in this new run.

Summary log/status: `Round2/Integration/evidence/final-validation.{log,exit}`. Prior rejected attempts remain in `PeriodicSlab/out/attempt01..05`, `ActualForce/out/attempt01`, and integration run failure evidence. Compiler-generated `sorryAx` prints in failed elaboration logs are **rejected diagnostics**, not accepted axioms or source placeholders. Attempt06/attempt02 respectively passed focused checks; final acceptance recompiles everything from the frozen sources in the manifest's dependency order without those exploratory object symlinks.

## 2. (a) Rigorous PDE comparison now proved

Fix one restart `0<t0<1`, `H=1−t0`, viscosity one, one common datum `a`, and the same comparator on every `0<S<H`. The raw theorem uses arbitrary fields `u,v,f,p,q` and a positive S; application interprets `u(s,x)=u_old(t0+s,x)` and `f(s,x)=f_old(t0+s,x)`.

Inputs are joint closed-slab smoothness of both velocities and both pressures, continuity of force, periodicity of **both velocities and both pressures**, divergence freedom and the literal forced/unforced residual identities on `(0,S)`, plus `u(0,x)=a(x)=v(0,x)`. The theorem does not assume its energy inequality, its gradient bound, primitives, relative error, comparator existence, or endpoint growth.

Let `w=u−v`, `E(s)=∫Q |w|²`, `D=Σi∫Q |∂i w|²`, and `g(s)=∫Q |f|²` on the real unit cube. Accepted subtraction/periodic integration gives

```
w_t = Δw − Du(w) − Dw(v) − ∇(p−q) + f,
E' = −2D − 2∫Q <w,Du(w)> + 2∫Q <w,f>,
E' + 2D ≤ (2B+1) E + g.
```

The new proof derives `B=B_S>0` from actual joint smoothness and compactness, bounds the genuine gradient operator norm, proves the genuine derivative of E on the open interval, discards nonnegative dissipation, proves endpoint continuity and common-datum zero energy, and supplies FTC for literal integrals. For `A(s)=∫₀ˢ(2B+1)dr` it concludes, **including s=0 and s=S**,

```
E(s) ≤ exp(A(s)) ∫₀ˢ exp(−A(r)) g(r) dr.
```

The constant function L=B is a proved admissible majorant, not necessarily sharp. No uniformity of B as S↑H is inferred. The proof never differentiates `sqrt(E)` at zeros. This is L² comparison only, not evaluation or H³ stability.

**Endpoint distinction:** interior derivatives and endpoint continuity suffice for this integrated theorem. It does not claim a full time derivative at zero, or at S from an arbitrarily extended closed-slab comparator. The reference's new-zero `derivWithin (Ici 0)` equation remains a separate frozen translation result. A full closed-slab arbitrary-datum Comparator adapter is still O1. On a common larger domain `[0,H)`, S<H is instead interior; these are different contracts.

## 3. Resolving periodic-slab / actual-force interfaces

### Newly checked L² interface

`candidate_shift_force_continuous` maps actual `CandidateProperties.force_smooth` to continuity of `(s,x) ↦ f_old(t0+s,x)` on any `[0,S]`, for nonnegative t0. Only force regularity is used: no reference velocity smoothness at time 1 is asserted.

`candidate_cell_budget` obtains a **single** C>0 for the force on the fixed closed `[0,H]`, using future smoothness and force periodicity. With the actual cube volume checked equal to one, it proves

```
g(s) = ∫Q |f_old(t0+s,x)|² ≤ C²                (0≤s≤H),
g is interval-integrable on [0,S],
∫₀ˢ g(r)dr ≤ C²s                            (0≤s≤H).
```

These are integrals of spatial integrals, not `∀x, ∫|f(t,x)|dt`, and do not interchange an unproved supremum/time integral. One H and one force serve all S. Choosing H=1−t0 includes the force trace at old time 1, which is smooth even though the reference velocity need not be. The continuity output directly supplies the `hf` input of `periodic_slab_comparison`; the integrated estimate consumes g itself. The budget establishes finiteness, **not the necessary growth-relative weighted tolerance**.

No new theorem chooses the actual selected witness and packages the comparator simultaneously. The source-level candidate contract is available from the baseline construction; this last specialization and O1 must not be confused with proving existence.

### (b) Generic/conditional strong-norm tools — ordinary analysis only

The workers' stronger budgets are coherent after fixing norm conventions:

- Write `N²=Σ|α|≤3 ||∂^α w||²₂`, over the 20 multiindices, for the strong-error calculation.
- Write `H³_B` for the Fourier/Bessel norm. Its derivative identity is `Σj binom(3,j) Σordered words length j ||∂word f||²₂`. Thus `N(f)≤||f||H³_B`; use a Bessel bound as an **upper bound** for the multiindex forcing term, not as a claim that these norms are equal.
- Baseline `PeriodicSobolev` uses a third norm, `derivativeH3Norm`. Smooth commuting-derivative/Fubini adapters give `N²≤derivativeH3Energy≤7N²`; those adapters are ordinary analysis here. More directly, baseline `mixedEnergy≤N²` and its pointwise square estimate give `|w(x)|≤sqrt(8)N≤3N`. Merely citing `|w|≤3 derivativeH3Norm` would not by itself justify `3N` without this sharper subsum argument.
- For uniform full jets Cj, restriction to unit spatial directions and actual finite-volume integration give
  `Bk² = V Σj≤k binom(k,j) 3^j Cj²`.
  In particular `B3²=V(C0²+9C1²+27C2²+27C3²)` and `B2²=V(C0²+6C1²+9C2²)`.
  Default periodic V=1 is safe. The sharper V=π/32 (or containing-cube V≤1/8) requires the specific compact support and separated-periodization construction, not arbitrary candidate properties.
- Leray projection is an H^k contraction, not an assumed L∞ contraction or support-preserving map. The force input to strong stability can be `F3(s)=||P f_r(s)||H³_B≤B3` in L¹ time; with viscous integration by parts/Young it can instead be an L²-time H²_B bound. These are **not interchangeable scalar energies** with g above: g is the squared L² cell norm.

Under smooth periodic PDE hypotheses, the workers derive in ordinary analysis

```
(1/2)(N²)' + D3 ≤ a N² + C_N N³ + N F3,
a(s)=45 sqrt(20) max_{1≤|β|≤4} ||∂^β u_r(s)||∞.
```

A sharper product estimate may use `C||u_r||H⁴`. The extra reference derivative, pressure cancellation, nonlinear commutators and sqrt regularization at zero must all be formally supplied. The dissipative variant trades one force derivative for part of D3. **Neither variant is newly accepted Lean.** The already-proved periodic evaluation theorem is not a viscous stability theorem. R³ also needs actual comparator/error integrability and boundary-flux closure; reference compact support is not comparator support.

## 4. Actual budget versus growth target

The source-supported target speed is eventually `j_* τ^(−α)`, where `τ=H−s`, `α=1/2+h∈(1/2,1)`, and h, j_*, t0, H and schedule are fixed. The assembled selected-axis value wrapper is not newly exported here. Base axis derivatives cannot be transferred just by differentiating an origin point-value identity.

A sufficient nonlinear bootstrap target for the multiindex norm is

```
b(s) = (ρ j_*/3) τ^(−α),   0<ρ<1,
K(s) = ∫₀ˢ [a(r)+C_N b(r)]dr,
exp(K(s)) ∫₀ˢ exp(−K(r)) F3(r)dr < b(s)   for every 0<s<H.
```

This is the **unproved test**, not a success premise relabeled as an achieved theorem. Its quadratic-bootstrap contribution has finite integral because α<1. The hard issue is the reference-dependent amplification and actual projected force work.

For the exact diagnostic model `N'≤κ N/τ+M`, zero initial error and M≥0, the sufficient envelope is

```
M [H^(κ+1)−τ^(κ+1)] / [(κ+1)τ^κ].
```

Relative to the reference speed it has a factor `τ^(α−κ)`. If κ<α it tends to zero but earlier times/bootstrap still require checking; if κ=α an actual constant comparison is required; if κ>α and M>0 this envelope cannot certify the target near H. The analogous `F0 τ^p` formula replaces κ+1 by κ+p+1 in the accumulated numerator. Vanishing terminal tails do not erase earlier positive weighted work for a **fixed** restart.

The new L² C, and the unformalized strong Bk, are existential finite constants. No numerical values, projected smallness, or useful bound of a for the selected candidate have been extracted. For fixed t0, `∫₀ˢ ||P f_r||Hk` approaches a full restart budget as S↑H, **not a shrinking terminal tail**. This is why finiteness and short-interval smallness do not solve O8.

The actual-force report further derives in ordinary analysis, with `F_*=||P f(1)||Hk`,

```
| ∫₁₋ℓ¹ ||P f(t)||Hk dt − ℓ F_* | ≤ Dk ℓ²/2.
```

Neither F_*=0 nor F_*>0 is known for the selected force. Whole-space solenoidal trace vanishing could improve tail powers, but origin flatness does not establish it; even such tail powers do not remove previously accumulated work. The specific presingular periodic construction has zero mean force by compact divergence/residual integration. This removes the harmonic constant obstruction and makes the actual comparator error mean zero from common data, **conditionally on that still-unformalized deduction**. It does not prove curl(f)=0 or close the vorticity estimate. Exact pressure absorption would still require an admissible periodic potential and uses **p−φ**.

## 5. (c) Unproved bridges and (d) heuristic negative evidence

The explicit dependency graph and O1–O10 ledger are in [`DEPENDENCIES.md`](DEPENDENCIES.md) and [`DEPENDENCIES.json`](DEPENDENCIES.json). In brief: O5 is closed at the raw-field/cached level; O8's L² mixed interface advances; O1/O2 comparator admissibility/coverage, O3/O4 exact removal, O7 strong stability, O8 weighted smallness, O9 derived evaluation transfer, O6 R³ closure and O10 compactness remain open.

For the slow base, the workers derive the saddle strain `diag(−2,−2,4)/τ`. In the velocity-error energy term, transverse error is amplified and axial error damped; axial **vorticity** is stretched. Swirl is skew at the axis and cancels in this energy pairing. Global operator-norm majorants discard that structure. The deliberately coarse coefficient would greatly exceed α/τ if the base strain transfer to selected jets were assembled. This is negative evidence for that **sufficient global envelope**, not a theorem about actual error. The selected germ/jet bridge is itself unfinished.

A scalar stretching ODE or inviscid support transport is not a replacement. The fixed origin is not a material trajectory; diffusion is leading-order at the transverse core scale; pressure is nonlocal. A plausible different mechanism would need a genuinely viscous, spatially resolved propagator/relative-core estimate exploiting the strain signs and rotation cancellation, or an actual exact-gradient force identity. Neither is established. Failure of the present estimate cannot rule either out.

## 6. Clean provenance and installed trust root

Read the complete historical [`clean-provenance.md`](clean-provenance.md). Its no-build/no-clone verdict describes the worker pass, not this integration pass. Under current PLAN, the external read-only snapshot is an accepted preservation seal, **not filesystem-immutable/WORM storage**. Its SHA256SUMS digest remains

`192e15dc0ff1cb79cae02a19941e0f816dc194e91123c205153ccf808322a488`.

Actual external checkout:
`/home/velvet/research-builds/unforced-round2-clean-20260909T221339Z/`

Durable external evidence sibling:
`/home/velvet/research-builds/unforced-round2-clean-20260909T221339Z-evidence/`

- `acquisition.log`, `acquisition.exit` (0), `acquisition-status.json`: `git clone --no-local --no-hardlinks --no-checkout` from the isolated repository, detached full baseline, no object alternates; eleven exact git revisions fetched with hooks disabled. Private HOME/cache/environment recorded. No original-checkout access.
- `controls.json`, `build-controls.json`: verified CPU `200000 100000`, memory `17179869184`, swap 0, tasks 128; 80-GiB disk-floor checks. Initial resource probe also recorded under new integration evidence.
- `initial-inventory.json`: pinned tracked source hashes, all package configs/nested manifests for review, recursively checked escaping links and preexisting artifacts.
- `build-driver.log`, `build-driver.exit` (1): **preflight** assertion at the zero-trace gate. Rejected upstream tracked files: `.lake/packages/proofwidgets/widget/package-lock.json.trace` and `.lake/packages/proofwidgets/widget/js/lake.trace`.
- `CLEAN-VERDICT.json`: exact trace contents/hashes/tracked status and explicit failure. Worktree copy: `Round2/Integration/evidence/clean-verdict.json`.

No external `build.log` or `build-status.json` exists because the driver stopped **before** Lake. No dependency compiler failure, OOM, timeout, successful clean closure, or imported-object provenance chain is invented. The configured no-cache command was `lake --no-cache --verbose build Common NavierStokes Euler`, but it was **not executed**. Installed Lake help/config sources were inspected; no guessed scheduler flags or cache/update invocation were used. The source-built environment is therefore unavailable for final proof checks. No retry, deletion of tracked trace files, disabling of ProofWidgets' error guard, or cached-object substitution occurred. Reviewer disposition is needed before another campaign.

The final checks deliberately remain cached. Installed toolchain trust root:

- Lean **4.34.0-rc2**, aarch64, commit **6a10ac8c22beadecabdbb0919c2b50214762f91d**.
- Prefix `/home/velvet/.elan/toolchains/leanprover--lean4---v4.34.0-rc2`; shim `/home/velvet/.elan/bin/lean`; actual compiler resolved under prefix.
- `bin/lean` SHA-256 `79fb1d26fa5a39385d59fdc48a711a14b0710ca6480271acce99b4d177cea085`.
- `bin/lake` SHA-256 `f80f50cbab5322e35bcb0bf88937e22e9d908b5e4e336e83ddfc30eb1506aacf`.
- Core/Lean/Lake objects, runtime/compiler/linker, host OS/hardware are trusted installed inputs, **not bootstrapped**. Full executable/core hashes and host identity are in final `toolchain.json`; hashes alone are not independent release authentication.

## 7. Runnable validation and criteria preservation

From the authorized worktree:

```sh
python3 Research/UnforcedRestart/Round2/Integration/selftest.py
python3 Research/UnforcedRestart/Round2/Integration/validate.py
# Deliberate fail-closed clean request; currently exits 1, never a clean PASS:
python3 Research/UnforcedRestart/Round2/Integration/validate.py --clean
```

The first command's 11 source-tool tests pass. The actual `--clean` negative test exits 1 with the clean blocker (`evidence/clean-negative-test.{log,exit}`). The normal runner makes a new timestamped directory on every run, never overwrites historical evidence, and creates `CACHED_SUCCESS.json` only after every gate passes. A failed run has `FAILURE.json`, not a stale success. There is no generic `SUCCESS` that could be mistaken for clean acceptance.

This is a **new independently implemented runner**, not a patch, import/execution, or literal rerun of the path-bound frozen Python validator. It preserves its criteria: exact old hashes, complete source classification, exact imports, source construct/option triage, all imported project/research constants including generated helpers, unsafe rejection, transitive standard-axiom enforcement, every imported module's inventory, before/after baseline/index/pin/path/source preservation. It strengthens baseline checks to byte comparisons and records installed trust-root artifacts. New acceptance cannot be empty. Frozen audit content is also strictly recompiled unchanged into new outputs before the new aggregate audit.

Every final compiler invocation is serialized by `Round2/Integration/focused.lock`, uses direct pinned Lean `-j1 -DautoImplicit=false -DwarningAsError=true`, `LEAN_NUM_THREADS=1`, isolated explicit resolver paths, enforced 1-CPU/6-GiB/no-swap/32-task cgroups and 600-second timeout. No whole-project build, dependency update, or cache fetch occurred in this worktree. Source-built clean certification is deliberately **not implemented as a permissive mode**: this runner refuses it until an independently verified complete source-build chain exists. A future clean verifier must add provenance gates, not relabel these checks.

All repository writes are within new Round2 research/docs. Baseline/config/challenge files, frozen round-one sources/manifests/validator/evidence and the external snapshot remain unchanged. No commit, push, merge, global setting, or original checkout modification.

## 8. Questions for reviewers

1. **Clean preflight conflict:** upstream pins themselves contain JS build traces. How should a reviewed second campaign distinguish tracked source distribution metadata from reused build evidence while retaining the original zero-trace criterion? Is a separately specified source-only export/JS source rebuild permitted? Do not silently exempt or delete these files and claim unchanged criteria/pins.
2. Does the new raw-field O5 theorem capture precisely the intended arbitrary-common-datum application, with both periodic pressures and only interior PDEs? What smallest Comparator adapter discharges O1 without a zero-datum wrapper?
3. Can the selected witness be specialized once to the new force-cell interface and actual axis value/germ theorems, without confusing compact/periodic existential components or differentiating pointwise-only identities?
4. Can the H³ multiindex/Bessel/baseline norm interfaces and viscous commutator estimate be formalized with useful constants, rather than just finite ones? Audit the derivative-four reference dependence and dissipative H²-force alternative.
5. What can be proved about the **whole-domain** projected terminal force or curl, especially the localization annulus? Mean zero and origin flatness alone are insufficient. Could O3 hold exactly?
6. Is there a genuinely viscous relative-core propagator that exploits axial damping, transverse strain and skew rotation cancellation and meets the fixed-restart weighted budget? If not, prioritize a different mechanism rather than promoting the coarse envelope.

**Disposition:** retain the two checked finite-slab/cell-budget sources and the explicit open graph. Current force-removal endpoint strategy is **blocked and requires a sharper/different mechanism**; no impossibility conclusion follows.
