# Round5 final report — partial certificates accepted; discriminator unresolved

## Verdict and literal witness

**Accept the bounded partial results only. PLAN target acceptance is blocked: N, W and Z remain unproved.** There is no proved target and no weaker actual selected-force curl obstruction. There is a genuine positive heat-model scalar certificate and exact restricted selected-sum identities. Neither is a selected-force nonzero component certificate.

Throughout, `d := UnforcedRestart.Round3.WitnessFeasibility.selected` (the existing `Classical.choice data_nonempty` record), `f := d.forcing`, and `a := d.schedule`. Set `A := WitnessFeasibility.potentialSum a`, `v := WitnessFeasibility.directSum a`, and `p := WitnessFeasibility.pressureSum a`. These are the literal three stage sequences and sums of that record. Its extension data, selected schedule, candidate, smoothness and jets are retained. No replacement witness, effective numerical schedule, assumed nonzero-curl contract, cancellation hypothesis or growth-preservation hypothesis is introduced.

Viscosity, terminal time and spatial periods are one. Budget is `ActualCandidateConstruction.selectedBudget` (definitionally zero), threshold is `selectedThreshold` with its proved geometry, and `h := CorrectionInitialization.ActualPrimary.h`; none is reselected. The residual equality for this force is inherited on **0<t<1**, not obtained by evaluating a potentially singular terminal velocity.

## Exact checked statements and assumptions

All names below are under `UnforcedRestart.Round5`; source files are in `Research/UnforcedRestart/Round5/`.

### Actual scalar certificate: `RadialPrimitive.lean`

Define

- `E := BaseExterior.nominalHeatNormalization CorrectionInitialization.ActualPrimary.nominal`;
- `F(1,s,z) := TailGaugePotential.extendedHeatCoefficient E h (1,(s,z))`;
- `k(s) := TailGaugePotential.heatPrimitive E h (1,(s,0))`.

The checked exports are:

| Theorem | Exact mathematical conclusion / explicit hypotheses |
|---|---|
| `RadialPrimitive.normalization_pos` | `0 < E`, with no free hypothesis |
| `RadialPrimitive.terminal_coefficient_pos` | For every real `s,z`, `0<s → 0<F(1,s,z)` |
| `RadialPrimitive.terminal_primitive_strictAnti` | `StrictAntiOn k (Set.Ioi 0)` |
| `RadialPrimitive.terminal_primitive_pos` | `0<s → s<1 → 0<k(s)` |
| `RadialPrimitive.transition_primitive_pos` | `s ∈ Set.Icc (1/64) (1/32) → 0<k(s)` |

These use the actual primary construction's proved positivity and derivative facts, not extra sign assumptions. In particular **both endpoints** of the closed transition interval are covered.

Proof sketch: normalization is the positive outgoing amplitude times a positive switch radius to a real power. The actual heat extension at terminal time gives `F>0`. The inherited `heatPrimitive_hasDerivAt` supplies `k′=-F<0` on positive radii; strict decrease and the anchor `k(1)=0` give positivity for `0<s<1`. The inherited primitive derivative proof supplies interval integrability on the positive anchor segment. No totalized nonintegrable-integral positivity argument or new limit/integral interchange is used.

**Certificate boundary:** `k(s)>0` is unconditional scalar nonvanishing for this construction. No theorem identifies it with a component or jet of `f`.

### Literal exterior identities: `SelectedExterior.lean`

Let `Nr := ActualCandidateConstruction.residualBand budget threshold` and

`D := ActualExteriorPrefix.exteriorDomain Nr`.

Precisely, `w ∈ D` means `w ∈ PhysicalWaveSum.preterminal`, `PhysicalWaveSum.physicalQ h w < ChartScales.Q Nr`, and `w ∉ ActualPolarCoverage.active` (the source's `mem_exteriorDomain`). Write

`c₀(w) := SmoothCutoffs.scaledCutoff (a 0 : ℝ) (PhysicalWaveSum.physicalQ h w)`.

`cutBasePotential` and `cutBasePressure` are respectively `c₀(w)` times the actual `TailGaugePotential.finalPotential` and `FinalSlowBase.pressure`, with `ActualPrimary.certificate`, `modulation`, `upper`, and the same budget. The four checked exports are:

- `SelectedExterior.selected_potential_eqOn`: `Set.EqOn A cutBasePotential D`;
- `SelectedExterior.selected_direct_eqOn`: `Set.EqOn v 0 D`;
- `SelectedExterior.selected_pressure_eqOn`: `Set.EqOn p cutBasePressure D`;
- `SelectedExterior.selected_exterior_germs`: for `w ∈ D`, all three equalities hold eventually in the ambient neighborhood filter `𝓝 w`, simultaneously.

Proof sketch: the actual `ActualCandidateAssembly.exteriorStages` kills every positive potential/pressure stage and every direct stage. A singleton-supported tsum reduces potential/pressure to stage zero; a pointwise-zero tsum gives the direct identity. Openness of `D` gives ambient germs. No derivative/tsum interchange or additional convergence assumption is needed.

**Identity boundary:** the stage-zero diagonal cutoff is retained, not assumed constant. These are preterminal interior exterior germs, not incoming terminal germs. `v=0` does not imply velocity or curl zero: the curl of the localized potential survives.

### Partial acceptance: `Acceptance.lean`

The three exports are exactly:

1. `Acceptance.literal_selected_curl_continuous`: `Continuous (SpatialCurl.spatialCurl d.forcing)` — inherited from Round3;
2. `Acceptance.literal_transition_primitive_positive`: `∀ s : ℝ, 1/64 ≤ s → s ≤ 1/32 → 0<k(s)`;
3. `Acceptance.literal_selected_direct_exterior_zero`: `∀ w : SpaceTime, w ∈ D → v(w)=0`.

`Audit.lean` adds aggregate validation, not a mathematical discriminator. The name “Acceptance” means **partial acceptance only**, not an existential selected-curl certificate.

## Missing selected-force proof

The proposed calculation in [CALCULATION.md](CALCULATION.md) is analytically consistent but **conditional and not Lean-checked here**. For `s=(x₀²+x₁²)/2`, `η(s)=cutoff(32s)` and a genuine smooth spacetime identification `H=ηK`, Cartesian orientation would give

```text
U = curl(H e₂) = (x₁ H_s, −x₀ H_s, 0),
(U·∇)U = −H_s²(x₀,x₁,0),
G = H_t − 2(s H_s)_s,
C₂(1,x) = −2(s G_s(1,s))_s.
```

The axial nonlinear curl vanishes in this model. Full pressure cancellation requires the curl of the entire gradient `∇(χp)`; split cross terms cancel with opposite signs. Before a joint plateau germ is proved, activation contributes `ρ′ curl U`, the linear coefficient `ρ`, and nonlinear coefficient `ρ²`. Radial, axial, mixed and diagonal cutoff derivatives cannot be discarded. Equality only on the central plane is insufficient for axial derivatives.

Remaining obligations, in dependency order:

1. **Incoming germ composition:** for this fixed selected record, simultaneously prove the precise exterior inequalities, stage-zero plateau, the entire anchor segment's heat-exterior regime, the single periodic copy, and late activation on a common spacetime neighborhood. Do not differentiate nearest-lattice representatives or replace the anchored gauge.
2. **Cartesian residual-curl calculation:** prove the complete formula with regularity, localization derivatives, nonlinear and pressure cancellations.
3. **Terminal force adapter:** transport the interior identity to the actual smooth `d.forcing` at `t=1` by incoming limits/extension jets and selected curl continuity.
4. **Endpoint jets and regular ODE uniqueness:** with `ℓ=1/64`, `b=1/32`, zero proposed axial curl implies `(sG′)′=0`, hence `G=A log s+B`. To conclude `G=0`, prove **`G(b)=G′(b)=0`** from sufficient higher cutoff jets and coefficient regularity. Merely displaying `η(b)=η′(b)=0` does not supply these conditions. Then establish

```text
2s k η″ + (2k+4s k′)η′ + (2k′+2s k″−j)η = 0,
j(s) = K_t(1,s).
```

Positivity of `2sk` on the closed interval makes the proposed equation regular; it does not prove the equation or uniqueness. Continuous-coefficient homogeneous linear ODE uniqueness with `η(b)=η′(b)=0` would force `η=0`, contradicting `η(ℓ)=1`. The `j` term cannot be dropped. None of this composition is a completed selected-force theorem.

## Point witnesses, terminal intervals and pressure

Let `C(t,x) := NavierStokes.SpatialCurl.spatialCurl f (t,x)`, with physical Cartesian convention `(D₁f₂−D₂f₁, D₂f₀−D₀f₂, D₀f₁−D₁f₀)`.

- **N:** `∀ t₀<1, ∃ t, max(0,t₀)<t<1 ∧ ∃ x, C(t,x)≠0`.
- **W:** `∃ t, 0<t<1 ∧ ∃ x, C(t,x)≠0`.
- **Z:** `∃ τ, 0≤τ<1 ∧ ∀ t, τ<t<1 → ∀ x, C(t,x)=0`.

All three remain unproved. A nonzero terminal component at one fixed point, together with checked continuity, would give nonzero curl there at every sufficiently late interior time, hence N and W. No such component is supplied. W alone obstructs C² spatial gradient absorption near its witness, or on intervals containing it; W can coexist with a later Z slab. N would obstruct every terminal slab. Zero at terminal time alone, even terminal pointwise flatness, does not imply Z or pressure absorption.

Round4 proves ordinary coordinate-cell mean zero for this same force on `[0,1]`. Mean zero alone is not gradient absorption. Even Z plus mean zero still requires a **periodic potential with joint smooth time regularity** satisfying `f=∇φ` on the same slab, to replace pressure by `p−φ`. No such potential or its impossibility is proved here. No terminal absorption, terminal absorption obstruction, restart, lifespan comparison or growth transfer follows.

## Validation, receipts and trust boundary

The two supplied independently executed strict source replays each passed all four current-source modules, using the established validation/parser implementation and verified historical dependencies read-only:

- `/home/velvet/research-builds/round5-independent-curl-b6RvRdXn/`: `FINDINGS.md`, `audit-34b951vd/receipt.json`, `sealed-receipt.json`;
- `/home/velvet/research-builds/round5-independent-provenance-FMU99bGU/`: `FINDINGS.md`, `receipt.json`, `audit-m01a2sca/receipt.json`, `preflight.json`, and per-attempt artifacts.

Each replay checked 12 printed export closures and an aggregate of **11,101 imported modules and 42,895 project constants/helpers**. Only `{propext, Classical.choice, Quot.sound}` occurred; unsafe project declarations and forbidden challenge imports were rejected. Four fail-closed parser regressions passed. Coverage counts do not establish N, W or Z.

Compiler: pinned Lean v4.34.0-rc2, SHA256 `79fb1d26fa5a39385d59fdc48a711a14b0710ca6480271acce99b4d177cea085`. Commands retain `-j1 -DautoImplicit=false -DwarningAsError=true`, one thread, CPUQuota=100%, MemoryMax=6G, MemorySwapMax=0, TasksMax=32, and timeout 600 seconds per compiler invocation. Exact commands, source bytes, direct-import provenance, logs and object hashes are in separate attempt directories. Transitive imports use first-prefix-root resolution against frozen source/object correspondence or fresh strict receipts. Dependencies were not rebuilt or downloaded.

Original rejected attempts remain preserved: the symlink preflight failure and the nonexistent `tsum_eq_zero` compilation error described in REPORT-DRAFT are not accepted proofs. The curl replay's sealed receipt explicitly records one incidental live `launch.log` hash discrepancy caused by final stdout flushing; accepted compiler logs and receipts were unaffected. No prior receipt is overwritten to hide diagnostics.

Finalization evidence is under `/home/velvet/research-builds/round5-finalization-wufn0o2e/`: all four modules passed fresh strict source replay (`receipt.json`, `driver.log`, per-attempt artifacts), with aggregate `audit-gr1bum89/receipt.json`, `parser-tests.log`, and `final-preservation.json`. This is another execution of the established workflow, **not a new independent checker**. `validate.py audit` by itself audits stored evidence; it is not a fresh source compilation.

Preservation is checked against `/home/velvet/research-snapshots/research-and-companion-20260912T192848Z/research-manifest.json`, SHA256 `526af3db371a2f9211f3b2b79dfe80847359b2265ac100036ed3ceb001e165fd`, including exact symlink targets and file hashes. Same-repository HEAD, refs, index, prior research files and prior receipts remain unchanged. Repository additions in this finalization are confined to this Round5 report; new receipts are external and versioned by their unique directory. The separate authorized documentation worktree's status is not frozen or tested. No commits, ref/index writes or pushes occur.

Trust roots remain the pinned Lean compiler/kernel/core/runtime, host, and historically source-built dependency objects. Reusing the validation implementation is not independent implementation of its checks. **No independent kernel checker was run; Comparator/Nanoda was not run.**

## One best next move — proposed, not launched

Prove the **simultaneous incoming selected-sum germ** for the literal selected record near the central radial transition, retaining the anchor segment and all cutoffs until their plateau hypotheses are established. This is the first missing link between the checked scalar and selected force; generic additional curl identities cannot replace it. Stop this round at partial acceptance rather than promoting the conditional ODE route to a theorem.
