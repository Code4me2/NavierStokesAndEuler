# Final review dispositions

## Verdict and preservation

Both independent adversarial reviews accept the conditional finite-pulse calculation with qualifications. This finalization incorporates their concrete corrections; it is not a third independent review, a full source audit, or kernel certification. No all-stage datum, general initial-data obstruction, autonomous seed supplier, or positive evidence for unforced B is obtained. Stop the specified preload/force-deletion campaign on these inputs; no successor is launched.

Reports preserved unchanged:

- [Analytic seed and smoothness](REVIEW-analytic-seed-and-smoothness-0a461a437dca41b58700c6afab1a64a6.md), abbreviated **A** below.
- [Nonlinear mechanism and source fidelity](REVIEW-nonlinear-source-fidelity-7c4e91b2.md), abbreviated **N** below.

`CALCULATION.md` was copied to `CALCULATION-FINAL.md` before editing the copy. Historical `OVERVIEW.md`, `CALCULATION.md`, `INPUTS.json`, and `CHECKS.json` remain unchanged. Their provisional language and old check scope are historical, not the final verdict. Only the three requested final Markdown files were created in the existing owned root. No repository changes, builds, Lean implementation, Git operations, Comparator repairs, or publication occurred.

## Issue-by-issue resolutions

| Issue | Disposition in corrected calculation |
|---|---|
| A §1; N §§2,5: seed amplitude versus pointwise velocity and cutoff trace | **Resolved, §3 (7).** Renamed the boxed object as an uncut physical amplitude norm and defined it explicitly. Cosine zeros and zero cutoff entry trace are excluded. Necessity concerns a prescribed midpoint amplitude in the finite ODE, not all ways to realize averaged stress. |
| A §2; N §2: equations (5)–(10) | **Retained with explicit proof details.** Substitution `s=u/2+uv/L` gives the arcsinh integral and cubic coefficient `7/24`. Differentiation gives the stated positive bounds on `−g′`, hence the Gaussian bounds. The Riccati upper barrier is at most `−39e/16`; the lower barrier has the opposite sign, and the case `e=0` is now explicit. Growing-column lower and energy upper bounds give the largest singular value; the absolute damping comparison gives the determinant and smaller singular value. Equation (9) remains exactly modal Euclidean SVD, not an ambient SVD or PDE inverse. Forward filtering and covariance tolerance remain distinct from inverse output selectivity. |
| A §3; N §§3,5: divergent storage preload | **Claim weakened precisely, §4 (12).** Require a uniformly controlled infinite band sequence with positive amplitudes and `max(0,−log 𝒜ℓ)=o(Q^(−1−h))`. Quantitative interior lower bounds suffice; mere nonvanishing does not. No actual evaluated selected-point sequence is extracted. The heat test stays conditional; an obstruction for smooth periodic Fourier data requires infinitely many distinct actual Fourier frequencies, not finitely many modes or localized annular covectors. |
| A §3: smooth versus analytic, all derivative orders | **Resolved, §4.** Fixed-order losses times `exp(−cℓ²)` are summable with controlled polynomial label losses. Derivative-order and finite-stage constants may vary. No factorial/analytic control, common-time trace, or uniform-in-stage bound is asserted. Nonzero compact cutoffs are not analytic; positive-time NS analyticity is not addressed by these seeds. |
| N §5.1; A §4: raw tangency is not localized solenoidality | **Resolved, §5 steps 2–4.** Apply cutoff to potential/pressure, then full curl before improved interaction bounds. Second-harmonic amplitude stays in `W(1−κs)` and its curl correction is in `W(3/2−2κs)`. Cutoff tails and uncancelled sources remain additive residuals. |
| N §1: exact repaired return coefficient | **Included and checked, §5 (14).** With complete amplitudes `a₂,a₋₁`, exact divergence gives transport coefficient `𝔗(a,b)+𝔗(b,a)+(𝔇a)b/2+2(𝔇b)a`. Both displayed divergence-term signs are plus. It has physical residual factor `Q^(−2A−1/2)` and the opposite sign as an evolution source. This is not a computed Leray/growing projection; pressure and possible further cancellation remain. |
| A §4; N §§1,5.3: second-harmonic damping | **Resolved, §5.** Exact factor is `exp(−3∫_w^v d)` inside the propagator/Duhamel integral. No uniform extra `exp(−cL)` gain is claimed for all source times. The `P(w)` cancellation gives polynomial slot losses and exponent preservation; it does not amplify a source upper bound by `exp(G)`. |
| A §4; N §§1,5.2: relative nonlinear size | **Qualified, §5.** `ε^(1−2κs)` compares natural upper scales at fixed finite order. A ratio to an actual primary requires quantitative interior amplitude lower bounds; never a pointwise ratio at cosine nodes or tiny masks. The return response is feedback dependent on the primary, not an independent seed or a full-PDE estimate. |
| A §5; N §§4,5.4: same selected producer and domains | **Retained and checked, §6.** Reconstruct `family` using `(ActualPrimary.choice B N0).prepared`, not another witness. `construction_frame := rfl` routes its absolute damping estimate to that construction. A general `PhaseConstruction` one-sided damping field would not suffice. Native carrier, slot, positive stress, large-band conditions and `partitionFactor` remain. No numerical active label or effective constants are fabricated, and no stored threshold is replaced. |
| Both reviews: scope and recommendation | **Retained, §7 and final overview.** Reject only the specified conditional unchanged-carrier storage and immediate/finite-order supplier arguments. Other overlapping parents, earlier large-scale storage/shearing, pressure coupling, and arbitrary autonomous trajectories are not ruled out. No candidate mechanism is established; common datum, timing, stress, background, localization, and full `f=0` closure remain exact obligations before Lean work could be justified. |

## Bounded finalization inspection

In addition to reading all six original owned-root documents in full, finalization directly inspected the following source bodies under the manifest export `/home/velvet/upstream-strategy-f9e8bc5-9d96jtuy/`:

- `upstream/NavierStokes/CorrectionInitialization.lean:3906–3953`: selected preparation, phases, covariance integral bridge.
- `upstream/NavierStokes/PrimaryGeometryAssembly.lean:300–363`: construction of the literal family and use of stored `large` field.
- `upstream/NavierStokes/BasePhaseGeometry.lean:870–967,1050–1067`: absolute damping, coefficient control, and construction-frame identity.
- `upstream/NavierStokes/HarmonicWaveInteraction.lean:192–256`: exact ordered transport coefficient, cylindrical connections, and solenoidality hypothesis for improved class estimate.
- `papers/navier-stokes.txt:5330–5489`: cutoff residual retention, Lemma 9.2, finite-stage and fixed-derivative quantifiers. Targeted formula-context inspection at (7.18), (7.19), (7.39), and the following cutoff construction confirms the propagator and complete-amplitude divergence conventions.

This is bounded inspection of the disputed routes, not a fresh audit of the global paper, supplier existence, historical reports, or source revision identity. The broader inspections described by A and N remain attributable to those reports. `INPUTS.json` supplies exact source paths, pins, and byte hashes; all 26 input hashes were rechecked successfully during finalization. Hash agreement does not authenticate Git-object provenance or mathematical truth.

## Exact arithmetic and documentary checks

Executed rational checks (Python `Fraction`, no simulation or build):

- `(1−1/8)/3=7/24` in the integrated damping polynomial.
- `−3+1/2+1/16=−39/16` for the upper Riccati barrier.
- `(1/5)²/2=1/50` for the cutoff Gaussian exponent.
- Ordered harmonic ratios `−(−1)/2=1/2` and `−2/(−1)=2` for (14).
- Primary quadratic harmonics are exactly `−2,0,2`.
- `(1−κs)+1/2−κs=3/2−2κs`; relative exponent `1−2κs>0` at exact `κs=1/100000`.

The differentiation, Riccati invariance, trace/SVD deduction and source interpretation are human arguments; these arithmetic checks do not certify them. Final documentary checks enforce the overview's 650-word cap, existing local link targets, absence of new files outside the three requested outputs within the owned root, and unchanged bytes for the six originals. They are not a host-wide preservation audit.

Original SHA-256 preservation identifiers:

```text
CALCULATION.md d45cd18665ac68a965bb145c37fe65120e334f31476ce94b074e6c50d23a299d
OVERVIEW.md bb1907fb8e778acb56bfc99767e7970b1bee162cd3b4bfb50834ba7df5e88ee6
INPUTS.json 9555b00ba3744127ab68ece12b4d501da9f9d1d816ded0bffdd81de403a2a075
CHECKS.json 568aaa427b926e96a64288f7e98d2565c86db32e428f34712da8318681154e01
REVIEW-analytic-seed-and-smoothness-0a461a437dca41b58700c6afab1a64a6.md 6cbd3b081020c6e25165fce2fbc7e0b159300244b7ad7cd3d3cc830d8905bee0
REVIEW-nonlinear-source-fidelity-7c4e91b2.md 91ecb0ddcb6f0f32b49067721bf8c4bc3d5f943e075fb58a6f8016baf354b0e0
```

No concrete review issue is left silently unresolved. Missing sequence witnesses and common-time/PDE estimates are explicitly unproved limitations, not invented obligations claimed to hold. The mathematical verdict is final for this bounded investigation.
