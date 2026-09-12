# Round3 final report — mathematical decision blockers remain

**Decision (3): neither exact absorption nor an actual obstruction is certified.
Force mean zero, a total-curl decision producer, and comparator lifespan/growth
transfer remain unproved. No A/B conclusion follows.** Validation hardening and
fresh replay succeeded; this is not complete research.

## Snapshot and preservation

* Frozen local validated snapshot SHA: `e970490cf8f0cfb41fca101c62702fab7347c17c`.
* Worktree HEAD: `597692fa5d55e07d810b2d96ead1a67972585425` (unchanged).
* Only new Round3 files were written. All 3,157 inventoried preexisting files,
  HEAD, refs and index are unchanged; tracked/index diffs are empty. The older
  snapshot/external-evidence verifier passed too. No commit, push or merge.
* [STATUS-ADDENDUM.md](STATUS-ADDENDUM.md) updates the stale differentiation
  obligation without modifying DECISION.md, ACCEPTED-SOURCE-MAP.md or any receipt.

## Candidate-specific mathematics versus generic tools

**No new mathematical theorem was proved during this repair.** All six accepted
Round3 source files were freshly recompiled. The substantive bridge accepted
before this repair, beyond the original five-module integration, is precisely:

`SelectedBridge.selected_compact_temporal_integral_zero`:
for every `t ∈ (0,1)` and `i : Fin 3`,

`∫ x : Space, (temporalDerivative MeanTopology.compactVelocity t x) i = 0`.

This is exactly the frozen selected activated compact velocity, not another
existential field. Its four supporting results establish joint smoothness at
every spatial point (including the support boundary), C¹ regularity on closed
interior slabs, uniform support in the same compact cylinder at all times, and
component integral differentiation on an interior slab. An actual dominated
integral theorem and uniqueness against zero momentum justify the conclusion;
there is no use of cancellation from a nonintegrable totalized integral.

Earlier candidate-specific results retain their exact scope: actual residual
identity and same-schedule force equality on `(0,1)`; compact momentum/transport
cancellation there; selected force-mean continuity on finite closed intervals;
terminal origin jets, tensor-to-curl identification, and joint curl continuity.

Generic or conditional tools remain separate: compact derivative/integration
infrastructure, extension uniqueness, strict-exterior cut-residual jet lemmas,
periodic-potential mean-zero necessity, and the conditional unequal-entry curl
interface. `terminal_curl_ne_zero` does **not** produce its unequal entries.
The new `ValidationRepair/Audit.lean` is metaprogramming audit tooling, not a
candidate theorem or an independent kernel checker.

## Curl and mean: time domain, witness, and missing compositions

The witness throughout is `d = WitnessFeasibility.selected`, with its frozen
schedule; force is `d.forcing`, not an arbitrary future extension or surrogate.

| Time/space domain | Checked knowledge | Still unresolved |
|---|---|---|
| `0<t<1`, all R³, compact V | Momentum, transport and now temporal component integrals are zero | Pressure-gradient and Laplacian cancellation; integrability for residual splitting |
| `0<t<1`, selected periodic force, full cell | Actual residual identity; force-mean continuity | Separated periodization and coordinate-measure transport; no checked force-mean zero theorem |
| `t=0,1`, cell mean | Continuity on finite closed intervals | Endpoint zero composition after interior cancellation; no terminal velocity trace assumed |
| `3/4<t<1`, inner cube | Actual localized residual curl identity | Total curl sign/vanishing, including plateau, annular transitions, caps and overlaps |
| `t=1`, lattice origins | All selected terminal jets vanish; origin curl zero | This pointwise result gives no all-space or slab identity |
| `t=1`, nonzero representatives | Actual terminal antisymmetric tensor/curl interface | No derived unequal total entries; plateau as well as transitions unresolved |
| Strict spatial exterior, terminal jets | Generic cut-residual exterior theorem | Closed selected specialization and boundary-continuity composition are not newly proved |
| Any single full terminal slab `[τ,1)` | No all-space curl-zero producer | Curl **and** mean zero at every time, smooth periodic potential and pressure composition |
| Fixed restart `[1/2,1)` | Same selected datum must be retained | Later absorption cannot identify an evolution restarted at `1/2` |
| Postterminal times | Data has an existential finite future force-support endpoint | No new prescribed shutdown time or support/mean/curl theorem for this selected extension |

Curl zero alone misses nonzero constants; mean zero alone misses periodic
solenoidal modes. Even all-order terminal flatness cannot prove slab absorption:
a time-flat multiple of `(0,sin(2πx₀),0)` is a logical counterexample, not the
selected candidate. An isolated nonzero localization contribution does not decide
total curl; paired pressure-curl terms must both be kept.

## Validation repair and fresh audit

New tooling and commands: [ValidationRepair/README.md](../../../Research/UnforcedRestart/Round3/ValidationRepair/README.md).
Evidence paths below start `Research/UnforcedRestart/Round3/ValidationRepair/`.

* `replay-1oafv980/receipt.json`: six strict compilations, exit **0**, unique
  outputs, **36 prior + five bridge** printed export closures, reparsed and
  exactly reconciled with historical recorded exports. Only `propext`,
  `Classical.choice`, `Quot.sound` occur.
* `aggregate-btau1ozq/receipt.json`: fresh aggregate imported-project/helper
  audit, exit **0**, **42,928 constants**, with unsafe/forbidden-axiom rejection;
  **11,105 imported modules** resolved and matched to source/object provenance.
* Preflight compares **13,618 historical object/artifact hashes**, verifies
  manifest/resolver/compiler pins and external evidence hashes, and checks
  Lean-resolved direct imports. This is comparison with clean-build history,
  not merely a new inventory of current hashes.
* Incremental dependency-union additions are explicitly recorded with original
  source inventory hashes, object hashes and source-build log/command references:
  `NavierStokes.R3.ProblemStatement`, `CompactEnergy`, `CompactTimeIntegral`.
* Four parser regression tests passed. Read-only receipt verification and the
  prior preservation verifier passed. Receipt creation is explicit and unique;
  verification never overwrites historical or current receipts.

Exact replay source SHA256s (prefix `Research/UnforcedRestart/Round3/`):

| Source | SHA256 |
|---|---|
| WitnessFeasibility/Main.lean | `7d77092a3da73faedebac0a052c6fd2ce6fc46d340f48f796dd5e45f926be8da` |
| WitnessFeasibility/Certificates.lean | `89f21ae88123d46f07eedaaf8c09216f98bbeb1111c73ae660c29dfc291a9d85` |
| CurlGeometry/Main.lean | `4fe5a5fda25cd5a2e70fec1d0a40c0b79bbadec12f23bca9bed4883e5c15c81d` |
| MeanTopology/Main.lean | `0c106afc75bcfed595457f9a7f77fe1c9bd0699ba5e33caf694d86cc40cdb963` |
| LocalizedForce/Main.lean | `77570f73bccf5aa00987dacaabed688ddd2867b9137bab83d0ff913af033ebd7` |
| SelectedBridge/Main.lean | `1db715d10a38f74df0bc294bbabd49c7b200b56388a9bb93a5c09b9c472603c5` |

Compiler SHA256:
`79fb1d26fa5a39385d59fdc48a711a14b0710ca6480271acce99b4d177cea085`.
All commands, exact source/log/output hashes, environment, resource limits and
baseline preservation are in the receipts and adjacent command/log files.

**Trust boundary:** established clean source-built dependencies were reused
read-only, not rebuilt in this repair. The fresh aggregate audit checks imported
project constants and their transitive axiom closures, not every unused
library/core metaprogram. Pinned installed Lean/core/runtime and host remain trust
roots. **No new independent Comparator/Nanoda check was run.**

## Numerical verdict and A/B boundary

**No-go for certified actual-candidate numerics with current inputs.** No numerical
experiment ran. Certified actual schedules/profile/threshold, retained finite
stages, cutoff jets, inner Borel errors and full derivative/integration errors
are absent. Positive-q finite-prefix control is not a terminal-jet evaluator.
An inconclusive enclosure, failed sign calculation or failed sufficient
response budget is not an obstruction theorem.

If exact absorption were proved, pressure would be corrected to `p−φ` on that
same slab. It would not supply an admissible comparator lifespan or identify a
restart at `1/2` when absorption begins later. Growth transfer still requires
viscosity, projection, activation, the nonlinear remainder, the same datum and
separate PDE estimates. Nonlocal pressure and diffusion invalidate an argument
from annular support to dynamical independence. Thus neither A nor B is certified,
and failure of the proposed sufficient estimate does not show transfer impossible.

## One recommended next experiment

**A symbolic Lean integration experiment:** prove compact pressure-gradient and
Laplacian component cancellation for the same selected interior germs, with
explicit residual-splitting integrability. Success closes the remaining local
integral terms without introducing another witness; failure should identify the
precise adapter needed. Periodization/measure transport and endpoint composition
would still be required before naming a selected-force mean-zero theorem.
