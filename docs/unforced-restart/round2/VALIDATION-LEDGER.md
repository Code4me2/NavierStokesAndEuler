# Review repair ledger

## Technical verdict

**Finite-slab/candidate-budget results retained at cached-check scope. Clean acceptance and endpoint force removal remain BLOCKED.** No new PDE theorem was proved during this repair; no accepted Lean source, hypothesis, or axiom whitelist was changed. Baseline and round-one preservation is checked by the independent Round2 runner, not by rerunning the frozen path-bound validator.

## Findings and disposition

| Review finding | Disposition / repair |
|---|---|
| Dependency inventory omitted split objects and IR | Repaired in `Round2/Integration/validate.py`: per-module `.olean`, `.olean.server`, `.olean.private`, `.ir`, `.ir.sig` hashes and resolved paths; conservative full resolver/core artifact inventories before and after compilation; equality rejects content changes, additions, deletions and symlink retargeting. Fresh research output hashes are rechecked after all compilations. Installed executable hashes are rechecked. This is stability evidence, not authenticated source-build provenance or an adversarial concurrent-write monitor. |
| Core inventory omitted IR | Same artifact predicate now covers core IR/signatures, split objects and native libraries/objects. Installed core/runtime remain trusted binaries, not bootstrapped. |
| Markdown exact-removal graph required all of O9 | Repaired: exact route requires `axis_value_wrapper`, O1/O2 and O3/O4, matching JSON. It does not require O7/O8 or derived perturbative relative error. |
| Endpoint growth transfer unproved | OPEN O7–O9. L² concentration prevents evaluation control; finite C or Bk does not imply useful tolerance. No hidden growth-preservation premise added. |
| Comparator application/fixed restart unassembled | OPEN O1/O2. Required order: one t0, H=1−t0, arbitrary datum a and fields v,q, then every S<H restricts these same fields. Adapter must retain periodic pressure and continuity at H. Existence on [0,H) alone does not give endpoint continuity. Global arbitrary-datum existence may be an explicit reductio input, never the baseline zero-datum wrapper or a conclusion here. |
| Strong-force bounds only establish membership | OPEN O8: selected constants, whole-cell projected residual and actual weighted tolerance are missing. Origin flatness and zero mean do not imply gradient force. |
| Divergent sufficient envelope mistaken for actual instability | No upgrade made. N≡0 satisfies N′≤κN/τ+M for M≥0; failure of a positive comparison envelope gives no actual-error lower bound. Selected germ/jet specialization is itself open. |
| Finite-slab signs, pressure cancellation, FTC and force terminal trace | Source inspection confirms the accepted chain; no corrective Lean edit indicated. Report's displayed budget integration-variable mismatch corrected to ∫₀ˢg≤C²s. |
| Clean campaign rejected tracked ProofWidgets traces | BLOCKED, not waived. Existing trace hashes and tracked source inventory reverified read-only. No deletion, exemption, retry, Lake invocation, dependency compilation or object substitution. An explicitly reviewed policy disposition and successful pinned-source build chain are still prerequisites. Requested research replay against source-built dependencies cannot run because that environment does not exist. Cached replay is separately labeled, not a clean fallback. |

## Exact retained statements (viscosity one)

`PeriodicSlab.periodic_slab_comparison`: for S>0, jointly smooth velocities u,v and pressures p,q on the closed slab, all four spatially periodic, continuous force f, divergence-free velocities and forced/unforced residual equations in (0,S), and common arbitrary initial datum, there exists B_S>0 bounding the reference spatial derivative on the cell, with

`E(s) ≤ exp((2B_S+1)s) ∫₀ˢ exp(−(2B_S+1)r) g(r) dr`, for every s∈[0,S],

where E=∫Q|u−v|² and g=∫Q|f|². The source states the constant exponent as a literal integral. It derives the derivative/majorant/FTC inputs; it assumes neither comparator existence nor relative error. The inherited rate is E′+2D≤(2B_S+1)E+g. No uniform B_S as S↑H.

`ActualForce.candidate_cell_budget`: for CandidateProperties u p f, t0≥0 and fixed H>0, there exists one C>0 with g(s)=∫Q|f(t0+s,x)|²≤C² on [0,H], g interval-integrable on every [0,S], and `∫ r in 0..S, g(r) ≤ C²*S` for every S∈[0,H]. This uses force smoothness/periodicity, not terminal velocity smoothness or growth. No selected-witness or comparator specialization is claimed.

## Reproducibility and provenance

Driver command: `python3 Research/UnforcedRestart/Round2/Integration/review-check.py`. The driver records exact subprocess commands, exit statuses, log hashes, accepted-source and tool hashes, all eleven external dependency pins and a hash inventory of preserved external campaign evidence. It verifies every tracked source hash in the external preflight inventory. It runs source-only negative tests, the fail-closed `validate.py --clean` request, and a separately labeled cached strict replay of all 14 mathematical sources and both audits.

The updated Round2 manifest changes only the two repaired tool hashes; inherited and new mathematical-source hashes remain identical. Previous validator hash: `0f77b033f30a8163ea2aad47ba29573567260e9cdf6487a2fd449922ba63f267`; previous selftest hash: `075deb6b6bb9b2ed0f5c86107a735eadb163339818e01820572a6a3e22e3e5ca`. Historical evidence is not rewritten. The new selftest tests all five module artifact types and rejects mutations/additions/deletions.

### Completed repair checks

Evidence: `Research/UnforcedRestart/Round2/Integration/evidence/review-20260909T225709Z/`; driver transcript: `Integration/evidence/review-driver.log`. Each command below has its command/exit/log-hash JSON there.

- `python3 Research/UnforcedRestart/Round2/Integration/selftest.py`: exit **0**, 12 source-tool test groups.
- `python3 Research/UnforcedRestart/Round2/Integration/validate.py --clean`: exit **1**, expected fail-closed blocker; preserved run `Integration/runs/20260909T225710Z/FAILURE.json`. Zero Lake invocations and zero source-build compilations.
- `python3 Research/UnforcedRestart/Round2/Integration/validate.py`: exit **0**, independent cached run `Integration/runs/20260909T225712Z/`. All **16** strict compilations exit 0. **96** named exports, **42,939** project/research constant closures, **11,110** imported modules; all closures within `{propext, Classical.choice, Quot.sound}`. Complete enumeration: `declarations.tsv`.
- **72,657** conservative compiler-input artifacts have identical before/after inventories; **53,438** resolved per-module artifact records include split objects and IR; **15,127** core artifacts inventoried. These counts include a conservative superset of possibly consumed inputs, not a claim that every object was loaded. Fresh research artifacts and executable hashes also passed stability checks.
- Byte preservation: **2,335** baseline files and **114** archived files unchanged; all **11** worktree dependency pins match. External provenance recheck verifies **12,363** tracked source hashes and all eleven pins, and preserves hashes of the rejected campaign evidence. Source acquisition is not a successful dependency build.
- Repaired manifest SHA-256: `631023189131a49280fd50367195025fdd07f0194c86568e6a1db2530282765f`. Exact accepted source/tool hashes: `sources.json`; pins/source-evidence chain: `clean-provenance-recheck.json`; compiler commands and source/output hashes: run `CACHED_SUCCESS.json` and per-source JSON.

No cached object was installed into the external clean checkout. No clean acceptance, new mathematical closure, commit or push.

## Next narrow recommendation

First obtain an explicit policy decision on the two tracked ProofWidgets JS traces, preserving the rejected campaign, before authorizing a new source-build campaign. Mathematically, specialize one selected witness/restart and certify a whole-cell curl component or projected coefficient **including the localization annulus**. Nonzero curl at any slab point excludes exact pressure absorption on that slab; nonzero terminal curl excludes every terminal slab by continuity. A zero terminal trace alone is inconclusive. Only then prioritize a spatially resolved viscous projected response with controlled truncation and growth-relative error; linear success would still leave nonlinear closure.
