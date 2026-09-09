# Validation and open-finding ledger

## Final response to supplied second reviews — 2026-09-09

**Verdict: reviewed explanatory companion with explicit remaining obligations; needs revision for textbook completeness.** The conditional outer argument received targeted agent-review passes. It is not an independently complete human proof. Complete source/hypothesis audit remains open; Lean/kernel validity, Comparator fidelity and external-prose equivalence receive no new certification.

Provenance: the user supplied two second-review reports against baseline `597692fa5d55e07d810b2d96ead1a67972585425`. The first explicitly describes one independent agent using two perspectives, not two reviewers; the second describes an independent textbook-readability agent review. These are supplied reports, not reviews launched or reproduced by this finalizing coding agent, and neither is human PDE signoff. No new reviewers were launched. Their reported 379-link checks and mathematical recomputations are prior review evidence, separate from the current executions below.

| Finding / response | Final disposition |
|---|---|
| Stale live Euler scope transition | Corrected to the delivered partial scope chapter; external inclusion still open. Historical absence statements below remain historical. |
| Euler scale index ambiguity | EUL-002 now explicitly assigns the scales to insertion from stage n to n+1. Inspected `stages_initial_step` in `Euler/PacketInfiniteConstruction.lean`: the n+1 datum equals the n datum plus the joined input at frequency n, under n≠0. The forward base exception remains intact. |
| Coverage ambiguity | README and SOURCE-MAP now explicitly limit mapping to the 30 authored NSC/NSA/EUL IDs. Scope has no stable SCOPE IDs; scope/interface assertions and all source hypotheses are not independently covered. INT-001 and the NSA-005 scope-ID handoff stay open, rather than adding cosmetic IDs to suggest completion. |
| RI-04 / NS native construction | **Blocker, partial only:** profile equations, stock/shear inputs, normalization, retained operator, carriers and five-row inverse/cancellation lack a continuous contract and derivation. NSC-005 (12) is not a self-contained analytic interface. OBL-NSC-001/004 remain open. |
| RI-05 / Euler corrected child | **Blocker, partial only:** phase graph, physical evaluation and scale-dependent chain-rule/gradient transfer, preservation of amplification and renewed geometry are unexpanded. One metric/radius/growth coefficient must serve every order and the same child. Cylinder energy alone cannot close OBL-EUL-002/003. |
| Pressure, force extension, broad-class conversion | **Blockers:** retain OBL-NSA-002–004 and OBL-EUL-006. Actual pressure-gradient recovery requires the equation and both slab energy bounds; Poisson inversion modulo arbitrary harmonic pressure is insufficient. Finite-energy compact-curl persistence and div–curl/time recovery cannot be replaced by smoothness. |

### Current review-gate summary (supersedes historical table below)

| Gate | Current evidence and limit |
|---|---|
| G1 technical mathematics | Targeted conditional outer calculations passed in supplied reports; analytic producers remain blockers. No complete PDE signoff. |
| G2 source/hypotheses | Selected signatures, fields and proof bodies inspected in supplied reviews; complete dependency/instantiation and external inclusion audit open. Current source inspection is limited to the Euler index correction. |
| G3 calculations | Supplied reviews support fixed-stage losses, distinct finite heads, diagonal derivative counts, Euler horizon directions and Young exponents. Those are reported independent checks, not newly executed calculations here. |
| G4 links/IDs | Current mechanical checks below; only 30 authored IDs, not complete scope/interface coverage or semantic verification. |
| G5 cold reading | Delivered partial scope translation and conditional outer-proof readability accepted with limitations by supplied agent reviews. Native NS and same-child Euler constructions cannot be reconstructed from prose alone. Textbook acceptance withheld. |

### Current execution and preservation record

Before edits, copied the entire companion to `/tmp/proof-companion-second-review.FVqolu/proof-companion/` using `backup=$(mktemp -d /tmp/proof-companion-second-review.XXXXXX); cp -a docs/proof-companion "$backup/"; printf 'Backup: %s\n' "$backup"`. This is a local safety backup, not a portable dependency. Only `04-euler.md`, companion `README.md`, `SOURCE-MAP.md` and this ledger were edited. Root README's pre-existing four-line addition and all untracked user research were left untouched.

Executed from repository root:

```sh
python3 docs/proof-companion/validate.py
(cd /tmp && python3 /home/velvet/Desktop/NavierStokesAndEuler/docs/proof-companion/validate.py)
git diff --check
git diff 597692fa5d55e07d810b2d96ead1a67972585425 --name-status
python3 - <<'PY'
from pathlib import Path
import subprocess
base='597692fa5d55e07d810b2d96ead1a67972585425'
paths=subprocess.check_output(['git','ls-tree','-r','--name-only',base],text=True).splitlines()
protected=[p for p in paths if p.endswith(('.lean','.json','.toml','.yaml','.yml')) or p=='lean-toolchain']
changed=[p for p in protected if not Path(p).is_file() or Path(p).read_bytes()!=subprocess.check_output(['git','show',f'{base}:{p}'])]
assert not changed, changed
print(f'PASS: {len(protected)} baseline proof/config files byte-identical.')
files=list(Path('docs/proof-companion').glob('*.md'))+list(Path('docs/proof-companion').glob('*.py'))
bad=[f'{p}:{i}' for p in files for i,line in enumerate(p.read_text().splitlines(),1) if line.rstrip()!=line]
assert not bad,bad
print(f'PASS: no trailing whitespace in {len(files)} companion Markdown/Python files.')
backup=Path('/tmp/proof-companion-second-review.FVqolu/proof-companion')
print('Companion files changed since backup:', ', '.join(p.name for p in sorted(Path('docs/proof-companion').iterdir()) if p.is_file() and p.read_bytes()!=(backup/p.name).read_bytes()))
PY
git rev-parse HEAD
git status --short
```

Results: both validator invocations **PASS (mechanical scope only)**: 9 Markdown files, **381 relative links, 30 human IDs, 30 mapped lemmas, 161 lexical source targets**. `git diff --check` had no diagnostics. Baseline diff listed only `M README.md` (the pre-existing root change). **2327 baseline proof/config files were byte-identical**, including tracked Lean, JSON/TOML/YAML and toolchain files; all 10 companion Markdown/Python files had no trailing whitespace. Backup comparison listed exactly the four edited files above. HEAD remained the baseline; status retained `M README.md` and untracked `REVIEW.md`, `SIMPLIFICATIONS.md`, `docs/proof-companion/`, `review-notes/`. Final reruns of the two validator commands and whitespace check after recording this evidence returned the same counts and no diagnostics. No new mathematical calculation or Lean `#check` probe was needed for navigation/index/status corrections; none was run. No build, kernel/axiom check, dependency operation, Comparator run, commit or push was performed.

Prior formal evidence, **not rerun here**: [REFACTOR_PROGRESS.md](../../REFACTOR_PROGRESS.md), “Finalization update — review finding addressed,” reports a successful strict `lake build` (11087 jobs) and exactly `[propext, Classical.choice, Quot.sound]` for the four delivered theorems. That same record explicitly defers cold Comparator to a fresh sandbox; it is not evidence of completed Comparator validation. Current prose review neither upgrades nor repeats those claims.

Recommended next audit: first expand one actual NS native cycle from complete profile/operator data through its same-field physical output, and one Euler forward/joined corrected child through graph evaluation and renewed geometry. Then independently audit the force-extension, actual-pressure and finite-energy compact-vorticity bridges. Allocate stable scope/interface assertion IDs with full hypothesis mappings during that substantive work, not as a replacement for it.

## Revision after first independent reviews — 2026-09-09

**Overall status: conditional partial companion; no self-contained-proof certification.**
The user supplied three agent-review reports against `597692fa5d55e07d810b2d96ead1a67972585425` (also the observed HEAD in this revision). Each report states its own limited scope; the mixed-perspective passes are not three separate mathematics/source/pedagogy signoffs each, and none is a human PDE signoff. The revisions below are author responses, not independent acceptance of the revised text. Earlier integration history below is preserved as dated history: its missing-chapter and no-independent-calculation-evidence statements describe that earlier pass.

| Finding ID (consolidated) | Review findings / response | Evidence and residual status |
|---|---|---|
| RI-01 | All reports: central analytic producers remain blockers. Retained every U1–U6 and NS/Euler obligation; added finer interface obligations rather than silently replacing their goals. | Displayed algebra remains conditional. No native estimate, same-child amplification, extension, pressure recovery or class-bridge derivation is newly certified. **Open.** |
| RI-02 | First review stress support/nondegeneracy and both technical reviews' cone hypothesis distinction. NSC-002 now says radial support on η∈[−1,1], leading-only nondegeneracy, and actual cone/matrix amplitude argument. Retained the flat-edge counterexample as evidence. SOURCE-MAP corrected. | Inspected `FinalSlowBase` geometry, stress estimate declarations/local transports and support interfaces; `LeadingStressWeights.FullTrueCone`; `ActiveAnnulusWeight` and `FlatCutoff` definitions. `weighted_jets` has no additional cone premise, unlike the leading estimates. Prose correction complete; analytic obligation remains open. |
| RI-03 | All reports: derivative domains in (6). Explicit D_(X,η), full blown (r,X,η) derivative with q frozen, separate physical derivatives. | Inspected `SlowBorelBase.blownJet` and `FinalSlowBase.leading_radial_jets` interfaces. Physical transfer still U6. Notation correction complete, not a new physical bound. |
| RI-04 | NS cold-reading interfaces. Added exact cone test, explicit edge weights and rank debt functional/scaling in INTERFACES.md. | Read `TrueConeLoop.InTrueCone`, `ConeAlgebra.coneBound`, `CorrectionState` moment/debt definitions and `MeanRankUpdate` scaling/constructors. **Partial:** prepared-profile equations/stocks/matching/C_*, retained linear operator, omitted Gaussian terms, carrier geometry and five-row cancellation remain explicit RI-04a/b under OBL-NSC-001/004. No pedagogical signoff. |
| RI-05 | Euler cold-reading interfaces. Defined cylinder and actual finite metric Gevrey norm before interpreting the correction budget; distinguished cylinder coercivity conversion from physical gradient control. | Read `AllOrderDriftBudget`, `GevreyMetricEstimate`, `BaseWordMetric`, `WeightedCylinderEnergy`, weight definition in `EulerProof/Foundations`, and cylinder/domain source. **Partial:** packet formula, physical graph, restriction inequality, pressure and same-child amplification remain OBL-EUL-002/003. |
| RI-06 | Missing scope chapter. Added 01-scope.md: data/force quantifiers, boundary conventions, internal competitor restriction direction, distinct Euler lifespan/global contracts and external inclusion checklist. Updated navigation. | Inspected actual NS solution/force structures and complete Euler SolutionDefinitions. Internal prose translation delivered; **INT-001 and OBL-NSA-005 remain open** for complete external-prose correspondence and adapter review. File existence is not closure. |
| RI-07 | Restart interval now explicitly 0≤t₀<1; shifted datum and admissible scalar pressure retained. | NSA-010 uses only the existing nonnegative-time contract. Documentation fix complete. |
| RI-08 | Euler limiting datum renamed u_init throughout chapter, preserving stage family u_n and exceptional stage-zero/first-insertion logic. | Text/reference check; no source notation changed. Documentation fix complete. |
| RI-09 | NSA-004/005 local presentation loop. NSA-005 now assumes only prior estimates and component exterior models for its algebra, then explicitly orders compatibility → force extension → candidate assembly. | This repairs the local assumption rather than deleting the dependency explanation. INT-004's independent producer audit remains open. |

The supplied reviewers report conditional recomputation of base curl/gauge, primitive sign, covariance/exponent arithmetic, diagonal derivative counts, localization/activation/scaling, energy regularization, pressure Young exponents, Euler comparison/summability/H3 bootstrap and outer maximality. They report no algebraic defect under those premises and no established flaw in a delivered Lean theorem. Those are **reported independent calculation checks**, not fresh executions by this revising agent, dependency-closure audits, kernel checks or external-prose verification. Their force/gauge/pressure/confinement counterexamples support retained restrictions, not construction certification.

### Revision checks and boundaries

- Documentation validator executed from root: **PASS**, 9 Markdown files, 379 relative links, 30 IDs, 30 mapped lemmas, 161 lexical source targets Final reruns from root and `/tmp` returned those same counts and PASS. `git diff --check` returned no diagnostics; a separate scan of untracked companion Markdown found no trailing whitespace. HEAD remains the baseline and reported working-tree status categories are unchanged.
- No temporary Lean probe was needed for these definition/prose corrections; none was run. No Lean elaboration/kernel/axiom or Comparator result is claimed. Lexical matches cannot justify mathematical estimates or section hypotheses.
- Source inspection was targeted, not an audit of every map helper or dependency closure. New interface sources are linked in INTERFACES.md; the 30 main lemma IDs and their obligations remain intact.
- Documentation-only changes in this revision; no Lean, build, dependency or research-file changes, commits or pushes. Pre-existing root README modification and untracked research files were left untouched.

## Historical initial integration record

**Overall status at integration: partial companion; no independent mathematical signoff.**
Baseline and observed HEAD at integration start: `597692fa5d55e07d810b2d96ead1a67972585425`.
Integrator: coding agent, harness `PI_MODEL=gpt-6-astra` (environment actually queried). No separate agents or human reviewers participated in this integration. Author inspection remains author inspection; integration is not an independent PDE review of the authors' dependency closures.

## Preservation and scope of this pass

- Read PLAN and all three existing chapters completely, including text beyond truncated tool output. `01-scope.md` is absent. Did not create a pretend scope chapter or allocate SCOPE lemma IDs to an undelivered author.
- Before chapter edits, copied PLAN and all chapters plus the repository README outside the repository to `/tmp/proof-companion-integration.1X17ng/` (root README saved as `repository-README.md`). This is a local safety backup, not a portable artifact or committed dependency.
- User authorization for documentation integration and a minimal discoverability link supersedes PLAN's earlier directory-only restriction for that link. PLAN remains unchanged as historical authoring instructions. Existing chapters were preserved with targeted transitions and interface/notation edits.
- Independently read the NS/Euler public submission signatures and complete solution-class definition files in this pass. The source map preserves authors' additional interface inspections; those were **not all repeated** by the integrator. Additionally inspected the exact `option_C_of_candidate` / `option_D_of_candidate` signatures, namespaces and local proof bodies via source search; both take their candidate record and ν>0, then choose zero datum and the rescaled force. This is limited adapter inspection, not expansion of every candidate field or dependency.
- Initial status: untracked `REVIEW.md`, `SIMPLIFICATIONS.md`, `review-notes/`, and the companion directory. Research files are protected and were not edited. No Lean/proof/dependency/build-setting edits, reset/stash/clean, builds, dependency operations, commits or pushes.

## Checks and reproducible commands

Run from repository root:

```sh
python3 docs/proof-companion/validate.py
git rev-parse HEAD
git status --short
git diff --name-only
git diff --check
```

The Python script is standard-library-only and read-only, resolves paths relative to itself, performs no network operations, and does not import project code. It checks inline relative Markdown links, explicit anchors/simple heading anchors, uniqueness of human IDs, source-map coverage, repository discoverability, and **lexical declaration suffixes in explicitly linked source-map files**. It does not resolve qualified namespaces, generated projections, section variables, or elaborated hypotheses. Source helpers not separately listed in the map retain chapter citations and need independent source review. Code-fenced examples and external URLs are outside the script's link scope; it is not a full Markdown parser.

| Check | Result / evidence |
|---|---|
| Environment and initial provenance | Executed: PI_MODEL=`gpt-6-astra`; HEAD matches baseline; initial status recorded above. |
| Companion link/anchor/coverage and lexical source-map check | **Executed, PASS in mechanical scope:** 7 Markdown files, 344 relative links, 30 unique human IDs, 30 mapped lemmas, 161 lexical source targets. Initial run falsely counted PLAN's inline example anchor (31 IDs); corrected the script to recognize live line-leading HTML anchors, then reran successfully. |
| Script location independence | **Executed, PASS:** `(cd /tmp && python3 /home/velvet/Desktop/NavierStokesAndEuler/docs/proof-companion/validate.py)` produced the same counts and result. |
| Final preservation / whitespace check | **Executed:** `git diff --check` returned no diagnostics; HEAD unchanged; tracked diff contains only root `README.md` (four added lines). The companion remains untracked, as do the unchanged pre-existing research paths. Git's tracked whitespace check does not cover untracked companion files; a separately executed standard-library scan found no trailing whitespace in companion Markdown/Python files. Byte comparison also confirmed PLAN unchanged from its integration backup. |
| Lean syntax or `#check` probes | **Not run.** No temporary Lean probe results are claimed. |
| Build, kernel, axioms, Comparator | **Not run in this task.** Existing source `#print axioms` commands and repository reports are not newly executed evidence. |
| External manuscripts / Clay correspondence | **Not retrieved or verified in this pass.** No external-prose equivalence signoff. |

A lexical PASS cannot establish a proposition, a namespace, an analytic estimate, successful elaboration, or challenge fidelity. Future formal validation requires separate authorization and the unchanged [Comparator instructions](../../ComparatorChallenges/README.md) and [repository validation plan](../VALIDATION-PLAN.md), including their fresh unprivileged sandbox requirements. Do not run build recipes in this working tree as part of companion review.

## Historical initial five review gates

Legend: **open** means not independently completed; **partial** names limited evidence, not a pass. Chapter authors cannot be their sole final reviewer.

| Unit | G1 technical PDE | G2 source/hypotheses | G3 calculations | G4 links/IDs/source targets | G5 cold reading |
|---|---|---|---|---|---|
| Scope / delivered classes | Open: full chapter missing | Partial: integrator read public signatures/definitions; external bridge open | Open: full norm/boundary translation | Mechanical summary/map checks only; no SCOPE IDs exist | Open |
| 02 NS construction | Open | Author local inspection only | Displayed algebra, no separate recomputation signoff | Integrated script only; namespace and hypothesis audit open | Open |
| 03 NS analysis | Open | Author local inspection; cross-chapter IDs now attached, actual instantiation open | Displayed calculations, no independent signoff | Integrated script only; semantic source audit open | Open |
| 04 Euler | Open | Author local inspection only | Displayed calculations; full insertion and analytic criteria unexpanded | Integrated script only; semantic source audit open | Open |
| Integration | No new mathematics certified | Many-to-many map, not full dependency audit | Deductions distinguished from packaged theorems | Reproducible narrow checks; see executed results | Open |

## Integration findings and resolution history

| ID / owner / state | Finding and affected claims | Evidence needed / history |
|---|---|---|
| INT-001 / scope coordinator / **open** | Reserved `01-scope.md` is missing. Exact four-statement narrative, external norm/derivative/boundary/energy translation, and official-prose competitor inclusion are not fully authored/reviewed. Affects NSA-005 scope handoff and global interpretation of both branches. | Integrator added a source-based summary, not scope signoff. Scope owner must provide the full chapter and stable SCOPE IDs, then separate review. No file-presence placeholder counts as closure. |
| INT-002 / NS construction + analysis / **open** | Same-field handoff had no attached NSC IDs. Analytic realization and schedule coherence remain load-bearing. | IDs now attached: NSC-003,007–009 → NSA-001–005. Independent reviewer must trace `physicalData`, `estimates`, selected witness and origin germs for identical parameters/fields. Linking only resolves navigation, not OBL-NSA-001. |
| INT-003 / integrator / **closed with documentation evidence** | NS similarity η conflicted with analysis spatial cutoff η; notation otherwise changes locally across branches. | NSA-005 cutoff changed to ρ; glossary records raw/post-cutoff gains, prefix inclusivity, direct-field versus budget B, Euler-local q/η/indices, and spatial versus joint derivatives. Pressure difference in NSA-007 is now r_p throughout, distinct from cutoff ρ. Closure concerns notation only; cold-reader review remains open. |
| INT-004 / integrator + reviewers / **open** | Apparent NSC-005/006 and NSA-004/005 dependency cycles need substep ordering. | README explains independent finite-head lemma and localization algebra before extension/candidate assembly. Reviewers must verify no producer depends on its downstream conclusion. |
| INT-005 / source reviewer / **open** | Full qualified-name, section-variable, record-field and instantiation audit not executed by integration. Lexical matches are weaker. | Review all map rows and helper citations at the baseline; report exact discrepancies. Any syntax probes must actually run and be logged separately, never inferred from spelling. |
| INT-006 / integrator / **closed with documentation evidence** | Accessible entry point, source/deduction distinctions and obligation visibility were distributed across drafts. | README, SOURCE-MAP, this ledger, chapter transitions and minimal root README link added. This is integration closure only, not mathematical or pedagogical signoff. |

## Analytic obligation register

All obligations below are **open**. Owners, precise hypotheses, affected lemma IDs, source leads and required closure evidence are retained in the linked chapter ledgers; this table collects rather than weakens them. History: author opened during source inspection; integrator linked/propagated, no analytic closure evidence added. Same-topic obligations across chapters are deliberately not merged into a false closure.

| IDs / owner | Missing analytic assertion and affected conclusions | Closure evidence |
|---|---|---|
| OBL-NSC-001 / construction | Closed prepared profile, outgoing matching, finite modulation and true cone; NSC-002 onward. | Full ordered ODE/moment/cone derivation and independent hypothesis check. |
| OBL-NSC-002 / construction | All-order actual base remainder and weighted edges on `PhysicalApproach`; all residual conclusions. | Common Borel bundle/coefficient identities with derivative-loss estimates. |
| OBL-NSC-003 / construction | Anchored heat primitive and actual exterior gauge extensions; NSC-003 and NSA-004–005. | Central/off-plane neighborhood and coefficient arguments for same potential. |
| OBL-NSC-004 / construction | Native Volterra/signed quotient estimates, supported covariance, tail identity, temporal/rank/pressure gain; NSC-005 onward. | Complete analytic cycle under U4, not just cancellation algebra. |
| OBL-NSC-005 / construction | Initialization, physical transport/overlaps, same coherent run; NSC-007 onward. | Chart-germ and exterior identities for every component, including direct stage zero. |
| OBL-NSC-006 / construction | All-order physical raw/prefix/residual bounds with losses fixed before stage; NSC-008 onward. | Full coordinate/gluing/logarithmic bookkeeping. |
| OBL-NSA-001 / both NS owners | Same-field physical estimates, support and axis germs; candidate applications NSA-001–010. | Independently verify actual NSC-003,007–009 instantiation; inherits all six NSC obligations. |
| OBL-NSA-002 / analysis + construction | Anchored exterior and raw off-plane models, uniform support; NSA-004 onward. | Actual coefficient/heat-primitive proof; overlaps NSC-003 but includes raw stage models. |
| OBL-NSA-003 / analysis | Taylor–Borel force extension of actual normal jets with spatial locality; NSA-004 onward. | Compact-exhaustion thresholds, all-order gluing and compatibility proof. |
| OBL-NSA-004 / PDE reviewer | Actual pressure recovery and flux/localized analytic estimates; whole-space NSA-007–009. | Harmonic Sobolev-dual/Riesz/commutator proof plus Sobolev/transport bounds; periodic comparison does not need this route. |
| OBL-NSA-005 / scope + integrator | Constructed-data admissibility and direction from prose competitor into excluded class, including scaling; interpretation of NSA-008–010. | Full class/pressure/energy/boundary audit, separate from challenge agreement; blocked in part by INT-001. |
| OBL-NSA-006 / independent reviewers | All five review gates and displayed calculations. | Separate source/math/calculation/cold-reading reports; mechanical checks alone do not close it. |
| OBL-NSA-007 / future research | Terminal zero or pressure-absorbable force, shifted datum/class bridge; **only conditional NSA-010 restart**. | New force-removal theorem preserving blowup. Not needed for forced exclusion; shutdown after one is insufficient. |
| OBL-EUL-001 / Euler | One full fixed scale/guard ledger; EUL-002 onward. | All actual cost substitutions, base exceptions and renewal sums checked simultaneously. |
| OBL-EUL-002 / Euler | One forward and one joined physical packet, ray growth, pressure, inverse-growth amplitude and renewed geometry; EUL-003 onward. | Continuous physical derivation and perturbation bounds for the same child. |
| OBL-EUL-003 / Euler | Weighted all-order correction solver, pressure, coherence and graph-to-physical Euler identity; EUL-004 onward. | Actual norm/energy/solver proof and same-field growth check. |
| OBL-EUL-004 / Euler | Physical H_m majorants, shifted tail, exceptional first datum and common compact limit; EUL-006 onward. | Field identities, representative/support proof, not elementary summability alone. |
| OBL-EUL-005 / Euler + PDE reviewer | H4-dependent H3 stability, local/endpoint theory and whole-space logarithmic/BKM estimate; EUL-007–010. | Exact ordinary-class analytic proof or hypothesis-matched standard-theory replacement. |
| OBL-EUL-006 / Euler + scope reviewer | Displacement, compact-vorticity persistence from finite energy, div–curl/time recovery, canonical and scalar-class adapters; EUL-001,008–010. | Truncation/elliptic/pressure audit and both closed Sobolev adapter directions; no assumed global derivative bounds. |

Detailed records: [construction ledger](02-ns-construction.md), [analysis ledger](03-ns-analysis.md), [Euler ledger](04-euler.md). Positive-viscosity packet survival and replacement for compact-vorticity confinement in EUL-011 are additional **new research**, not asserted source results.

## Review instructions and signoff template

1. **Scope reviewer:** deliver missing scope work; distinguish existence of admissible constructed data from inclusion of every intended competitor in the excluded class. Do not infer external Clay equivalence from copied definitions.
2. **NS reviewer:** follow one fixed profile/run/schedule. Recompute base curl and gauge, signed-stress moment error, all covariance terms, finite-band head, finite-prefix plateau, derivative losses, activation force, separated-translate locality, zero-norm energy regularization, pressure absorption and inverse viscosity scaling.
3. **Euler reviewer:** verify forward versus positive-history insertion, one common numerical choice, inverse-growth initial amplitude, physical H_m majorants, H4 reference constants, both horizon inequality directions, exact maximality and compact-vorticity upgrade. Do not assume t_n<T_*.
4. **Source reviewer:** for every map row read declaration, enclosing namespace/section and all record fields; check actual inputs and conclusion direction. Label new deductions and proposed strengthenings separately. Re-run mechanical checks after any edit.
5. **Cold reader:** without Lean or research reports, state each theorem class, explain why the same field retains growth and satisfies the needed equation, reconstruct displayed calculations, and identify every boxed input. Log confusing notation and missing transitions.

For each review add: reviewer identity and role (agent or human), date, baseline/working-tree scope, lemma/obligation IDs, exact inspected sources and any executed commands/output, findings, proposed revisions, and limitations. Close an obligation only with evidence and a separate reviewer where required. Keep four verdicts separate: human mathematics, Lean/kernel validity, Comparator challenge fidelity, and equivalence to external prose. None currently receives overall signoff here.
