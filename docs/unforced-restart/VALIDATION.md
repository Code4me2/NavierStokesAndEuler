# Agent 18 — independent Astra review disposition

## Scope

The three supplied reviews accept bounded formal research, not an unforced restart. This pass repairs documentation and records blockers; it does not purport to solve the missing PDE analysis. User authorization for this repair supersedes the historical read-only reviewer assignment. Only isolated research/docs paths are written; baseline sources, configuration and original checkout are preserved. No commits or pushes.

The accepted manifest remains comprehensive and unchanged: twelve mathematical Lean files, 82 theorems and 6 definitions, plus the aggregate audit; the setup import probe is explicitly classified separately. No new conditional theorem, definition, hypothesis or axiom is introduced. No accepted proof was reported invalid. Successful elaboration of conditional algebra is not existence or stability.

## Finding IDs, changes and unresolved obligations

IDs below consolidate the repeated findings across the three supplied reviews. All mathematical stress tests here are explanatory Markdown, not newly formalized theorems.

| ID | Disposition and evidence | Remaining blocker |
|---|---|---|
| **AR18-01 — exact force removal (critical)** | Retain O3–O4 explicitly. `candidate_shift_unforced` requires terminal vanishing; `absorb_on` requires an admissible gradient identity and uses **p−φ**. Cutting force leaves the old-field defect `(1−ρ)f`. Shutdown at 2 is after singular time 1. | No actual selected-field terminal zero-force interval or potential is supplied. Smoothness, origin flatness and curl-free forcing are insufficient. A nonzero constant torus vector has nonzero circulation on some fundamental cycle and is not a periodic scalar gradient. A smooth force supported away from the origin is origin-flat without vanishing everywhere. |
| **AR18-02 — strong norm and growth (critical)** | Corrected the erroneous vector-potential construction in `strong-norm-growth-transfer.md`: use `A=½χ(a×x)`, not a potential constant near zero. Its curl equals a near zero. Clarified periodization inside one cell. Retain O7–O9: scalar `N` and `herr` are explicit conditional inputs, not established NS stability. | With `wε=ε⁻¹ curl A(x/ε)`, squared L² error scales as ε but origin magnitude as ε⁻¹. Thus energy control cannot supply evaluation. Define a genuine norm, prove fixed-positive-viscosity stability and its evaluation embedding; H² velocity/H³ gradient are candidate orders, not proved stability. Derive `herr` for the actual reference, rather than assume the desired comparison. |
| **AR18-03 — weighted threshold (high)** | Retain O8 and the quantitative acceptance test without weakening it. Fixed-ε short-interval time budgets are proved; mixed-norm packaging and the actual weighted threshold are not. | For H>0, `E(s)=(Hs−s²/2)/(H−s)` solves `E′=E/(H−s)+1`, `E(0)=0`, on `[0,H)`. The source budget is ≤H while E diverges. This refutes only the generic small-budget inference, not actual PDE stability. Derive reference-dependent amplification and meet its tolerance for **one fixed restart**, not a changing datum on each slab. |
| **AR18-04 — existence and horizon (high)** | Retain O1–O2. Actual snapshot admissibility is genuine but the zero-datum `Solution` wrapper cannot encode a nonzero restart. | Supply arbitrary-data class adapters and applicable existence/continuation with adequate lifespan for construction. A hypothetical global A/B comparator supplies existence in a reductio, but still supplies neither force removal nor stability. |
| **AR18-05 — energy adapter (medium/high)** | Retain O5–O6. Accepted viscosity-one periodic identity uses `E=∫|w|²`, `energyRate=−2D−2C+2W`, and `energyRate+2D≤(2B+1)E+∫|f−g|²`. Pressure and velocity periodicity are explicit; B bounds the operator norm of Du. No sign/factor repair is indicated. | Assemble slab differentiation (`PeriodicUniqueness.energy_hasDerivAt`), endpoint continuity, FTC and Gronwall. No whole-space pressure-flux closure or strong norm follows automatically. Reference compact support must not be assigned to a viscous comparator. Arbitrary real viscosity in subtraction algebra is not a dissipativity assertion. |
| **AR18-06 — cutoff/scaling compactness (medium)** | Retain O10 and cutoff obligations. Pointwise force convergence and a base-axis identity do not export an assembled nonlinear limit. | Width-d cutoff derivatives cost d⁻ᵏ. If both velocity and pressure are multiplied by time-only ρ, then `Rν(ρu,ρp)=ρRν(u,p)+ρ′u+(ρ²−ρ)Du(u)`; cutting force alone addresses neither extra term. Prove residual covariance, assembled transfer, compactness, nonlinear-product convergence and solution-class/nontriviality, or justify a new normalization and its altered equation. Base-axis r⁻²ʰ growth obstructs locally uniform velocity compactness only after assembled transfer; no general weak-limit impossibility is claimed. |
| **AR18-07 — cached provenance (medium)** | Preserve the validator, frozen hashes and strict acceptance criteria. Fresh research/audit elaboration and source/artifact inventories remain narrower than independent foundational verification. | Hashing source and object separately does not prove their build correspondence. A clean dependency rebuild and independent Comparator verification in a separate environment are needed for those stronger claims; neither is attempted here. |
| **AR18-08 — historical labels (low)** | Added explicit supersession notices to `pressure-absorption.md` (integrated B) and `actual-forcing-budget.md` (integrated A), and an all-task-report notice in `SYNTHESIS.md`. The integrated per-declaration manifest is authoritative. | No mathematical blocker is resolved by relabeling. Research categories A–D are **not** Clay problem alternatives A/B/C/D. |

## Exact source changes

- `docs/unforced-restart/strong-norm-growth-transfer.md`: corrected nonzero-curl construction and periodic concentration explanation (AR18-02).
- `docs/unforced-restart/pressure-absorption.md`: historical classification notice (AR18-08).
- `docs/unforced-restart/actual-forcing-budget.md`: historical classification notice (AR18-08).
- `docs/unforced-restart/SYNTHESIS.md`: review disposition link, historical scope and authoritative classification notice (AR18-08).
- `docs/unforced-restart/VALIDATION.md`: this finding/evidence/obligation ledger.

No accepted Lean, audit, validator or manifest edits. O1–O10 in [OBLIGATIONS.md](OBLIGATIONS.md) remain unproved applications, not additional hypotheses silently counted as achieved progress. The exact-route identities, comparator existence/class, strong-norm error estimate, weighted primitives/threshold and assembled compactness premises have not been established together for the actual candidate. Their conditional tools remain useful only as explicit targets for that work.

## Rerun evidence

Post-repair invocation of the unchanged frozen validator completed with **exit 0**:

```sh
python3 Research/UnforcedRestart/integration/validate.py
```

- Agent-18 invocation log: [agent18-run.log](../../Research/UnforcedRestart/integration/agent18-run.log); status: [agent18-run.exit](../../Research/UnforcedRestart/integration/agent18-run.exit).
- **All 13 strict compilations passed**: twelve accepted files and aggregate audit, each with `-j1 -DautoImplicit=false -DwarningAsError=true` and `LEAN_NUM_THREADS=1`.
- Fresh [SUCCESS.json](../../Research/UnforcedRestart/integration/validation/SUCCESS.json) records 88 research exports, **42,929** audited project/research constant closures, **11,108** imported-module inventory entries and baseline checks PASS. All checked closures use only subsets of `propext`, `Classical.choice`, `Quot.sound`.
- Frozen research/audit/validator hashes, comprehensive Lean-file classification, prohibited-source scans, tracked baseline/index equality, eleven package pins/working diffs and nonescaping-path checks passed. The validator regenerated `declarations.tsv`, `dependencies.json`, compiler logs/exit files and fresh research/audit objects solely in its isolated research output directory. Inventory hashes record current cached dependencies; this rerun does not claim independent build provenance.
- Baseline remains `597692fa5d55e07d810b2d96ead1a67972585425`. No baseline/configuration edits, commits, pushes or original-checkout operations.

The supplied independent-review logs are reviewer-reported evidence, not checks newly performed by agent 18. This evidence section was filled after the successful code checks; it changes no compiled input.

## Limits

No unforced A/B conclusion, independent certification of baseline C/D claims, or Millennium solution. The actual mathematical blockers are left open, not replaced with weaker success criteria. No clean dependency rebuild, independent Comparator execution, or independent audit of the entire candidate construction is claimed.
