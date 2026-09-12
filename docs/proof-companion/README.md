# A human-readable proof companion

**Status: agent-reviewed explanatory companion with explicit remaining obligations; not an independently complete human proof.**
Source baseline: `597692fa5d55e07d810b2d96ead1a67972585425`.
The chapters explain the mathematics for a graduate PDE reader; Lean names are an audit trail, not prerequisites. Substantial analytic steps remain boxed and conditional in the human exposition. Their presence as source theorems does not supply their missing human derivations. The supplied second reviews give a targeted pass to the conditional outer argument, but retain **needs revision for textbook completeness**. Full source/hypothesis audit remains open; agent review is not human PDE signoff.

## The idea in plain language

**Navier–Stokes:** begin with a singular core whose speed at the origin grows without bound. Correct its equation error repeatedly while preserving that same core. A carefully chosen infinite diagonal has an error smooth enough to extend as an external force. Spatial localization and time activation give zero initial velocity and a compact presingular solution. Uniqueness on each shorter time slab makes a hypothetical smooth global competitor agree with it, contradicting bounded speed on a compact set through the singular time. The force is smooth, **not asserted zero**.

**Euler:** construct different exact, unforced solutions with increasingly large sampled gradients, but initial data converging to one smooth compact datum. Stability against any sufficiently long regular reference solution would keep those gradients bounded. This gives a finite maximal lifespan. Continuation criteria give the terminal C1/vorticity conclusions; a separate compact-vorticity argument excludes the broader global solution class. This is not a formula for one trajectory passing through every packet activation.

<a id="scope"></a>
## What the four delivered statements say

This summary was checked against the two submission files and their definitions. The new [scope chapter](01-scope.md) supplies a partial internal class translation; external-prose equivalence and independent hypothesis review remain open.

| Delivered declaration | Mathematical quantifiers and class |
|---|---|
| `NavierStokes.Comparator.navier_stokes_breakdown_R3` | For **every** fixed viscosity ν>0 there **exist** smooth divergence-free rapidly decreasing data and smooth rapidly decreasing external forcing with no global solution in the specified whole-space class. The adapters choose zero datum. |
| `NavierStokes.Comparator.navier_stokes_breakdown_periodic` | For every ν>0 there exist smooth unit-periodic data and force, with force derivatives rapidly decreasing in future time, excluding the specified global periodic class. Again the constructed datum is zero. |
| `Euler.euler_breakdown_R3` | There exist smooth divergence-free rapidly decreasing data with no global **unforced** Euler solution in the specified whole-space class. |
| `Euler.exists_compact_smooth_euler_singularity` | There exist nonzero compact smooth data, 0<T_*≤1, and an unforced solution on [0,T_*) in the all-order Sobolev class, with bounded energy. Closed-interval existence from these data for T>0 holds exactly for T<T_*. C1 bounds and vorticity integrals are finite on every shorter slab, but terminal C1 **limsup** and the full presingular vorticity integral are infinite. The same datum also excludes the broader global class. |

The **global whole-space classes** require velocity and scalar pressure jointly smooth on R³×[0,∞), the equation and divergence condition for t≥0, the initial trace, timewise L² membership, and **one** bound on ∫|u|² over all future times. They do not impose pressure decay or all-order global Sobolev bounds. The time derivative at zero is right-sided (`derivWithin`). The **periodic NS class** requires both velocity **and scalar pressure** unit-periodic, with no explicit energy field; periodicity of the pressure gradient alone is not the stated class.

Rapid decrease of datum means ∀m∈N ∀K∈R ∃C ∀x, |D_x^m u₀(x)|≤C/(1+|x|)^K. For whole-space force replace the denominator by (1+|x|+t)^K, t≥0, and use joint derivatives within the future half-space; for periodic force use (1+t)^K uniformly in x. These are exact quantifier patterns, not one constant for all derivatives.

The **Euler lifespan class is different**: velocity and a strong time-derivative witness have spatial L² jets of every order, continuous in time. Scalar pressure is spatially differentiable at interior times; the strong time law and equation are imposed only at interior times. See [EUL-001](04-euler.md#eul-001) and [EUL-010](04-euler.md#eul-010) for the nontrivial bridge to the global class. A total-function value at T_* is not a solution at T_*.

Exact endpoints: [NS submission](../../NavierStokes/ComparatorSolution.lean), [NS definitions](../../NavierStokes/ComparatorDefinitions.lean), [Euler submission](../../Euler/Solution.lean), [Euler definitions](../../Euler/SolutionDefinitions.lean). The [source map](SOURCE-MAP.md#delivered-statements) names their declarations and adapters.

**Not established by this companion:** unforced NS breakdown, a fixed-positive-viscosity Euler packet construction, equivalence to external Clay prose, prize eligibility, a fresh kernel check, or a fresh Comparator check. Smooth or infinitely flat forcing is not zero forcing; shutdown after the singular time does not give an unforced restart before it. An unresolved audit is not a demonstrated source flaw.

## Reading order

1. Read the [scope chapter](01-scope.md), summary above and evidence key below. The [interface sheet](INTERFACES.md) defines selected construction inputs and identifies the still-unexpanded mathematical interfaces.
2. [02 — NS construction](02-ns-construction.md): the coordinate and base, conditional correction-cycle bookkeeping, finite-band defects, coherent physical prefixes, one diagonal.
3. For the particular-wave step, detour to [05 — Native weighted control](05-native-weighted-control.md): one selected copy, geometry-produced energy, full-path source jets, exact joint-jet bound and pressure. This supplemental chapter uses baseline `26e896e…`; its [separate ledger](native-control-validation.md) records remaining higher-order input debt and does not extend the historical 30-ID coverage.
   For those primitive inputs, read [06 — Primitive derivative bounds](06-primitive-derivative-bounds.md): the same summed base, finite-order frame constants and numerical native pressure recurrence. Its [separate ledger](primitive-derivative-validation.md) retains the finite-profile and localization assumptions; chapter 05 and its historical ledger are unchanged.
4. [03 — NS analysis](03-ns-analysis.md): start from those very prefixes; follow tail estimates, residual flatness, localized force extension, comparison and nonextension. NSA-006 is an additional energy deduction, not an input to construction.
5. [04 — Euler](04-euler.md): an independent branch. Read the forward/joined distinction before the summability and H4-dependent stability arguments.
6. Use [SOURCE-MAP.md](SOURCE-MAP.md) to audit hypotheses and [VALIDATION.md](VALIDATION.md) to find open obligations and review assignments. [PLAN.md](PLAN.md) preserves the authoring contract and provenance; its initial directory-only restriction is superseded only by the user's explicit authorization for the minimal repository README discoverability link.

## Dependency diagram

Arrows mean mathematical inputs, **not completed review**. Bracketed obligations remain open.

```text
Statement classes (01-scope; external translation still open)
  |
  +-- NSC-001–003: profile, base, axis and anchored gauge [NSC-001–003]
  |     -> NSC-004–006: fixed ledger, native cycle, weighted finite band head [NSC-004]
  |     -> NSC-007–008: one physical run and fixed-loss estimates [NSC-005–006]
  |     -> NSC-009 / NSA-001–003: one schedule, prefix plateau, flat residual
  |     -> NSA-005 localization algebra + NSA-004 exterior models / force extension
  |          [NSA-001–003; same run and gauge throughout]
  |     -> NSA-005: compact activated candidate -> separated periodic lift
  |          + NSA-007: slab uniqueness [NSA-004 for whole-space pressure]
  |     -> NSA-008: nonextension -> NSA-009: arbitrary fixed ν>0
  |          [NSA-005: class bridge]     \-> NSA-010: restart only if NEW premise
  |     \-> NSA-006: energy deduction (not a required arrow into nonextension)
  |
  +-- EUL-002–004: fixed scales, forward then joined exact insertions [EUL-001–003]
        -> EUL-005: growing sampled gradients
        -> EUL-006: one compact initial-data limit [EUL-004]
        -> EUL-007: H3 comparison with H4 reference control [EUL-005]
        -> EUL-008: finite maximal lifespan
             -> EUL-009: energy, C1 limsup, BKM integral [EUL-005]
             -> EUL-010: compact-vorticity broad-class bridge [EUL-006]
        No arrow from this branch to positive-viscosity NS.
```

The cycle uses NSC-006's **abstract** finite-head calculation, not a conclusion of a completed cycle; this is not circular. Likewise NSA-005's localization algebra precedes NSA-004's application to the localized residual, while the final candidate assembly uses the extension afterwards.

## Notation across chapters

| Symbol | Convention / translation |
|---|---|
| u(t,x), p(t,x), f(t,x) | Velocity, scalar pressure, external force; comparator source usually writes `v x t`. Euler parent `force` means ∇p, not external force. |
| Δ, R_ν | Forward Laplacian Σ∂²; R_ν=∂ₜu+(u·∇)u−νΔu+∇p. NS equation R_ν=f; Euler R₀=0. |
| x=(x₀,x₁,z), s | z=x₂; s=(x₀²+x₁²)/2. NS axis vector e₂=(0,0,1). |
| q, X, η | NS positive terminal scale q−z²q^(2h)=1−t; X=s/q; η=z/q^(1/2−h). q is not pressure or distance. NSA-005 uses ρ for the spatial cutoff to avoid reusing η. |
| h, κ, J, j, n | NS fixed h>0 and κ=10⁻⁵; J completed cycles, j increment, n similarity band. σ_J=1/5+J/10; raw g_j=hj/10, post-cutoff γ_j=g_j/2. Never shrink h with J. |
| A_j, B_j, P_j | NS potential, direct angular velocity, pressure increments. Prefix includes j=0 through J. B_j is not the scalar source budget `B` (written B_bud when ambiguity matters). |
| b_k, a_j | NS slow-coefficient Borel schedule versus later physical diagonal schedule. All three physical component sums share a_j. |
| D^m, norms | NS physical estimates: full joint spacetime derivatives; NSC-002 profile jets use D_(X,η), blown jets use (r,X,η), and NSC-004 uses coefficient derivatives. Euler: spatial derivatives only. Operator tensor norms are equivalent to coordinate norms with order-dependent constants, not identical. |
| ∥u∥₂², E_kin | ∫|u|² versus physical kinetic energy ½∫|u|². Gradient energy in NSA-006 uses the Hilbert–Schmidt norm. |
| T_* | General terminal time; NS normalized to 1 until scaling, then 1/ν. Euler canonical lifespan; not asserted equal to the limit of packet activation times. |
| Euler-local indices/scales | J,D,X,n,a_n,k_n,ℓ_n,t_n,T_n restart their meaning in chapter 04. Its construction-order q is not NS q; its error budget η is not NS similarity η. |
| H_m, C₁, W | Euler H_m is the sum of spatial tensor L² norms through m; C₁ is the sum of speed and derivative **pointwise** spatial suprema; W is the curl supremum. The latter two may be +∞. |

## What “proved” means here

- **Expanded calculation / prose deduction:** a displayed argument from stated hypotheses; supplied agent reviews checked selected calculations, not every analytic dependency. Not automatically a packaged Lean theorem (notably NSA-006, the local strengthening in NSA-008, NSA-010 and EUL-011).
- **Source-established (author label):** an author inspected a named declaration and local interface/proof. This is not fresh elaboration, kernel validation, or a dependency-closure audit by the integrator.
- **Unexpanded input:** a substantive analytic producer supplied by source but not derived in the companion. Downstream human conclusions inherit its obligations; linking the producer does not close them.
- **New research:** a missing strengthening, such as terminal force removal or a viscous packet cascade; it must not be used as an existing theorem.

Run the read-only local checks with `python3 docs/proof-companion/validate.py` from the repository root (or use the script's absolute path from elsewhere). They check documentation paths, explicit anchors, coverage of the 30 authored NSC/NSA/EUL IDs and lexical source targets only. Scope has no stable SCOPE IDs; scope/interface assertions and every source hypothesis are not independently covered by that count. **They do not certify mathematics, namespaces, elaborated hypotheses, or Lean validity.** See the [validation ledger](VALIDATION.md) for current checks, supplied reviews and preserved historical evidence.
