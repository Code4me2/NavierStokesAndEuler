# Next target — reconstruct the finite drift-aware correction theorem

**Pin:** 5fdcfe346d399f68f19a820526b59b5326f28939. Proposal only; no source edits or formal executions authorized.

## One bounded target

Give a complete human derivation of `EulerDriftGlobalInviscidGevrey.exists_global_inviscid_gevrey_PDE` (`Euler/DriftGlobalInviscidGevrey.lean:21–67`) for the actual initialized input of `EulerAllOrderDriftCorrection.finite_exists` (`Euler/AllOrderDriftFinite.lean:19–47`). Keep all existing objects and quantifiers. Do not widen this into a full packet or ordinary-local-theory reconstruction.

**Exact missing exposition obligation:** from the literal finite SpatialBudget, separate drift bound and inverse MetricBudget at input order q+2, derive an inviscid path e∈C([0,T],H^(q+1)) with zero initial trace, divergence constraint, retained energy at every surviving cutoff, and the signed-pressure equation in H^q. Explain how regularized existence, uniform Gevrey bounds, convergence and nonlinear-source/pressure passage produce that *same* e. The current top body obtains the limit from `exists_gevrey_inviscid_energy_limit`, then uses `correction_limit_equation` and `correction_sobolev_hasDerivAt`; these are the next analytic interfaces, not a completed explanation.

This is **exposition debt**, not an absent formal theorem or demonstrated mathematical gap. The source theorem is present. A separate attribution/export gap concerns the selected GeometryJoinedChoice.Q's internal numerical-radius formula; this target neither needs nor claims to close that gap.

## Why this target

The map now explains where small drift comes from, which literal scalars serve every order, and how uniqueness assembles finite corrections. The remaining central analytic dependency is the finite solver itself. Re-explaining the Budget or the final lifespan contradiction would not advance that boundary.

## Testable acceptance contract

1. Fix L>0, T>0, q≥6, coherent A, inverse metric K and all scalar bounds **before** regularization/extraction. Instantiate input order q+2 and cutoff N=q−4; track retained q+1 and equation q. Identify each norm and every derivative loss.
2. State the actual regularized PDE, pressure operator and initial condition. Derive the energy inequality with full background in growth constants but actual drift in radius loss. Account for all metric time/space terms and pressure cancellations. No assumed solved-wave energy bound.
3. Show radius ≥ρ0/2 and E≤2R exp(3Ct)≤Δ/2 uniformly in the regularization parameter. The common scalar calculation in MAP.md B4 may be imported, but its analytic energy premise may not.
4. Specify compactness topology, spatial-tail control and time equicontinuity; show convergence strong enough for every nonlinear and pressure term in the H^q equation. Explain retained energy via the actual limit argument, not smoothness alone.
5. Track zero trace and solenoidality into the same limit, including interior versus endpoint time laws. Then explicitly match the solver output to `A.lower_twice` and the exact `finite_exists` conclusion.
6. Finish with a field-use matrix distinguishing the fields needed for existence/energy from the smaller base-order comparison interface already inspected. Any proposed interface simplification must preserve κ,direction, common metric, coefficients, approximation, residual and representative identity; no new solution choice or changed theorem route.
7. Every unresolved sublemma gets its exact input/output and retained body citation. Acceptance requires a continuous derivation rather than a chain of renamed bundles. If pressure/compactness cannot be reconstructed in this bound, report that failure without calling it a formal gap.

## Scope ceiling

Only the finite correction/energy/compactness/limit-equation dependency chain. Exclude forward/joined frame renewal, broad-class compact-curl recovery, NS and Research, selected-certificate strengthenings, and generic library consolidation. A read-only reconstruction can satisfy the contract; any future implementation or verification requires separate authorization.
