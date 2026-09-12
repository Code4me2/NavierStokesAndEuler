# Decision — bounded radial producer attempt

The strongest candidate-specific analytic proposal is the radial cutoff ODE obstruction (N), not the active-stage sampling argument. The source primitive is anchored at s=1 and its terminal coefficient is positive. W has an independent analytic energy proof, but its curl-free primitive reconstruction and periodic uniqueness adapters are also new proofs; this attempt will not switch into an open-ended second implementation.

Binding: d = UnforcedRestart.Round3.WitnessFeasibility.selected, f = d.forcing, a = d.schedule; A, v, p are WitnessFeasibility's sums for this a. No new witness or schedule is chosen.

Intended target: for every t0 < 1 there is max(0,t0) < t < 1 and x with SpatialCurl.spatialCurl f (t,x) ≠ 0. The proposed producer first needs a nonzero terminal axial component at s in (1/64,1/32).

Substantive missing composition: a joint incoming germ for the *selected diagonal sums*, eliminating all positive stages and putting stage zero on its plateau, and identifying the entire anchor segment with the heat exterior; full Cartesian differentiation of curl(cutoff*K*e₂); nonlinear and pressure cancellation; passage to the selected force's terminal curl; and second-order ODE uniqueness with endpoint jets. None is supplied by the existing conditional unequal-entry lemma.

Bounded implementation starts with the actual nominal terminal coefficient and anchored primitive positivity, with no assumed nonzero input. These are candidate-construction facts, not a selected-force curl theorem. If the full composition is infeasible, Acceptance.lean will explicitly check only retained partial statements, never disguise a conditional curl assertion as N or W. The report must then say that neither target was checked. No integrals will be manipulated without integrability proofs; positivity can instead follow from the existing derivative theorem and strict monotonicity.
