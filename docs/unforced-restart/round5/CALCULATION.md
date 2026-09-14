# Radial calculation — proof boundary

## Binding and checked input

Throughout d is exactly `UnforcedRestart.Round3.WitnessFeasibility.selected`, f=d.forcing and a=d.schedule. A, v, p are `WitnessFeasibility.potentialSum a`, `directSum a`, `pressureSum a`. We do not choose another record or replace any schedule. The actual primary profile supplies

E = `BaseExterior.nominalHeatNormalization ActualPrimary.nominal`, h = `ActualPrimary.h`.

`Round5/RadialPrimitive.lean` checks E>0 directly from the source normalization: outgoing amplitude times a positive switch radius to a real power. For s>0 the extended terminal coefficient is

    F(1,s) = E * s^(RadialHeatProfile.spatialExponent (1+h)) / sqrt(2*s) > 0.

The source's `heatPrimitive_hasDerivAt` gives k'(s)=-F(1,s) for k(s)=heatPrimitive(E,h)(1,(s,0)). Thus k is strictly decreasing on (0,∞). Its source anchor value k(1)=0 implies k(s)>0 for 0<s<1, in particular for every s in the closed interval [1/64,1/32]. The new proof uses derivatives and strict monotonicity, not an unproved assertion about positivity of a totalized integral. No new Lean integral expression or interchange occurs.

`Round5/SelectedExterior.lean` checks, on the *precise* `ActualExteriorPrefix.exteriorDomain (residualBand budget threshold)`,

    A(w) = cutoff(a₀*q(w)) • finalPotential(w),
    v(w) = 0,
    p(w) = cutoff(a₀*q(w)) • FinalSlowBase.pressure(w).

The identities reduce the actual tsum using actual raw-stage exterior equalities. They retain stage zero's diagonal cutoff. Openness gives ambient germs at each point of this interior exterior domain. These are not yet terminal incoming germs; in particular they do not assert a₀q<1/2. The pressure identity is retained rather than replacing the selected pressure extension.

## Proposed continuation — NOT Lean-checked here

Let s=(x₀²+x₁²)/2, ℓ=1/64, b=1/32 and η(s)=cutoff(32s). To use the checked input for f requires a single incoming neighborhood of each (1,x), x₂=0, s>0, on which all of the following hold simultaneously:

* the exterior-domain time, scale and non-active conditions;
* |a₀q|<1/2 as an open condition;
* the entire anchor-to-radius segment is in the actual heat exterior;
* a single periodic copy agrees as a germ and the time switch is one.

The source supplies ingredients, including `exists_terminal_segment_neighborhood`, but this selected-sum composition has not been implemented. Positivity of the model k alone does not identify any jet of f.

After that composition the proposed local velocity is U=curl(H e₂), H(t,s)=η(s)K(t,s). At the central plane, with axial cutoff identically one nearby, the Cartesian convention would give

    U = (x₁ H_s, -x₀ H_s, 0),
    (U·∇)U = -H_s² (x₀,x₁,0).

The latter field's axial curl is zero, accounting for the full nonlinear contribution to this component. With G=H_t-2(sH_s)_s, the proposed axial residual-curl formula is

    C₂(1,x) = -2(sG_s(1,s))_s.

This is a proposed terminal *force* identity, not an evaluation of a singular terminal velocity and not a theorem in the new files. It needs the interior identity followed by the incoming limit using selected curl continuity.

For the general activated field ρU the total curl retains

    ρ' curl U + ρ(∂t curl U - Δ curl U)
      + ρ²((U·∇)curl U - (curl U·∇)U).

The stretching term has the minus sign. Pressure contributes zero only as the full curl of grad(χp); splitting gives ∇χ×∇p and ∇p×∇χ, which cancel. No independent pressure sign survives. Radial, axial, mixed and diagonal cutoff derivatives cannot be omitted before a germ removes them.

If the proposed C₂ expression vanished for every ℓ<s<b, endpoint flatness at b would force G=0 there. At time one this becomes

    2s k η'' + (2k+4s k')η' + (2k'+2s k''-j)η = 0,
    j(s)=K_t(1,s),  η(b)=η'(b)=0.

The checked k>0 would ensure a regular leading coefficient on [ℓ,b]. Linear ODE uniqueness would imply η=0, contradicting η(ℓ)=1. This requires a further formal uniqueness/endpoint argument, not an assumed nonzero-curl premise. It retains j: no heat-PDE identity or sign of K_t is assumed.

The missing calculation, limit and ODE composition are substantive. The new files do not imply that the displayed C₂ is unequal to zero anywhere. Caps need not vanish for an existential radial witness, but the actual pointwise single-copy identity must first be proved. Neither terminal flatness at the origin nor mean zero supplies this identity.
