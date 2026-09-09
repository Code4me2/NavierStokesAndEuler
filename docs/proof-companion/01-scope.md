# 01 — Scope and class translation (partial)

**Status:** internal mathematical class translation, not external-prose equivalence or full proof certification. The four endpoint quantifiers are listed in the [scope summary](README.md#scope). This chapter separates admissibility of constructed data from inclusion of competitors. Source definitions inspected for this revision: [NS definitions](../../NavierStokes/ComparatorDefinitions.lean), `InitialVelocityConditionDecay`, `ForceConditionDecay`, `ForceConditionPeriodic`, and the three solution structures; [Euler definitions](../../Euler/SolutionDefinitions.lean), including both global and lifespan classes. Declaration comments about reference fidelity are not an independently executed Comparator test.

## Data and force

On R³, admissible data are smooth and divergence-free, and for every spatial tensor order m and real K there is C with
\[
 \|D_x^m u_{\rm init}(x)\|\le C(1+|x|)^{-K}.
\]
NS forcing is jointly smooth on the future half-space. Its order-m joint derivative **within that half-space** has bound C(1+|x|+t)^{-K}, for all x and t≥0, with C chosen separately for each m,K. Periodic data and force are unit-periodic in each spatial direction; force decay uses C(1+t)^{-K}, uniformly in x. At a smooth boundary extension, these within-derivatives agree with the restricted extension derivatives; this is not a demand for an equation at negative times.

Conditional on the construction chapters, NS chooses zero datum and a smooth force compact in space and future time. Bounded derivatives on that compact cylinder imply the stated weighted bounds. Separated periodization replaces compact spatial support by unit periodicity. Euler chooses a nonzero smooth compact datum; compactness likewise implies every decay bound. These observations establish admissibility **only after** the actual smoothness/support constructions are proved. They do not include competitors in an excluded class.

## Global competitors and restriction direction

A global competitor has scalar pressure p and velocity v jointly smooth on R³×[0,∞), the prescribed initial trace, divergence freedom and the PDE at every t≥0. The time derivative at zero is right-sided. In the whole-space class, v(t) is in L² for each t≥0 and there is one finite E such that ∫|v(t)|²<E for every future time. Energy here is twice the physical kinetic energy. No pressure decay, global derivative bounds or uniform all-order Sobolev norms are imposed.

For NS, restricting such a competitor to [0,T], T below the constructed singular time, gives the smooth slab, equal datum/residual and slab-uniform energy required by [NSA-007](03-ns-analysis.md#nsa-007). Inverse viscosity scaling in [NSA-009](03-ns-analysis.md#nsa-009) must be applied to that same competitor and force. The periodic route instead restricts both periodic velocity **and periodic scalar pressure**; it does not replace the latter by periodic pressure gradient. For example v=a(t)e₁ and p=−a′(t)x₁ have periodic velocity and pressure gradient, but are not competitors in this scalar-periodic class. This restriction direction is the one needed for exclusion.

## Euler lifespan competitors are a different class

For I=[0,T) or [0,T], the source lifespan class requires spatially smooth velocity with every spatial derivative tensor in L² continuously in time on I. There is a strong time-derivative witness w with the same all-order spatial L² continuity. At **interior times only**, the L² path derivative equals w and
\(w+(v\cdot\nabla)v=-\nabla p\); scalar p is spatially differentiable there. Divergence holds on I and the initial trace is prescribed. There is no endpoint time-law premise. The total-function value at an excluded endpoint has no solution meaning.

A jointly smooth global finite-energy competitor does **not** automatically satisfy this stronger lifespan contract. The required direction is: global competitor → local compact-vorticity persistence → all-order div–curl and time regularity → ordinary Sobolev evolution agreeing with the constructed one. Confinement then permits restart of the hypothetical competitor through the terminal time. [EUL-010](04-euler.md#eul-010) retains the analytic class bridge as OBL-EUL-006. Ordinary-class exclusion alone cannot replace it.

## External interpretation gate remains open

For any intended external competitor, one must still verify, from the actual external statement, joint boundary smoothness and derivative conventions, initial trace, scalar-pressure requirements, norm/energy quantifiers, and the exact forcing alternative, then map **every** such competitor into the excluded internal class. Constructed-data admissibility is a separate direction. No external manuscript or official prose was retrieved for this revision; no equivalence is claimed.

**Unexpanded scope obligation RI-06 / INT-001 / OBL-NSA-005:** complete and independently review that external translation and the source adapters, including tensor versus coordinate norms and boundary regularity. File delivery resolves the missing entry point, not this obligation. Source-copy agreement, Lean/kernel validity, Comparator validation, external-prose equivalence and human mathematical completeness remain separate verdicts. No unforced NS conclusion follows from smooth or flat forcing; the restart in NSA-010 additionally requires 0≤t₀<1 and the stated shifted-data and admissible-pressure conditions.
