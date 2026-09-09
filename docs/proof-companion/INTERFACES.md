# Mathematical interface sheet — partial, not a replacement for the analytic inputs

This sheet responds to the first independent agent reviews. Definitions below were checked in source; remaining undefined construction operators are explicit obligations, not arbitrary objects one may choose to satisfy the estimates. Read with [NSC-002](02-ns-construction.md#nsc-002), [NSC-005](02-ns-construction.md#nsc-005), and [EUL-004](04-euler.md#eul-004).

## NS profile and cone

Profile coordinates are `(X,η)`, with `X>0`; the active estimates use `X_L<X<X_R`, `−1≤η≤1`. Logarithmic radius is `y=log X`. The outgoing construction supplies scalar profiles E and U on this radial domain; the reconstruction uses their aligned slow coefficients, not arbitrary stress data. “Outgoing” and “clean cone” name an intermediate prepared matching construction, not radiation conditions for physical NS.

The actual true-cone test on four real inputs `(p₁,p₂,A,C)` is
\[
 A>0,\quad 2<A(1+(C/A)^2),\quad 2<p_1+p_2C/A,
\quad A(1+(C/A)^2)<B(p_1+p_2C/A,p_2-p_1C/A),
\]
where
\[
 B(P,J)=P+J^2/4-|J|\sqrt{(P-2)/2+J^2/16}.
\]
It is imposed at every point of the active strip on the two profile stocks and the angular and signed axial shears. Source definitions: [TrueConeLoop](../../NavierStokes/TrueConeLoop.lean), `InTrueCone`; [ConeAlgebra](../../NavierStokes/ConeAlgebra.lean), `coneBound`; [LeadingStressWeights](../../NavierStokes/LeadingStressWeights.lean), `FullTrueCone`. It supplies leading stress geometry, not uniform nonvanishing of a Borel-corrected stress.

**Unexpanded interface obligation RI-04a (OBL-NSC-001):** the governing prepared-profile equations, stock/shear formulas, boundary/matching conditions, finite modulation constraints and the normalization C_* still need a continuous mathematical specification and derivation. The inequality above defines the cone test but does not yet define its actual profile inputs. Source leads remain [OutgoingProfile](../../NavierStokes/OutgoingProfile.lean) and [PreparedOutgoing](../../NavierStokes/PreparedOutgoing.lean). The graduate-reader goal is not closed by this sheet.

## NS mean compatibility and native waves

At each band and frozen slow variable, let M_k(f) be the radial integral of r^k times the full auxiliary-torus average of f. The source's three-component rank debt is
\[
 (P,J_\theta,J_z)=
 (M_0(g_r),\ M_2(Q_{z\theta}),\ M_1(Q_{zz})-\tfrac12M_2(g_r)).
\]
Here g_r is the state's radial pressure source; Q is the corresponding base/mean interaction tensor plus the stored oscillatory covariance. These are the **post-temporal state's** quantities. This is the explicit compatibility functional, not the pointwise residual and not the temporal zero mean. Source: [CorrectionState](../../NavierStokes/CorrectionState.lean), `radialMoment`, `pressureDefect`, `thetaDefect`, `axialDefect`, `debt`.

The rank inverse uses three debt rows together with two moment-preservation constraints. It constructs supported angular and desired axial increments in a reserved radial patch; the latter is realized by a divergence-free stream. For physical length ℓ and velocity scale V, debt normalization divides its three entries respectively by V², ℓ³V² and ℓ²V². See [MeanRankUpdate](../../NavierStokes/MeanRankUpdate.lean), `normalizeDebt`, and [FiveRowRank](../../NavierStokes/FiveRowRank.lean). This explains why the periodic temporal inverse alone cannot complete the repair.

**Unexpanded interface obligation RI-04b (OBL-NSC-004):** expand g_r and Q in the chart variables, all five inverse rows and their cancellation signs, the retained linear-good differential operator and every omitted Gaussian/alias term, and the actual carrier cells, phases and support intersections. The debt formula identifies what is measured; it does not prove its repair or native estimates. In particular equation (12) cannot yet be used as a self-contained differential-operator theorem.

## Euler's actual finite metric energy

The lifted cylinder is \(\mathbb R^3\times(\mathbb R/L\mathbb Z)\), L>0. Lifted fields are vector-valued functions of four spatial variables, with the product measure used in [LiftedTransport](../../Euler/EulerProof/LiftedTransport.lean), `LiftDomain`, `liftMeasure`, `LiftL2`. Derivative words below range over its four coordinate directions. For external words I of length at most P and base words a of length at most six, write e_{I,a}=D^{aI}e for the actual strong L² derivatives (the source fixes the concatenation order). Then the norm used in EUL-004 is
\[
 \mathcal E_{P,\rho,K}(e)=
 \sum_{|I|\le P}\frac{\rho^{|I|}}{(|I|!)^2}
 \left(\sum_{|a|\le6}\langle K e_{I,a},e_{I,a}\rangle_{L^2}\right)^{1/2}.
\]
Each sum includes **all ordered words**, including the empty word. K is the common inverse-metric operator on lifted L², with positivity/coercivity supplied by the metric budget; this is a sum of metric roots, not the square root of one Gevrey square sum. It requires derivatives through P+6. The radius is positive. Sources: [GevreyMetricEstimate](../../Euler/GevreyMetricEstimate.lean), `energyNorm`; [WeightedCylinderEnergy](../../Euler/WeightedCylinderEnergy.lean), `weightedMetricSum`; [BaseWordMetric](../../Euler/BaseWordMetric.lean); [EnergyWordCoordinates](../../Euler/EnergyWordCoordinates.lean); [Foundations](../../Euler/EulerProof/Foundations.lean), `EulerPacketWeights.weight`.

Under \(\langle Kv,v\rangle\ge c^2\|v\|_2^2\), c>0, the source's retained weighted Sobolev sum is at most \((1+\sqrt{5461}/c)\mathcal E\); `weightedNorm_le_energy` proves this fixed-cutoff-independent conversion. This is a **cylinder norm conversion**, not a physical gradient estimate.

**Unexpanded interface obligation RI-05 (OBL-EUL-002–003):** specify the actual oscillatory/mean packet, phase graph and physical evaluation map, lifted divergence/projected pressure operators, residual, and the quantitative graph-to-physical gradient bound with its scale factors. An L² bound on the cylinder alone does not control restriction to a graph. Neither the displayed norm nor its budget proves that the same exact corrected child retains amplification. The finite-order solver, all-order coherence and renewed packet geometry remain analytic blockers.
