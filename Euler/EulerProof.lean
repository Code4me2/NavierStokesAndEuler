import Euler.EulerProof.Foundations
import Euler.EulerProof.LiftedTransport
import Euler.EulerProof.CylinderSobolev
import Euler.EulerProof.Mollification
import Euler.EulerProof.CutoffsAndEnergy
import Euler.EulerProof.PacketGrowth
import Euler.EulerProof.PacketFrames
import Euler.EulerProof.PacketScales

/-!
# The Euler construction (aggregator)

`Euler.EulerProof` used to be a single 16k-line file.  Its contents are now
split, along the top-level namespace blocks it already had, into the parts
imported above; this module only re-exports them, so `import Euler.EulerProof`
still brings the whole development into scope.

The parts are strictly sequential -- each one imports its predecessor and may
`open` namespaces introduced earlier.  Only part 1 lists the Mathlib imports of
the original file; parts 2-8 inherit them through that chain, so a new Mathlib
dependency needed anywhere in the development belongs in
`Euler.EulerProof.Foundations`.  The parts are, in order:

1. `Euler.EulerProof.Foundations` -- Gevrey factorial estimates, smooth uniform
   limits, packet weights, and the coercive projection and its inverse.
2. `Euler.EulerProof.LiftedTransport` -- the lifted `L^2` and gradient space,
   the pressure solve on it, metric transport, spatial regularity and jets, and
   the metric energy evolution.
3. `Euler.EulerProof.CylinderSobolev` -- Fourier-based Sobolev norms on
   `Domain d`, the cylinder chart, and the Sobolev algebra on the cylinder.
4. `Euler.EulerProof.Mollification` -- mollifiers on the cylinder and the smooth
   representatives, tensors and pressures they produce.
5. `Euler.EulerProof.CutoffsAndEnergy` -- terminal energy and traces, vector
   calculus, the Gevrey cutoff family, and the weighted energy and pressure
   bounds.
6. `Euler.EulerProof.PacketGrowth` -- the Riccati comparison, its perturbation
   theory, and the ray system.
7. `Euler.EulerProof.PacketFrames` -- the moving frame, global Picard-Lindelof
   existence, and the bookkeeping for a single stage.
8. `Euler.EulerProof.PacketScales` -- the scale sequences chaining the stages
   into the cascade.
-/
