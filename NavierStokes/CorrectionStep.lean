import NavierStokes.CorrectionStep.Fields
import NavierStokes.CorrectionStep.SignedStages
import NavierStokes.CorrectionStep.CycleConstruction
import NavierStokes.CorrectionStep.WaveGains
import NavierStokes.CorrectionStep.MeanComposition
import NavierStokes.CorrectionStep.CycleInvariants

/-!
# Exact field bookkeeping for one correction cycle

The residuals in this development are the differentiated nonlinear fields in
(32).  In particular, changing the wave covariance and changing a mean velocity
are not treated as independent black-box state transitions.  Every old/new
cross term is retained in the displayed residual differences.

This module is an aggregator: the development lives in
`NavierStokes/CorrectionStep/`, split along its original section boundaries
into six parts, each depending only on the ones before it.

* `Fields` — the shared vocabulary (`ScalarField`, `Tensor`, `TensorClass`, the
  covariance changes) and the full differential residual, both re-exported from
  `NavierStokes.SignedMeanGain` and `NavierStokes.HarmonicResidual.Actual`,
  together with the physical chart representation, the temporal construction and
  the gauge mean bookkeeping.
* `SignedStages` — the physical residual decomposition, the signed stage
  parameters and their linear coefficient bridge, the gauge rank mean, and the
  moving-support, periodized and particular constructions.
* `CycleConstruction` — the cycle parameters, the constructed temporal and rank
  stages, cycle mass preservation and mean completion, and the native equations.
* `WaveGains` — the linear wave theory of the constructed families, the
  supported wave gain, the cycle recurrence, the periodized curl identities and
  the uniform and constructed wave gains.
* `MeanComposition` — uniform periodized coefficients, the coherent reference
  particular family, the constructed mean stages, the uniform gains, and the
  moving covariance and Gaussian means.
* `CycleInvariants` — what one full cycle preserves: the cycle mean gain,
  regularity preservation, residual grouping, the real coefficient structure,
  the analytic invariant, and the wave cycle and derived request gains.

Importing this module gives exactly what importing the former single file gave.
-/
