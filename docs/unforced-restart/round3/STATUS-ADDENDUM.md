# Append-only status addendum

This new file updates the current reading of the frozen [DECISION.md](DECISION.md)
(§§2, 4, 8) and [ACCEPTED-SOURCE-MAP.md](ACCEPTED-SOURCE-MAP.md) (§§C–D).
Those historical documents and all accepted evidence remain byte-for-byte unchanged.

**Time differentiation is now checked, but force-mean cancellation is not.**
[SelectedBridge/Main.lean](../../../Research/UnforcedRestart/Round3/SelectedBridge/Main.lean)
proves `selected_compact_temporal_integral_zero`: for the frozen selected
`MeanTopology.compactVelocity`, each component of its temporal derivative has zero
whole-space integral for every `0 < t < 1`. Joint smoothness includes the support
boundary, and one fixed compact cylinder supports dominated differentiation.
(The repository-relative source path is
`Research/UnforcedRestart/Round3/SelectedBridge/Main.lean`.)

Still missing: compact pressure-gradient/Laplacian cancellation, residual-splitting
integrability, separated periodization and coordinate-measure transport, then
composition with force-mean continuity at both endpoints. No force-mean theorem
on `[0,1]` has been accepted.

No actual unequal total terminal entries or whole-slab curl cancellation has been
produced. Decision **(3)** remains unchanged. Transfer estimates and comparator
lifespan remain separate obligations for the same restart datum at `1/2`.

See [FINAL-REPORT.md](FINAL-REPORT.md) for the fresh six-module replay, aggregate
project/helper audit, bounded trust scope, and numerical no-go verdict. New
read-only verifiers supersede use of the historical receipt writers; they do not
modify those writers or their receipts.
