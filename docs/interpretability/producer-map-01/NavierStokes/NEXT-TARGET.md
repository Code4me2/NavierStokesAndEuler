# One bounded next target: reconstruct Euler's weighted physical error transfer

**Proposal only; research remains paused.** Baseline `5fdcfe346d399f68f19a820526b59b5326f28939`. No implementation, build or validation campaign is proposed here.

## Exact target

Reconstruct the single estimate consumed in `Euler/PacketInitializedUniformFlow.lean`, `initialized_uniform_flow_and_shear`: its call to `Q.physical_gradient_hessian_of_weighted` (`Euler/PacketWeightedPhysicalErrors.lean:47–121`), followed by the two approximate-packet error bounds and `physical_error_le_inverse_quarter`.

Starting with **one specified** initialized correction budget Q, the actual parent map X and continuous inverse Y, derive the physical velocity-gradient and pressure-Hessian error bounds for that same correction. Explain every graph restriction, inverse-map derivative, Piola/metric coefficient and frequency factor. Finish at the retained `SourceErrors` fields of `GeometryJoinedChoice`, not at an unrelated exact solution or a newly selected budget.

This is the highest-value next human reconstruction because the current map exposes its precise cost `C/k + E k Δ`, but has not fully derived E from the weighted cylinder estimates. The top transfer body was inspected: E is `((1+9CF)*physicalFixedCost(D,R,CF,ρ⁻¹,1))*(sobolevEmbeddingConstant(period,3)*Cw)`. The next obligations are `pointField_wordSum_gevrey`, `physicalReconstruction_power_bound`, and `physicalPressureForce_power_bound`, not another repetition of the top bundle. Cylinder L² smallness alone does not control graph restriction. The outer stability contradiction is already explained and is not the target.

## Missing obligation and classification

- **Exposition gap, with source producer:** derive the weighted graph-to-physical derivative/pressure estimate and the approximate packet remainder bounds used by the cited body. Their Lean suppliers exist; this map has not exposed their full analytic proof.
- **Not an identified mathematical gap:** no source theorem failure is established by leaving this derivation unexpanded.
- **Potential export issue, not prerequisite:** a classically selected GeometryJoinedChoice does not retain all explicit canonical-Q radius/target identities from the existence exhibit. Work first with the explicitly defined Q in UniformFlow; conclude only fields actually retained by GeometryJoinedChoice. Do not assert equality of selected Q with the exhibit.
- **Not new research:** no viscous Euler adaptation, new lifespan bound, force deletion or unforced NS result is sought.

## Testable acceptance contract

1. Give explicit formulas for physical correction velocity and pressure, including evaluation at Y(t,x), oscillatory graph, physical x/ell scaling, and all determinant/inverse assumptions. Explain why gradient and Hessian estimates concern the same Q.
2. Expand every consumed weighted estimate: derivative cutoff, six base cylinder derivatives, radius ρ0/4, coefficient/frame constants, and the pressure/time towers. State fixed-before/existence-after quantifiers. No uniformity in parent or order beyond the actual contract.
3. Derive the graph restriction estimate with its frequency loss. Show why the correction term is bounded by `E k Δ`, and why the approximation term is `C/k`; a citation to another bundle is insufficient.
4. Reproduce both inequalities for all t in the closed parent horizon and all physical x. Keep the genuine scalar-pressure Hessian distinct from the lifted signed pressure field and Euler's `force=∇p` convention.
5. Recover `C/k+E k Δ≤k^-1/4` under the literal universal frequency guards, then follow those two estimates through `ParentUniformJoinedChild` to `GeometryJoinedChoice.errors`, and into both physical_bounds and lowBounds. Do not replace the sharper one-sided curvature budget by the absolute Hessian bound.
6. Supply a finite producer/consumer table with pinned body citations, recording every remaining analytic input. Success means a continuous mathematical derivation of this boundary, not a count of referenced files or another proof-validation run.

## Stop boundary

Do not reconstruct the full packet recursion, scale-existence proof, finite inviscid PDE solver, initial-data series or broad-class bridge in this target. Keep their exact inputs visible. If graph transfer needs an unavailable stronger statement, report its precise quantifiers and distinguish an export/exposition gap from a genuinely new theorem.

The NS map's next analytic boundary—native extraction plus closure/polar pullback with fixed loss—is recorded but is **not a second parallel campaign**. No production interface simplification should be implemented until the relevant mathematical identity and domain contract are reconstructed.
