# Notes from removed heartbeat-investigation modules

These thirteen modules were near-verbatim clones of live modules, created while investigating elaboration resource limits (`maxHeartbeats`) and whether the proofs go through without option overrides. They were unreachable from every theorem root, compiled only because the lakefile globs matched their names, and were removed in the simplification pass. Their module docstrings are preserved here for provenance.

## `NavierStokes/CorrectionInitializationNoOptions.lean`

# Construction of the initial correction fields

The operations in this file use the actual shifted pressure primitive, torus
inverse, stream potential, and five-row inverse.  The covariance identity is
also differentiated as an identity of functions, retaining all derivatives of
the squared partition.  Quantitative initialization is assembled below from
the estimates on these same operations.

## Removing the local heartbeat override

This independent copy uses a separate namespace. `AssembledPrimary.covariance_bounds`
is split into three private lemmas: uniform block bounds, supports and sum identities,
and transfer of the generic covariance estimates. The final theorem assembles these
lemmas. Its assumptions and conclusion are unchanged, and no resource-limit override
is used in this file.

Check with:
`lake env lean -DautoImplicit=false -DwarningAsError=true NavierStokes/CorrectionInitializationNoOptions.lean`

## `NavierStokes/DiagonalJetBoundsNoOptions.lean`

# Quantitative jets of the actual diagonal sum

Local finiteness identifies derivatives of the actual `tsum` with finite sums
of actual `iteratedFDeriv`s. Pointwise stage estimates then give quantitative
tail estimates. The stage estimates themselves are explicit hypotheses, not
conclusions of the numerical cutoff selection. The prefix must depend on the
requested derivative order and decay power; no fixed tail is declared flat.

## Removing the heartbeat override

This independent copy of `NavierStokes.DiagonalJetBounds` uses a separate namespace
and retains all definitions and theorem statements. Removing the local heartbeat
override alone makes `tsum_sub_prefix_jet` exceed the default limit of 200000.

The expensive step is elaborating `summable_nat_add_iff` with an implicit `f`.
Supplying the jet sequence explicitly reduces the measured theorem cost from about
216000 to 2700 heartbeats in the current environment. This is the only proof change;
the entire file passes with default resource limits.

Check with:
`lake env lean -DautoImplicit=false -DwarningAsError=true NavierStokes/DiagonalJetBoundsNoOptions.lean`

## `NavierStokes/ActualParticularDynamicsNoOptions.lean`

# Actual particular dynamics with default heartbeat limits

Replacement proofs for the two declarations in `ActualParticularDynamics` that
use `maxHeartbeats 1000000`. The imported module supplies the definitions and
supporting lemmas; the proofs below do not invoke either original target theorem.
The theorem statements are unchanged. This investigation edits only this file.

* `native_fast`: restrict `slotDirection_transport` to the left-hand side with
  `conv_lhs => erw [...]`, then use ordinary `rw` for the remaining rewrites.
  The original unrestricted `erw` also tries to match the transport expression
  against the right-hand side, causing expensive definitional unfolding.
* `selected_principal`: prove the equality between the selected normal and the
  original normal once (`hnormal`, by `rfl`), then rewrite with it in `hN` and
  `hδ`. This avoids rediscovering that equality underneath the squared norm by
  unfolding the Euclidean norm and the reindexed data.

Separate `#count_heartbeats in` measurements without profiler tracing, on the
repository's Lean 4.34.0-rc2 toolchain:

| Declaration | Original | Replacement |
| --- | ---: | ---: |
| `native_fast` | 247571 | 24054 |
| `selected_principal` | 367429 | 125519 |

Both replacement proofs pass with the default 200000-heartbeat limit and use
only the standard axioms `propext`, `Classical.choice`, and `Quot.sound`.
A temporary copy of the complete original module also passes with these proofs
substituted and both heartbeat overrides removed.

Check with:
`lake env lean -DautoImplicit=false -DwarningAsError=true NavierStokes/ActualParticularDynamicsNoOptions.lean`

## `Euler/ParentGeometryForwardChoiceNoOptions.lean`

# Geometry forward choice with default heartbeat limits

This is an independent copy of `Euler.ParentGeometryForwardChoice` in a separate
namespace. Its definitions, structure fields, and downstream proofs are unchanged.
The investigation's edits are confined to this file.

Removing the original `maxHeartbeats 3200000` override alone exceeds the default
200000 heartbeats while Lean generates `GeometryForwardChoice.mk.inj`. The costly
step compares `LabelData (I.parent.child flow ... )` for two distinct flow variables.
Definitional equality unfolds `Parent.child` and its large displacement, velocity,
and acceleration constructions before recognizing that the types differ.

The section around `GeometryForwardChoice` makes `Parent.child` locally
irreducible. The failed comparison then stops immediately, and Lean generates
the heterogeneous equality for the dependent labels as usual. Constructor
injectivity generation stays enabled. Ending the section restores the ordinary
transparency of `Parent.child`, so subsequent proofs need no changes.

Separate `#count_heartbeats in` measurements without profiler tracing, on the
repository's Lean 4.34.0-rc2 toolchain, give 353857 heartbeats for the original
structure declaration and 3224 for this version (about 110 times fewer).
Both generated injectivity theorems are present and use only the standard axioms.

Check the complete file with the Euler library's strict compiler options:
`lake env lean -DautoImplicit=false -DwarningAsError=true Euler/ParentGeometryForwardChoiceNoOptions.lean`

## `Euler/BaseFirstPacketEvolutionNoOptions.lean`

# First-packet evolution estimates without heartbeat overrides

Independent proofs of the two estimates in `BaseFirstPacketEvolution`.
The statements and imports are unchanged. The verified changes have also
been applied to `BaseFirstPacketEvolution.lean`.

The working changes are:
* Keep `initialParent` locally irreducible while elaborating the concrete
  estimates, so unification does not expand the underlying initial flow.
* For `physical_bounds`, unfold the small state/data wrappers explicitly
  before matching the estimates, and transport the force norm using the
  pressure-Hessian equality with `congrArg`.
* For `center_error`, prove the transfer through `forwardChild` for an
  abstract parent first, using `packetChild_center_error`, then specialize
  it to the first packet. This avoids constructing and rewriting the full
  concrete `packetChild_increment_fderiv` identity.

Observed heartbeat counts with Lean 4.34.0-rc2:

| Declaration | Original | This version |
| --- | ---: | ---: |
| `physical_bounds` | 329888 | 75407 |
| `center_error` | 613092 | 143997 |
| Generic center-error helper | — | 2881 |

Counts were measured with `#count_heartbeats in` in temporary copies.
This uninstrumented file passes at the default 200000-heartbeat limit:

```
lake env lean -DautoImplicit=false -DwarningAsError=true Euler/BaseFirstPacketEvolutionNoOptions.lean
```

Both estimates depend only on `propext`, `Classical.choice`, and `Quot.sound`.

## `Euler/GevreyGeneratingDerivativesNoOptions.lean`

# Generating derivatives with default resource limits

This is an independent copy of `Euler.GevreyGeneratingDerivatives`, in a separate
namespace so both modules can be imported together. The definitions and theorem
statements are unchanged. This investigation's edits are confined to this file.

Simply removing the original `maxHeartbeats 1800000` override makes
`derivativeSum_comp_id_add_le` exceed the default 200000 heartbeats. Profiling
locates the expensive conversion at the `hgj` argument of `derivativeSum_comp_le`:
its expected type uses `((id + f) x)`, whereas the hypothesis uses `x + f x`.
Automatic definitional equality unfolds `iteratedFDeriv` and operator norms
repeatedly while comparing these types.

The only proof change below is to normalize that argument with
`simpa only [Pi.add_apply, id_eq] using hgj`. All declarations then compile with
default resource limits; no helper lemma or additional import is needed.

Separate `#count_heartbeats in` measurements, without profiler tracing, report
608336 heartbeats for the original theorem and 2864 for the modified theorem
on the repository's Lean 4.34.0-rc2 toolchain (about 212 times fewer).

Check with the Euler library's strict compiler options:
`lake env lean -DautoImplicit=false -DwarningAsError=true Euler/GevreyGeneratingDerivativesNoOptions.lean`

## `Euler/LpCylinderCoefficientTimeInvestigation.lean`

# Removing the coefficient product rule's heartbeat override

This standalone copy of `LpCylinderCoefficientTime.lean` uses a separate namespace
and the original imports, so it checks the replacement without importing the
original theorem or modifying the original file. No heartbeat override is needed.

## Recommended change

In `supportedProduct_hasDerivWithinAt`, retain the construction of `hd` using
`clm_apply`, then replace both `change` steps and the final `rwa` with:

```
  dsimp only [extendPath] at hd
  simp only [projIcc_of_mem hT t.property] at hd
  exact hd
```

`dsimp` exposes the clamped time argument, `simp only` removes the clamp at `t`,
and `exact` checks the remaining definitional equalities of the multiplier maps.
The statement, hypotheses, and endpoint behavior are unchanged.

## Measurements

With the repository's Lean v4.34.0-rc2 and current dependencies, command-level
`#count_heartbeats in` measured approximately:

* Original proof: 223,000 heartbeats; removing its override alone times out at
  the default limit of 200,000.
* Replacing only the final `rwa` with
  `simpa only [projIcc_of_mem hT t.property] using hd`: 190,000 heartbeats.
* The replacement below: 120,500 heartbeats.

Tactic profiling attributes about 35,100 and 34,700 heartbeats to the original
two `change` steps and 33,300 to the final `rwa`. The one-line `simpa only`
alternative costs about 413. Splitting `rwa` into its components shows that
the rewrite itself accounts for almost all of its cost.

To reproduce counts, temporarily import `Mathlib.Util.CountHeartbeats` and put
`#count_heartbeats in` between `include hA in` and the product theorem's docstring.
That profiling command disables the limit while counting; the actual acceptance
check below uses the normal default limit, with no profiling wrapper:

```
lake env lean -DautoImplicit=false -DwarningAsError=true -DElab.async=false \
  Euler/LpCylinderCoefficientTimeInvestigation.lean
```

## `Euler/BaseFirstPacketChoiceNoOptions.lean`

# First packet choice with default heartbeat limits

This independent copy of `Euler.BaseFirstPacketChoice` uses a separate namespace.
All definitions, structure fields, and theorem statements are unchanged. The
investigation's edits are confined to this file.

The original file has two `maxHeartbeats 3200000` overrides:

* `FirstPacketChoice`: generation of `noConfusion` compares label types belonging
  to different computed parents and unfolds the entire base flow construction.
  Making `Parent.child` and `initialParent` locally irreducible just around the
  structure avoids that work. Using `initialParent`, rather than
  `packetBaseParent`, still lets Lean compute the time horizon of the restricted
  parent. The section restores ordinary transparency before the following proofs.
* `exists_firstPacketChoice`: implicit conversion between normalized and
  initialized fields is expensive underneath derivatives and norms. Rewrite with
  the existing `normalizedPacketVelocity_forwardInitialized` and
  `normalizedPacketPressure_forwardInitialized` lemmas first. Restrict the
  pressure-term rewrite to the subtracted term and specify its packet data.
  These field-identification lemmas require `Euler.ParentForwardInitialSupport`.

Separate `#count_heartbeats in` measurements without profiler tracing, on the
repository's Lean 4.34.0-rc2 toolchain:

| Declaration | Original | Replacement |
| --- | ---: | ---: |
| `FirstPacketChoice` | 1973969 | 6342 |
| `exists_firstPacketChoice` | 313840 | 181075 |

Both fit the default 200000-heartbeat limit. A complete copy using the original
namespace also passes, and both local transparency annotations are restored.
The generated `noConfusion`, `mk.inj`, and `mk.injEq` declarations remain present;
the checked declarations use only `propext`, `Classical.choice`, and `Quot.sound`.

Check the complete file with the Euler library's strict compiler options:
`lake env lean -DautoImplicit=false -DwarningAsError=true Euler/BaseFirstPacketChoiceNoOptions.lean`

## `Euler/BaseInductionStageNoOptions.lean`

The first stage of the actual induction is constructed from the
literal compact base solution and the first same-Q packet choice.

## `Euler/ParentGeometryJoinedChoiceInvestigation.lean`

# Joined geometry choice with the default heartbeat limit

This standalone copy of `ParentGeometryJoinedChoice.lean` uses the original
imports and a separate namespace. It does not import or modify the original
declaration. All structure fields, theorem statements, and downstream proofs
are preserved, including the local transparency setting for `Parent.child`
during constructor injectivity generation.

## Fix

Remove the `maxHeartbeats 3200000` override on `exists_geometryJoinedChoice`
and replace both `rw [← hterminal]` calls with `simp only [← hterminal]`.
Keep the intervening `erw [pressureTerm_eq_coefficient]` unchanged.
The restricted simplifier rewrites the same terminal equality in the large
source-error propositions more cheaply.

## Measurements

On the repository's Lean v4.34.0-rc2 toolchain and current dependencies:

* Removing the override alone times out at `isDefEq` in the final
  `exact (herror t x).2`, at the default 200000-heartbeat limit.
* Command-level profiling of the original theorem uses approximately 212260
  heartbeats; the version below uses approximately 154673 (27% fewer).
* The velocity-error branch drops from approximately 87794 to 59281 heartbeats;
  the pressure-error branch drops from approximately 117007 to 87910.

To reproduce the measurements, temporarily import `Mathlib.Util.CountHeartbeats`
and put `#count_heartbeats in` before `exists_geometryJoinedChoice`.
The profiling wrapper disables the limit while counting. This file contains
no such wrapper or heartbeat override; check it with the normal default limit:

```
lake env lean -DautoImplicit=false -DwarningAsError=true -DElab.async=false \
  Euler/ParentGeometryJoinedChoiceInvestigation.lean
```

## `Euler/MeanPacketEnvelopeBoundsNoOptions.lean`

# Removing the heartbeat override from the mean packet envelope estimate

This is an independent copy of `SobolevData.envelope_bounds` from
`Euler/MeanPacketEnvelopeBounds.lean`, with the same statement and imports.
The original file is left unchanged.

Simply deleting the heartbeat override times out at the `obtain` applied to
`E.normalized_bounds` (200000 heartbeats). The two conjunction eliminations
using `obtain` are expensive: retain their results with `have` and use
`.1`, `.2.1`, and `.2.2` instead. No helper theorems or option overrides are
needed; the mathematical proof is otherwise unchanged.

With Lean 4.34.0-rc2, `#count_heartbeats in` in temporary copies importing
`Mathlib.Util.CountHeartbeats` measured 262131 heartbeats for the original
proof and 98578 for this version. The uninstrumented file also passes with
the default 200000 limit and the Euler library's strict options:

```
lake env lean -DautoImplicit=false -DwarningAsError=true Euler/MeanPacketEnvelopeBoundsNoOptions.lean
```

The scalar amplitude is normalized before the actual solve and restored by
proved homogeneity. Every radius condition depends only on the fixed source
data and the fixed normalized forcing scale, never on the recursive grade
or its forcing envelope. Zero envelope is treated by actual zero forcing.

## `Euler/PacketShiftArithmeticNoOptions.lean`

# Packet shift arithmetic with default resource limits

This is an independent copy of `Euler.PacketShiftArithmetic`, in a separate namespace
so both modules can be imported together. The definitions and theorem statements are
unchanged.

Removing the original recursion-depth override makes all nine `simp only` calls fail
before reaching `omega`. Replacing them with `dsimp only` suffices: only definitional
unfolding is needed, and all the original `omega` steps then succeed with Lean's default
recursion-depth and heartbeat limits. No resource-limit override is needed in this file.

Check with the Euler library's strict compiler options:
`lake env lean -DautoImplicit=false -DwarningAsError=true Euler/PacketShiftArithmeticNoOptions.lean`

## `Euler/TransversePacketCorrectorNoOptions.lean`

# `Data.potentialCoefficientPath_time` at default recursion depth

This separate namespace reuses the original definitions and proves the same statement
from `Data.potential_hasDerivWithinAt`. It changes only the derivative value using
`HasDerivWithinAt.congr_deriv` and the interval projection identity.

The original `simpa only` proof exceeds the default recursion depth in an isolated
reproduction. The proof below passes with default resource limits and the Euler
library's strict compiler options:
`lake env lean -DautoImplicit=false -DwarningAsError=true Euler/TransversePacketCorrectorNoOptions.lean`
