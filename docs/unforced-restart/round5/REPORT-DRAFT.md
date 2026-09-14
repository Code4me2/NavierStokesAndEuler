# Round5 report draft — checked radial inputs, discriminator unresolved

## Result

**No selected-force nonzero-curl theorem was completed. Neither N, W nor Z is claimed.** The strongest proposed route remains the source-specific radial cutoff ODE contradiction. This bounded implementation checked its actual normalization/primitive positivity and the selected sums' exterior reduction. It did not complete the Cartesian residual-curl, terminal-limit or ODE uniqueness composition. These partial facts are not a replacement success criterion.

The literal record is `UnforcedRestart.Round3.WitnessFeasibility.selected`; the force is that record's `forcing`. The sums use its `schedule`, with no second witness, numerical schedule or effective profile substituted. No new hypothesis assumes cancellation, nonzero curl, or growth preservation.

## Checked new mathematical content

* `Research/UnforcedRestart/Round5/RadialPrimitive.lean`: actual nominal normalization positive; actual extended terminal heat coefficient positive; actual anchored heat primitive strictly decreasing on positive radii and positive for 0<s<1, including every s∈[1/64,1/32]. This is an input from the selected candidate's construction, not yet an identity with selected force jets.
* `Research/UnforcedRestart/Round5/SelectedExterior.lean`: actual selected potential and pressure sums reduce on the precise exterior domain to their actual base fields multiplied by the **retained stage-zero diagonal cutoff**. The actual direct sum is zero there. The identities hold as ambient germs at interior exterior points. No all-region or terminal-slab claim is made.
* `Research/UnforcedRestart/Round5/Acceptance.lean`: explicit **partial acceptance**, checking the literal selected-force curl continuity, exact closed transition positivity and selected direct-sum exterior zero. The continuity fact is inherited. This file deliberately does not pretend to check the requested existential curl target.

Readable derivation and exact proof boundary: [CALCULATION.md](CALCULATION.md). Pre-implementation decision: [DECISION.md](DECISION.md).

## Precise blocker

The checked positive scalar k is the heat model primitive, not a selected terminal force component. To derive nonzero selected curl one must still prove:

1. a simultaneous incoming selected-sum germ with stage zero identically on its plateau, the full anchor segment in the heat exterior, and the single-copy/late-activation identifications;
2. the Cartesian scalar residual-curl calculation (including the nonlinear axial cancellation and full pressure cancellation);
3. its passage to the actual smooth selected force at t=1;
4. the regular homogeneous second-order cutoff ODE contradiction, including endpoint jets and uniqueness on [1/64,1/32].

The selected exterior identities implemented here remove one raw-stage/tsum obstacle but not these compositions. No existing unequal-entry implication provides the missing inequality. This is a formal implementation blocker, not a counterexample to the analytic proposal or an assertion that N is impossible. The attempt stops at this boundary; it did not launch a second open-ended stability, Hodge or analytic-smoothing implementation. W's proposed potential-reconstruction/periodic-uniqueness proof also remains unformalized here.

## Exact quantifiers and pressure implications

Write C(t,x)=`SpatialCurl.spatialCurl selected.forcing (t,x)`.

* N would say: ∀t₀<1, ∃t, max(0,t₀)<t<1 and ∃x, C(t,x)≠0.
* W would say: ∃t, 0<t<1 and ∃x, C(t,x)≠0.
* Z would say: ∃τ, 0≤τ<1 and ∀t, τ<t<1 → ∀x, C(t,x)=0.

A proved nonzero terminal component at one fixed x plus continuity would give nonzero C(t,x) for **every** sufficiently late t<1, hence N and therefore W. The implementation has no such terminal witness. W alone would obstruct gradient absorption on intervals containing its witness time, not exclude later terminal slabs. A terminal-slab energy bound from nonzero data does not force zero velocity.

N would exclude a C² spatial pressure potential with f=∇φ on any terminal slab. Z plus the checked Round4 mean zero would remove the curl and constant-mode obstructions, but a smooth periodic, jointly time-regular potential must still be constructed to absorb f using pressure p−φ. The new partial results establish neither such a potential nor its impossibility. No restart, terminal pressure absorption, A/B, comparator lifespan or growth-transfer result follows.

## Validation and preservation

New validator: `Research/UnforcedRestart/Round5/validate.py`. Unique external outputs:

`/home/velvet/research-builds/unforced-round5-3kfmgeg8/`

Initial audit receipt:

`/home/velvet/research-builds/unforced-round5-3kfmgeg8/audit-lxs4s_b1/receipt.json`

Four modules passed strict source compilation with pinned Lean, `-j1 -DautoImplicit=false -DwarningAsError=true`, one thread, CPU quota 100%, 6 GiB, no swap, TasksMax=32 and 600-second timeout per compiler invocation. The imported original source-built dependencies were reused read-only; no dependency build/cache download or blanket build ran. Each compiler attempt has separate source bytes, command, direct-import provenance, log and receipt. Successful final exports use only propext, Classical.choice and Quot.sound.

`Round5/Audit.lean` reuses the Round4 aggregate project/helper audit body unchanged after the import line. Its final environment audit covered 11,101 modules and 42,895 project constants, rejected unsafe project declarations and forbidden/challenge imports, and checked axiom closure. Every imported module was resolved with first-prefix-root semantics and matched against the frozen Round3 source/object correspondence or a fresh strict Round5 receipt. The established export and aggregate parsers were reused without alteration; all four existing fail-closed parser regression tests passed. These numbers describe coverage, not mathematical success.

Preservation checks compare all preexisting baseline files, HEAD, current refs, index and tracked/index diffs, plus every entry in the supervisor's research manifest (hashes for files, exact symlink targets). The manifest itself is pinned. The only editable preexisting baseline entry is this new Round5 validator itself; its final hash is recorded in audit receipts. The snapshot sources, Round1–4 sources/manifests/receipts, original Lean/configuration and dependency bytes were not modified. New repository files are confined to the authorized Round5 trees. No Git writes or historical receipt writers ran.

Diagnostic history is not hidden: the first validator preflight treated an archived directory symlink as a regular file and failed before compilation; this was repaired to check its exact symlink target. The first SelectedExterior compilation failed on the nonexistent identifier `tsum_eq_zero`, producing an error-recovery `sorryAx` in its **rejected diagnostic log**, not in any accepted source/object. That attempt remains `attempt-atqqp3pm` with nonzero exit. Replacing it by a pointwise zero tsum simplification passed in `attempt-f4sti582`. There were five compiler attempts, four successful; no explicit sorry/admit/new axiom/unsafe shortcut was added.

Trust scope remains the pinned Lean compiler/core/runtime/host and historically source-built library objects. This is not independent kernel rechecking of every library declaration; Comparator/Nanoda was not run. The old validators' historical preservation policies were not altered or falsely reported as passing: the additive Round5 baseline preserves the current refs including the documented concurrent ref.

Repeat audit (reads preserved inputs; writes only a fresh unique external receipt):

```sh
python3 -B Research/UnforcedRestart/Round5/validate.py audit
```

**Bottom line:** genuine selected-construction inputs were checked, but the requested selected-force discriminator remains unresolved. Partial Acceptance is explicitly not target acceptance.
