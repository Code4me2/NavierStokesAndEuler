# Round3 initial investigation — precisely unresolved annular curl

## Decision

**Precisely unresolved obstruction**, not exact removal and not a controlled perturbative route. We can name one coherent actual selected force and its full terminal tensors symbolically. We cannot yet evaluate/certify its annular terminal curl or prove a whole-interval periodic gradient identity. Existential choices are not numerical input data. This is not a proof that removal is impossible, nor any A/B conclusion.

The ordinary-analysis mean argument cancels the actual selected force's cell mean on 0<t<1 and then at t=1 by force continuity. It includes the entire localization region via compact divergence/residual integration; it needs Lean adapters and is not added to the formal acceptance set. Even a checked zero mean would leave all nonconstant solenoidal modes. See [MeanTopology](MeanTopology.md).

## Durable preservation

Local source snapshot: **`e970490cf8f0cfb41fca101c62702fab7347c17c`**.

Ref: `refs/heads/research/unforced-validated-snapshot-20260912T175850171580Z`.

Created with alternate GIT_INDEX_FILE, read-tree HEAD, 64 explicit accepted-source/docs/manifest/tool/provenance paths, write-tree/commit-tree and create-only update-ref. HEAD remains `597692fa5d55e07d810b2d96ead1a67972585425`; active index bytes and all prior refs are unchanged. No original-checkout access, remote contact, push or merge. The preserved local fork/main ref is still 26e896e; actual remote state was not queried.

`round3/snapshot/` contains the receipt, exact source hashes, excluded path/hash inventories, documentation link audit and concise anchored clean-replay evidence. All **2,878** preexisting baseline/research/docs files verified unchanged. All **16** frozen accepted-source/audit hashes match the completed clean replay. Every entry of its external evidence hash manifest was rechecked. Frozen validators/manifests and historical failed/blocked reports were not rewritten or rerun.

Excluded from the source snapshot: generated objects/native outputs, logs and giant enumerations, caches, task out/, integration runs/evidence, build symlinks, unaccepted DRAFT.md and unrelated untracked files. They were not deleted. Historical dangling/external documentation references are itemized rather than silently repaired. Clean evidence remains at `/home/velvet/research-builds/unforced-round2-clean-20260909T221339Z-evidence-attempt2/`; verified source-built dependency checkout is reused read-only. The installed Lean/core/compiler/runtime and host are the trust root. No WORM/sudo or duplicate build.

Round3 additions after this snapshot are **not in that preservation commit**, and are not claimed to have been historically clean-replayed. They remain isolated sources/docs, with the following focused evidence.

## Ownership and actual source handoff

[PLAN](PLAN.md) assigns exclusive `Research/UnforcedRestart/Round3/<Role>/` and matching reports to WitnessFeasibility, CurlGeometry, MeanTopology and LocalizedForce. These roles were performed sequentially in this pass, not by independent concurrent reviewers. Coordinator owns Integration and planning/preservation/final reports. No cross-role source edits.

* [WitnessFeasibility](WitnessFeasibility.md): new `Main.lean` fixes a complete `selected : Data` once from `ActualCandidateAssembly.selected_witness`. It retains actual schedule, sums' away extensions, periodic force, candidate/smoothness and full terminal jets. Checked `terminal_origin_jets` specializes existing origin flatness to that selected record; it does not imply annular flatness.
* [CurlGeometry](CurlGeometry.md): spatial antisymmetric part of order-one terminal tensor is the precise target; cell seams/annulus and temporal scope distinguished. No certified sign or global vanishing identity obtained.
* [MeanTopology](MeanTopology.md): ordinary compact moment-divergence, residual integration, periodization and terminal-continuity argument; formal composition outstanding.
* [LocalizedForce](LocalizedForce.md): explicit full cutoff and activation residual expansion; derivative and effective representation gaps identified. No base-only numerical surrogate.

Fixed B=0; N0=ActualCarrierGeometry.startingThreshold 0; h=FinalSlowBase.actualProfile.outgoing.data.h; same selected schedule/ASum/BSum/PSum/ea/eb/ep/forcing. ν=1, T=1, unit periods, t0=1/2, H=1/2. Spatial χ is cutoff(16r²)cutoff(4x₂); annulus includes radial transitions, axial caps and support boundary. Activation is identically one only after 3/4, so a full restart argument from 1/2 must retain activation terms. Full declaration/path map is in PLAN.

Freeze for downstream read-only use of the new wrapper:

`Research/UnforcedRestart/Round3/WitnessFeasibility/Main.lean`

SHA-256: `7d77092a3da73faedebac0a052c6fd2ce6fc46d340f48f796dd5e45f926be8da`.

## Validation commands and scope

From the authorized worktree:

```sh
python3 Research/UnforcedRestart/Round3/Integration/verify.py
python3 Research/UnforcedRestart/Round3/Integration/focused.py WitnessFeasibility
git diff --exit-code
git diff --cached --exit-code
```

Preservation verifier: **PASS**. Focused Lean: **exit 0**, first attempt, direct pinned compiler with `-j1 -DautoImplicit=false -DwarningAsError=true`, unique role output and read-only source-built resolver, 1 CPU/6 GiB/zero swap/32 tasks/600s bounds. Evidence: `WitnessFeasibility/out/strict-14ku121j/command.json`, `result.json`, `compile.log`; result includes exact source/compiler/output hashes. Each rerun creates a new output directory.

Eight substantive named exports print only propext/Classical.choice/Quot.sound. This is **focused export checking**, not aggregate Round3 semantic/generated-helper/imported-module acceptance. Round1/2's full clean-replay audit remains frozen and valid in its documented trust scope. No new Lean files were created for the other roles; their reports are source analysis/ordinary mathematics only. No rejected Lean attempts, fresh source build or dependency operations occurred.

## Next exact obligation

Derive the selected cut-residual **first spatial jet** on a nonzero representative in the localization annulus with all cutoff/direct-field terms, using actual germs/one-sided extensions. Either certify a nonzero curl component (plus continuity to exclude arbitrarily late absorption), or prove whole-cell curl zero and then separately prove a periodic gradient identity on an entire fixed terminal slab. Nonzero only at a preterminal time excludes slabs containing that time; terminal zero alone proves neither slab identity nor perturbative control. Literal f=0 and nonzero absorbable ∇φ are different routes; the latter corrects pressure to p−φ.
