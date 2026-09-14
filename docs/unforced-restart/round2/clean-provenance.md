# Clean provenance — integration update; historical worker report below

**Current integration verdict: clean acceptance BLOCKED at the zero-trace preflight, not at snapshot authorization.** PLAN's supervisor clarification accepted the read-only, tamper-evident seal and transferred the settled campaign to the integrator. The snapshot was reverified without modifying it.

The integrator created `/home/velvet/research-builds/unforced-round2-clean-20260909T221339Z/` using `git clone --no-local --no-hardlinks`, detached the exact baseline, and acquired all eleven pinned git dependencies with hooks disabled and a private HOME. Actual enforced clean cgroup limits were 2 CPUs, 16 GiB, no swap, 128 tasks. No object alternates or old dependency-object copies were used.

The mandatory prebuild scan rejected two **upstream tracked** ProofWidgets files: `widget/package-lock.json.trace` and `widget/js/lake.trace`. This is a genuine PLAN zero-preexisting-trace failure. No trace exemption/deletion, retry, Lake configuration elaboration, cache fetch, or dependency compilation followed. Source acquisition succeeded; a usable source-built environment does not exist. The configured `Common NavierStokes Euler` build was not launched. This is not a compiler proof failure or clean acceptance.

External evidence: `/home/velvet/research-builds/unforced-round2-clean-20260909T221339Z-evidence/`, especially `acquisition.log`, `initial-inventory.json`, `build-driver.log` (exit 1), and `CLEAN-VERDICT.json`. Exact trace hashes/content and tracked status are recorded. See [REPORT.md](REPORT.md) for the independent cached-only final validation, installed toolchain trust root, preservation evidence and reviewer questions. Final Round2 acceptance is two new sources/eight exports, 16 strict source/audit recompilations, standard axioms only; it must not be called a clean dependency check.

---

# Historical worker report — blocked before acquisition

## Verdict

**NOT RUN; snapshot gate unresolved.** PLAN and the initialization REPORT explicitly require an authorized immutable-store deposit or explicit user acceptance of the weaker seal before the fresh campaign. The supplied handoff still labels immutability blocked and builds pending the gate. The role assignment is not treated as a silent waiver of that explicit prerequisite. No privilege escalation or `chattr` retry was attempted.

Snapshot: `/home/velvet/research-snapshots/unforced-round1-20260909T221339Z`.
Reserved external clone: `/home/velvet/research-builds/unforced-round2-clean-20260909T221339Z/` (**not created; absence checked**). No reusable source-built dependency setup exists from this pass.

## Checks actually executed

From the snapshot directory:

```sh
sha256sum SHA256SUMS
sha256sum -c SHA256SUMS
```

Combined shell command exited 0. Digest matched the externally recorded value:
`192e15dc0ff1cb79cae02a19941e0f816dc194e91123c205153ccf808322a488`.
All eight listed entries returned OK: HEAD.txt, README.txt, inventory.json, source-docs.tar.gz, staged.diff, status.txt, tracked-files.txt, tracked.diff. This verifies the archive/inventory seal, not filesystem immutability or correspondence of existing dependency binaries to source.

From the authorized worktree, the exact command was:

```sh
git rev-parse HEAD && git diff --exit-code 597692fa5d55e07d810b2d96ead1a67972585425 -- && git diff --cached --exit-code && test ! -e /home/velvet/research-builds/unforced-round2-clean-20260909T221339Z; printf 'combined_exit=%s\n' "$?"
```

Output: baseline `597692fa5d55e07d810b2d96ead1a67972585425`, `combined_exit=0`; both diffs silent. This checks tracked preservation, not filesystem immutability or a fresh all-file inventory. Tool transcripts retain these command outputs; no build log or compiler exit exists because no build was launched.

Read PLAN, initialization REPORT, snapshot README, round-one FINAL-REPORT, OBLIGATIONS, complete accepted JSON manifest and complete frozen validator. The validator is path-bound and overwrites historical validation outputs; it was neither executed nor modified.

## Acceptance accounting

- No clone, dependency acquisition, Lake invocation, compilation, cache fetch, or resource-control launch.
- No accepted new declarations, exports, axioms, or mathematical progress claimed by this provenance role.
- Historical manifest lists 12 accepted research sources and aggregate audit, with 88 named exports. Their historical success is **cached elaboration**, not a clean-build result from this pass.
- No rebuilt hashes, new semantic enumeration, resolver audit, or clean closure coverage exists yet. No empty audit is a PASS.
- No compilation failure/root error exists to diagnose; the blocker is the prerequisite gate, not a proof error.
- No independent Comparator/Nanoda run, A/B claim, or clean-success marker.
- Only this owned new report was written. Original checkout, baseline configuration, round-one sources, frozen validator and old artifacts were not written; no commits/pushes/global changes.

## Handoff after gate clearance

The sole authorized campaign remains unspent. First verify cgroup controls and disk, then source-only clone with `--no-local --no-hardlinks`, detach at the full baseline, acquire all eleven exact manifest revisions without hooks, inspect package settings and inventory zero non-core artifacts/escaping links before any Lake elaboration. Use private HOME/cache and sanitized resolver variables; inspect supported Lake scheduler/cache controls rather than guessing flags. Trust only the installed pinned official Lean/core/Lake and recorded host toolchain, not existing project/dependency objects.

Build explicit `Common NavierStokes Euler` and required dependency closure (not the default challenge target), under 2 CPUs/16 GiB/no swap, 8-hour wall budget, stopping below 80 GiB free disk. Retain exact commands, resource evidence, logs and statuses. Copy frozen source-only research from the verified archive; retain historical hashes and independently record rebuilt hashes. Strictly compile all twelve sources plus audit; coordinate any frozen Round2 additions with integrator and perform separate complete coverage/axiom/provenance validation. A partial build cannot satisfy acceptance. Do not patch the old validator or replace any failed rebuilt object with cache.
