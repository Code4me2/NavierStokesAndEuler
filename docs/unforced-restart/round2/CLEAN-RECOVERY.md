# Source-built clean recovery — accepted research replay

## Verdict

**`SOURCE_BUILT_RESEARCH_CHECKS_PASS`** for both round one and Round2.
All **14 frozen accepted mathematical files and both frozen audit modules (16/16 targets)** compiled successfully with `-DautoImplicit=false -DwarningAsError=true`. All compiler exits, replay driver exit, and replay service exit were **0**. No accepted statements, manifests, validators, historical failures, or library settings were changed. No merge, commit, or push.

This is a new external recovery validation, not a rerun or modification of the old validators. Historical `clean blocked`/cached statuses in the frozen manifests remain historical facts. The library-only handoff verdict remains unchanged; this report adds the research acceptance audit it explicitly lacked.

## Locations and commands

- Read-only original: `/home/velvet/worktrees/unforced-restart-20260909T202951Z`
- External checkout: `/home/velvet/research-builds/unforced-round2-clean-20260909T221339Z`
- Attempt-two evidence: `/home/velvet/research-builds/unforced-round2-clean-20260909T221339Z-evidence-attempt2`
- New replay script: `research-replay.py` in that evidence directory.
- New replay records: `research-replay/` in that evidence directory.
- Fresh compiled research outputs: `research-replay-attempt2/lib/` in the external checkout.

The completed library command was `lake --no-cache --verbose build Common NavierStokes Euler`: **11,084 jobs, 15,312.203 seconds (4h 15m 12s)**; Lake/driver/service exits 0. The replay did not rebuild the libraries or fetch caches.

Every target used the installed pinned compiler directly, from the external checkout:

```text
/home/velvet/.elan/toolchains/leanprover--lean4---v4.34.0-rc2/bin/lean
  -j1 -DautoImplicit=false -DwarningAsError=true
  -o <fresh-target>.olean -i <fresh-target>.ilean <frozen-source>.lean
```

`research-launch.txt` records the full systemd launch. `research-replay/01.command.json` through `16.command.json`, corresponding `.result.json`, `.exit`, and `.log` files record exact commands, working directory, timing, source hashes, exits, and logs. `resolver.json` records the complete explicit environment and ordered paths: fresh research output, external root library output, external source-built package outputs, plus installed trusted core. No original checkout or historical research object directory is on the resolver. `LEAN_SRC_PATH` is unset; no Lake environment/config elaboration was used during replay.

## Coverage

| Audit | Named exports | Research constants including helpers | All project/research constants | Imported modules |
| --- | ---: | ---: | ---: | ---: |
| Frozen round-one audit | 88 | 103 | 42,929 | 11,108 |
| Frozen combined Round2 audit | 96 | 113 | 42,939 | 11,110 |

The accepted set is the 12 round-one files in frozen manifest order, then `Round2/PeriodicSlab/Main.lean` and `Round2/ActualForce/Main.lean`, followed by `integration/Audit.lean` and `Round2/Integration/Audit.lean`. The sole excluded Lean source remains the frozen setup import probe. No accepted mathematical file was omitted.

Both audits enumerate all imported project/research constants, including generated helpers, reject unsafe project constants, enumerate imported modules, reject challenge imports, and traverse each constant's axiom closure. Every named export also passed its inline axiom check. The only allowed axioms are **`propext`, `Classical.choice`, `Quot.sound`**. No sorry/custom axiom, unsafe project constant, or challenge dependency was found. Source triage also rejected `sorry`, `admit`, `axiom`, `unsafe`, `native_decide`, and `implemented_by` in accepted/project dependency sources; accepted files could not override options.

Complete enumerations: `15-declarations.tsv`, `16-declarations.tsv`, both `*-modules.json`, and both `*-research-exports-helpers.json` under `research-replay/`. `dependencies.json` covers the full 11,110-module union: **9,261 source-built non-core library modules, 14 fresh research modules, and 1,835 trusted installed core modules**.

## Source/artifact provenance and preservation

The reviewed library initial inventory had **zero non-core compilation artifacts**. All **12,363 pinned inventoried sources** matched before and after the library build and again before and after research replay. The only two library replay log entries were the authorized ProofWidgets JavaScript metadata targets, not Lean objects. Package revisions and clean root/package diffs were checked. Installed official Lean/core was trusted, not rebuilt.

For every resolved non-core library module, `dependencies.json` links the exact source hash and resolved object path to its actual source compilation command's line in the successful `build.log`; `library-command-map.json` preserves those commands. This establishes correspondence from the clean initial inventory, pinned sources, exclusive resolver, and successful source build—not equality to historical cached object hashes. Research sources and both audits were copied **byte-for-byte**, with original/destination hashes in `source-copies.json`; no oleans, ileans, native outputs, or other compilation artifacts were copied from the original.

The fresh output inventory was empty. Full compiler-input inventories (including split Lean objects/IR and installed core) were equal before/after replay. Fresh research artifacts and toolchain executable hashes were rechecked. These hashes establish within-run stability only; they are not an independent compiler authentication or a historical cached-object correspondence claim.

`original-before.json` and `original-after.json` match across **2,877 original baseline/research/documentation files**, including historical outputs. Baseline bytes were additionally checked against `git archive`; the sealed 114-file round-one snapshot and frozen tool hashes passed. This report is the sole subsequently added original-worktree document; `final-preservation.json` in attempt-two evidence records that exception and the final original hash check. All old validators, manifests, failures, and first-attempt evidence are preserved.

## Resources and limits

Both campaigns retained **2 CPUs / 16 GiB / no swap / 128 tasks / 8-hour wall cap**. Library peak memory was 16 GiB with no OOM kills. Research replay peak was **1,731,158,016 bytes**, with no memory-limit or OOM events. Final replay service status and resource records are retained externally.

This accepts the frozen research against genuinely source-built non-core dependencies within the documented trusted Lean/core/compiler/runtime and host OS/hardware boundary. It is **not** independent kernel/Comparator certification, an authenticated/bootstrap rebuild of Lean/core, an audit of every unused external metaprogramming constant, or a mathematical A/B upgrade. Local existence, restart lifespan, strong-norm transfer, and previously recorded unproved obligations remain unproved. No accepted statement was strengthened or repaired to obtain this result.
