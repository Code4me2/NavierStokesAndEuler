# Local commit of completed research, rounds 1–5

The user authorized committing the completed research and reviewed companion documentation. They remain on separate local branches; this is not authorization to merge into or push remote main. The original Lean proof and configuration are unchanged.

## Mathematical status

- Rounds 1–2: restart admissibility, conditional comparison, and finite-slab energy estimates; no strong-norm growth-transfer theorem or unforced breakdown result.
- Rounds 3–4: the literal selected periodic forcing has zero component cell mean for every time in `[0,1]`, including endpoints by force continuity. See round4/FINAL-REPORT.md for the exact statement and replay evidence.
- Round5: checked actual radial-primitive positivity and selected exterior identities, but no selected-force nonzero-curl certificate, terminal-slab curl identity, or pressure-absorption conclusion. See round5/FINAL-REPORT.md. Partial acceptance is not acceptance of the curl target.

## Source commits versus machine-local evidence

The source commit includes research Lean files, validation scripts, reports, stable manifests and small metadata. Generated compiler objects, diagnostic source copies, logs, large imported-object inventories, and large machine-local receipts remain untouched locally and are excluded by the new scoped Research/UnforcedRestart/.gitignore. They are not source dependencies of the original proof.

Before staging, the supervisor archived every file/symlink in Research/UnforcedRestart and docs/unforced-restart, and the entire reviewed proof companion, then verified each archive member against a SHA-256 file manifest and rechecked the live files. These archives include generated and rejected-attempt evidence, not only accepted outputs:

```
/home/velvet/research-snapshots/precommit-all-work-20260912T202410Z/
  research.tar
  research-manifest.json
  companion.tar
  companion-manifest.json
```

Archive SHA-256:

- research.tar: `525cb8fcc7936d5d034af6e7370edec1733e7ca62b5ccc18852ab8314e901aac` (2,986 entries).
- companion.tar: `27f9eacbac2b17bda268e8bb970d5d5d1a4b1519886a8cbc95b852692a2258f3` (16 entries).

The archives precede this new note and ignore file. External clean-build and independent-review receipts remain at their original paths recorded in each final report; no claim is made that those external directories are embedded in this source commit. Archive files/manifests are read-only by permissions, not immutable storage.

Historical validators deliberately pin old HEAD/index/ref inventories and absolute evidence paths. Committing changes Git metadata under this explicit authorization: a subsequent historical exact-state failure does not mean the accepted mathematics changed. Do not rewrite historical manifests or weaken those validators to hide the transition. New validation should distinguish preserved source hashes from authorized commit metadata and report its own baseline. A fresh clone of the source commit does not by itself contain the full machine-local replay environment; restoring/provisioning its evidence and verified dependencies is a separate operation.

No new kernel build or mathematical validation is claimed by packaging these files. Prior accepted compilation/axiom results retain their stated trust scope. Nothing has been published by this commit.
