# Additive validation repair

No historical file is edited. `audit.py` replaces the *future validation workflow*,
not the frozen SelectedBridge/check.py or validate.py. Default verification is
read-only (stdout only); receipt generation requires `--replay` and uses mkdtemp.
`aggregate.py --run` likewise creates a unique directory; `--verify` is read-only.
Do not rerun the historical receipt writers.

## Commands actually run (cwd = repository root)

```sh
python3 Research/UnforcedRestart/Round3/ValidationRepair/audit.py --replay
python3 Research/UnforcedRestart/Round3/ValidationRepair/aggregate.py --run Research/UnforcedRestart/Round3/ValidationRepair/replay-1oafv980/receipt.json
python3 Research/UnforcedRestart/Round3/ValidationRepair/test_audit.py
python3 Research/UnforcedRestart/Round3/ValidationRepair/aggregate.py --verify Research/UnforcedRestart/Round3/ValidationRepair/aggregate-btau1ozq/receipt.json
python3 Research/UnforcedRestart/Round3/Integration/verify.py
```

Stdout/stderr are in `launch.log`, `aggregate-launch.log`, `tests.log`,
`verification.log`, `prior-preservation.log`, respectively. All compiler commands,
resource limits, cwd/environment, source/compiler/log/output SHA256s are recorded
in the unique directories. Tests: four passing fail-closed parser regressions.

## Scope and results

* `replay-1oafv980/receipt.json`: all six distinct accepted Round3 source files,
  strict exit 0, 41 exact printed export closures. Historical log lists are
  reparsed and equated with recorded lists (not merely checked against a whitelist).
* `aggregate-btau1ozq/receipt.json`: 11,105 imported modules, 42,928 imported
  project constants including generated helpers. Unsafe project constants and
  axioms outside propext/Classical.choice/Quot.sound are rejected.
* Preflight compares 13,618 historical object/artifact hashes (the olean inventory
  plus inherited research outputs), rather than merely recording current hashes.
  Accepted manifest/resolver/compiler pins and the external evidence manifest are
  checked. Direct imports use Lean --deps; the aggregate environment module list
  is resolved with first-prefix-root semantics and matched to source/object hashes.
* The aggregate receipt explicitly records additions absent from the earlier
  research dependency union: NavierStokes.R3.ProblemStatement, CompactEnergy,
  CompactTimeIntegral. Each is linked to the initial source inventory, matching
  historical object hash and historical source-build log lines/commands.
* `baseline.json`: 3,157 preexisting non-.git/non-.lake files; hashes unchanged,
  HEAD/refs/index unchanged, tracked/index diffs empty. Historical snapshot and
  external-evidence verifier also passed. Dependency roots are read-only;
  no dependency rebuild, Lake/cache download, commit, push or merge was performed.

This completes the stated project/helper axiom and module-provenance audit, not
an independent kernel validation of every library/core declaration. Source-built
libraries and pinned installed Lean/core/runtime retain their established trust
scope. **Comparator/Nanoda was not run.** None of these tools adds a mathematical
result or supplies an actual curl/force-mean decision producer.
