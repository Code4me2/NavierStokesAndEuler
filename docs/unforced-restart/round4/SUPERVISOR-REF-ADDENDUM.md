# Supervisor provenance clarification: authorized concurrent documentation ref

The supervisor independently checked the shared Git ref discrepancy reported by the Round4 reviewers.

The single added branch `refs/heads/docs/native-weighted-control-20260912T185404Z` points to `26e896edbdbe1215c0d50ddba24b2b6453646f5f`. It was created by the supervisor's explicit `git worktree add -b` command for the user's separately authorized native-weighted-control companion workflow. Its worktree is `/home/velvet/worktrees/proof-native-control-20260912T185404Z`. Git worktrees share repository refs; this is not an unexpected modification by the mean-zero research agents.

The original proof worktree is at 26e896e; the mean-zero research worktree HEAD remains 597692fa5d55e07d810b2d96ead1a67972585425. This observation does not waive any source, index, old-ref, theorem, artifact or axiom check.

For final preservation acceptance, record the exact authorized additive ref above and require: every previously inventoried ref unchanged, no deleted refs, and the ONLY newly added ref exactly this name/value. Do not reset/delete the documentation branch, move its worktree, or rewrite historical snapshots/receipts to conceal the discrepancy. Preserve the earlier exact-ref-equality failure as historical evidence and add a new explicit concurrent-ref-aware preservation result. Any other unexpected ref delta must still fail.

This is a reviewed accounting clarification of an already authorized action, not permission for arbitrary ref changes. No extra approval gate is necessary.
