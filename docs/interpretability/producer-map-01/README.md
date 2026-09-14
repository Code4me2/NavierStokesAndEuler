# Technical interpretability: producer map 01

Pinned proof source: `5fdcfe346d399f68f19a820526b59b5326f28939`.

## Authoritative reading order

1. [Final overview](FINAL-OVERVIEW.md) and [final mechanism atlas](FINAL-MECHANISM-ATLAS.md).
2. [Final reconstruction corrections](FINAL-RECONSTRUCTION.md), read **together with** the [detailed reconstruction](RECONSTRUCTION.md). The final file is an addendum, not a standalone full derivation.
3. [Review dispositions](REVIEW-DISPOSITIONS.md), [mathematical review](REVIEW-mathematical-and-quantifier-audit.md), and [source/interpretability review](REVIEW-source-lineage-and-explanatory-value.md).
4. [Machine-readable final map](FINAL-MAP.json), and the more detailed historical branch maps in `Euler/` and `NavierStokes/`.

Final corrections take precedence over historical drafts, contracts, next-target proposals and statuses. Both reviewers accepted the conditional reconstruction with qualifications; final corrections were not independently re-reviewed. The retained maps document inspected boundaries, not a complete source audit or a minimal proof.

The worked Euler limit argument takes the uniformly controlled viscous family as an explicit upstream input. It is a human reconstruction, not a new Lean result or kernel verification. The Navier–Stokes map has narrower sampled review coverage. No unforced-NS advance or formal source defect is asserted.

## Archival provenance

Copied reports and JSON maps preserve the completed external investigation, except for two explicitly recorded inline-code formatting repairs in the historical nested Euler map (mathematical indexing otherwise rendered as broken Markdown links). `COPY-PROVENANCE.json` records source and published-copy hashes, these formatting adaptations, and the external scripts, logs and preservation snapshot deliberately not added to Git. Original external artifacts are unchanged. Historical checks encode the old filesystem/ref state and should not be rerun as current-state validation. Some source citations and evidence locations are machine-local; source pins and repository-relative Lean paths are retained. This packaging makes no portability or fresh semantic-validation claim.

The published proof, build configuration and dependency pins are unchanged. The subsequent drift-aware energy/bootstrap investigation is separate work and is not part of this record.
