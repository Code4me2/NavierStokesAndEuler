# Bounded upstream H3/pressure port

This port adds four library modules (651 Lean lines) from upstream `f9e8bc5b38b6e212696e8a30e3e91517af887bbd` to refactored baseline `26e896edbdbe1215c0d50ddba24b2b6453646f5f`. No retained proof source, public theorem route, build configuration, or dependency pin changes.

Files: `NavierStokes/R3/{H3Approximation,H3PressureDistribution,H3DivCurlFourier,H3PressureOrthogonality}.lean`.

The first two files adapt imports and the moved smooth-partial helper namespace. H3Approximation additionally imports Mathlib's canonical Euclidean measurable/volume infrastructure. The last two are byte-identical to upstream. No theorem statement, proof body, or record field was changed.

## Capability and limits

Approximation-based H1/H3 records, distributional derivative and Fourier div/curl tools, and whole-space pressure orthogonality. The pressure theorem assumes an approximation-H1 divergence-free field, C1 pressure and L2 pressure gradient; pressure itself need not be L2. This is not general H3 density, a torus theorem, different-force stability, or progress on unforced problem B.

## Accepted pilot evidence

Local report: `/home/velvet/h3-pressure-pilot-z7lj1we_/FINAL-REPORT.md`; machine disposition: adjacent `RESULT.json`.

Three source replays (implementation and two independent audits) each passed all 16 project closure modules and three probes. The audits checked 66 elaborated contracts, 446 project constants, and a complete 4,696-module semantic import closure using authenticated historical source-built dependencies. Permitted axiom set: `{propext, Classical.choice, Quot.sound}`. Separate probes establish ordinary integrability of the pressure pairing. All retained files stayed byte-identical.

These receipts certify the bounded strict-Lean pilot, not a full original regression or independent-kernel/Comparator check. Broader validation is a separate, newly authorized task; do not infer its outcome from this note.

The user subsequently authorized local commits and isolated broader validation. Historical receipts intentionally retain the precommit HEAD/index/ref state and must not be rewritten to conceal that authorized transition. Build evidence and failed attempts remain outside Git at their recorded paths. The source commit packages existing accepted bytes; it is not a new mathematical validation run.

## Scope control

No wholesale upstream merge. No new umbrella imports. Old theorem producers and selected research witnesses remain on their previous dependency routes. Additional upstream families require a concrete use and a separate scope decision. The user has not authorized publishing or merging into the original/fork published branches.
