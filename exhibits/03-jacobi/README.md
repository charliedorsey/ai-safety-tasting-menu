# 03 — Jacobi: certified spectral distance

**Start with:** [R0005 manuscript PDF](MANUSCRIPT_AND_REFERENCE/ASTER_JACOBI_WORKING_MANUSCRIPT_R0005.pdf), [LaTeX](MANUSCRIPT_AND_REFERENCE/ASTER_JACOBI_WORKING_MANUSCRIPT_R0005.tex), and the complete selected [Lean project](LEAN_PROJECT/).

This is a selected **complete manuscript + flagship Lean project** from the 2026-10-24 source archive, not the entire original archive of historical research worktrees. It contains **all 75 files** from the original `LEAN_PROJECT/` and the manuscript and exact Python reference programs, excluding a private editorial submission-gate note. The old logs and supplemental unrelated RML research experiments have not been imported.

## Reproduction

Lean version and Mathlib are pinned in [LEAN_PROJECT/lean-toolchain](LEAN_PROJECT/lean-toolchain) and [LEAN_PROJECT/lake-manifest.json](LEAN_PROJECT/lake-manifest.json). With Lean/Lake installed:

```sh
cd LEAN_PROJECT
lake exe cache get
lake build AsterPublicProducer JacobiMatrixFinal DiscreteSturm AsterAccuracyCheckR0001 AsterLogFuelR0001 AsterFastProducerR0001 AsterEmitted3x3R0001 AsterLiteralIndependentCheckR0001
lake env lean scripts/PrintAxioms.lean
```

The 22-page manuscript and exact reference numerics remain separate from the formal proof surface. This branch does **not** claim a new independent cold replay. Historical warm receipts and the original archive have not been bundled.

## Honest mathematical scope

The selected project contains a named certificate checker, an executable proof producer, and an independently checked three-site literal example. The manuscript also discusses broader conditioning and Diophantine contexts that must **not** be advertised as Lean-proved without theorem-level matching. A previously identified interface issue concerns zero padding versus constant padding beyond the physically supplied `b_0=b_1=1` array. Public-facing API descriptions should not claim an unconstrained padding-invariance theorem until that point is resolved.

## Provenance and rights

Original uploaded archive SHA-256: `dbba5ca20390d8dff27f9fc2ebb4b81a64140246bb7073f44284204582cc3070` (2026-10-24). The paper/source files are byte-preserved from that archive. This curated exhibit has a **new** manifest; it is not falsely presented as the entire 439-member archive.

**Release gate open:** exact permissions and scholarly/third-party rights for previously unpublished manuscript and Lean sources require owner signoff before a public visibility change.
