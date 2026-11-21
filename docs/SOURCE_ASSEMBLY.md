# Source assembly ledger — public first edition R0001

This packet is organized as **one repository containing self-contained exhibits**. The sources have deliberately different toolchain pins and distinct rights/claim grades. Nothing here requires building the seven exhibits together.

| Course | Source binding | What is actually inside | State |
| --- | --- | --- | --- |
| [WEIL](../exhibits/01-weil/) | Public `weil-bounds-toolkit` at `7adcd23667b063ae54cc0e8707c89ce259e8fd31` | **All 62 public source-tree files**, including Lean, Lake, proofs, docs, examples, license | FULL SOURCE STAGED |
| [KMS](../exhibits/02-kms/) | Public KMS companion at `db536c2026e703400de3749bee0259b3e1ab7a07` | **All 83 public source-tree files**, paper/TeX, reading site, Lean, explorer, mixed licenses | FULL SOURCE STAGED |
| [Jacobi](../exhibits/03-jacobi/) | Uploaded ZIP SHA-256 `dbba5ca20390d8dff27f9fc2ebb4b81a64140246bb7073f44284204582cc3070` | 75/75 flagship `LEAN_PROJECT` files and R0005 paper PDF/TeX/Markdown plus exact reference programs; private release-gate note omitted | COMPLETE SELECTED SOURCE; SCOPE/RIGHTS RECORDED |
| [Raccoon/Oxbow](../exhibits/04-tool-field-guide/) | Fresh generalized public-safe synthesis | Complete new architectural sketch; no internal original files | GENERALIZED DESIGN SKETCH, NOT INTERNAL ORIGINAL |
| [Paper B](../exhibits/05-paper-b/) | Uploaded R0007R3 ZIP SHA-256 `d04546886e62885658beb9aa1266794fb70b2c0d140a1c8aa61f098482dc82d4` | **All 172 original files:** Paper B, K1, guide, complete atlas, both oral histories, viewer and sealed Lean ZIP | FULL ORIGINAL EDITION; PROVISIONAL K1 CITATION AND THIRD-PARTY RIGHTS DISCLOSED |
| [SHIU](../exhibits/06-shiu/) | Public Palomar release at `e95766703ddf14b6b0d920bc17f6199e5797834c` | **All 192 public source-tree files**, Lean/Mathlib pins and docs | FULL SOURCE STAGED |
| [The Catch](../exhibits/07-the-catch/) | Original synthetic public-retired cases and new standalone HTML | 5 complete cases, probe handling, deterministic end feedback, explanatory source | SYNTHETIC PUBLIC PRACTICE DEMO, NOT PRIVATE EVALUATION |

The root [SOURCE_MANIFEST.json](../SOURCE_MANIFEST.json) records file-level SHA-256 digests for every staged exhibit, including binary PDFs and the Paper B sealed ZIP. This is a *new* manifest for the curated repository, not a claim that these files constitute the original unchanged private bundles.

## Source-rights and privacy decisions

**Public-source copying:** WEIL, KMS and SHIU are selected entire snapshots of already-public repositories; their original copyright and license terms remain in place.

**Jacobi:** The 439-member uploaded archive includes 159 historical-staging files, 112 supplemental RML research files and 82 historical receipts. None was presented as part of the flagship Lean source. The full matching flagship project and manuscript are present, but publication rights and mathematical prose alignment need review, including array-padding semantics.

**Paper B:** The full exact R0007R3 research edition was restored from the supplied 172-file archive, including K1, the original atlas, both oral histories and the original welcome page. All 171 source checksums verified. Charlie confirmed the literary works have already been reviewed; historical consent-pending statements remain in the exact source but should not override that newer confirmation. One K1 predecessor-citation placeholder and component-specific software-rights labeling remain to polish.

**The Catch:** The original 19-item benchmark source, private item keys and encrypted probes have **not** been copied. The new practice bank is synthetic and permanently unsuitable as an uncontaminated blind holdout.

**Release model:** Each course is standalone and retains its pinned Lean/Lake version, rights and proof grade. There is no shared Lean build and no umbrella license.

## Public first edition

The exact copies described above are included. Remaining limitations are explained in [Public status](PUBLICATION_STATUS.md) and [Rights](RIGHTS_AND_ATTRIBUTION.md). The original source identities and review receipts are historic snapshots, not claims that every research and editorial objective has been completed.
