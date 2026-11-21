# Paper B R0007R3 — final publication packaging audit

**Status:** integrated edition assembled, verification acknowledged, **not published**. R0007R3 is a packaging/navigation edition derived from the private R0007R2 verified candidate; scientific Paper B TeX/PDF and 8-page guide remain byte-identical to R0007R2.

## Gates closed by existing evidence

1. **Paper B external Lean replay:** Alex Breakell independently completed the pinned `PaperB` Lake target on Ubuntu/WSL2 with reported build exit 0 and a 9,599-job success receipt; the printed terminal axiom query exited 0 with only `propext`, `Classical.choice`, and `Quot.sound`.
2. **Source custody:** the R0007R2 master file set passed its 268-entry SHA-256 manifest check before repacking; the sealed R0003 source capsule is unchanged. The new R0007R3 SHA-256 manifest covers the actual staged archive.
3. **Paper/guide layout:** the 31-page Paper B and 8-page reading guide were visually audited in R0007R2. R0007R3 preserves their bytes; no new Lean build or mathematical rewrite was attempted.
4. **K1 recovery:** the original 72,173-byte K1 TeX is exposed as a separate research manuscript. A 31-page PDF preview compiles with a reconstructed external bibliography. The K1 TeX is unmodified and **the bibliographic reference to an unpublished predecessor must be confirmed**.
5. **Reader navigation:** the clickable top-level launcher opens `Docs/OPEN_READING_ROOM.html`, with mathematical reading room, atlas, documentary, K1, paper, guide, and source navigation.

## Before public distribution of the full edition

- **Bibliography:** replace or approve the provisional reference `DorseySecondLayer2026` in `Docs/K1/references.bib`. Verify no K1-specific analytic or formal claim is implied by the independent Paper B build.
- **Documentary:** human publication approval for the exact oral history editions, participant privacy/consent and literary credits, as recorded in prior editorial/custody notes. The AI literary editor Linnea is credited; this is not a transcript of private reasoning or interviews.
- **Source:** decide/verify the Apache-2.0 software license, redistribution of sealed Lean files and readable source snippets, and third-party source permissions. **CC BY 4.0 for authored text does not automatically relicense code.**
- **Publication metadata:** settle the exact title(s), whether Paper B and K1 get distinct records, any full-source DOI record, final scholarly abstract/keywords and publication venue. Do not fabricate a DOI.
- **Recipient-side browser:** inspect the extracted local launcher and the full interactive atlas in a normal desktop browser to catch environment-specific `file://` behavior.
- **Research review:** the external technical replay is genuine but does not replace independent human mathematical scrutiny, novelty/priority review or journal refereeing. This is not a reason to rerun the same Lean build.

## Publication structure recommendation

Keep the integrated research edition as one navigable object. When ready for public dissemination, optionally issue two linked persistent records: (1) scholarly paper(s) and (2) the entire reader/source companion edition. **Do not allow the registry's paper-only convention to discard the reading room or oral history.** If approaching a journal first, prepare a conventional clean submission PDF as a *projection* of this complete edition, not the master version.

Original package SHA-256 and historical restrictions remain in the private custody of the complete master. The raw private verification emails/logs and original internal approvals are deliberately not part of the clean reader-facing staging package.
