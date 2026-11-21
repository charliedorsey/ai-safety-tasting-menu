# Paper B R0007R3 — completed archive QA and publication handoff

**Date:** 2026-11-02 (America/Denver). **Status:** technically packaged and release-candidate staged, no public upload.

## Summary

R0007R3 preserves the paper's verified mathematical release bytes from R0007R2 while reorganizing the entire reading experience into two primary directories, `Docs/` and `Source/`. The root `OPEN_ME_READING_ROOM_HERE.html` opens the full guided edition. The K1 manuscript is now visible as a 31-page separate preview and original TeX; K1's source bibliography was absent, so a transparent reconstructed bibliography includes one predecessor-title placeholder requiring human signoff. The documentary and atlas remain in the complete research edition rather than being discarded.

## Verified properties

- **Independent Paper B technical replay:** Alex Breakell reported `BUILD_STATUS=0` and `AXIOMS_STATUS=0`, the build log ends `Build completed successfully (9599 jobs)`, and the terminal axiom log gives only `propext`, `Classical.choice`, `Quot.sound`. Earlier source seal `SEAL_PASS 683 HASHED_FILES` is recorded. This does not establish external mathematical peer review or verify K1 specifically.
- **R0007R2 source archive audit:** all 268 hashed payloads in the old sealed release ZIP matched their recorded SHA-256 before reorganization.
- **Paper B:** original 31-page PDF and its TeX are byte-identical to R0007R2. No mathematical text edits and no Lean recompilation were carried out for the repack.
- **Reading guide:** original eight-page PDF byte-identical to R0007R2.
- **K1:** 72,173-byte source TeX byte-identical to the sealed R0003 source ZIP. Derived preview PDF has 31 pages, with internal references resolved; first/last pages visually reviewed. The five-entry bibliographic reconstruction is documented and one predecessor entry needs author correction.
- **Sealed source:** SHA-256 `e8bccaf4c607a3b2458a47833bdd98f598a59229f7af0175927b994318d7b2a1`, unchanged.
- **Top-level HTML and source links:** syntactic JavaScript checks passed for five script blocks. Static relative links and file targets are verified after reorganization; the atlas dynamic helper for source links was migrated to `Source/Viewer/atlas_pages/`. The historical manuscript link now has a real `Docs/history/` target. Browser runtime test could not be performed because this environment's Chromium administrator policy blocked both local `file://` and loopback `http://` navigation; recipient-side extraction/browser test remains advised, not asserted as passed.
- **Privacy:** the reader-facing staging ZIP excludes raw private replay logs, mixed historical editor notes, correspondence and original approval documents. The private master includes them in `_PRIVATE_CUSTODY/` with the unmodified original R0007R2 ZIP.

## Remaining decisions for public release

1. **K1 predecessor citation:** replace/approve the `DorseySecondLayer2026` placeholder in `Docs/K1/references.bib` before posting K1 PDF publicly.
2. **Public rights and source scope:** author's CC BY 4.0 choice covers author-controlled original scholarly documents. Code/source/embedded third-party materials must be cleared and correctly licensed separately (Apache-2.0 is the prior software proposal). Do not upload the source-bearing reader staging ZIP as if CC BY 4.0 granted all rights.
3. **Oral history:** final exact-edition publication/participant consent and literary editorial credits; an AI literary editor was involved, and the narrative is not a recorded interview transcript.
4. **Venue and DOI metadata:** no DOI or journal submission is assumed or created. One journal submission PDF can coexist with a more complete two-record research/companion archival architecture once the scope is approved.
5. **Independent mathematics:** Alex's technical verification proves reproducibility of the targeted Lean build and axiom check, but neither novelty nor correctness of every informal argument has been evaluated by an external human referee.

## Technical release diagnosis

**Release technical/packaging gate: PASS.** **Public redistribution of the full edition: CONDITIONAL** (K1 reference/rights/consent/venue decisions above). No writer revision, mathematical source edit or further repetition of the same Lean build is indicated by these packaging tests.

## Exact tree verification

The checks below were run **before** the final audit and publication-route notes were inserted. The finished staging ZIP has **171 hashed payload files**; the private master has **286**. Both finalized archives are separately reopened and all final SHA-256 entries validated by this script.

```json
{
  "staging": {
    "html": {
      "html_files": 112,
      "local_links_checked": 567,
      "missing": []
    },
    "manifest": {
      "files": 171,
      "errors": [],
      "missing_entries": [],
      "stale_entries": []
    },
    "pdf_pages": {
      "paper_b": 31,
      "reading_guide": 8,
      "k1_preview": 31
    },
    "pdf_first_page_titles": {
      "paper_b": "Pointwise Transfer of Anchored Singular Series at Fixed Modulus Charlie Dorsey October 2026 Abstract For a fixed positive squarefr",
      "k1": "Boolean CRT Fibers in an Anchored Singular-Series Sum Charlie Dorsey September 2026 Abstract For even h, we compare the singular s"
    },
    "pdf_has_unresolved_question_marks": 0,
    "paper_pdf_unchanged": true,
    "paper_tex_unchanged": true,
    "reading_guide_unchanged": true,
    "k1_tex_byte_identical_to_sealed_r0003": true,
    "sealed_source_sha256": "e8bccaf4c607a3b2458a47833bdd98f598a59229f7af0175927b994318d7b2a1",
    "documentary_pdf_count": 2,
    "private_evidence_path_present": false
  },
  "private_master": {
    "html": {
      "html_files": 112,
      "local_links_checked": 567,
      "missing": []
    },
    "manifest": {
      "files": 286,
      "errors": [],
      "missing_entries": [],
      "stale_entries": []
    },
    "pdf_pages": {
      "paper_b": 31,
      "reading_guide": 8,
      "k1_preview": 31
    },
    "pdf_first_page_titles": {
      "paper_b": "Pointwise Transfer of Anchored Singular Series at Fixed Modulus Charlie Dorsey October 2026 Abstract For a fixed positive squarefr",
      "k1": "Boolean CRT Fibers in an Anchored Singular-Series Sum Charlie Dorsey September 2026 Abstract For even h, we compare the singular s"
    },
    "pdf_has_unresolved_question_marks": 0,
    "paper_pdf_unchanged": true,
    "paper_tex_unchanged": true,
    "reading_guide_unchanged": true,
    "k1_tex_byte_identical_to_sealed_r0003": true,
    "sealed_source_sha256": "e8bccaf4c607a3b2458a47833bdd98f598a59229f7af0175927b994318d7b2a1",
    "documentary_pdf_count": 2,
    "private_evidence_path_present": true
  }
}
```
