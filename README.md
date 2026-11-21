# AI Safety Tasting Menu

**Raccoon Labs** · a collection of mathematical proofs, readable research, and exercises in epistemic security.

> **Public research sampler · R0001 (November 20, 2026).** Seven source-bearing courses, each with different evidence grades. This is not a blanket certification of the mathematics, software security, publication rights of third parties, or completeness of future research. See [Known limits and evidence](docs/PUBLICATION_STATUS.md) and [Rights and attribution](docs/RIGHTS_AND_ATTRIBUTION.md).

## Before the proof, a question

*What would it take to trust something an AI has found?*

Imagine a model announces a theorem. Or suggests a program. Or discovers a remarkable chess move. The response may be beautiful, and it may even be right. But “it sounds right” is not a verification method.

The more quickly machines can produce plausible discoveries, the more valuable a quieter craft becomes: **knowing exactly what has been shown, how to check it, and what remains unknown.**

This tasting menu is an invitation into that craft. Seven courses, seven different ways to ask for evidence. Here are rigorous number theory, interactive readers, a real executable Lean producer and checker, and an exercise in judging AI answers. There is also a sketch of how mathematical evidence, provenance, and permission might fit together in research software.

Some things are proved in Lean under exact hypotheses. Some are reproducible artifacts or transparent exercises. Others are architectural ideas or research ambitions. **Those are not interchangeable.** We will tell you which is which and give you the source.

You don't need to know Lean to begin. Curiosity is sufficient. Precision is waiting when you want it.

**Five minutes:** [Try The Catch](exhibits/07-the-catch/index.html), a deliberately synthetic, fully disclosed practice game—not a blind benchmark. **Fifteen minutes:** open the [Shifted KMS offline reader](exhibits/02-kms/OPEN_ME.html), then meet [Jacobi's executable certificate checker](exhibits/03-jacobi/PRODUCER_CHECKER_TOUR.md). **An afternoon:** follow a source theorem in WEIL or SHIU.

## Choose a course

| Course | Start here | What you actually get |
| --- | --- | --- |
| 01 · WEIL Bounds Toolkit | [README](exhibits/01-weil/README.md) | Complete public Lean 4 source at a frozen commit, Kloosterman–Weil bound, worked examples and verification material |
| 02 · Shifted KMS | [Start offline reader](exhibits/02-kms/OPEN_ME.html) · [README](exhibits/02-kms/README.md) | Complete paper PDF/TeX, Lean source, theorem atlas, guides and offline interactive reader |
| 03 · **Jacobi: executable Lean** | [Producer/checker tour](exhibits/03-jacobi/PRODUCER_CHECKER_TOUR.md) · [Manuscript](exhibits/03-jacobi/MANUSCRIPT_AND_REFERENCE/ASTER_JACOBI_WORKING_MANUSCRIPT_R0005.pdf) · [README](exhibits/03-jacobi/README.md) | R0005 paper PDF/TeX/Markdown and complete flagship Lean source: produce an exact spectral-distance witness; check it separately |
| 04 · Raccoon/Oxbow | [Public-safe field guide](exhibits/04-tool-field-guide/README.md) | A generalized map of reasoning, evidence, reusable tools, coordination and release gates; no internal operating map |
| 05 · **Paper B: complete reader** | [Original full reading room](exhibits/05-paper-b/OPEN_ME_READING_ROOM_HERE.html) · [edition note](exhibits/05-paper-b/README.md) | **All 172 owner-supplied R0007R3 files**: Paper B, K1, full atlas, source, and both reviewed oral-history works |
| 06 · SHIU | [README](exhibits/06-shiu/README.md) | Complete source tree of the publicly released, Palomar-registered Lean formalization |
| 07 · The Catch | [Try the synthetic five-case prototype](exhibits/07-the-catch/index.html) · [fidelity review](exhibits/07-the-catch/EDITORIAL_FIDELITY.md) · [README](exhibits/07-the-catch/README.md) | A local judgment game: tell clean answers from flawed ones, preserve partial truth, ask for referents instead of echoes |

**Everything described as included above resides within this repository.** Provenance links complement the files; they are not used as substitutes for them.

## Where it goes next

### Producer/checker asymmetry

A producer may spend considerable effort proposing a theorem, an executable program or a numerical witness. A checker can sometimes validate that proposed result much more cheaply. Jacobi actually implements this in Lean: data-driven rational certificate production, a formal singular-or-witness contract, and a literal independent checker that does not import the producer. See the [source-backed walkthrough](exhibits/03-jacobi/PRODUCER_CHECKER_TOUR.md).

### Mathematics as a reusable research substrate

The Raccoon Math Library (RML) pursues durable, interconnected theorem contracts, mathematical representations, consumer edges and negative knowledge. An idea that was interesting but false should not silently become institutional fact. A Lean theorem is no stronger than its assumptions, dependencies and exact statement.

### Chess as an adversarial laboratory

I want to connect chess positions and search constraints to reusable mathematical structures, then hunt surprising **bridges to checkmate** while running Stockfish as a hostile benchmark opponent. The ideal is proof-aware search with independently checked moves and claims. **I am not claiming a certified starting-position forced mate or a demonstrated exploit against Stockfish.** More on the agenda in [Research Directions](docs/RESEARCH_DIRECTIONS.md).

### Executable trust

Cryptography binds bytes to a pinned identity **when the expected digest is itself trusted**. Formal verification establishes scoped claims relative to a formal model. Runtime controls enforce what can actually happen. The larger direction is to combine them: proofs and provenance become admission criteria at executable boundaries, not decorations in a PDF.

## Suggested reading

- [The 15-minute and afternoon tasting orders](docs/TASTING_ORDER.md)
- [Research directions: what is known, what is proposed](docs/RESEARCH_DIRECTIONS.md)
- [Source versions and assembly ledger](docs/SOURCE_ASSEMBLY.md)
- [Release and privacy gates](docs/RELEASE_GATES.md)

Each original mathematical project has its **own** Lean and Mathlib version; there is intentionally no aggregate Lake build. If you want to check a specific theorem, enter that course and follow its pinned build instructions.

## Intellectual honesty

A green Lean build is not proof of novelty or end-to-end system security. A digest match does not authenticate an author by itself. A successful chess tactic against one version/configuration of an engine is not a general attack. A public exercise with exposed answer keys is not an uncontaminated model benchmark.

All of those boundaries matter. The point of this menu is to make them visible, interesting and useful.

### Provenance and rights

Each exhibit retains its original authorship and rights; this repository does not apply one blanket license to seven different objects. The **WEIL, KMS and SHIU source files are frozen copies of already public releases**. Jacobi is fully staged as a flagship executable Lean project and manuscript. **Paper B includes the complete original R0007R3 edition**, including both reviewed oral histories. K1 retains one clearly identified provisional predecessor bibliography entry; different software and scholarly rights are explained in the [rights note](docs/RIGHTS_AND_ATTRIBUTION.md). The new Catch demo is synthetic and retired for blind benchmarking; the original private 19-item bank is not in this release. No VAALER material is included. Source-specific licenses and copyright notices govern each course; no blanket repository license is asserted.
