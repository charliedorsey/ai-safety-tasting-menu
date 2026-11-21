# Safety research directions — a candid roadmap

> **Status: forward-looking research ideas, not completed safety guarantees.**

## 1. Formal mathematics as a checkable research substrate
RML (Raccoon Math Library) aims to preserve mathematical objects, theorem contracts, provenance, proof consumers and negative knowledge in reusable form. A Lean declaration and a reproducible build establish specific facts; the connected RML record helps determine how a proof may transfer, where it does not, and whether a downstream consumer has actually imported it.

**Exhibits:** WEIL for a complete public theorem library and genuine independent mathematical reuse; Jacobi for a more recent search/verification workflow. **Open question:** Can reusable typed contracts and counterexample history materially improve research throughput without elevating weak evidence to theorem status?

## 2. Producer/checker asymmetry
When discovery is costly and checking a candidate is cheaper, separate a creative **producer** from a minimal, reproducible **checker**. The Jacobi materials should show the actual certificate format, theorem surface, scope and measured replay—not an invented asymptotic advantage. Cheap checking is a possibility to exploit, not a universal property of computational problems.

**Open experiment:** Define and compare proposal cost, independent validation cost, rejection rates, and source-bound provenance.

## 3. Chess as an adversarial verification laboratory
Model standard legal chess states, move transitions, tactical targets and search assumptions with typed interfaces. Use the RML to suggest *bridges*—mathematical structures or proof obligations connecting otherwise disconnected candidate lines. Let a search producer hunt concrete candidate paths, and check every candidate with an independent rules engine and reproducible engine analyses.

Stockfish is a **benchmark adversary** in this proposal, not a victim of a known cybersecurity exploit. An ambitious target is to find surprising, verifiable forced-mate paths or model-specific adversarial weaknesses. An engine evaluation or locally winning search line is **not** a proof that Stockfish can be beaten from the starting position; search settings, versions, time controls and opponent responses matter.

**Questions:** Does the Lean/rule-checking overhead pay for itself? Can a local theorem or constraint eliminate meaningful search? How do we prevent a producer and checker from sharing the same bug?

## 4. Proof-aware programming and executable trust
The architectural ambition: compile narrow, verifiable guarantees into **runtime admission, provenance checking and authorization controls**. A cryptographic digest can bind artifacts to bytes; a Lean proof can certify a mathematical property relative to specified axioms; executable policy can enforce conditions at an actual interface. Each component is independently limited, and none alone proves a deployed system secure.

Proposed building blocks: a pinned input manifest; source/hash-bound build receipts; an explicit capability model; runtime validation of request identity; deny-by-default failure behavior; provenance-aware reconciliation; separate human permission for irreversible actions.

**Evidence needed:** A threat model, scoped invariants, fresh replay against a frozen release, adversarial tests, and concrete runtime traces showing the boundary being enforced.

## 5. Human understanding as a safety property
The KMS reading guide and generalized field guide are not decoration. A reliable system should be legible enough that an outside reader can identify which assertions are proof-checked, which are numerically illustrated, which are historical and which are experimental. Clear reading paths are part of the trust story.

## Nonclaims
No full AI alignment guarantee; no code generation free of error; no proof of general-purpose runtime safety; no certified Stockfish defeat; no claim that a SHA-256 hash authenticates a publisher by itself. The point is to make important claims **falsifiable, bounded and independently repeatable**.
