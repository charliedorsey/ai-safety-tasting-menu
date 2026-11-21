# The Raccoon/Oxbow tool habitat — a public architectural sketch

> **Purpose:** A generalized discussion of research-software design patterns.
>
> **Status:** Editorial draft. It is not source code, a complete security audit, a deployment manual, a system threat model, or a claim that every pictured component is active. Internal paths, private operational material and authorization arrangements are intentionally omitted.

## Why a field guide?

AI-assisted research generates hypotheses, scripts, artifacts, proofs, test logs and discussions faster than a person can remember their status. The problem is not solely *how to produce more*. It is how to distinguish what was proposed, what was checked, what failed, what was reused, what is installed, and who or what may perform the next action.

The Raccoon/Oxbow architecture explores five complementary layers.

## I. Orientation, identity and presentation

An incoming task first needs **situating**, not merely text prediction: What kind of work is requested? What evidence exists? What is unknown? Which specialist is appropriate?

One family of tools models portable **context capsules** with source identity, stable semantics and a strict separation between small frequently needed context and larger selectively retrieved material. Presentation tools can render those capsules for people without conferring new privileges. The important design boundary is **representation is not authorization**.

An attractive page can faithfully display a candidate that has not been admitted or verified. A model's preferred route can remain a suggestion.

## II. Portable knowledge and organizational learning

Research knowledge is more than a chat transcript. It includes source-backed records of what worked, what did not, and what conditions made a result applicable.

Some tool patterns move or inspect **immutable logical packages**. Others preserve **case studies and counterexamples** or convert a repeatedly validated practice into a reusable, narrowly scoped suggestion. Distinct kinds of state must not be collapsed: backing up an object does not prove its factual claims, and transferring its bytes does not transfer someone else's decision authority.

## III. Work coordination

A live activity channel can tell workers **what has happened**, what needs attention and which source to inspect. It should not independently decide that a theorem has been proved, that a submission may be published, or that a named person is authorized to act.

This is the difference between **observability** and **governance**. A well-designed coordination event includes the event type, originating source, time, status and a route to its evidence. Uncertain events should stay uncertain.

## IV. Mathematical research and exact verification

The Raccoon Math Library (RML) is conceived as a collection of mathematical objects, theorem contracts, representations, formal interfaces, downstream consumers, unresolved obligations and negative knowledge.

A question registry can track research hunts and rejected approaches without automatically accepting every returned file as a theorem. A bounded empirical laboratory can falsify hypotheses without claiming kernel proof. Pinned proof-execution tools can reproduce exact Lean/Lake builds and generate receipts tied to source snapshots.

These are different evidence grades:

| Evidence | What it establishes | What it does not establish |
| --- | --- | --- |
| Candidate/idea | Someone proposed a mathematical direction | Truth |
| Computation | An experiment produced a result under specified conditions | A universal theorem |
| Source snapshot + digest | Specific bytes were fixed and can be checked for integrity | Authorship or correctness by itself |
| Lean kernel check | A formal declaration has a proof term accepted against its specified dependencies and axioms | Novelty, full system security, or accuracy of every informal gloss |
| Independent consumer build | A separate project can import or apply a source-bound interface | That all intended applications are proved |
| Runtime policy trace | An executable boundary did or did not permit a specific action | That every future execution is safe |

A useful architecture preserves those labels and does not promote them through typography or enthusiasm.

## V. Publication and audience-facing work

An external paper, toolkit, interactive reader or code package needs a distinct release contract. Source ownership, third-party licenses, mathematical claims, exact source cuts, independent tests, prose, illustrations and human approval all matter.

A green build is not a registry entry. A registry entry is not journal peer review. A polished diagram is not a proof. A successful dry run is not permission to publish.

## Four illustrative workflows

**Review a theorem.** Find the underlying mathematical object; inspect hypotheses; check the formal declaration; reproduce one pinned build; identify actual consumers; report limits.

**Explore a new connection.** Record a conjectured bridge; choose a bounded search method; return positive and negative results; admit only checked outcomes into the trusted index.

**Package a tool.** Collect one reproducible source snapshot; verify checksums; run exact tests; record known platform limitations; keep deployment separate from acceptance.

**Prepare a public research artifact.** Align informal claims to formal statements; check attribution and rights; build a human-readable reader; require explicit approval of the final immutable object.

## Design ideas worth debating with AI safety researchers

- Should an AI agent be permitted to execute an action without presenting a provenance-bearing, machine-readable justification?
- Which critical guarantees belong in a type system or proof assistant, and which must be implemented in the actual runtime?
- Can a deliberately smaller independent verifier outperform large generative systems at detecting subtle validity failures?
- How should an organization preserve failed approaches without teaching its assistants that an old hypothesis is a current fact?
- Can a system make the cost of verifying a decision substantially lower than the cost of generating it?

## What this guide deliberately excludes

Private hostnames, local paths, personnel or role capsules, prompts and operational instructions, live infrastructure topology, unpublished personal correspondence, accession tokens, credentials, installation/runbook details, archived internal reports and unapproved source packages.

The field guide is a **map of design ideas**, not the full internal estate. Source code for the mathematical and paper exhibits is handled separately under the exact-source release gate.
