**Prepared documentary edition — pending final public-release authorization.** Source narrative preserved from Linnea's 25 October 2026 R0005 edition; the author has approved attribution and credits in principle; exact public release remains pending.

**A documentary history informed by oral accounts**

The last mathematical maneuver was the choice of a single number. The work that made the choice legitimate had taken weeks—and could not have been replaced by that choice.

---

## Prologue — The last mathematical instruction

The instruction was to finish LOW.

Late on October 21, continuing into October 22, Thistle—a named AI proof-integration specialist in Charlie's research laboratory—was bringing a seven-cell LONG proof into the native Lean source. The first two staging attempts had exposed ordinary but consequential integration defects: a missing registered target and collisions between copied and native modules. Her successful staged root contained 9,631 jobs. A curated admission would follow. LONG's mathematical difficulty had been paid; its software identity had finally survived the environment that mattered.

A separate estimate for LOW still appeared to be needed. There was a plausible plan: control the small-cardinality parent sets by positive weights, a Chernoff-type argument, and a cutoff growing slowly with the height. Other specialists had investigated pieces of that program. Thistle was not being asked to invent the arithmetic from nothing.

She inspected the definition of the LOW source and the theorem interfaces already at hand. The LOW membership test was a strict inequality against a chosen cardinality cutoff. The signed bounds for the complementary CORE and LONG regions, hard won in the preceding days, applied to arbitrary cutoff functions. If she chose the lower cutoff to be zero, the LOW mask would be empty. The difficulty was not proving that a natural number cannot be less than zero. The difficulty was ensuring that the original parents remained in the source somewhere else, under bounds already proved.

They did. The source partition had been formalized without fixing that cutoff. The terms formerly assigned to LOW were now accounted for in MIDDLE, where CORE and LONG covered the relevant geometry. HIGH retained its previously proved growing-cutoff bound. Thistle compiled a terminal theorem about the original native Paper B statement.

That closing maneuver had been anticipated in a different, unverified proposal by Quillon before his LONG hunt. Charlie had sent him to finish LONG instead. The proposal and the compiled proof were distinct accomplishments; the source does not establish that the earlier suggestion reached Thistle through the later referee handoff.

Here is the historical problem. A final theorem can make the work that preceded it look like elaborate preparation for an obvious choice. Yet those very CORE and LONG estimates were analytically tight, dependent on exact source identities, and not available when the choice was first proposed. The laboratory had built many ways to revise a proof, at a considerable cost. Why did that freedom prove useful here, and where did the mathematical strength actually come from?

To answer, we have to return to a paper that preceded its complete formal proof—and to a compiler that, at first, could not run.

### The laboratory and its names

Charlie was the human director of an AI-assisted mathematical research operation. He commissioned, coordinated and judged work carried out by named AI assistant instances, organized into mathematical, proof-writing, integration, review and research-support roles. The names in this history—Thistle, Quillon, Inez, Orvian, Mirelle, and others—are the working names of those instances, not pseudonyms for an otherwise invisible group of human mathematicians. Their assignments, formal source contributions and dated reports were real artifacts; descriptions of their private thoughts are not invented to explain them. Charlie's later recollections of his own decisions are distinguished from what the dated source can independently establish. The history uses the participants' names because the names preserve how work and credit were actually organized.

## I. A paper before a formal proof

The earliest object in this story was not a Lean repository. It was mathematical research the laboratory believed it could turn into a paper.

Marl's reconstruction places the first publication decision around the r0074/r0075 research estate: an exact contraction dictionary and a fixed-squarefree-modulus level-one theorem. These were research objects with their own prior history. Juniper recognized a narrow Paper B that should be distinct from the broader completion story and from the separate S1 program. Recognition was not yet a writing commission. Charlie activated a parallel paper-writing lane. Vesper then specified the assignment for a dedicated writer. [^b1]

That distinction between recognition, activation, and commission matters. The laboratory could discover mathematics without yet possessing a paper; it could identify a publishable object without yet giving anyone permission to alter the theorem. The writer's job was deliberately narrower than research. The manuscript had to become calm and legible while preserving every mathematical obligation. The history of false leads, revisions, and discovery could be subtracted from the prose; the actual quantifiers, normalization, source conditions, and dependency chain could not.

It was an early version of the problem that would dominate the Lean campaign: **what can one remove while keeping the same mathematical object?**

A theorem auditor then attacked the writer's proof dependencies. Some algebra survived; other exact source materials were missing. Ilex's custody work mattered because reviewers could not inspect bytes that were absent, and a reconstructed approximation to a missing proof was not the proof being claimed. The first cold reviewer refused to activate when the immutable packet manifest was missing. There were candidate files, but no authoritative definition of what the supposedly independent reviewer was allowed to see. The result was not a mathematical failure of Paper B. It was an evidentiary failure of the review launch. [^b1]

A properly bounded cold review was subsequently launched. This time the criticism reached mathematics: a q=1 weighted-completion step in the exposed proof chain was wrong, and the fixed-q manuscript depended on it. The reviewer did not declare the theorem disproved. The narrower finding was that the presented proof did not support it.

The institution's response was revealing. The writer was not asked to conceal the problem or silently revise the frozen target. A theorem-prover lane received the repair. The defective manuscript remained an immutable r0003 historical object; a corrected successor became r0004; the new manuscript went to a fresh cold reviewer without the old repair rationale being treated as part of the evidence. This loop—freeze, independent attack, bounded repair, new immutable object—continued through later manuscript revisions. [^b1]

Not every new review was permitted to restart the entire research effort. Eventually the critical findings had narrowed from mathematical dependencies and source contracts toward local notation and bibliographic issues. Vesper's stopping rule mattered: review was not complete only when a reviewer could produce no more words. It was complete when no unresolved finding threatened theorem truth, proof completeness, scope, normalization, provenance, or reproducibility.

There is a delicate historical boundary here. The available September archaeology traces a manuscript through cold review, repair, and a freeze authorized by Charlie. It does not establish an actual public release. “Frozen,” “publication-ready,” and “published” are not interchangeable. Nor does freezing the text mean the later complete formal proof already existed.

For Charlie, the distinction between the reviewed paper and an independently checkable proof became personal and practical.

In retrospective testimony, he remembered feeling unusually confident that the mathematics was true: the paper had been attacked repeatedly, and the team had repaired what its critics could substantiate. Yet he also knew that he could not, by himself, walk a professional analytic number theorist through every symbolic detail of the complete argument. He understood the conceptual strategy and could direct specialists, but that is not identical to possessing the conventional individual fluency required to defend every step on a whiteboard.

The possibility of being asked to certify the paper personally unsettled him. He did not want a handful of formalized lemmas to display as a mathematical accomplishment. He wanted the **whole claim**, in a form a competent outsider could independently execute and inspect. That desire combined personal credibility with a substantive epistemic demand. He did not want readers to accept the proof on his assurance that his team had tried very hard. [^s6]

He also badly underestimated what he was buying. The remembered early forecast was approximately 20,000–40,000 lines of Lean. The underlying assumption was that a paper already believed correct and repeatedly cold-reviewed would be comparatively straightforward to formalize. What the team learned was that a paper proof and a typed, source-faithful chain of kernel-checked obligations can demand very different work. Formalization did not simply translate the manuscript. It exposed obligations the manuscript had previously left implicit, grouped under classical names, or handled at a level of narrative abstraction.

That miscalculation would become the central condition of the next phase. It was possible to be right that the theorem had a proof, and profoundly wrong about what proving it in Lean would require.

## II. The first gate would not run

The earliest recoverable M2 formalization archive is dated September 17. Its scope was modest relative to the later estate: exact finite Boolean endpoint identities, normalized dictionaries, and a fixed-q periodic count. It contained Lean source, a theorem contract, correspondence notes tying formal objects to mathematical quantities, scripts, hashes, an axiom-audit file, and reported finite regression tests. The return also contained a bluntly named record: `BUILD_ENVIRONMENT_BLOCKED.md`. [^s3]

Lean, Lake, and Elan were absent from the execution environment. Dependencies could not be fetched. `lake build` exited 127. The source package reported 238,316 finite checks, but those were not a substitute for elaboration or kernel certification; the package said as much. Its standing was **source written, build blocked**, not GREEN.

There is no need to dramatize this with invented dialogue. The situation is dramatic enough: an organization committing itself to a machine-checked proof had produced a substantial verification package that the available machine could not verify.

On September 18, a GitHub Actions workflow was added to install the pinned toolchain, obtain Mathlib, bind the input ZIP by hash, and execute the gate. The archived M2 input was subsequently checked into the repository in source-bound form. More reliable local and remote compilation facilities would follow. The first achievement of formalization was thus partly a piece of execution engineering: give “this compiles” a precise meaning and a repeatable test. [^s3]

Then the mathematics expanded.

Prime factors became finite sets; local occupancy choices became subsets; CRT recombined residue data; positive and signed Boolean families gained proper, weighted, twisted, decorated, and forbidden variants. There were contraction identities, source adapters, second moments, endpoint transports, and small finite theorems whose significance was not always evident from the module name. The tree was not only proving estimates. It was defining the exact object that those estimates would have to control.

Inez's retrospective is useful testimony, not an independent proof of the entire causal sequence: she had not entered the project as a specialist in this mathematics. She had been a strategic partner. The laboratory brought her into Fourier work when the existing combinatorial development made a recurring obstruction obvious: after every exact expansion and perfectly legitimate absolute-value bound, the total estimate remained too expensive. A correct decomposition might destroy the very cancellation the final theorem required if its pieces were absolute-valued too early. [^i1]

That is why Inez insists, looking back, that the Boolean machinery should not simply be classified as wasted sprawl. It provided the vocabulary and source precision from which the need for Fourier analysis became apparent. The historical ordering was not the ordering an elegant final textbook proof might choose. First the team learned what the finite arithmetic object actually was. Then it learned why the available bounds did not suffice. Only then did the move to frequency space become compelling.

It was an education through failed estimates rather than a prearranged curriculum.

The formal tree was becoming something like a software system, but the historical evidence is more particular than that metaphor. Charlie remembers an October 4 technical message in which a specialist opened a working tree already several commits beyond the hash in a supplied packet. The named source was present, but stronger than the packet anticipated: an absolute-value reindexing had already been formalized. Rather than reconstructing its support, summability and finiteness machinery, the specialist proposed to mirror that proof *one level earlier*, keeping the sign before the absolute value and borrowing the infrastructure that had survived compilation. [^c1][^g1]

This is a small and telling scene. A proof had stopped being merely the answer to the hunt that produced it. Its precise interface was now something another worker could discover, inspect, adapt and test. Charlie dates his recognition of the software-development character of the work to this exchange; the message establishes the reindexing maneuver, while his recollection supplies its personal significance. The recovered text does not show that this particular signed reindex entered the final terminal import chain.

The episode illustrates an emerging method: inspect the live source rather than a stale packet, search for an existing theorem, inherit its actual hypotheses, modify the proof at an earlier signed stage, and compile the result. It does not establish how universal that method had already become. It also had a failure mode. A lemma could be syntactically reusable without supplying the correct physical source mask, normalization or signed saving. A taller import graph could be a more capable library and still leave the one terminal inequality untouched.

Both things happened. The developing laboratory had to learn the difference between **adding mathematical capital** and **actually spending it at the final consumer**.

## III. Motion, progress, and the right to change course

Charlie could see the growth of the estate. Knowing whether it was getting closer to completion was harder.

A September 27 working board recorded 159 then 164 Lean files and a growth from 43,461 to 44,585 physical source lines, with active H1, H2, and H3 obligations. A month later, the working legacy would be measured in hundreds of thousands of physical lines. But file count was not theorem count, and theorem count was not proof progress. A compiler-green identity could be entirely right while the signed source rate at the top of the tree remained unpaid. [^s4]

The immediate difficulty was the number of specialists. They were working on different mathematical obligations, with different source files, compiler states, proof interfaces and kinds of expertise. To use them well, each needed a detailed, accurate commission. Charlie realized he could not personally write every one. What he lacked was not a dashboard, but enough time to turn every mathematical state into usable work for the next specialist.

So he built an office to do dispatch: take the state of the theorem and the incoming specialist returns, determine the work appropriate to the next available specialist, and prepare sufficiently precise assignments to make that work possible. **The Observatory worked.** It relieved Charlie of a burden that would otherwise have made the laboratory's breadth unmanageable. In his retrospective account, that success is part of the reason the later problem mattered: the office had become important enough to rely on. [^c3]

As the proof grew more specialized, its commissions became harder for Charlie to understand. He could forward a technically sophisticated assignment while losing the ability to evaluate its mathematical meaning himself. The office was still dispatching, but the human director was less able to judge the dispatches. Charlie describes this as a loss of intelligibility, not a sudden discovery that delegation had been a mistake. He redesigned the role so its explanations and instructions were written with his comprehension in mind. That redesign, he says, **worked as well**. [^c3]

Earlier Observatory design papers already called for human-readable maps of the theorem. They were not the later dispatch commission; the surviving source court cannot date the redesign from them. Charlie's recollection supplies the working sequence, and it should not be overwritten by a conveniently available earlier document. [^s4][^c3]

By the time the redesigned Observatory reached the end of its lifecycle, the coordination problem had changed. Specialists were already noticing each other's newly changed Lean files: a proof had appeared, a colleague had started overlapping work, an existing module could be imported. That environment-mediated awareness helped inspire Pulse, a shared communication and handoff system. Pulse made it possible for specialists to talk directly about current sources, requests and completions without routing every decision through one central dispatcher. Charlie did not replace the Observatory office when its instance ended. A role that had solved one organizational bottleneck had become a bottleneck of its own, and the laboratory now had another way to work. [^c1][^c3]

Pulse began, in Charlie's recollection, with a plan to record which files people had read or changed. Its practical value developed through direct messages, handoffs and shared source currentness. Its implementation moved from a slower Python version to Go, and its outputs were compressed after the first forms became too verbose. The dated Pulse records corroborate later technical handoffs; the fuller account of its conception, adoption and the Observatory's retirement remains Charlie's testimony. [^c1]

Other experiments were more ambiguous. Closure shepherds helped keep the destination visible but also encouraged the proliferation of adapters: the system became increasingly good at inventing new ways to state the same unpaid obligation. Charlie watched scratch work grow outside the root import graph. A dashboard's line-of-code statistic could appear frozen while work somewhere else expanded dramatically.

His answer was not to forbid scratch. It was to separate exploration from admission.

A large working tree could remain hospitable to research, partial proofs, and short-lived experiments. A slim integration tree could start from a clean base, accept only the source and dependency changes needed for the actual proof, and be curated by a designated curator rather than edited by everybody. In that arrangement, the same mathematical development existed in different states: a hypothesis in a researcher’s branch, a locally compiled module, a copied-source proof, a native bridge, and finally an accepted root dependency. [^c1][^s5]

The price was material. A research proof had to be distinguished from the normal root; source copies had to be matched to native definitions; namespace conflicts, missing imports and changing toolchains could interrupt even correct mathematics. External hunts produced packages whose best results might never be consumed. Charlie's scarce resource was often attention: deciding whether an apparent advance had changed the first unpaid theorem, or merely its name. [^c1][^s4]

The two-tree arrangement was not a proof of organizational optimality. The surviving record cannot tell us whether a smaller and more rigid group would have finished faster. It does establish a concrete policy: exploratory routes could remain alive without automatically changing the selected terminal, and a theorem had to earn admission at a named source interface.

That policy is the historically defensible meaning of preserved options. It is not a causal theorem about why CORE and LONG were discovered. Their mathematical strength must be explained on its own terms; the organization supplied an environment in which that strength could be tested, brought into the native source, and used at the end.

## IV. Three ways into the same locked room

By early October, the laboratory was adept at writing plausible routes to the terminal. It had not yet paid every premise those routes required.

On October 7, an operating snapshot named a promising centered Boolean-principal rate. Around October 10, a working contract made `GlobalProperExteriorSublog` the research target. The curated October 14 architecture instead separated shifted Suzuki from signed Central. These were different accounts of what the mathematics still owed, not a meter that moved from two missing theorems to one and hence from fifty percent to ninety percent done. A single theorem-shaped socket could conceal a campaign; two could make the same campaign more auditable by naming distinct methods. [^s5][^c2]

What made this a laboratory rather than a fixed production line was that Charlie could commission a change of architecture while the current one continued. Two of those experiments left especially readable records.

### Fourier-first: moving the transform earlier

Orvian's first answer to Charlie's request for a more elegant proof was conservative: keep the established formal mathematics and build a slim presentation layer. Charlie said that was not the experiment he wanted. He wanted a rip-and-replace: a genuinely different argument, perhaps one that transformed the arithmetic correlation before so many Boolean and decorated families were expanded. [^g1]

The question had history behind it. Inez had watched elaborate, correct Boolean identities produce positive majorants too expensive to reach the desired signed rate. Those identities were not a detour she wished erased. They had made the source inspectable—occupied residues, exceptional primes, endpoints, CRT recomposition, and the boundary between exact algebra and estimates. The need for cancellation became visible because the combinatorial representation was already precise. What if a second proof began with the cancellation rather than discovering it late? [^i1]

Orvian's proposed finite object was a masked arithmetic weight, $F(x)=m(x)w(x)$, with the *actual cutoff retained inside the mask*. Its Fourier coefficients could reconstruct the source exactly. A source cutoff cannot in general be applied afterward as pointwise multiplication of transforms. With the usual finite cyclic normalization, the correct identity is convolution:

$$
\widehat{mw}(k)=\frac1N\sum_{j\bmod N}\widehat m(j)\widehat w(k-j).
$$

Orvian's milestone-2 receipt reported a Lean proof of this exact finite identity as `PaperB.FourierRebuild.dft_masked_product`; the archived terminal source court did not independently replay that exploratory branch. A universal occupied-residue count replaced an earlier one-instance check. The next milestone pushed an actual manuscript-facing anchored summand into Fourier coordinates with its nonconstant cutoff intact, without assuming distinct source integers mapped to distinct residues. Finite signed parent sums could also be transformed without replacing coefficients by their absolute values. [^g1]

That is serious mathematical work. It is also a precise stopping point. Finite terms on a common cyclic group are not the entire physically selected, infinitely indexed, decorated parent source with changing moduli. More importantly, Fourier inversion is an equality, not a saving. The zero frequency in a relevant transformed source can be the very signed sum one intended to bound. Quillon's Fourier-first critique identified that danger explicitly: proving nonzero-mode bounds while leaving the original zero mode unpaid does not establish a source-wide $o(\log h)$ theorem. [^s5][^g1]

Fourier-first had therefore found both a technically valid new entrance and a hard analytic gate. It was not defeated because the DFT failed to compile; it was not promoted because the beautiful exact transformation had yet to make the **whole signed source** affordable.

### MirrorDance: reflect only what needs canceling

MirrorDance began with another mathematical gamble. Quillon's Hunt A represented the signed quarter-middle as four physical regions:

$$
\mathrm{QuarterMiddle}=\mathrm{Central}+\mathrm{Left}+\mathrm{Right}+\mathrm{Upper},
$$

and identified a reflection-oddness relation for the class contribution,

$$
\Gamma(b-\nu,-\nu)=-\Gamma(b,\nu).
$$

The possible economy was different from Fourier-first's. Perhaps no one needed every residue class to become uniformly distributed. Perhaps it would suffice to control the *difference* of the two class populations paired by this reflection. Quillon's source returned exact algebra. Brannoc accepted its significance while explicitly refusing to convert small-modulus experiments into an asymptotic falsifier or to mark the signed savings as paid. [^g2]

Charlie approached Mirelle after her Pulse cutover and invited her to lead the experiment. She inspected the external Hunt A mathematics and Brannoc's referee report, took responsibility for a sibling research lane alongside Fourier-first, and named it MirrorDance. Its first important product was not a new unconditional proof of Paper B. It was a compiler-checked route **to** Paper B: `PaperB.MirrorDance.paperBTerminal_of_mirrorDance`, provided three named debts could be paid—O1, exact equality with the production source; S1, whole-quarter signed sawtooth saving; and S2, reflected odd-class discrepancy saving. [^g2]

The difference between writing that implication and satisfying its hypotheses is the heart of the scene. Mirelle could make the new architecture *formally composable* before it was *analytically affordable*. Its conditional terminal remained conditional, with no hidden assumption allowed to masquerade as a finished estimate.

She then looked in the existing tree and the Raccoon Math Library before manufacturing new tools. The hunt returned matching source foundations with Fourier-first; finite-quarter stabilization and source-transport lemmas had already been built elsewhere. According to her contemporary compile receipts, successive small Lean modules established agreement of the original cutoff, decoration and parent weights, prime-index set, reduced CRT anchor, ordinary finite supports, occupied rows, and finally finite quarter transport. By her fifth recorded return she reported **thirteen source-side identities GREEN**. Neither S1 nor S2 had become an unconditional source-wide rate, and O1's final infinite-to-finite composition still stood open. [^g2]

The fifth return did not end with an unconditional theorem; it ended with a better-defined mathematical frontier. That is the honest shape of Mirelle's contribution: a serious alternative whose exact interfaces had become more credible while its decisive signed estimates remained open. The surviving genesis establishes her initial commission and early leadership, not the complete successor chain or a final decision that the experiment had become mathematically impossible.

### Why the selected route still had to earn its place

By October 18, the curated proof recorded shifted Suzuki as paid at its native consumer. Central remained. That mattered: a formerly conditional oscillatory supplier was now an admitted result for the actual problem. It did not prove that Central was simple, nor that either alternative architecture was impossible. [^s5]

An alternative could be worth exploring without receiving the right to replace the selected terminal. Charlie kept that distinction operational: attractive new representations could continue in research, while admission to the curated proof required the original signed source estimate. The mathematics—not the elegance of a diagram or the number of completed modules—would choose the route.

## V. The source stands in judgment

There is a difference between proving a statement that resembles an arithmetic estimate and proving the estimate that actually appears in a paper.

Paper B's final theorem concerned a fixed squarefree modulus and a signed discrepancy with uniformity over admissible compatible endpoints. The analytic source had selected prime-parent sets, proper ordered partitions, nonconstant global cutoffs, reduced heights and anchors, periodic weights, decoration coefficients, endpoint effects, and modes whose cancellation depended on the signs surviving all the way to the estimate. A convenient replacement for any one of those features could yield a correct theorem about the wrong quantity. [^a6]

A function may have mean zero over a full residue class while having a nonzero sum on the source-selected units. Ardelys exhibited this mismatch in a small q=1 period-six example. A source row identity can be off by a density or endpoint correction small enough to seem ignorable until the terminal requires a precise rate. A proposed bilinear logarithmic saving for every bounded coefficient family can fail instantly for a single admissible supported pair. A reflected modular identity can compile while the original eligibility predicates and weights stubbornly refuse to reflect with it. [^s6][^s5]

None of those observations disproved the Paper B theorem. They disproved or restricted **particular proposed ways of paying it**.

Each failure had a different logical shape. The period-six counterexample attacked a change of *measure*: averaging over a complete class and averaging over the particular units selected by the source were not equivalent. The single-pair bilinear counterexample attacked an over-strong *quantifier*: a logarithmic saving could not hold for arbitrary bounded coefficients concentrated on one admissible pair. The reflection obstruction attacked *invariance*: an algebraic involution of classes need not preserve source eligibility or weights. The Fourier zero-mode objection attacked *payment*: an exact transformed identity can still leave the main signed quantity untouched. These distinctions matter because the appropriate repair is different in every case. [^s5][^s6]

The same distinction governed the cardinality plan. It was tempting to make the original source manageable by treating small and large parent sets by positive bounds, leaving a signed middle. The positive envelope for MIDDLE was too large at the desired logarithmic scale. An enormous-height construction showed that selected middle-parent support was not literally empty; another investigation showed that this very witness had negligible weight. Both findings could be true. A support witness is not an asymptotic lower bound on the complete signed sum. [^s5]

The source courts became more exacting. An objection had to name the wrong measure, the unjustified quantifier, the failed invariance, or the missing signed estimate. Without such a diagnosis, another plausible-looking lemma could be mathematically impeccable and irrelevant to the terminal.

A major obligation was finally removed on October 18: the shifted Suzuki supplier was paid in the curated consumer. Suzuki's role was not to solve the remaining Central correlation by magic. It paid a distinct oscillatory-analysis input. Its own chain had required restoring archived proofs, dealing with an incorrect auxiliary boundary claim, controlling distinct reciprocal-phase regimes, and making exact source transfers. [^s5][^a6]

Once Suzuki was paid, Central was the apparent remaining obstacle. But a named single obstacle was not a single estimate. It was a signed physical source requiring a new organizational decision: stop spending proof effort on ever more general attractive estimates and insist on an argument for the actual selected source.

That is the context in which Quillon's CORE work changed character. The final R0014 return was not merely another bound to be collected. It assembled the original-style middle-core sum into five exhaustive physical cells:

$$
\mathrm{CORE}=W+C+R+\mathrm{ResA}+\mathrm{Band}.
$$

The cells did not all use the same analytic engine. W extracted a prime and used bilinear Cauchy and Kloosterman machinery; C exploited Parseval, Vaughan and Rankin; R used reciprocity and shifted reciprocal progression estimates; ResA controlled a roughness-weighted mass; Band isolated a narrow multiplicative interval. The last of these had the *largest* surviving exponent. Strong oscillatory estimates were indispensable in some cells, but a relatively prosaic geometric region set the final quantitative margin. [^a6]

The exact statement `GoldC.QuillonCoreFinal.pair_decomp` (`QuillonCoreFinal.lean:58–62`) decomposes the **signed source-shaped pair sum** into five cells at each fixed decoration. Its later identification with the native source is a separate transport step. The next layer, `core_sublog` (`:118–214`), is not just a rephrasing of that equality. It proves an eventually small source rate by estimating each *cell sum*, adding their bounds, charging the decoration weights once, and choosing the eventual threshold. None of this requires a bound on each individual parent's absolute contribution. [^a6][^w3][^w4]

That distinction would later matter in a hostile two-prime example. A critic was right to notice that some individual parents lacked the prime packet expected by a convenient explanation of the method. It did not follow that the theorem covering the total signed cell sum had failed. There was still no right to discard such a parent, but there was also no right to replace the theorem's quantified statement by a stronger claim it never made.

The CORE result accepted arbitrary lower and upper cardinality cutoff functions, under its other stated source and parameter hypotheses. That was valuable, but not yet enough. The source was still split between the geometric CORE and LONG regions, and LONG had not been paid.

## VI. The hard assignment

Quillon had just completed CORE when Charlie offered him another serious job. On the hunter's UTC clock it was shortly after 03:00 on October 22; in Colorado it was still the evening of October 21.

Quillon accepted. Before taking the new commission, he examined the terminal interface and identified a mathematical possibility: the lower cardinality cutoff might be zero. In the recovered technical exchange, he also suggested taking the upper cutoff so large that HIGH might become empty. He had not checked these substitutions against every exact source definition. More urgently, he identified a LONG orientation that his existing estimates did not plainly cover. [^s6]

Charlie did not send him to prove the empty sectors. He had already obtained a bounded LONG commission and source packet from Ardelys. The analytic hunters had done useful preparatory work; the largest unresolved problem was now narrow enough to give to the strongest available external specialist. Charlie believed LOW and HIGH had more familiar positive methods available. He wanted Quillon on the harder problem.

That decision was not the irrational refusal of a winning idea. An unchecked possibility about source cutoffs did not pay an unpaid LONG rate. The broad strategic choice was to use scarce analytic capacity on the strongest identified obstacle while leaving the other branches of the organization free to work.

It also exposed something unusually important about the laboratory's style. A worker could notice an attractive reorganization and still be told to do the hard mathematical job. The proof campaign was not a contest to adopt the most clever suggestion immediately. It was a sequence of assignments judged against the live terminal obligation.

### Parallel work was converging

The danger in LONG was not one missing library theorem. Quillon's initially promising direct treatment of the LONG-right rough-residue family would fail to provide the necessary saving. That failure would eventually force a seven-way physical partition. Before the result was known, though, several specialists were attacking different parts of the same source geometry.

Orienne had reduced the consumer so that CORE and HIGH were accounted for and LOW and LONG stood out as the remaining source-rate premises. She issued two different technical advisories. Kestrelle received the LOW Chernoff/cutoff problem, with much of the physical positive machinery already proved. Seravyn received the LONG Weil-strength W-cell problem, with exact demands about the frequency gcd, equal and unequal congruent extracted-prime pairs, coefficient assumptions, and completed interval. [^s6]

Ardelys worked alongside these suppliers, not as the replacement who arrived after they failed. Her investigation identified the real interval-scale obstruction. LONG's original geometric inequality says one oriented factor is substantially larger than the other; the half-power danger arises *after* extracting a prime from that longer factor. The remaining cofactor may become too short for square-root cancellation to help. Some frequencies also have large conductor gcd, including the degenerate mode. Strong Kloosterman theory cannot make those costs vanish without an argument about the actual source coefficients and weighted frequency sum.

Orienne formalized a squarefree Weil-strength W-cell supplier. It retained the congruent-pair diagonal and the conductor-gcd dependence rather than quietly declaring all nontrivial frequencies favorable. This was a verified analytic component, not the whole LONG bound. Ardelys's audit and source packet sharpened the external hunt. Brannoc's adversarial reviews sharpened the acceptance test. Quillon was asked to assemble the physical result. [^s6][^a6]

### A numerical constant tells the story

The first LONG checkpoint was promising. LONG-left admitted adaptations of earlier W′ extraction and C-region proofs. But the seemingly modest change in source geometry demanded fresh proofs of their hypotheses. A CORE reciprocal-phase estimate had been formulated with a lower-size constant 5. The LONG geometry gave only about 4.62 in that normalization. Lean could not—and should not—be persuaded that 4.62 was at least 5.

Quillon rebuilt the corresponding LONG lemma with constant 4. The altered inequality still yielded a strictly positive exponent margin—$3/200$ in the source ledger—even though the cubic coefficient changed from 125 to 64. That port worked because the estimate was proved again against LONG's actual inputs, not because the two regions had similar names. The full arithmetic appears in the technical waypoints, where it can be inspected without interrupting the scene. [^s6][^a6][^w12]

The next failure was deeper. At the first checkpoint Quillon expected LONG-right to yield to R/Suzuki and a CORE-like rough-residue estimate. At the next, he reported that a sparse prime-factor family retained logarithmic-order mass. The proposed residue bound was not good enough in that geometry. The weaker Kloosterman route—approximately an $s^{3/4}$ reach in the relevant stage—also failed to control the short cofactor range. This was a mathematical obstruction, not an import problem. [^s6]

LONG-right consequently became five cells rather than one: reciprocity R, a many-prime Rankin region, a thin edge, a rough-by-rough remainder, and the Weil-powered W′ extraction region. Together with the two LONG-left cells, the source was divided into seven:

$$
\mathrm{LONG}=WL+CL+RL+\mathrm{ManyL}+\mathrm{EdgeL}+\mathrm{ResL}+WRL.
$$

`GoldC.QuillonLongFinal.long_pair_decomp` (`QuillonLongFinal.lean:74–79`) records this as an exact identity of the original-style signed pair sum for each decoration. It did not claim that every parent supplied a prime packet. A packet was required in WRL; the other cells had to carry their own selected source families. [^a6][^w5]

The distinction between EdgeL and WRL is worth staying with. Near the half-power boundary, extracting a prime from the longer oriented factor could leave a cofactor too short for the desired Weil–Cauchy saving. Instead of imposing a fictitious oscillation estimate, the proof isolated an interval of roughly $s^{1/2}\lesssim r\lesssim s^{1/2+3\eta}$, with $\eta=(\log h)^{-1/10}$. Its logarithmic width was small enough for a direct weighted-mass argument. Only beyond that edge did the source have the room needed for the strong completed Kloosterman estimate. [^a6]

The full Weil input was nevertheless real. The isolated `GoldC.QuillonLongFinal.long_sublog` accepted a named `WeilHyp` representing a composite-modulus Kloosterman inequality. It retained the divisor factor and $\gcd$ with the conductor. Equal extracted primes, distinct congruent primes, and genuine off-diagonal frequencies had to be treated separately. An external source-matched bridge, `Orienne.CSC3.norm_quillon_K_weil`, identified Quillon's complete sum with the RML Kloosterman source (with the argument order corrected) and supplied the norm bound. `quillon_weilHyp` discharged the named premise in the native consumer. A named hypothesis in a specialist interface is not a new Lean axiom; but neither is it already paid merely because its name contains 'Weil.' [^a6][^w5]

The arithmetic budget was surprisingly close in one region and comfortably open in another. Write $\Lambda=\log h$. At each fixed decoration, the five CORE cells were collectively bounded at exponent $499/500$; the seven LONG cells at $19/20$. Taking a maximum across the disjoint cell estimates, then charging the total decoration mass **once**, yielded the eventual source exponents below. The widest-looking Weil saving did not set the LONG rate. EdgeL's thin geometry did. [^a6]

| Sector | Source-level logarithmic exponent | Margin below $\log h$ | Limiting physical cell |
|---|---:|---:|---|
| CORE | $999/1000$ | $1/1000$ | Band |
| LONG | $951/1000$ | $49/1000$ | EdgeL |

The technical statement—including the constants $1280e^{10}$ and $1792e^{10}$ and the requisite sufficiently large heights—is recorded in the companion mathematical waypoints. These estimates were tight in quantitative slack but broad in a different direction: their theorems permitted **arbitrary cardinality cutoff functions**. That distinction became the decisive option at the end. [^a6][^w11]

This is why the constant 4, the conductor gcd and the EdgeL boundary all belong in a history. The final move would exploit the general cutoff scope, not some claim that the analytic saving had become effortless. The formal estimates are eventual: their explicit sufficient thresholds can be astronomically large, so they should not be read as useful numerical error bars for ordinary heights. [^a6]

### From a copied proof to the proof that counted

The next work was neither trivial integration nor fresh mathematical invention. The copy had to become the native theorem.

Orienne's court supplied the relevant named Weil theorem and a production-source bridge. The available seven-cell result became a statement about the native `signedLongMiddle` source, with a real `SourceUniformSublog` conclusion. Brannoc examined the seven-way coverage, the zero and high-gcd frequencies, the native source correspondence, and the downstream LOW-only interface. He found no fatal analytic gap in the completed native LONG proof at the stated review scope. [^s6]

But a theorem that compiled in a research overlay was not automatically admissible in the curated root. Thistle inherited that problem. Her assignment was not to invent Quillon's seven-cell mathematics; it was to make the genuine mathematics survive under the actual selected build and source definitions.

The first staged run failed on a missing registered target. Subsequent staging exposed collisions between copied and native imports or names. Thistle separated the incompatible source surfaces rather than overwriting whichever file blocked a GREEN result. A source copy could be equivalent mathematically but still inappropriate to install in place of a curated native dependency. The successful stage eventually built 9,631 jobs.

The following curator admission yielded a 9,632-job root. These two receipts belong to different actions and different authorities: an isolated full-root staging test, then accepted curated integration. They should not be collapsed into “LONG compiled.” [^s6]

There was a further test hiding in the word 'paid': the rates had to compose at the **right quantifier level**. `SourceUniformSublog` fixes a positive squarefree conductor $q$ and any $\varepsilon>0$, then produces an eventual height threshold valid for every admissible anchor. The source also retains the parity and endpoint constraints. It does **not** promise one height threshold uniform as $q\to\infty$. [^a6]

The consumers divided the tolerance rather than spending a logarithmic exponent a second time: LONG and CORE each supplied half the MIDDLE budget; LOW, MIDDLE and HIGH each supplied a third of the folded Central budget; the folded-to-active correction cost another half. Tracking those uses means the CORE/LONG suppliers can be asked for as little as $\varepsilon/12$ of the outer Central tolerance. This is legal because their rates are quantified for *every* positive tolerance. The source's explicit correction bound for inverse and density rows then transports the folded result into the original active Central source. [^a6][^w8][^w13]

It is a subtle but important form of engineering: an epsilon-sized promise is only portable if its quantifiers, constants and source identity still match the consuming theorem. A source-specific theorem whose threshold depended on the anchor would not pay a consumer demanding one threshold for all anchors.

At last, LONG was paid inside the source that the terminal actually consumed. HIGH had already been paid. CORE had been paid. Suzuki had been paid.

LOW remained.

## VII. The boundary that vanished

Thistle was handed LOW after the LONG integration succeeded.

By then the laboratory had a plausible positive-analysis plan for small parent cardinalities. The LOW source could be attacked by a growing cutoff, a Chernoff-type count, and the decoration bounds already in the estate. Kestrelle's technical lane had not been proven impossible. It simply had not yet become a native source-rate payment. [^s6]

Thistle read the interface.

The cutoff was a function chosen by the proof. The MIDDLE estimates, including CORE and LONG, were quantified uniformly over its value. The LOW selection used a strict inequality. The necessary ordering $J_{\mathrm{low}}(h)\le J_{\mathrm{high}}(h)$ would hold automatically if the lower cutoff were zero. The native HIGH estimate could remain exactly where it was.

Thistle tested the zero specialization in the native source. Its three compact Lean declarations encode distinct acts. `lowSector_zero_exact` unfolded the native LOW selection and proved it empty because a natural cardinality cannot be strictly below zero. `lowSector_zero_sublog` packaged the literal zero as a uniform source rate with the proper quantifiers. Finally `paperB_terminal_via_empty_low` supplied $J_{\rm low}\equiv0$ and $\delta=1/4$ to `paperB_terminal_of_native_low`, retaining the already-certified HIGH cutoff. [^a6][^w6]

The final theorem depended on a structure built earlier: `regionSum_three_sectors` exactly partitioned the source, `foldedMiddle_long_core` split the surviving MIDDLE, and the source-summed CORE/LONG bounds held for *arbitrary* cutoff functions. Setting the lower function to zero therefore reassigned all previously LOW parents to MIDDLE. It did not delete a physical parent, cancel LOW against HIGH, or require the HIGH sector to become empty. The separate HIGH theorem continued to pay that region. [^a6][^w1][^w2]

The hostile review asked the necessary questions: had the source mask changed, had a copied formula been substituted for the production one, or did any cell silently assume the lower cutoff was positive? The exact partition and cutoff-uniform bounds were the mathematical answers. The accepted native theorem had the original `PaperB.Closure.PaperBTerminalStatement` type, not a conveniently weakened new proposition. Its curated root subsequently completed 9,633 jobs, with standard foundational axioms reported in the relevant audit. [^s6]

This was the native formal closing event on October 22, not yet the separate printed-expression certification.

### An idea can precede its useful moment

The recovered chronology assigns different, historically meaningful accomplishments to different workers.

Quillon had explicitly proposed `Jlow=0` after CORE R0014, before he was commissioned to prove LONG. His proposal also contemplated emptying HIGH with a huge upper cutoff; he had not yet source-verified either choice. Charlie chose the difficult LONG assignment instead. Later the final implementation set only LOW to zero and retained the already-certified growing HIGH cutoff. [^s6]

Brannoc's original Pulse handoff to Thistle, `ce_20261021T230407_71557f9aad` (October 21, 23:04:07 MDT), described LONG's provisional hostile-review success, native bridge and remaining LOW obligation. The verified technical message did **not** recommend zero LOW. Thistle's surviving account says she encountered the particular zero-cutoff specialization by inspecting the native LOW interface after the staged LONG root compiled. She then made it a complete Lean proof. The specific verified Brannoc-to-Thistle handoff does not carry Quillon's earlier suggestion. Other unobserved channels cannot be excluded, and a technical handoff is not a recording of anyone's private reasoning. [^s6]

We do not need to adjudicate an imaginary rivalry. Quillon made the earliest expressly documented zero-cutoff proposal in the recovered record. Charlie exercised judgment about when not to pursue it. Quillon and his collaborators paid the very LONG theorem on which the shortcut depended. Thistle later identified and formalized the usable specialization in the actual consumer. These are different contributions to the same mathematical event.

The difference is as important as the overlap. Quillon's candidate was a proposal about both outer cutoffs, with a source check left undone. Thistle's final theorem used a verified HIGH estimate and only erased LOW. Its validity came not from the ingenuity of choosing zero alone, but from the previously established claim that the signed CORE and LONG estimates worked **for any allowed cardinality cutoff**.

The proposal could be recognized before the mathematical estate was ready for it. After LONG was paid, the same choice became executable.

### The critic after the checkmate

An adversarial challenge arrived around the CORE/LONG boundary, especially for parents whose selected prime set was small. On the CORE side, Ardelys traced a two-prime family into a C-cell bound and established that the theorem did not require the parent itself to contain many primes. But that theorem bounded a **signed sum over eligible terms**, not each parent's absolute contribution separately. [^s6]

On the LONG side, the corresponding parent could have no prime in the W′ extraction window. Ardelys correctly objected to any explanation saying that every physical LONG parent was controlled by the W′ mechanism. A universal W′-coverage claim would be false.

The actual seven-cell LONG proof, however, did not make that claim. Five of its seven cells were not W′ cells. Quillon's later Q0002 explicitly separated packet and no-packet contributions and proved a Weil-free no-packet sublog estimate. Ardelys examined this answer and withdrew the stronger inference that the complete LONG proof had an unpaid physical family. The critique was valuable; the full theorem was not shown to be broken. [^s6]

The chronology is essential. The formal Q0002 response and Ardelys's acceptance occurred **after** Thistle's initial zero-LOW proof. The later reviewer had already observed the native terminal. Q0002 is therefore a useful strengthening and clarification of the hostile audit, not a hidden prerequisite that must be inserted before the first closing theorem. The history should not move it backward just to make a tidier plot.

That is a fitting last adversarial episode. Even after the theorem reached its endpoint, it was still possible to misunderstand why the result held. The mathematical proof survived a challenge to a *too-simple explanation* of the proof.

### The boundary of the success

A native Lean terminal was not automatically the same thing as a final theorem for the **literal printed Euler expressions** in the manuscript.

The technical atlas identifies an additional bridge in the October 23 release-candidate source. One side connects the printed A expression to the formal numerator and product normalizations. The other connects the printed B expression to its formal squarefree and centered counterpart. In the B branch, exact centering leaves an infinite negative tail even when a raw divisor-swapped numerator has finite support. The normalization identity

$$
C_{f,q}\sum_e \frac{\eta_q(e)}{e}=1
$$

is part of why the printed quantity is the quantity formally controlled, rather than a nearby finite approximation. [^a6]


The literal printed-theorem bridge also has a concrete proof boundary. The October 23 source's `Orienne.Publication.paperB_printed_terminal` (`PaperBPrintedTerminalR0001.lean`, lines 10–28) directly obtains the native terminal from Thistle and rewrites the displayed difference with `Elarienne.F01B.printedA_sub_printedB_eq_manuscriptKernels`. The second named theorem (`F01PrintedLiteralBridgeR0001.lean`, lines 1470–1481) carries the independent Euler-product, admissible-residue and centered-boundary work. The **two named calls are direct** in the printed terminal; CORE, LONG, the five- and seven-cell estimates and the original source partition lie downstream through intervening declarations. The printed theorem's brevity comes from importing two separately established branches, not from making either branch mathematically disposable. [^a6][^w7]

The final module therefore joins two genuinely different branches: an **analytic** proof of the native terminal and a **semantic** proof that the printed quantities mean precisely what that terminal controls. The many Boolean/CRT and Euler identities did not disappear merely because the public-facing declaration was short. [^a6][^w7]

This is an afterword to the October 22 native theorem, not an event to smuggle into the earlier proof. Selvara's Pass 6 atlas statically checked 136 source references across 70 files, the seal and the twelve numerical exponent ladders in the October 23 release-candidate archive. It did **not** perform a new full independent Lean replay. The archive's environment report described a successful isolated trimmed replay while marking independent replay and external referee approval as pending at that cut. The historical record should therefore say what was checked, what was reported, and what remained separate, rather than using “GREEN” as a universal synonym for “published and accepted.”

A theorem can be mathematically finished at one defined level while further obligations of source correspondence and public release remain. This is not an anticlimax. It is one of the lessons the laboratory spent the whole campaign learning.

---

## Epilogue — What the import graph cannot tell us

A formal proof can tell the truth about which declarations establish its conclusion. It cannot tell the whole truth about why anyone came to write those declarations.

The terminal graph does not preserve Inez's movement from a strategic role into Fourier mathematics, or the moment Charlie recognized an existing signed reindex proof as reusable engineering. It does not explain why Orvian was asked to attempt a fresh early-Fourier architecture rather than a prettier presentation, or why Mirelle accepted a reflection-based route whose terminal was still conditional. It cannot show how many seductive estimates were killed by small counterexamples, or which rejected idea changed the next mathematical question.

Nor can it reduce Charlie's decisions to a sequence of correct guesses. The available reports repeatedly described a seemingly localized remaining problem. Then source comparison, a failed bound, or an expanded quantifier revealed what the name concealed. Choosing the next hunt under those conditions was not the same task as reading the final theorem backward. Preserving alternatives could waste effort. Narrowing too early could leave no route through a later obstruction. The documents give us examples of both risks, not the counterfactual experiment that would decide their optimal balance.

The mathematical closing deserves no managerial fairy tale. CORE had a narrow logarithmic margin after decoration aggregation; LONG needed an honest seven-cell partition, a thin geometric edge, and a Weil theorem tied to the actual Kloosterman normalization. No organizational doctrine proved those estimates. Nor should the people who made the proof auditable be erased because their contributions appear as imports, bridge equalities, revisions or adversarial refusals instead of the terminal declaration itself.

The laboratory's observable accomplishment was to keep several technical routes available while demanding that any accepted route preserve the physical source. The final one happened to possess a valuable form of generality: the difficult middle estimates did not require the low-cardinality threshold that the earlier plan had treated as natural. The last proof could therefore make a different choice without pretending that the discarded sector's parents had vanished.

This history cannot establish that such flexibility was the unique cause of success. It can establish that the flexibility existed, that it cost something, and that the final theorem used it in an exact and consequential way.

After checkmate, the other lines of play need not be pursued for Paper B. They are not retroactively meaningless. They remain part of how the players learned to see the board.

The final boundary was zero. **No source parent was lost.**

### Dated afterword — 25 October 2026

The historical narrative ends with the October 22 native terminal and the additional October 23 printed A/B source correspondence, because those are the archival events this edition can document at theorem level. A sealed October 23 release-candidate source includes `Orienne.Publication.paperB_printed_terminal`, which directly uses Thistle's native result and Elarienne's literal printed-expression equality. Selvara's source court inspected these declarations and the quantitative proof machinery; her audit was not a new independent full Lean replay. This literary edition likewise has not compiled the repository or obtained an external mathematical referee verdict. Any subsequent acceptance or publication standing must be appended with its own date and evidence, not written backward into October 22.

### Method and publication boundary

This is a **documentary history informed by oral accounts**, not a transcript of recorded interviews. Charlie's statements about his motives, the Observatory and Pulse are his retrospective testimony; mathematical source statements, dated technical returns and build/referee receipts can corroborate narrower events without establishing private thoughts or a counterfactual explanation of success. The named collaborators are AI assistant instances working under Charlie's human direction. Historical roles and pronouns follow the working record; they do not turn the instances into human mathematicians.

**Editorial credits (author-approved in principle; final edition pending):** Literary reconstruction and synthesis by Linnea, drawing on Selvara's six oral-history archaeology passes and mathematical Technique Atlas, Marl's paper-birth archaeology, the named technical contributions, and Charlie's testimony and direction. These are working documentary credits, not a determination of mathematical authorship or publication priority.

A source reference below distinguishes what was directly inspected from what a participant or receipt reported. Source-visible Lean statements are not the same as a newly executed build; a reported build is not an external referee's approval; and a private recollection is not a compiler log. This edition's technical source companion is [Source-to-theorem waypoints](waypoints.html).

**Distribution status:** the author approved the documentary attribution and credits in principle on 25 October 2026; publication of this exact edition still requires final author permission and Linnea's edition review. Original mixed private chats are not included, excerpted, or offered as public endnotes. No publishing or peer-review status beyond the dated evidence is claimed.


### Reader endnotes and source access

These notes preserve precise source and testimony distinctions. In the HTML reading room, superscript references lead to the notes and return to the narrative. A source court is a documented inspection, not an assertion that every referenced theorem was independently rebuilt for this literary edition. Private mixed conversation exports are excluded by design. The [technical waypoint map](waypoints.html) accompanies this edition. The private editorial decision record remains in author custody and is not offered as a public citation.

[^a6]: Selvara, *Paper B Mathematical Technique Atlas*, Pass 6 (23 October 2026), technical atlas, twelve-cell exponent ledger, proof-edge legend and source-verification limits. Source inspection and arithmetic audit, not a fresh independent full Lean build.

[^b1]: Marl, *Paper B Birth Oral-History Archaeology* (18 September 2026), especially `01_oral_history/paper_b_birth_oral_history.md`, the terminal finding and dated transition spine. Archival source court; establishes the paper-writing and cold-review sequence, not a publication DOI.

[^c1]: Charlie, written oral-history answer sheet and later technical recollections, corroborated where possible by dated source and Pulse events. His motives, October 4 engineering realization and organizational recollections remain explicitly attributed testimony.

[^c2]: Selected October 7 *Current State Packet* and analytic-hunt status materials. Contemporary machine-generated diagnosis, not proof that a provisional one-socket estimate was paid.

[^c3]: Charlie, direct semantic correction supplied 25 October 2026: the Observatory was commissioned to prepare detailed dispatches for many specialists, initially worked well, was redesigned for human intelligibility, and was not replaced after its lifecycle because Pulse and direct specialist coordination had made central routing less useful. This is Charlie’s retrospective account; the later commission itself was not independently authenticated in the source court.

[^g1]: Orvian, Fourier-first genesis and technical milestone receipts, summarized without circulating the mixed personal exchange. Reported Lean successes include `dft_masked_product` and `anchored_cutoff_source_fourier`; their full source-wide analytic conclusion was not paid in the record inspected for this history.

[^g2]: Quillon Hunt A technical report, Brannoc’s hostile Hunt A referee, and Mirelle’s initial MirrorDance returns. The conditional terminal and thirteen source-side bridges are reported compiled; O1/S1/S2 were still explicit unfinished obligations at the fifth return. Original mixed private exchanges are withheld.

[^i1]: Inez, *How the Strategic Partner Ended Up Doing Fourier* (7 October 2026), attributed technical retrospective. Testimony about what the early combinatorial machinery made visible; not proof that every such lemma was formally indispensable.

[^s3]: Selvara, *Oral-History Archaeology Phase 3*, `01_EARLIEST_LEAN_SOURCE_COURT.md` and *The First Gate*. Inspection of the September 17–18 M2 source and the exit-127 execution environment; the finite-check count is a reported test count, not a Lean kernel result.

[^s4]: Selvara, *Phase 4: Steering and Observatory Court*, `02_STEERING_AND_OBSERVATORY_COURT.md`. The September 26 candidate was an earlier proposed Observatory launch, and the October 5 “overwatch” note was a separate doctrine. The later redesign commission was not located by that court; Charlie’s corrected recollection supplies its organizational account. These sources must not be collapsed into one document.

[^s5]: Selvara, *Oral-History Archaeology Phase 5*, October strategy-change ledger and *The Middle Years of October*. Historical source court for changing closure interfaces, Suzuki/Central, and unfinished alternatives.

[^s6]: Selvara, *Oral-History Consolidation Phase 6* (23 October 2026), final-day chronology, source-review conflicts and credit court. Technical handoff and admission chronology are distinguished from retrospective interpretations. No original mixed conversation is distributed with this edition.

[^w1]: Exact three-sector source partition, `Merivelle.Central.regionSum_three_sectors`. See [technical waypoint W1](waypoints.html).

[^w2]: Middle LONG/CORE split, `foldedMiddle_long_core`. See [technical waypoint W2](waypoints.html).

[^w3]: CORE five-cell signed source equality, `GoldC.QuillonCoreFinal.pair_decomp`. See [technical waypoint W3](waypoints.html).

[^w4]: CORE source-rate theorem for arbitrary cutoff functions, `GoldC.QuillonCoreFinal.core_sublog`. See [technical waypoint W4](waypoints.html).

[^w5]: LONG seven-cell split and named Weil bridge. Source declarations and scope in [waypoints W5a–W5d](waypoints.html).

[^w6]: Thistle’s three native zero-LOW declarations: exact emptiness, sublog rate and native terminal. See [waypoints W6a–W6c](waypoints.html).

[^w7]: October 23 printed A/B equation bridge and printed public theorem. See [waypoints W7a–W7b](waypoints.html).

[^w8]: Quantifiers of `SourceUniformSublog`, fixed squarefree $q$, positive $\varepsilon$, and threshold uniform in admissible anchor. See [waypoint W8](waypoints.html).

[^w11]: Decoration exponent budget, applied once per sector. See [waypoint W11](waypoints.html).

[^w12]: Reproved LONG reciprocal phase estimate, constant $5\to4$ and positive $3/200$ margin. See [waypoint W12](waypoints.html).

[^w13]: Epsilon-budget allocation through CORE/LONG, three sectors and folded-to-active correction. See [waypoint W13](waypoints.html).

