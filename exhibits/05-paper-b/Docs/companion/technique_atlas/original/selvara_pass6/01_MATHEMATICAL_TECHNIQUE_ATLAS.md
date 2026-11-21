# Paper B: a mathematical technique atlas

**Selvara / FACET · Pass 6 synthesis · 23 October 2026 release-candidate cut**  
**Scope:** source-bound mathematical exposition of `PAPERB_PRINTED_TERMINAL_RC_R0003_TRIMMED_20261023.zip`. The original source has not been modified. This atlas does **not** repeat the full Lean build or replace the independent referee. “Direct” dependencies refer only to named uses visible in inspected proof bodies; the transitive elaborated Lean constant DAG remains unaudited. Classical attribution is descriptive, not an external originality or priority determination.

**Notation:** \(\Lambda=\log h\), \(e(t)=\exp(2\pi i t)\), \(q\) a fixed positive squarefree modulus, and \(a,b\) compatible reduced endpoints. The proof's source often uses \(H=h/D\), where \(D\) is the product of a decoration's primes; this is *not* the global height \(h\). All mathematical descriptions below retain the source's exact guards, even where the exposition abbreviates them. A **physical cell** means a sum over an actual *source-selected* parent population, for a fixed decoration \(d\), including the signed folded row and original weights—not a pointwise estimate on an individual pair.

## Reading map

| Part | Mathematical question | Main proof layer |
|---|---|---|
| 1. One public theorem, two proof branches | What quantity is controlled, and is it literally the manuscript's? | Printed terminal / F-01 / native terminal |
| 2. Finite arithmetic and Euler products | How do literal singular series become kernel formulas without approximation? | F-01, Boolean dictionary, divisor expansion |
| 3. Analytic engines | Where is cancellation actually purchased, and with which hypotheses? | Suzuki, Karatsuba, Vinogradov, Vaaler, Kloosterman |
| 4. Twelve physical cells | Why does each arithmetic region require a different technique? | CORE 5, LONG 7 |
| 5. Quantitative economy | Why do all savings survive weights, constants, and cutoffs? | Cell→outer→decoration→sublog→printed |
| 6. Reusable mathematics and standing | What is novel about the *assembly*, and what is not established? | Mechanism / dependency / source court |

---

## 1. Two enormous proof branches meet in one line

The public theorem (`Orienne/Publication/PaperBPrintedTerminalR0001.lean:10–28`) is an *eventual* estimate: for every fixed squarefree \(q>0\) and every \(\varepsilon>0\), there exists \(h_0\) such that all eligible \(h\ge h_0\), all reduced anchors \(a,b\), their congruence \(a+h\equiv b\pmod q\), and the requisite parity condition satisfy

\[
\left|A^{\rm printed}_{1,q}(a;h)-B^{\rm printed}_{1,q}(a,b;h)\right|
\le\varepsilon\log h.
\tag{1}
\]

Its proof body makes *two* named substantive calls. One obtains the native estimate from `Thistle.LOW.paperB_terminal_via_empty_low`. The other rewrites the printed difference using `Elarienne.F01B.printedA_sub_printedB_eq_manuscriptKernels`. The final application is then the already supplied native inequality.

This means the result has two logically distinct branches:

\[
\begin{aligned}
\textbf{semantic branch:}\quad
&A^{\rm printed}_{1,q}-B^{\rm printed}_{1,q}
 =A^{\rm kernel}_{1,q}-B^{\rm kernel}_{1,q},\\
\textbf{analytic branch:}\quad
&|A^{\rm kernel}_{1,q}-B^{\rm kernel}_{1,q}|
 \le\varepsilon\log h.
\end{aligned}
\tag{2}
\]

The semantic branch is not a rebranding of terms. It constructs the printed Euler quantities independently, proves that the infinite products exist, checks exact small-prime factors, and matches the centered arithmetic sums. The analytic branch carries difficult signed-source cancellation through a series of exact source-preserving transformations. A short terminal theorem *cannot* make one branch do the work of the other.

The two central forms of exactness recur throughout:

1. **Equality of represented objects**: printed product vs native kernel; copied vs curated source; original unfolded source vs a folded signed row.
2. **Sufficient analytic control**: a genuine small power of \(\log h\) saved after every factor, with a threshold quantified uniformly in the permitted endpoint choices.

These are the main organizing species of the atlas. Neither can substitute for the other.

### 1.1 The exact source is preserved across two partitions

The native Central source first receives an exact cardinality split

\[
\boxed{\mathrm{CENTRAL}=\mathrm{LOW}+\mathrm{MIDDLE}+\mathrm{HIGH}}.
\tag{3}
\]

For every parent \(e\) in the original quarter-parent set, the tests are \(|e|<J_{\rm low}\), \(J_{\rm low}\le|e|<J_{\rm high}\), and \(J_{\rm high}\le|e|\). There is no missing equality case. Source: `Merivelle.Central.regionSum_three_sectors` (`PaperB/Gate3/CentralTransfer/ThreeSectorConsumer.lean:84–92`).

Then the physical middle sector is divided by a ratio guard and its logical complement:

\[
\boxed{\mathrm{MIDDLE}=\mathrm{LONG}+\mathrm{CORE}},
\quad \mathrm{LONG}:=\bigl(s^{1+\delta}<r\bigr)\lor\bigl(r^{1+\delta}<s\bigr).
\tag{4}
\]

The second identity is `foldedMiddle_long_core` (`MiddleLongCoreConsumer.lean:19–26`). The two LONG orientations are disjoint at positive \(\delta\). Neither split changes the underlying signed `foldRow`, original quarter-parent cutoff, decoration, or proper ordered orientation.

Finally, `GoldC.QuillonCoreFinal.core_sublog` and `GoldC.QuillonLongFinal.long_sublog` hold for **arbitrary** cutoff functions \(J_{\rm low},J_{\rm high}:\mathbb N\to\mathbb N\) (with the surrounding terminal imposing the order needed for the three-sector identity). At the final source specialization, \(J_{\rm low}\equiv0\). Since no natural-cardinality parent has \(|e|<0\), LOW is identically zero. Every formerly low-cardinality parent is now in MIDDLE, where the preexisting CORE/LONG estimates already apply. The terminal selects \(\delta=1/4\).

The disappearance of LOW is an exact change of partition, **not** a claim that its former physical contributions vanished.

---

## 2. A primewise calculation becomes a literal theorem

For a finite displacement set \(H\), define the number of residues it occupies modulo \(p\),
\(\nu_p(H)=|H\bmod p|\). The frozen singular series is

\[
\mathfrak S_q(H)=\prod_{p\nmid q}
\frac{1-\nu_p(H)/p}{(1-1/p)^{|H|}}.
\tag{5}
\]

The product is infinite. It is **not** automatically convergent or nonzero merely because each displayed factor looks elementary. The independent formal definitions are `occupiedResidues`, `printedLocal`, and `printedRestrictedSingularSeries` (`Orienne/Publication/F01PrintedLiteralBridgeR0001.lean:13–31`); the frozen TeX defines the same mathematical target (`MANUSCRIPT/paper_b_frozen.canonical.tex:51–63`). Primes dividing \(q\) contribute the exact inactive factor 1.

The manuscript's admissible interior set and count are

\[
I_q(a;h)=\{0<y<h:(a+y,q)=1\},\qquad N_q(a;h)=|I_q(a;h)|.
\tag{6}
\]

Its two level-one quantities have the literal shapes

\[
\begin{aligned}
A_{1,q}&=\sum_{y\in I_q(a;h)}
 \left(\frac{\mathfrak S_q(\{0,y,h\})}{\mathfrak S_q(\{0,h\})}-1\right),\\
B_{1,q}&=\sum_{y\in I_q(a;h)}(\mathfrak S_q(\{0,y\})-1)
+\sum_{y\in I_q(a;h)}(\mathfrak S_q(\{h,y\})-1).
\end{aligned}
\tag{7}
\]

These are finite sums of *infinite* Euler products. Their precise normalization is necessary for the cancellation problem.

### 2.1 The A branch: dividing Euler products legally

At an active prime, define

\[
\rho_p(h,y)=
\frac{1-\nu_p(\{0,y,h\})/p}{1-\nu_p(\{0,h\})/p}
\cdot\frac1{1-1/p}.
\tag{8}
\]

Primewise arithmetic gives the formal local quotient identity. To multiply it over primes and identify it with the quotient of two full Euler products, three *different* obligations have to be paid:

- The endpoint product converges. For sufficiently large primes its local factor becomes \(c_1(p)=p(p-2)/(p-1)^2=1-(p-1)^{-2}\), whose deviation from 1 is absolutely summable over primes.
- Every active endpoint factor is positive. For \(p\ge3\), the pair occupies at most two residues. For \(p=2\), parity and exclusion by \(q\) are treated explicitly.
- The endpoint **infinite product** is nonzero. Nonzero factors are insufficient in general: the proof combines absolute deviation control with the appropriate infinite-product nonvanishing theorem before applying the product-quotient law.

The triple product's convergence is handled with a high-prime ratio and a finite exceptional correction. The file then proves the primewise quotient for every *active* prime, including 2 and 3, and writes the low factors as an actual finite product (`printed_quotient_eq_occupied_euler`, roughly F-01 lines 453–500). No \(O_q(1)\) simplification is made at this equality stage.

The exact admissibility identity is

\[
\sum_{y\in I_q(a;h)}(R_y-1)
=\sum_{0<y<h}{\bf1}_{(a+y,q)=1}R_y-N_q(a;h).
\tag{9}
\]

`printed_admissible_count_eq` proves the translated finite-cardinality statement; `printedA1Literal_eq_weighted` applies the Boolean-index indicator to the actual summand; `printedA1Literal_eq_manuscriptA1Kernel` finishes the A bridge (`F01:539–617`). This avoids the tempting but invalid substitution of the mean density for the exact finite count.

The high-prime factors later admit a four-case divisor-selector expansion, with \(p\mid h\), \(p\mid y\), and \(p\mid(h-y)\) treated separately. Its two main baselines are

\[
c_0(p)=\frac{p(p-3)}{(p-1)(p-2)},\qquad
c_1(p)=\frac{p(p-2)}{(p-1)^2}.
\tag{10}
\]

The multiplicative selectors \(1+1/(p-2)\) or \(1+1/(p-3)\) appear *only in their true divisibility cases*. That algebra is the gateway from the anchored Euler product to two-dimensional divisor constraints, not an analytic estimate of them (`PaperB/FixedQ/DivisorExpansion.lean:33–83,1581–1606`).

### 2.2 The B branch: a finite numerator and an infinite subtraction

The free endpoint pair uses, for active \(p\ge5\), the exact factor

\[
F_p(\{0,y\})=c_1(p)\left(1+\frac{{\bf1}_{p\mid y}}{p-2}\right),\qquad p\ge5,\ p\nmid q,
\tag{11}
\]

where the display isolates only the *high-prime selector*; the rigorous identity includes a fixed high-prime constant and the explicit primes 2 and 3. Multiplicative expansion of the selector gives a squarefree-divisor series with coefficient \(\eta_q(e)\). The corresponding normalization theorem is exact:

\[
\boxed{C_{f,q}\sum_{e\ge1}\frac{\eta_q(e)}e=1.}
\tag{12}
\]

This has two separate roles. First, the sum is absolutely convergent, so regrouping with the fixed high-prime product is legitimate. Second, the value is **exactly** 1, so it can be subtracted from the literal row count without an error term. It follows that the source-centered one-boundary expression takes the form

\[
\boxed{S_{q,a}(h)=C_{f,q}\sum_{e\ge1}\eta_q(e)
\left(R_e(a;h)-\frac{N_q(a;h)}e\right).}
\tag{13}
\]

The first numerator rearrangement is finite: if \(e\ge h\), no such \(e\) divides a positive interior displacement \(y<h\), so the actual constrained row mass \(R_e(a;h)\) vanishes. **But the centering term** \(-N_q(a;h)/e\) **does not vanish** for \(e\ge h\). Formula (13) is therefore a genuinely infinite, absolutely controlled centered series, not a finite sum disguised by formal notation. Losing this tail would destroy the exact B bridge.

The second boundary is not justified by copying the first endpoint's proof: source reflection sends \(y\mapsto h-y\), preserves the interior endpoints, and uses \(a+h\equiv b\pmod q\) to transform the relevant coprimality indicator. It must respect both boundary terms, not merely the formal shape of the singular series. `printedB1Literal_eq_manuscriptB1Kernel` completes this step (`F01:1432–1468`).

### 2.3 Boolean contraction and CRT: the finite arithmetic basement

The older endpoint dictionary contains its own striking exact identity. Two commuting Möbius transforms operate on different finite Boolean coordinates, with endpoint evaluation and endpoint zeta inversion satisfying a contraction law schematically of the form

\[
Z_E M_E M_T=M_T\operatorname{ev}_E.
\tag{14}
\]

Its source representation produces the completed/free normalization dictionary and exact finite-admissibility counts. The proof uses finite-set algebra, Möbius inversion, and residue arithmetic rather than a limit passage. The equation is a valuable foundational mathematical object in this estate.

**Dependency caution:** the final printed terminal consumes the F-01 bridge and native terminal. The presence of the M1/M2 Boolean modules in the import closure does not, by itself, establish that each M1/M2 lemma is a transitive proof-term dependency of the printed terminal. The atlas marks that boundary rather than fabricating a kernel DAG.

---
## 3. Four analytic engines, four different sources of control

The analytic branch needs bounds on *signed, clipped, source-selected* sums. Its tools are classical in ancestry, but their roles are more specific than their names suggest. Vaaler constructs a safe pointwise majorant; Suzuki controls an oscillating reciprocal phase; Kloosterman bounds control arithmetic completion; Parseval, Abel, Ramaré, Vaughan, Rankin and roughness convert those inputs to estimates on actual parent populations. None supplies a blanket theorem covering every region.

### 3.1 Suzuki: when the reciprocal phase changes scale

The target sharp sum is

\[
S(Y,\vartheta;N,U)=\sum_{N<m\le U}e\!\left(\frac{Y}{m+\vartheta}\right),
\quad Y\ge2,\quad N\ge1,\quad0\le\vartheta\le1,\quad U\le2N.
\tag{15}
\]

The proved `GoldB.Iface.ShiftedSuzukiCore` is uniform in \(Y,N,\vartheta,U\): with constants \(C\ge0,c>0\) independent of those variables,

\[
\boxed{|S|\le C\left[N\exp\left(-c\frac{(\log N)^3}{(\log Y)^2}\right)+\frac{N^2}{Y}\right].}
\tag{16}
\]

The two summands on the right are not arbitrary conveniences: they arise from *different proofs*. At \(N\ge4096\), the disjunction

\[
\log Y<\tfrac32(\log N+\log2)
\quad\text{or}\quad
\log Y\ge\tfrac32(\log N+\log2)
\tag{17}
\]

routes to low-\(Y\) or high-\(Y\). Equality is explicitly in the second branch. For smaller \(N\), the elementary \(|S|\le N\) bound is absorbed into the uniform statement after enlarging a fixed coefficient (`GoldB/Suzuki.lean:190–299`).

**Low \(Y\): phase increments and discrete Kusmin–Landau.** The logarithmic condition implies \(Y<N^2/2\). With \(L=N+1\), \(T=Y/L\), the reciprocal phase increment can be moved into \((0,1)\) by adding a linear integer phase. The complex denominator identity

\[
\frac1{e(t)-1}=-\frac12-\frac i2\cot(\pi t),\qquad0<t<1
\tag{18}
\]

and monotonicity of the cotangent support a telescoping/summation-by-parts argument. It produces \(|S|\le 8L/T\le16N^2/Y\) in its range. No Vinogradov mean-value theorem is used in this branch (`GoldC/VKRegimes.lean`, `GoldB/QuillonLowY.lean`).

**High \(Y\): many useful derivative orders, not one lucky derivative.** Set \(P=N\), \(t=\log Y/\log P\), and \(k=\lfloor26t\rfloor\). For \(f(x)=Y/(x+\vartheta)\),

\[
\frac{|f^{(j)}(x)|}{j!}=\frac{Y}{(x+\vartheta)^{j+1}}.
\tag{19}
\]

The Lean source constructs a finite set of selected orders \(J_s\subseteq\{1,\ldots,k\}\), with \(|J_s|\ge k/39\), that obey the specified two-sided derivative windows. A top-derivative bound controls Taylor's remainder. Those are the exact hypotheses of the Karatsuba lemma (`GoldB/QuillonSelectedOrders.lean`, `GoldB/QuillonDerivativeWindow.lean`). One selected-order module labels itself as a reconstruction of a missing original supplier; preserve that historical provenance without confusing it with a gap in its current Lean statement.

**Karatsuba: averaging + polynomialization + mean values.** The abstract lemma controls a sharp partial interval through a shift average, Taylor expansion, a polynomial double sum, Hölder, and uniform Vinogradov counts. It returns

\[
|S_f|\le CP^{1-\gamma/k^2},
\tag{20}
\]

with \(\gamma>0\) depending on the fixed structural window constants, not on growing \(k\), \(P\), the phase or the clip. Its double sum contains distinct factors: a Vinogradov solution count \(J_c\) and products of \(\mathfrak S_j\). Selected derivative orders make the latter product sufficiently small; invoking VMVT without that bridge does not prove (20).

The relevant proved mean-value input is `GoldB.VinoMain.vmvt`, with \(\kappa=k(k+1)/2\), \(\Delta_\tau=\kappa(1-1/k)^\tau\) and explicit rapidly growing \(D_v(k,\tau)\):

\[
J_c(k,k\tau,[1,N])\le D_v(k,\tau)N^{\,2k\tau-\kappa+\Delta_\tau}.
\tag{21}
\]

This is not a generic slogan about Vinogradov: it is a quantified, order-uniform supplier that the Karatsuba parameter ledger actually consumes (`GoldB/VinoMain.lean`, `GoldB/Params.lean`, `GoldB/KaratsubaMain.lean`). The source eventually chooses \(k\le26\log Y/\log N\), so

\[
\frac{\gamma}{k^2}\log N\ge\frac{\gamma}{26^2}
\frac{(\log N)^3}{(\log Y)^2}.
\tag{22}
\]

The famous-looking `676` in the exponent is just \(26^2\), the cost of choosing orders at the required density. This is how the high-\(Y\) branch purchases the first term in (16).

**Dual use.** The same GoldB Suzuki result later enters two distinct consumer locations. It pays the Suzuki terminal input, but a residue-class translation \(\vartheta=\rho/Q\), \(Y'=|Y|/Q\) also supplies the physical CORE R and LONG RL cells. That latter application additionally needs exact arithmetic-progression reindexing, conjugation for negative numerator, Abel summation for variable Fourier coefficients, and source-specific coefficient bounds. A proved universal-looking exponential sum is not enough until its *physical* variable and sign are correct.

**VK terminology warning:** a separate `GoldC.VKCore.UniformVinogradovEstimate` is itself a proposition passed as a hypothesis to some conditional results. It is not the unconditional GoldB proof of Suzuki. The atlas lists those mechanism families separately and does not mark that conditional supplier as independently discharged simply because “VK” appears in both.

### 3.2 Vaaler: pointwise positivity without magic signed cancellation

The original sawtooth has jumps at integers. One cannot replace its sharp source value everywhere by a smooth Fourier expression and ignore the jump points. The positive Vaaler approximation uses a controlled finite trigonometric polynomial with a **nonnegative error envelope**, retained at those integer positions. This is the Gold A/positive pointwise input in the source campaign.

The distinction is categorical: a pointwise nonnegative approximation majorant controls the *cost of approximation*. It does not imply \(o(\log h)\) cancellation after the source selects weighted CRT classes, sign-sensitive orientations, or decoration subsets. The terminal's Central campaign was necessary precisely because source-specific signed cancellation could not be inferred from the Vaaler inequality alone (`PaperB/Gate3/SuzukiCentralOnly.lean` and Pass 3 Vaaler supplier anchors).

### 3.3 Weil–Estermann: a complete sum with a price tag

For the completed Kloosterman sum in modulus \(s\), the source pays the general-modulus bound

\[
\boxed{|K_s(a,b)|\le\tau(s)\sqrt{s\,\gcd(a,b,s)}.}
\tag{23}
\]

That theorem is itself a composite: prime-level estimates drawing on Carlitz/Stepanov machinery; prime-power analysis by stationary-phase and reduction for both unit and nonunit coefficients; and CRT multiplication with explicit control of the conductor gcd. The factors \(\tau(s)\) and \(\gcd(a,b,s)\) are **not thrown away** under a vague \(s^{1/2+o(1)}\).

For a squarefree source modulus \(s=\prod_{p\in P}p\), \(\tau(s)=2^{|P|}=4^{|P|/2}\). The frequency surcharge can be bounded in the form

\[
K_W(c)=4^{|P|/2}s^{1/2}
\left(\prod_{p\in P,\,p\mid c}p\right)^{1/2}.
\tag{24}
\]

The actual coupled Cauchy calculation distinguishes \(y=y'\), \(y\ne y'\) but \(y\equiv y'\pmod s\), and general off-diagonal pairs. In the latter case, \(c\) contains an inverse difference and the gcd is split into a base-frequency factor and a pair-difference factor. A weighted harmonic gcd moment then sums the latter through a divisor expansion. **After square-rooting Cauchy, a gcd quarter-power remains.** It is controlled by another harmonic mode-frequency bound, not erased (`GoldC/QuillonLWeil.lean`, `GoldC/QuillonLWeilB.lean`).

An apparently small normalization issue is indispensable. The formal source proves

\[
\mathrm{GoldC.QuillonKl.K}(s,a,b)
=\mathrm{GenKloosterman.kSum}(s,b,a)
\tag{25}
\]

*with the arguments reversed*, by definitional equality, before applying the general-modulus bound (`Orienne/CSC3/WeilQuillonBridgeR0002.lean:7–23`). In `GoldC.QuillonLongFinal.long_sublog`, the theorem is locally stated under named `WeilHyp`; only the Orienne bridge supplies that hypothesis and transports the copied source into the native source. This makes “Weil is paid” a precisely verifiable statement at the final terminal, not a reliance on a suggestive theorem name.

### 3.4 Why the two Kloosterman strengths cannot simply be substituted

CORE W′ uses an elementary fourth-moment/CRT majorant of the rough shape

\[
|K_s(b,c)|\le3^{|P|/4}s^{3/4}
\left(\prod_{p\in P,\,p\mid c}p\right)^{1/4}.
\tag{26}
\]

CORE's range \(0<\delta<1/3\) makes this sufficient when a suitable prime packet is present. LONG-right can approach a factorization where its cofactor is only about \(s^{1/2}\), so CORE's method cannot be ported without new arithmetic and a new range calculation. The eventual LONG W′ method improves the modulus power to \(s^{1/2}\) through (23), but pays different divisor and gcd costs and still fails to deliver fixed savings at the precise square-root edge.

The resolution was not a miraculous universal estimate. The proof draws a *boundary between two methods*: it counts the too-short edge by weighted geometric mass and reserves Weil for the nonedge with sufficient room. That distinction drives two of the seven LONG cells.

---

## 4. Twelve disjoint physical cells, not twelve unrelated estimates

The physical pair source contains original decorated prime subsets \(d\), proper ordered parent partitions \((B,C)\), reduced height \(H=h/\prod d\), positive arithmetic weights \(\omega(B)\omega(C)\), and a signed `foldRow` combining the saw and selected CRT-digit potential. Each cell is a *mask on these actual contributions*. The proof does not replace the physical coefficient family by arbitrary bounded coefficients and then infer cancellation for the source.

`QuillonCoreFinal.pair_decomp` proves a five-way identity using `split5`. `QuillonLongFinal.long_pair_decomp` proves a seven-way identity using `split7`. The latter's `split7` is literally a propositional case split on a sequence of guards; every surviving original term belongs to one cell, and no term is counted twice (`GoldC/QuillonLongFinal.lean:27–87`). This exactness is what makes it legitimate to take the sum of the bounds.

### 4.1 The five CORE cells

| Cell | Actual test / source geometry | Mechanism | Per-decoration physical bound |
|---|---|---|---|
| W | B contains a prime packet between \(X_p\) and \(\lfloor s^{u_0}\rfloor\) | Ramaré extraction, coupled Cauchy, elementary Kloosterman \(s^{3/4}\), four physical Fourier rows | \(\Lambda^{-80}\) |
| C | No W packet; B long relative to C in the CORE geometry | Parseval on one cofactor range, Vaughan/prime-sum on another, Rankin exceptional tail | \(\Lambda^{-15}\) |
| R | No W/C; C has the reciprocal-progression packet | Ramaré on C; reciprocity; Suzuki AP sum; Abel for coefficient variation | \(\Lambda^{-75}\) |
| ResA | No eligible W/C/R packet | Two-factor roughness; direct weighted mass | \(\Lambda^{1/10}\) |
| Band | Near diagonal, after exclusions | Weighted interval counting in a narrow logarithmic band | \(\Lambda^{998/1000}\) |

The **dominant CORE cell is Band**, not W or R. Its source band has logarithmic width approximately \(\Lambda^{199/200}\). Two roughness/counting overheads contribute \(1/4000\) each, giving the pre-absorption exponent

\[
\frac{199}{200}+\frac1{4000}+\frac1{4000}
=\frac{1991}{2000}.
\tag{27}
\]

There is only \(1/400\) exponent left to absorb a fixed constant before the physical target \(499/500\). A very strong \(\Lambda^{-80}\) estimate on W cannot change Band's exponent; different disjoint regions are summed, not multiplied.

### 4.2 LONG-left: two genuine ports

LONG tests whether \(s^{1+\delta}<r\) (left) or \(r^{1+\delta}<s\) (right). LONG-left is split between:

- **WL**: an eligible B prime packet; the CORE W′ architecture is ported with exact LONG-specific cutoffs. It gives \(\Lambda^{-80}\).
- **CL**: no WL packet; the CORE Parseval/Vaughan architecture carries over, with its own revised range hypotheses. It gives \(\Lambda^{-15}\).

Neither statement is that CORE's theorem can simply be applied to every LONG parent. The physical masks differ, and the source explicitly re-proves the interval and parameter conditions. The result is reusing mechanisms, not waiving hypotheses.

### 4.3 LONG-right: five disjoint reasons

The other orientation, \(r^{1+\delta}<s\), has a richer decision tree:

| Cell | Routing condition after earlier exclusions | Why it pays | Per-decoration physical bound |
|---|---|---|---|
| RL | C has a Suzuki-compatible R packet | Same reciprocal AP mechanism as CORE R, but with weaker log threshold **4** rather than **5** | \(\Lambda^{-75}\) |
| ManyL | No R packet, and \(|C|\) above a growing threshold \(K_0\) | Rankin suppresses many-prime-factor mass | \(\Lambda^{-50}\) |
| EdgeL | Few C factors; \(r\) near \(s^{1/2}\) | **No cancellation:** direct weight of an exceptionally thin interval | \(\Lambda^{19/20}\) |
| ResL | Outside EdgeL; no B W′ packet | B and C are both rough; count residual mass | \(\Lambda^{7/10}\) |
| WRL | Outside EdgeL; B W′ packet available | Weil–Estermann with Cauchy, gcd moment and all four source Fourier rows | \(\Lambda^{-80}\) |

The LONG-right no-packet parents are thus explicitly assigned to ResL, not silently presumed to possess a W′ prime. The proof's seven-way identity is unaffected by which methods are subsequently used to bound them.

### 4.4 EdgeL versus WRL: the geometric pivot

The source central gate gives \(r\ge s^{1/2}\); on EdgeL the additional cutoff is

\[
\boxed{s^{1/2}\le r<s^{1/2+3\eta}},\qquad \eta=\Lambda^{-1/10}.
\tag{28}
\]

That width is \(O(\eta\log s)=O(\Lambda^{9/10})\) on a logarithmic scale. Missing the R packet also makes the complementary factor rough. The exponent budget is exactly

\[
\underbrace{1/4000}_{\rm rough\ overhead}+
\underbrace{1/40}_{\rm inverse\ epsilon\ overhead}+
\underbrace{1/100}_{\rm interval\ weight}+
\underbrace{9/10}_{\rm thin\ width}
=\frac{3741}{4000}<\frac{19}{20}.
\tag{29}
\]

The gap \(59/4000\) pays the fixed constants. **No Weil estimate appears in this cell.**

Outside EdgeL, \(r\ge s^{1/2+3\eta}\). If B has a W′ prime \(y\le s^\eta\), extraction leaves a cofactor with room \(\gtrsim s^{1/2+2\eta}\), sufficient for the coupled Weil/Cauchy inequality. After the factor and mode accounting, each fixed outer factor receives a \(\Lambda^{-95}\) bound; the outer sum spends \(\Lambda^{10}\), and constant absorption yields \(\Lambda^{-80}\) (`GoldC/QuillonLRP.lean:156–244,385–566`).

The geometric lesson is sharp: *the arithmetic method is strongest just away from the region where there is too little room for it, while the too-short region is already small enough to count*. EdgeL and WRL are complementary, not competing solutions to the same set.

### 4.5 RL's unassuming but indispensable constant change

The CORE R argument requires a lower short-factor log condition with constant 5. The looser LONG gate cannot supply that exact condition; it supplies 4. The Lean proof rebuilds the eventual Suzuki exponent argument for 4. What matters is that

\[
3\sigma_0-\frac3{200}-2
=3\left(\frac23+\frac1{100}\right)-\frac3{200}-2
=\frac3{200}>0.
\tag{30}
\]

Replacing \(5^3\) by \(4^3\) alters a multiplicative coefficient but not the positive logarithmic exponent. That is enough to regain an eventual \(\Lambda^{-200}\) step under the honest LONG hypothesis, without pretending the stronger CORE parameter inequality transfers unchanged (`GoldC/QuillonREv.lean`; `GoldC/QuillonLR.lean`).

### 4.6 The twelve-cell ledger is an algorithm for where to stop asking for cancellation

It is mathematically tempting to see the negative-exponent cells as sophisticated and the positive-exponent cells as weak. The source suggests a better classification:

- **Extract oscillation** when there is a long variable, a prime packet, and a source-compatible Fourier/progression interface.
- **Pay by small measure** when that extraction is unavailable *but the support occupies a thin strip*.
- **Pay by arithmetic sparseness** when missing prime packets force roughness or an unusually large number of factors.

This triage is part of the proof's design. Proving separate estimates becomes possible because every source parent first receives a *legal* routing condition.

---
## 5. The quantitative economy: where every logarithmic saving goes

The twelve-cell proof is a collection of *eventual inequalities* with explicit quantifiers, not simply a display of negative powers. The quantitative route has five layers:

\[
\boxed{\text{fixed outer factor}\;\to\;\text{physical cell}\;\to\;
\text{fixed decoration sector}\;\to\;\text{sum over decorations}\;\to\;
\varepsilon\log h.}
\tag{31}
\]

Each arrow can spend a different kind of budget. The first might use a true cancellation estimate; the second often pays \(\Lambda^{10}\) from the outer weight; the fourth pays a small polylogarithmic decoration factor; the last absorbs fixed constants into a remaining positive power of \(\Lambda\).

### 5.1 Complete local exponent ledger

The table uses exact rationals. “Before constants” is the exponent after the stated outer losses but **before** relaxing by the positive power used to absorb fixed constants. These costs come from the physical theorem proof bodies, not from a new numerical experiment.

| Sector | Cell | Fixed-factor input | Outer exponent cost | Before constants | Physical exponent | Absorption slack |
|---|---|---:|---:|---:|---:|---:|
| CORE | W | −95 | +10 | −85 | −80 | 5 |
| CORE | C | −30 | +10 | −20 | −15 | 5 |
| CORE | R | −90 | +10 | −80 | −75 | 5 |
| CORE | ResA | direct mass | — | 51/2000 | 1/10 | 149/2000 |
| CORE | Band | direct mass | — | 1991/2000 | 499/500 | 1/400 |
| LONG | WL | −95 | +10 | −85 | −80 | 5 |
| LONG | CL | −30 | +10 | −20 | −15 | 5 |
| LONG | RL | −90 | +10 | −80 | −75 | 5 |
| LONG | ManyL | −100 | +40 | −60 | −50 | 10 |
| LONG | EdgeL | direct mass | — | 3741/4000 | 19/20 | 59/4000 |
| LONG | ResL | direct mass | — | 1051/2000 | 7/10 | 349/2000 |
| LONG | WRL | −95 | +10 | −85 | −80 | 5 |

The raw `ManyL` cost is \(\Lambda^{-100}\) from its Rankin penalty, plus \(\Lambda^{30}\) in the cubic moment and \(\Lambda^{10}\) in outer mass. The direct mass estimates (`ResA`, `Band`, `EdgeL`, `ResL`) are already aggregate weighted estimates, so one must *not* add the same outer \(+10\) again. This single distinction would change the central margin disastrously if handled incorrectly.

### 5.2 Disjoint sums take the maximum exponent—not the sum

From the exact five-cell and seven-cell identities, the triangle inequality gives, for sufficiently large \(\Lambda\),

\[
\left|\mathrm{CORE}_d\right|
\le \sum_{c\in \mathrm{CORE}}\Lambda^{e_c}
\le 5\Lambda^{499/500},
\tag{32}
\]

\[
\left|\mathrm{LONG}_d\right|
\le \sum_{c\in \mathrm{LONG}}\Lambda^{e_c}
\le 7\Lambda^{19/20}.
\tag{33}
\]

The adjective *signed* matters: the source identities are exact before taking absolute values, and the triangle inequality is spent only after each population has been assigned a method. If we wrongly multiplied the Band and ResA bounds, or charged two unrelated cell exponents additively, we would manufacture a loss the proof does not contain.

### 5.3 The decoration sum is a different proof operation

The physical source is the sum over allowed finite prime decorations \(d\), weighted by \(V_h(d)\ge0\). `GoldC.QuillonCopyG.decoration_mass_le_loglog_pow` bounds the total weight by a fixed-degree power of \(1+\log\Lambda\). In the source's bound this can, eventually, be paid by just \(\Lambda^{1/1000}\). This happens **once per complete CORE or LONG sector**, not once per physical cell and again at the end.

The source spells out the constants and converts (32)–(33) into:

\[
\boxed{|
\mathrm{CORE}|
\le1280e^{10}\Lambda^{999/1000},\qquad
|
\mathrm{LONG}|
\le1792e^{10}\Lambda^{951/1000}.}
\tag{34}
\]

Those are the effective forms used in the final quantified \(o(\log h)\) proofs (`GoldC/QuillonCoreFinal.lean:118–end`; `GoldC/QuillonLongFinal.lean:148–end`). Because the exponents are less than one, the normalizations \(|\mathrm{CORE}|/\Lambda\) and \(|\mathrm{LONG}|/\Lambda\) tend to zero for every *fixed* allowable \(q,\delta\).

The margins are unequal. CORE's last positive saving is only \(1/1000\); LONG has \(49/1000\). The dominant local estimates are Band and EdgeL, respectively. The enormous negative exponents from some oscillatory cells do not improve the final rate once the maximum positive exponent is fixed.

### 5.4 “Eventually” is implemented as an actual threshold

The definition `SourceUniformSublog S` has quantifier order

\[
\forall\,q>0\ \mathrm{squarefree},\ \forall\,\varepsilon>0,\
\exists H_0,\ \forall a,h\quad
\bigl[\text{source conditions, }h\ge H_0\bigr]
\Rightarrow |S(q,a,h)|\le\varepsilon\log h.
\tag{35}
\]

The source includes coprimality of \(a\) with \(q\), positivity, and the original parity implication. The key fixed-parameter distinction: \(H_0\) may depend on \(q,\delta,\varepsilon\); once chosen it is uniform in the admissible anchor and in the selected cutoff functions.

For CORE the proof takes three logarithmic thresholds: \(\Lambda_1\) from the five-cell physical rate, \(\Lambda_2\) from absorbing \((1+\log\Lambda)^8\le\Lambda^{1/1000}\), and \(\Lambda_3\) from

\[
\frac{1280e^{10}}{\varepsilon}\le\Lambda^{1/1000}.
\tag{36}
\]

It sets \(\Lambda_*=\max(\Lambda_1,\Lambda_2,\Lambda_3)\), then \(H_0=\lceil e^{\Lambda_*}\rceil+16\). LONG is analogous except the constant is \(1792e^{10}\) and the exponent available at the last absorption is \(49/1000\). The +16 is not an afterthought; it ensures the elementary lower bounds needed for positivity and the decoration-mass lemma.

The corresponding sufficient thresholds at \(\varepsilon=0.1\), considering only this *last* inequality, are approximately

\[
\log_{10}\Lambda\gtrsim8450\quad\text{(CORE)},\qquad
\log_{10}\Lambda\gtrsim175\quad\text{(LONG)}.
\tag{37}
\]

They are extraordinarily large, and the earlier thresholds can only enlarge them. They are **not** estimates of the smallest height for which the original theorem holds. The proof is optimized to establish eventual validity, not practical finite-height sharpness. The separate epsilon microscope in the browser makes this distinction explicit.

### 5.5 The other two rates are not paid by a power ladder

**HIGH:** At the source high-cardinality cutoff, the full physical HIGH contribution is bounded by a constant of the form

\[
|\mathrm{HIGH}|\le C_{\rm high}(q)=8e^{75}(4+48q).
\tag{38}
\]

For fixed \(q\), this is \(o(\log h)\) simply because \(\log h\to\infty\). There is no second \(\Lambda^{1/1000}\) decoration charge on this full-source bound (`Orienne/Central/HighCardGrowingR0001.lean`; `HighCardRateR0002.lean`).

**LOW:** At \(J_{\rm low}\equiv0\), LOW is literally a finite sum over no parents, hence zero. The rate theorem chooses \(H_0=1\). This is the only piece paid by *exact emptiness*, and that fact is useful only because (3) ensures the other parents remain inside MIDDLE (`Orienne/CSC3/LowZeroTerminalR0001.lean:8–42`).

### 5.6 Folded source to native Central and then to the printed theorem

Another exact source equation says

\[
\mathrm{activeCentral}
=\mathrm{foldedCentral}+\mathrm{invRow}+\mathrm{densRow}.
\tag{39}
\]

The paid inverse/density correction obeys

\[
\left|\mathrm{activeCentral}-\mathrm{foldedCentral}\right|
\le(6q+2)\,\mathrm{baseRate}(h),
\quad \mathrm{baseRate}(h)=4(1+\Lambda)^3Z(h)^{-1/2}e^{K_0}.
\tag{40}
\]

`baseRate_small` proves that the right-hand base rate tends to zero; the final source-to-native rate theorem requests the folded estimate at half the target epsilon and pays the error with the other half. Inside the partitions, MIDDLE requests CORE and LONG at \(\varepsilon/2\); CENTRAL requests LOW/MIDDLE/HIGH at \(\varepsilon/3\). By the time active Central is requested at tolerance \(\varepsilon\), the underlying CORE/LONG may be called at \(\varepsilon/12\). That is a **substitution of the epsilon parameter in already quantified theorems**, not a new logarithmic exponent loss.

The original R0056 Central source is reached through its own exact adapter, then the already-paid Suzuki terminal assembly yields the native `PaperBTerminalStatement`. The final public theorem applies the separate literal Euler equality (2). One line at the end is the meeting point of two very long, different proof traditions.

---

## 6. What kind of reusable mathematics is this?

The atlas deliberately distinguishes four different kinds of mathematical achievement. **Classical technique** includes Möbius/Boolean inversion, CRT, Vaaler, Suzuki/Kusmin–Landau, Vinogradov and Karatsuba, Ramaré, Vaughan, Parseval, Abel, Rankin, and Weil–Estermann. **Source-specific assembly** is the physical separation of the decorated, signed, restricted Central source into disjoint regimes with different admissible methods, followed by tight budget accounting. **Formal semantic transport** proves, rather than assumes, exact equality between copied and production source definitions, between the two complete-sum normalizations, and between the printed products and the manuscript kernels. **Failed or conditional route knowledge** explains why an attractive method cannot simply be extended across its geometric boundary, or why one exact identity is not itself an analytic estimate.

### 6.1 Three practical forms of mathematical capital

**A source-preserving partition can replace a missing analytic theorem.** Instead of proving an apparently hard global cancellation theorem in one shot, one proves an exact partition and routes every piece to a method genuinely supported by its geometry. When the final estimates are cutoff-uniform, the partition itself has degrees of freedom. This is what ultimately allowed LOW to be selected empty.

**A strong theorem is not a usable theorem until its losses match the source.** Weil does not buy LONG in one line. The argument order, the source's squarefree modulus, divisor-count factor, high-gcd modes, weighted coefficients, four Fourier rows, and sufficient cofactor length are part of the application theorem. The W-cell bridge is a mathematical *composite*, not merely an API rename.

**Exact normalization is a form of mathematical conservation.** The B Euler bridge keeps the infinite centering tail. The source partitions keep every signed parent. The folded-source adapter keeps its inverse/density correction. The eventual estimates keep their \(q\)-dependent constants and cutoff quantifiers. Much of this proof is dedicated to refusing to lose something small but necessary.

### 6.2 The most useful counterfactual questions

Any future reuse should confront the failure condition of the method, not just its successful bound:

1. Does the printed Euler denominator remain nonzero? If not, the quotient is illegal even when formal local algebra looks correct.
2. Is a divisor-swapped numerator finite *before* centering? If yes, are the infinite negative normalization tails retained afterward?
3. Does the extracted variable truly contain a prime packet in the physical mask? If not, the Ramaré/W′ or reciprocal-progression theorem is not applicable.
4. Is a source-gcd factor being dropped under a generic square-root estimate? The general Weil bound retains it.
5. Is the cofactor interval long enough for Weil/Cauchy? Near the half-power boundary the proof switches to geometric mass.
6. Is a lower logarithmic condition known with **5**, or only **4**? A Suzuki estimate cannot be reused under a stronger hypothesis than the source supplies.
7. Are outer summation, decoration mass and epsilon allocation each charged once? Confusing separate cell summation with multiplication or charging the decorations twice destroys the margin.
8. Does the target permit \(q\) to grow? The actual quantified theorem fixes \(q\) before requesting an eventual height; it is not a conductor-uniform theorem.
9. Does a local GREEN proof import the terminal consumer? A module import graph is not a transitive proof-constant graph.
10. Does a reconstructed historical attribution follow from the current source dependency? It usually does not. Formal dependency and mathematical influence belong to separate ledgers.

The companion structured data gives a direct, source-anchored answer to these questions for **each of the twelve physical cells**, and an additional thirty-five analytic and fifteen Euler/finite mechanism cards. The browser also preserves precise citation paths and clipped code excerpts.

### 6.3 Standing and the next honest validation

The R0003 archive's SHA-256 and ZIP structure were checked. The cross-pass reconciliation checked **136/136** source references and hashes across **70 distinct source files**, with no source mismatches. All twelve exact-rational exponent ladders agree between the independent physical-cell and quantitative-budget datasets. The atlas carries 62 mechanism cards, 16 terminal declaration nodes, a 41-node quantitative flow graph, twenty-five Euler equation transitions, and a normalized parameter registry.

Those checks certify the atlas as a **faithful static research artifact at this source cut**. They do *not* certify the underlying theorems independently. The RC archive supplies its own Lean seal; the independent external referee remains a separate court. A complete transitive proof-term dependency audit, cold external mathematical originality review, and publication acceptance are distinct questions. In particular, we have not proven that all modules importable from `PaperB.lean` occur in the final proof term.

**The central mathematical conclusion of the atlas:** the proof is not powered by one cancellation miracle. It is powered by an unusually exact geometry of the actual source, a selective purchase of powerful oscillatory estimates, and just enough quantitative slack—carefully protected through every change of representation—to carry an original fixed-modulus theorem into its literal printed form.

---

### Primary source waypoints (relative to R0003 `LEAN/`)

- `Orienne/Publication/PaperBPrintedTerminalR0001.lean:10–28` — printed theorem and two calls.
- `Orienne/Publication/F01PrintedLiteralBridgeR0001.lean:13–31,453–617,1432–1481` — Euler definitions and exact A/B bridges.
- `PaperB/Gate3/CentralTransfer/ThreeSectorConsumer.lean:84–92` — LOW/MIDDLE/HIGH identity and SourceUniformSublog.
- `PaperB/Gate3/CentralTransfer/MiddleLongCoreConsumer.lean:19–65` — MIDDLE = LONG + CORE, source rate assembly.
- `GoldB/Suzuki.lean`, `GoldB/VinoMain.lean`, `GoldB/KaratsubaMain.lean`, `GoldB/QuillonLowY.lean` — two-regime shifted reciprocal sum.
- `GeneralKloosterman/General.lean:61–115`; `Orienne/CSC3/WeilQuillonBridgeR0002.lean:7–23` — general bound and literal normalization.
- `GoldC/QuillonCoreFinal.lean:72–206` and `GoldC/QuillonLongFinal.lean:74–end` — exact physical sums and per-sector rates.
- `GoldC/QuillonResPhysical.lean`, `GoldC/QuillonLRP.lean` — Band and EdgeL mass budgets.
- `PaperB/Gate3/CentralTransfer/ThreeSectorTerminalAssembly.lean:23–142` — folded-to-active error and R0056 transfer.
- `Orienne/CSC3/LowZeroTerminalR0001.lean:8–42` — final source-exact zero-cutoff specialization.

**Reproduce every source anchor by extracting the untouched `PAPERB_PRINTED_TERMINAL_RC_R0003_TRIMMED_20261023.zip` and using the path printed on a card.** The companion `02_INTEGRATED_ATLAS_DATA.json` stores exact SHA-256 values and short source excerpts with original line numbers. The full source itself is not repackaged or changed.
