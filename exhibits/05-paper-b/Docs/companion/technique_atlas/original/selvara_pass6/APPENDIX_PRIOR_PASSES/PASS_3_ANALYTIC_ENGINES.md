# Paper B Mathematical Technique Atlas — Pass 3
## The analytic engines: shifted Suzuki, Karatsuba–Vinogradov, Vaaler, Weil–Estermann

**Source cut:** `PAPERB_PRINTED_TERMINAL_RC_R0003_TRIMMED_20261023.zip`, 23 October 2026.  
**Research method:** read-only inspection of the exact supplied Lean source; cross-reference declarations, proof bodies, source-specific transports, and numerical exponent budgets. **No full Lean build or kernel replay was conducted.**  
**Standing:** mathematical mechanism interpretation grounded in proof source; not a new formalization court, independent verification result, or claim of original invention of classical theorems.  
**Notation:** `Λ = log h` in CORE/LONG; `P=N` in Suzuki/Karatsuba; `s` is a complete-sum modulus in the Kloosterman analysis; `J` denotes a Fourier truncation index in Vaaler, while `Js` is a *selected set of derivative orders* in Karatsuba. These are different uses of the same letters.

## Executive finding

Paper B does not purchase one universal analytic cancellation estimate. It uses at least **four sharply differentiated mechanisms** at the classical analytic layer:

1. **Small reciprocal-frequency:** monotone phase increments, discrete summation by parts, and cotangent telescoping (Kusmin–Landau).
2. **Large reciprocal-frequency:** selected derivative orders, uniform-in-order Vinogradov mean-value estimates, a polynomial double-sum inequality, and a Karatsuba power saving that becomes a Suzuki logarithmic-exponential saving.
3. **Pointwise Fourier control:** a finite real Vaaler approximation to a sawtooth, with an explicitly **nonnegative Fejér/Dirichlet-square error** even at integer jumps.
4. **Complete arithmetic cancellation:** Kloosterman estimates at the prime, prime-power, and arbitrary-modulus levels; in the final LONG-right W′ cell, Weil–Estermann replaces an insufficient elementary fourth-moment modulus exponent, but its gcd and divisor-count losses remain visible.

The most interesting supplier reuse is *not* obvious from the published final theorem. `GoldB.shiftedSuzukiCore_unconditional` is used both to discharge the named shifted Suzuki terminal input and as an input to `GoldC.QuillonRLemma.suzuki_AP`, which controls CORE's R-cell arithmetic-progression sums (and feeds the corresponding LONG RL machinery). A tool that looks like a single external theorem thus operates in more than one physical location.

---

## 1. Proof-mechanism map, not a directory graph

```mermaid
flowchart TD
  U[Native Paper B terminal] --> B[Shifted Suzuki Core]
  U --> C[Signed Central closure]
  V[Vaaler positive finite approximation] --> U
  B --> H[High-Y Karatsuba]
  B --> L[Low-Y discrete Kusmin–Landau]
  H --> J[Selected derivative-order window]
  H --> K[Karatsuba sharp-clip lemma]
  K --> D[Vinogradov double-sum + Taylor averaging]
  D --> M[Order-uniform VMVT: p-adic step]
  B --> R[CORE R arithmetic-progression cells]
  C --> CORE[Five physical CORE cells]
  C --> LONG[Seven physical LONG cells]
  E[Elementary prime fourth-moment CRT: p^3/4] --> CORE
  W[General Weil–Estermann: tau(s) sqrt(gcd*s)] --> WR[LONG WRL / Weil W-prime]
  W --> P[Prime Carlitz–Stepanov]
  W --> PP[Prime-power p-adic stationarity]
  W --> CRT[CRT product and gcd ledger]
  WR --> LONG
  THIN[Thin critical edge: no Weil saving needed] --> LONG
```

**What the arrows mean:** mathematically relevant source-level applications; the graphic is not an exhaustive Lean kernel-constant DAG and does not assert that every module in an upstream imported branch is used by every theorem. For the precise anchor and status of each arrow, use `02_MECHANISM_CARDS.json` and `04_SOURCE_ANCHORS.tsv`.

### Exact consumers

- `PaperB/Gate3/SuzukiCentralOnly.lean`: `suzukiCore_paid : OrielUpper.ShiftedSuzukiCore := GoldB.shiftedSuzukiCore_unconditional`. This buys the *Suzuki input*, not Central.
- `PaperB/Gate3/ClassicalVaalerPaidTerminal.lean`: `paperB_terminal_of_suzukiCore_and_central` consumes the positive Vaaler theorem, Suzuki, and an explicitly hypothetical Central signed rate. Vaaler does **not** imply that rate.
- `GoldC/QuillonRLemma.lean`: `suzuki_AP` starts by destructuring `GoldB.shiftedSuzukiCore_unconditional` and reindexes a physical progression into a shifted reciprocal sum; this is a **second consumption** of the Suzuki machinery.
- `Orienne/CSC3/WeilQuillonBridgeR0002.lean`: matches Quillon's `K(s,a,b)` to `GenKloosterman.kSum(s,b,a)` by `rfl`. The order of the two coefficients is *reversed*; the final gcd bound is symmetric, but the equality is not stated with the same order.
- `Orienne/CSC3/PhysicalLongBridgeQ0001.lean`: discharges an explicit `WeilHyp` using the already-proved general theorem, transfers Quillon's copied LONG source to the native one by definitional equality, and pays a source-uniform LONG rate.

## 2. Suzuki: what exactly is proved

The object is the *sharp*, shifted reciprocal sum

\[
S(Y,\vartheta;N,U) = \sum_{N<m\le U} \exp\!\left(2\pi i\frac{Y}{m+\vartheta}\right),
\quad Y\ge2,\ N\ge1,\ 0\le\vartheta\le1,\ U\le2N.
\]

`GoldB.Iface.ShiftedSuzukiCore` is the following quantified estimate, for some constants \(c>0,C\ge0\) **uniform in** \(Y,N,\vartheta,U\):

\[
\boxed{\quad |S(Y,\vartheta;N,U)|\le C\left[N\exp\left(-c\frac{(\log N)^3}{(\log Y)^2}\right)+\frac{N^2}{Y}\right].\quad}
\]

The proof's `j=1, γ=0` interface is a precise selected mode, not the statement for every Fourier mode with independent constants. A later caller must handle scaling and sign to get a general numerator/coefficient. `GoldB/Suzuki.lean:21–49,51–71` defines and transports the source sum.

### 2.1 The regime division is an exact logical partition

For `N ≥ 4096`, the proof divides according to

\[
\log Y\ \begin{cases}
<\tfrac32(\log N+\log2),&\text{low-}Y;\\
\ge\tfrac32(\log N+\log2),&\text{high-}Y.
\end{cases}
\]

The *equality case belongs to high-\(Y\)*. For `1 ≤ N < 4096`, a trivial bound \(|S|\le N\) is converted into the full target form by enlarging a constant. In `shiftedSuzukiCore_of_lowY`, the final exponent constant is the smaller of the two branch constants; the coefficient constant is their sum. No “gap near the transition” is assumed away. Sources: `GoldB/Suzuki.lean:190–299` and `GoldB/QuillonLowY.lean:25–89`.

### 2.2 Low-\(Y\): geometrical phase increments and cotangent telescoping

The logarithmic condition implies \(Y<N^2/2\) at \(N\ge4096\). Put \(L=N+1\) and \(T=Y/L\). Then \(T\le L/2\) and every integer in the actual clip satisfies \(L\le m+\vartheta\le2L\).

For the reciprocal phase \(f(x)=TL/(x+\vartheta)\), adding an *integer-valued linear phase* \(x\) does not change \(e(f(x))\) on integers. This moves a negative reciprocal increment into a positive increment \(\Delta\) bounded away from both 0 and 1. The increments are monotone. The proof invokes the exact algebra

\[
\frac1{e(\Delta)-1}=-\frac12-\frac{i}{2}\cot(\pi\Delta),\quad0<\Delta<1,
\]

uses cotangent antitonicity and a discrete summation-by-parts identity, and establishes a Kusmin–Landau bound \(\left|\sum z_i\right|\le2+3/(2\lambda)\) for \(\lambda\le\Delta_i\le1-\lambda\). With \(\lambda=T/(4L)\), the specialized result is

\[
\left|\sum e\left(\frac{TL}{m+\vartheta}\right)\right|\le\frac{8L}{T}=\frac{8L^2}{Y}\le\frac{16N^2}{Y}.
\]

This is the `N²/Y` half of Suzuki's eventual conclusion. It uses **no mean-value theorem**. The source also treats `U≤N` as the empty sum, avoiding an implicit nonempty-range assumption. Sources: `GoldC/VKRegimes.lean:39–217,223–327`; `GoldB/QuillonLowY.lean:25–89`.

### 2.3 High-\(Y\): why a density of derivative orders is the key input

Let \(P=N\), \(t=(\log Y)/(\log P)\), and \(k=\lfloor26t\rfloor\). In high-\(Y\), \(t\ge3/2\), hence \(k\ge39\).

For \(f(x)=Y/(x+\vartheta)\), exact normalized derivatives satisfy

\[
\boxed{\frac{|f^{(j)}(x)|}{j!}=\frac{Y}{(x+\vartheta)^{j+1}}}
\qquad(x\in[P,2P],\ 0\le\vartheta\le1).
\]

The proof constructs a selected finite set `Js` of derivative orders satisfying

\[
\frac{4(t-1)}3\le j\le\frac{468}{61}\left(t-\frac{157}{144}\right),\quad1\le j\le k,
\quad\#Js\ge\frac{k}{39}.
\]

The slightly ungainly fractions are essential bookkeeping, not decorative constants. Since \(2P+1\le P^{157/144}\) for \(P\ge4096\), the selected range implies

\[
P^{-(599/624)j}\le\frac{|f^{(j)}(x)|}{j!}\le P^{-j/4}.
\]

The top derivative separately satisfies

\[
\frac{|f^{(k+1)}(x)|}{(k+1)!}\le P^{-(25/26)(k+1)}.
\]

Thus one gets not merely “some derivative is large” but a **positive proportion of derivative orders** controlled in a two-sided window, plus a controlled Taylor remainder order. This is what the Karatsuba lemma consumes. Sources: `GoldB/QuillonSelectedOrders.lean:18–103,105–147`; `GoldB/QuillonDerivativeWindow.lean:19–85`; `GoldB/Suzuki.lean:90–151`.

**Source-provenance warning:** `QuillonSelectedOrders.lean` explicitly describes itself as a *from-scratch reconstruction* of a missing interface from the archived Suzuki package, **not the original scratch file**. That is a formal-source fact and a historical distinction worth preserving in the technique atlas.

### 2.4 Karatsuba's abstract machine

`GoldB.Final.karatsuba_lemma` takes four real constants \(0<c_0<1\), \(0<c_3\le c_2<c_1<1\), any integer \(k\ge1\), any length \(P\ge1\), a smooth phase, a \((k+1)\)-derivative ceiling, and a finite set `Js` with \(\#Js\ge c_0k\) and two-sided derivative windows. It yields \(\gamma>0\) and \(C\ge0\), depending on these four constants **but not on** \(k,P,X,f\) or the clip, such that

\[
\boxed{\left|\sum_{\lfloor X\rfloor<n\le\lfloor X+P_1\rfloor}e(f(n))\right|\le CP^{1-\gamma/k^2}\quad(P_1\le P).}
\]

The proof in `Final.lean` handles the sharp partial interval by decomposing a long interval into left/right pieces and reflecting the right piece. This is what keeps the quantified interface a sharp interval, not a smoothed or conveniently centered one. It also separately handles small \(P\) by a trivial count.

Inside `KaratsubaMain.lean` and `CoreMain.lean`, the machine is:

- average short shifts \(a+yz\) while tracking the difference from the desired sharp sum; the boundary penalty is explicitly bounded;
- Taylor-expand the phase in powers of \(yz\), with a top-derivative remainder controlled by \(c_1\);
- apply the polynomial double-sum estimate via Hölder/mean-value counting and a product of `Sfrak` factors;
- use the selected derivative orders to make the logarithm of the product **negative enough** to dominate the positive constants and averaging losses;
- pick \(\gamma\) small enough to satisfy every inequality simultaneously.

The double-sum theorem is particularly diagnostic. For polynomial phase coefficients \(B_j\), it proves

\[
\left|\sum_{y,z\in[0,Q)}e\left(\sum_{j=1}^{k}B_j(yz)^j\right)\right|^{4b^2}
\le Q^{8b^2-4b}\,J_c(k,b,[0,Q))^2\,\prod_{j=1}^{k}\mathfrak S_j.
\]

The Vinogradov count \(J_c\) and the \(\mathfrak S_j\) factors are *different controls*; a treatment that simply says “apply VMVT” misses the selected-order saving that converts the analytic input into the stated Karatsuba lemma. Sources: `GoldB/DoubleSum.lean:115–145`, `GoldB/CoreMain.lean:40–150`, `GoldB/KaratsubaMain.lean:12–80,112–242`, `GoldB/Final.lean:24–183`.

### 2.5 What “uniform Vinogradov” actually buys

The proved `GoldB.VinoMain.vmvt` uses the explicit definitions

\[
\kappa=\tfrac12k(k+1),\quad \Delta_\tau=\kappa(1-1/k)^\tau,\quad
D_v(k,\tau)=2^{24k^4+5k^2\tau+2k\tau^2},
\]
\[
E(k,\tau)=2k\tau-\kappa+\Delta_\tau,
\]

and proves

\[
J_c(k,k\tau,[1,N])\le D_v(k,\tau)N^{E(k,\tau)}.
\]

This retains explicit dependence on *growing derivative order* \(k\). The proof uses an inductive p-adic step (`GoldB.StepThm.vstep`), the two-branch well/ill-conditioned decomposition, and a prime chosen on the appropriate scale. These are nontrivial prerequisites, not a black-box invocation of Mathlib's ordinary exponential-sum estimates. Sources: `GoldB/Vino.lean:17–22`, `GoldB/VinoMain.lean:201–325`, `GoldB/StepThm.lean:11–25`.

The parameter choice is a small budget system in its own right. In `GoldB.Params`:

\[
\rho=\min(c_3,c_1/4,(c_1-c_2)/2),\quad L_1=\log\frac8{\rho c_0^2},\quad
\gamma_1=\frac{\rho c_0^2}{128L_1^2},
\]
\[
\tau(k)=\lceil kL_1\rceil,\quad
\eta(k)=\min\left(\frac1{2k^2(k+1)},\frac{c_1-c_2}{4}\right),\quad
Q=1+\left\lfloor P^{c_1/2-\eta(k)}\right\rfloor.
\]

The final Karatsuba \(\gamma\) is the minimum of several demands: \(\gamma_1/2,1,c_1-c_2,1-c_1\). Its smallness is not a weakness to hide. It is the exact price of making all the Taylor, double-sum, and parameter arguments valid simultaneously. Source: `GoldB/Params.lean:28–38`; `GoldB/KaratsubaMain.lean:81–112`.

### 2.6 From a power saving to Suzuki's log-cubed exponent

For the reciprocal phase, substitute \((c_0,c_1,c_2,c_3)=(1/39,25/26,599/624,1/4)\) into `karatsuba_lemma`. The abstract bound is \(CP^{1-\gamma/k^2}\). Since \(k\le26\log Y/\log P\),

\[
\frac{\gamma}{k^2}\log P\ge \frac{\gamma}{676}\frac{(\log P)^3}{(\log Y)^2},
\]

and therefore

\[
\boxed{CP^{1-\gamma/k^2}\le CP\exp\left(-\frac{\gamma}{676}\frac{(\log P)^3}{(\log Y)^2}\right).}
\]

**Where the number 676 comes from:** \(26^2\), the square of the derivative-order coefficient. It is not an arbitrary global constant. See `GoldB/Suzuki.lean:88–188`.

### 2.7 Why the `VK` nomenclature requires a source court

`GoldC.VKCore.UniformVinogradovEstimate` is a **defined proposition**, *not a proved theorem in that file*. `reciprocalPhaseVK_of_uniform` and `GoldC.VKRegimes.recipSum_middle_T` explicitly **assume** it. Those conditional constructions should not be mistaken for the unconditional source of `GoldB.shiftedSuzukiCore_unconditional`.

The unconditional Suzuki path visible in the supplied source is **GoldB's proved Karatsuba/VMVT chain plus Kusmin–Landau**. Quillon's `VK`/`R` commentary can refer to the same broad analytic tradition, but declaration-level dependency controls the standing. Source: `GoldC/VKCore.lean:75–105`; `GoldC/VKRegimes.lean:328–396`; `GoldB/QuillonLowY.lean:85–89`.

### 2.8 Suzuki is also a Central supplier

`GoldC.QuillonRLemma.suzuki_AP` applies the unconditional Suzuki bound to the arithmetic progression \(\rho+Qt\): for \(0\le\rho<Q\), set \(\vartheta=\rho/Q\), \(Y'=|Y|/Q\). The source sum is converted exactly to a shifted reciprocal sum. When \(Y<0\), complex conjugation restores the positive \(Y'\) input. Its scope includes \(Q\ge1\), \(|Y|\ge2Q\), the correct partial interval \(M\le2N\), and exact coefficient normalization. The class filter is handled by a separate reindexing, rather than by pretending the physical source is already one contiguous interval.

This supplies CORE's physical `R_physical` rate (ultimately a \(\Lambda^{-75}\) cell bound) and related LONG-RL work. Thus the Gold B estimate is both a **terminal input** and **internal analytic capital**. Source: `GoldC/QuillonRLemma.lean:52–94,161–209`; `GoldC/QuillonRPhysical.lean`.

---

## 3. Real Vaaler: pointwise positivity, not Central cancellation

The positive Vaaler theorem approximates the centered sawtooth with a finite positive-frequency trigonometric polynomial and **controls its pointwise error by a nonnegative trigonometric polynomial**.

`OrielUpper.yevorin_realPositiveVaalerPointwise : RealPositiveVaalerPointwise` constructs explicit main and error coefficients. The main coefficients have \(\|a_j\|\le2/j\); the error coefficients have \(\|b_j\|\le2/(J+1)\). The final pointwise error has form

\[
\left|\operatorname{saw}(t)-\operatorname{Main}_J(t)\right|
\le\frac1{J+1}+\sum_{1\le j\le J}\operatorname{Re}(b_j e(jt)).
\]

The error polynomial is proved equal to

\[
\frac1{2(J+1)}+\frac{\left|\sum_{j=0}^{J}e(jt)\right|^2}{2(J+1)^2}.
\]

The square is genuinely nonnegative. On noninteger arguments, the proof invokes a real Vaaler interior inequality and the Fejér/Dirichlet norm-square identity. **At an integer**, \(\operatorname{saw}(0)=-1/2\): the argument explicitly checks the jump and the nonzero error there. Forgetting that case would silently strengthen a pointwise statement beyond what the finite Fourier series provides.

The consumer `OrielUpper.yevorin_realShiftedVaalerTransfer` then supplies the classical pointwise prerequisite for the signed source's analytic decomposition. This does not by itself estimate the signed Central remainder, and its result should not be presented as a signed source cancellation theorem. Sources: `PaperB/Gate3/VaalerCoefficients.lean:9–56`; `VaalerErrorPolynomial.lean:8–64`; `VaalerFullPointwise.lean:25–99`; `ClassicalVaalerPaidTerminal.lean:8–27`.

---

## 4. Weil–Estermann: from prime spectral geometry to one physical LONG cell

The general supplier is

\[
\boxed{|K_s(a,b)|\le\tau(s)\sqrt{\gcd(a,b,s)\,s},\quad s\ge1.}
\]

The source writes the divisor count \(\tau(s)\) as `s.divisors.card`, and \(a,b\) are `ZMod s` coefficients. It does **not** claim an unqualified \(2\sqrt{s}\) bound for arbitrary composite moduli.

### 4.1 Prime input: Carlitz spectral roots plus Stepanov

The prime nondegenerate estimate is proved via the `rml.stepanov` and `VPWStepanov` source. The concrete spectral endgame identifies two complex Carlitz roots \(\alpha,\beta\), with \(\alpha\beta=p\) and verified bounds \(\|\alpha\|^2,\|\beta\|^2\le p\). Since the product of their norms is \(p\), the individual norms must **equal** \(\sqrt p\). The normalized prime Kloosterman sum is \(- (\alpha+\beta)\), and the triangle inequality gives \(2\sqrt p\). The prime 2 is handled separately. This depends on a considerable finite-field/spectral/point-count development upstream; it is not just a declaration of Weil as an axiom. Sources: `VPWStepanov/StepanovPrimeWeil.lean:9–131`; `rml/stepanov/prime_weil_bridge.lean:9–19`; `rml/weil/prime_kloosterman.lean:12–18`.

### 4.2 Prime powers: p-adic stationary phase and descent

For \(p^k\) with unit coefficients and \(k\ge2\), stationarity reduces the complete sum to solutions of a quadratic congruence. A stationary-set cardinality argument bounds the number of contributions; odd prime powers use quadratic Gauss-sum analysis, while \(p=2\) has a dedicated small-exponent case (\(k\in\{2,3\}\)) and a separate argument above it. The assembled unit theorem gives \((k+1)\sqrt{p^k}\).

For **non-unit coefficients**, the proof distinguishes all cases. If exactly one coefficient is divisible by \(p\), the sum vanishes. If both are divisible, it descends by a power of \(p\), and the missing power reappears inside the \(\sqrt{\gcd(a,b,p^k)}\) conductor factor. Neither situation can be ignored by stating a unit-only bound. Sources: `GeneralKloosterman/PrimePowerUnit.lean:84–168,210–302`; `PrimePower.lean:50–193`.

### 4.3 CRT: the loss survives multiplication

`GenKloosterman.norm_kSum_le_aux` is a multiplicative induction over prime-power factors and coprime products. CRT changes the phase coefficients by *units*; the proof explicitly shows those twists do not change the gcd conductor. Multiplicativity of divisor counts, square-root multiplication, and the exact `kgcd_crt` identity assemble

\[
\prod_{p^k\parallel s}(k+1)\sqrt{\gcd_p\,p^k}
=\tau(s)\sqrt{\gcd(a,b,s)\,s}.
\]

This is a source-preserving, arithmetic operation, not a loose \(O_\epsilon(s^{1/2+\epsilon})\) replacement. Source: `GeneralKloosterman/General.lean:61–115`; `GeneralKloosterman/PrimePower.lean:112–193`.

### 4.4 Exact normalization into Quillon's completed modes

The production bridge is short but nontrivial semantically:

```lean
quillon_K_eq_rml : GoldC.QuillonKl.K s a b = GenKloosterman.kSum s b a := by rfl
```

The reversed arguments are preserved. The next theorem rewrites the general-modulus inequality into the literal normalization of `GoldC.QuillonKl.K`. Inside the Quillon LONG files the input is the **explicit hypothesis** `WeilHyp`; it is discharged, not postulated, by `Orienne.CSC3.quillon_weilHyp`. A direct native LONG statement is then obtained by a separate definitional `rfl` match between copied and original source sums.

The chain has three distinct guarantees: a Kloosterman bound, a complete-sum normalization equality, and a source-sum equality. Confusing them would manufacture an unproved application. Sources: `Orienne/CSC3/WeilQuillonBridgeR0002.lean:10–24`; `GoldC/QuillonLWeil.lean:30–39`; `Orienne/CSC3/PhysicalLongBridgeQ0001.lean:20–50`.

### 4.5 Squarefree conversion: from a global gcd to a local prime surcharge

For the physical squarefree modulus \(s=\prod_{p\in P}p\), \(\tau(s)=2^{|P|}=4^{|P|/2}\). A complete mode with frequency \(c\) is bounded by

\[
|K_s(b,c)|\le\underbrace{4^{|P|/2}s^{1/2}}_{\text{modulus and divisor cost}}
\underbrace{\left(\prod_{p\in P,\,p\mid c}p\right)^{1/2}}_{\text{conductor / zero-mode cost}}.
\]

The source calls this upper bound `KW P c`. It **does not delete frequencies divisible by primes of the modulus**. In the bilinear form, the frequency is a multiple of differences of modular inverses, and the gcd is split into the base frequency factor and divisors of \(y-y'\).

A weighted gcd-moment lemma (ported from Seravyn) sums the variable part of this surcharge through a finite divisor expansion and congruence-class counting:

\[
\sum_{\substack{1\le y,y'\le Y\\y\ne y'}}\frac{1}{yy'}
\left(\prod_{p\in P,\,p\mid y-y'}p\right)^{1/2}
\ \le\ 2(1+\log Y)^2\prod_{p\in P}(1+p^{-1/2}).
\]

This *off-diagonal* estimate does not cover the diagonal, which is treated separately. Source: `GoldC/QuillonLWeil.lean:37–180`.

### 4.6 The real W′ inequality retains three categories

`GoldC.QuillonLWeilB.W_piece_W` assumes the exact selected coefficient bounds \(\|\alpha_y\|\le A/y\) and \(\|\beta_n\|\le A/n\), support \(X\le y\le Y\) and \(N<n\le2N\), and unit conditions on the selected \(y\)'s. Its norm-squared bound has **three** pieces:

\[
\begin{aligned}
\|W\|^2\le 2A^4\Bigl[&\frac2X
+\frac{2(1+\log Y)^2}{s}\\
&+2(1+\log Y)^2\prod_{p\in P}(1+p^{-1/2})\,4^{|P|/2}G_0^{1/2}
\left(\frac{s^{1/2}}s+\frac{s^{1/2}(1+\log s)}N\right)\Bigr].
\end{aligned}
\]

Here \(G_0\) is the product of primes of \(s\) dividing the base frequency. The first term is the diagonal, the second is distinct-but-congruent pairs, and only the third is the Weil-controlled off-diagonal. The method does not replace one kind of pair with another or claim a generic coefficient-family saving. Source: `GoldC/QuillonLWeilB.lean:31–87`.

### 4.7 The Weil exponent is a conditional *range* advantage, not universal coverage

The LONG-right W′ parameter calculation chooses

\[
\eta=\Lambda^{-1/10},\quad Y\approx s^\eta,\quad L_w\approx s^{1/2+3\eta},\quad
D\approx L_w/Y\approx s^{1/2+2\eta}.
\]

Because \(D\) is larger than \(s^{1/2}\) by a controlled factor, the completed bracket has a power saving; the final source proves a very strong eventual bound (a bracket of at most \(6\Lambda^{-100}\)) after retaining factors such as \(8^{|P|}\le8\Lambda^{208}\). Frequency modes acquire a gcd exponent \(1/4\) after the Cauchy square-root step. Sources: `GoldC/QuillonLWR.lean:75–155,155–260`; `GoldC/QuillonLWeilB.lean:676–780`.

**Critical caveat:** as \(D\downarrow s^{1/2}\), this mechanism stops yielding a fixed saving. The final seven-cell LONG proof deliberately assigns the too-short edge to `EdgeL`, controlled by thin-window *mass*, not by pretending Weil gives extra cancellation. The complete LONG per-decoration budget is \(7\Lambda^{19/20}\), with `EdgeL` dominant; decoration aggregation leads to exponent \(0.951<1\). The geometric edge/Weil split is a major Pass 4 target. Sources: `GoldC/QuillonLongFinal.lean:74–148`; `GoldC/QuillonLRP.lean:385–573` (EdgeL physical theorem) and `GoldC/QuillonLWR.lean` (Weil physical parameter budget).

### 4.8 CORE's different, deliberately weaker Kloosterman estimate

The CORE W′ input uses a fourth moment of a prime Kloosterman sum, assembled by squarefree CRT:

\[
\|K_s(b,c)\|\le
3^{|P|/4}\,s^{3/4}\!
\left(\prod_{p\in P,\,p\mid c}p\right)^{1/4}
\quad(s=\prod P).
\]

This is built from `GoldC.QuillonKlComposite` and consumed by `GoldC.QuillonWCell`. CORE's geometry and its \(0<\delta<1/3\) restriction allow that elementary strength in the relevant W cell. The longer range, particularly LONG-right, cannot simply reuse CORE's residue argument or modulus exponent: the unsieved residual mass would be too large, and the needed cofactor can approach the square-root threshold. Source: `GoldC/QuillonKlComposite.lean:178–220`; `GoldC/QuillonWCell.lean:25–55`.

The **comparison must carry both directions of cost**. Weil improves \(s^{3/4}\) to \(s^{1/2}\) but changes the local coefficient constants and gcd weight. It is not valid to say “Weil is stronger so every CORE bound automatically improves”; the actual completed bilinear proof redoes the frequency moment and all parameter conditions.

---

## 5. Technique classification: classical input vs work of the formalization

| Engine | Classical mathematical origin | What this Lean tree actually adds or assembles |
|---|---|---|
| Discrete Kusmin–Landau | summation by parts, monotone increments | explicit endpoint-safe reciprocal phase, literal sharp clip, `N²/Y` normalization |
| Vinogradov mean-value / Karatsuba | mean-value counting, p-adic iteration, Taylor/shift averaging | order-uniform explicit constants, selected-order interface, exact derivative windows, sharp-clip reflection, Suzuki log-exponent calculation |
| Vaaler | finite trigonometric approximation and Fejér positivity | concrete real coefficient and integer-jump proof; exact shifted-source supplier |
| Weil prime bound | Stepanov–Carlitz / classical Weil | machine-checked normalization through spectral roots and prime Kloosterman sum |
| General Weil–Estermann | prime-power stationary phase, descent, CRT | exact all-coefficient gcd, divisor factor, coefficient order and native LONG K-sum bridge |
| Physical W′ and R-cell uses | Cauchy/Schwarz, completion, summation over classes | source-mask, frequency and decoration bookkeeping, exact cutoffs, separate diagonal/congruence/offdiag, actual saving on physical source |

**Novelty caution:** this is a classification of *mathematical roles and newly written formal assemblies*, not an independent priority or originality assessment. Many combinations are new *to the present formal proof* without being new theorems in the literature.

## 6. Source fidelity and hostile-reader checklist

There are at least eight ways a plausible account of these engines would be misleading:

1. Presenting a `Prop` named `UniformVinogradovEstimate` as if it were itself a proof. The final Suzuki supplier uses the proved `GoldB` chain.
2. Claiming a fixed derivative-order bound suffices when \(k\sim\log Y/\log N\) grows. The constants in Karatsuba must be uniform in \(k\).
3. Writing the shifted sum as an arbitrary smooth interval and losing the original `Finset.Ioc` endpoints. The source proves sharp clips with reflected halves.
4. Treating `Y<...` and `Y≥...` as overlapping or leaving an equality gap. The split is exact.
5. Replacing Vaaler's pointwise inequality by an average Fourier bound and ignoring integer jumps.
6. Applying prime Weil at a composite modulus without prime-power descent, the \(\tau(s)\) factor or conductor gcd.
7. Discarding zero/diagonal/congruent modes in the completed W′ expansion.
8. Using the full Weil cancellation bound inside `EdgeL` at the square-root threshold where it gives no saving; the actual proof uses a thin-window mass cell.

Also, the Quillon selected-orders module has documented **replacement provenance**. The exact final source is what matters for Pass 3, but a historical description must not attribute its code to the missing original file.

## 7. What is established in this pass, and what is not

**Established by source inspection:** theorem statement forms, actual `:=` and `by` applications in the supplied sources, quantitative exponents and parameter definitions, branch choice, explicit hypotheses, direct producer/consumer relationships, exact copied/native `rfl` transfers, source-side note on reconstructed order selection, and concrete norm/gcd loss ledgers. These are checkable in the associated source cut and card/source registers.

**Not established here:** independent kernel replay of the release candidate, exhaustive transitive proof-expression DAG, automatic verification of every historical attribution, or originality relative to all published literature. There is no claim that old optional conditional `GoldC.VKCore` routes were the final unconditional supplier.

## Pass 3 decision — CONTINUE, WITH A SMALL PRIORITY ADJUSTMENT

The planned Pass 4 is the five CORE and seven LONG **physical cells**. Keep it. However, start with a paired microscopic comparison:

1. **`EdgeL` versus `WRL`:** one critical region is small because of its geometry; the other is small because Weil cancellation is strong enough after `D>s^{1/2}` and a frequency-gcd moment. Track their precise partition predicate and exact shared/split parameters.
2. **CORE R versus LONG RL:** check where the already-proved Suzuki/AP supplier pays the physical rate and where the two regions need different source masks.
3. Then mine all other ten cells, including the exact source partition equality, decoration aggregation, and eventual-to-`o(log h)` steps.

No methodological pivot is needed. But Pass 3 showed why the “twelve cells” should not be mined as twelve independent filenames: each is a point where specific classical engines meet a literal piece of the signed source. That meeting is the object of Pass 4.

— **Selvara / FACET**, read-only mathematical-source archaeology.
