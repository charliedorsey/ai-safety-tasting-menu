# Paper B Mathematical Technique Atlas — Pass 5
## Where the savings survive: the quantitative proof budget

**Source:** `PAPERB_PRINTED_TERMINAL_RC_R0003_TRIMMED_20261023.zip`, SHA-256 `e8bccaf4c607a3b2458a47833bdd98f598a59229f7af0175927b994318d7b2a1`. **Scope:** semantic source audit and exact rational budget reconstruction, not independent Lean correctness certification. **Build:** no Lean build or kernel replay performed at the user's request. **Verdict:** quantitative chains accounted for; **CONTINUE** to Pass 6 (atlas synthesis).

Set throughout
\[
\Lambda=\log h,\qquad \sigma_0=\frac23+\frac1{100},\qquad 0<\delta<\frac13.
\]
The terminal later chooses \(\delta=1/4\). A numerical exponent in a source bound is not a statement about how big \(h\) must be for the bound to become useful; the proof is eventually valid and the explicit sufficient thresholds are enormous.

## 1. The entire quantitative spine, before the details

The live source is not replaced by a convenient synthetic sum. For each decoration \(d\), the original signed `foldRow` pair sum is partitioned into five CORE cells or seven LONG cells by exact equality (`QuillonCoreFinal.pair_decomp`, line 58; `QuillonLongFinal.long_pair_decomp`, line 74). The absolute value is taken *after* each physical cell sum, not term by term inside the oscillatory cells.

The source establishes, eventually and uniformly in the admissible anchor, the decoration, and **arbitrary** cardinality cutoffs,
\[
\begin{aligned}
|S_{\mathrm{CORE},d}| &\le 5\Lambda^{998/1000},\\
|S_{\mathrm{LONG},d}| &\le 7\Lambda^{19/20}.
\end{aligned}
\]
`GoldC/QuillonCoreFinal.lean:72–116` (`core_pair_le`) and `GoldC/QuillonLongFinal.lean:88–146` (`long_pair_le`). The LONG theorem at this layer takes a named `WeilHyp`; `Orienne.CSC3.quillon_weilHyp` later supplies it, not a project axiom.

The decorated source is of the form
\[
S_{\mathrm{sector}}(q,a,h)=\sum_{d\subseteq P_q(h)}V_h(d)S_{\mathrm{sector},d}(q,a,h),
\quad V_h(d)=\prod_{p\in d}\frac1{p-2}\ge0.
\]
In the actual proof, `d` belongs to `decoratedHeightPrimeSet q h`'s powerset, and the set members are proved to lie in `h.primeFactors`, with \(p\ge5\). This justifies using `core_pair_le` and `long_pair_le` for **every** decoration. Only now does the proof take
\[
\left|\sum_dV_h(d)S_d\right|\le\sum_dV_h(d)|S_d|.
\]
This step loses cancellation *between decorations*. It does not invalidate the signed cancellation already obtained **inside** each cell.

The decoration theorem gives
\[
\sum_{d\subseteq P_q(h)}V_h(d)
\le e^{10}\left(\frac{\log\Lambda}{\log2}+1\right)^8
\le 256e^{10}(1+\log\Lambda)^8
\le256e^{10}\Lambda^{1/1000}
\]
for sufficiently large \(\Lambda\). The first inequality is `GoldC.QuillonDecorationGronwall.decoration_mass_le_loglog_pow` at line 260, transported to the exact source copy; the second uses `QuillonLam.log2_gt_half`, and the third uses `QuillonLam.polylog_le 8 (1/1000)`. The factor 256 is \(2^8\), not a new power of \(h\). The power \(1/1000\) is a **deliberately convenient sacrifice** of an eighth power of \(\log\log h\), not the natural magnitude of the decoration mass.

Hence the complete physical rates satisfy
\[
\boxed{|S_{\mathrm{CORE}}|\le1280e^{10}\Lambda^{999/1000}},\qquad
\boxed{|S_{\mathrm{LONG}}|\le1792e^{10}\Lambda^{951/1000}}.
\]
`GoldC/QuillonCoreFinal.lean:176–214` and `GoldC/QuillonLongFinal.lean:204–241`. This is **one** decoration charge per sector. Multiplying the two sector estimates by a decoration factor a second time would be a serious budget error.

## 2. The twelve local budgets

All exponents below are exact rational arithmetic, reconstructed from their source proof bodies (see `02_TWELVE_CELL_POWER_LEDGER.csv` and Pass 4). The column *before absorption* is the exponent after identifiable powers are combined but before the source invokes an eventual `const_le_rpow` or equivalent lemma to absorb its fixed coefficient. `Fixed term` and `outer charge` are shown separately where a fixed-factor analytic estimate is followed by a positive weighted outer sum.

| Sector | Cell | Fixed term | Outer charge | Before absorption | Public exponent | Remaining slack |
|---|---|---:|---:|---:|---:|---:|
| CORE | W | −95 | +10 | −85 | −80 | 5 |
| CORE | C | −30 | +10 | −20 | −15 | 5 |
| CORE | R | −90 | +10 | −80 | −75 | 5 |
| CORE | ResA | — | — | 51/2000 | 1/10 | 149/2000 |
| CORE | Band | — | — | 1991/2000 | 499/500 | **1/400** |
| LONG | WL | −95 | +10 | −85 | −80 | 5 |
| LONG | CL | −30 | +10 | −20 | −15 | 5 |
| LONG | RL | −90 | +10 | −80 | −75 | 5 |
| LONG | ManyL | −100 | +40 | −60 | −50 | 10 |
| LONG | EdgeL | — | — | 3741/4000 | 19/20 | **59/4000** |
| LONG | ResL | — | — | 1051/2000 | 7/10 | 349/2000 |
| LONG | WRL | −95 | +10 | −85 | −80 | 5 |

The three negative-exponent analytic branches are not identical in mathematics; the table records only their *quantitative aggregation pattern*. W/WL/WRL use packet extraction plus a Kloosterman/Cauchy supplier (Weil strength needed for WRL). C/CL exploit Parseval and Vaughan. R/RL exploit shifted Suzuki/Vinogradov–Korobov cancellation. The +10 outer-sum factor covers a **weighted** fixed-parent outer sum, not an unweighted count of all parents; the actual proofs carry the original omega weights.

### The fragile positive-exponent cells

**CORE Band:** `GoldC.QuillonResPhysical.Band_physical` (`GoldC/QuillonResPhysical.lean:404–590`) establishes
\[
\Lambda^{1/4000}\cdot\Lambda^{1/4000}\cdot\Lambda^{199/200}
=\Lambda^{1991/2000}=\Lambda^{0.9955}.
\]
The first two powers are roughness/weighted interval overheads, and \(199/200\) comes from \(\varepsilon_p\Lambda=\Lambda^{1-1/200}\). The fixed multiplicative constant \(K=6(4+48q)(1+1/(u_0(\delta)/2)^5)\) is absorbed by \(\Lambda^{1/400}\), delivering \(\Lambda^{499/500}=\Lambda^{0.998}\). **Do not mistake \(1/400\) for the final margin below 1:** after absorption, the per-decoration margin is \(1/500\); decoration aggregation consumes \(1/1000\), leaving exactly \(1/1000\).

**LONG EdgeL:** `GoldC.QuillonLRP.EdgeL_physical` (`GoldC/QuillonLRP.lean:385–~560`) uses a very different geometric window: \(s^{1/2}\lesssim r\lesssim s^{1/2+3\eta}\) (with the exact floors and −1 kept in Lean), \(\eta=\Lambda^{-1/10}\). Its weighted interval cost has \(\log(v/u)\le1+3\Lambda^{9/10}\). The full exponent budget is
\[
\frac1{4000}+\frac1{40}+\frac1{100}+\frac9{10}
=\frac{3741}{4000}=0.93525.
\]
The eventual bound absorbs \(K=165(4+48q)\) into \(\Lambda^{59/4000}\), giving \(\Lambda^{19/20}\). It is deliberately a **mass bound**, not a failed attempt to squeeze Weil cancellation out of its critical exponent.

**ResA:** the exponent is \(1/4000+1/4000+1/40=51/2000\), enlarged to \(1/10\). **ResL:** \(1/2000+1/2+1/40=1051/2000\), enlarged to \(7/10\); here \(1/\eta^5=\Lambda^{1/2}\) is explicitly rewritten in `QuillonLRP.lean:~346`. **ManyL:** a large-prime-factor Rankin suppression \(\Lambda^{-100}\) survives a total \(+40\) of exterior factors as \(\Lambda^{-60}\), rounded to \(\Lambda^{-50}\). These are not extra estimates after `long_pair_le`; they are the *ingredients already priced into* the cell suppliers.

### Why max, not sum of exponents?

The exact partition allows a triangle inequality across **five** CORE cells or **seven** LONG cells. For \(\Lambda\ge1\), every CORE exponent is at most \(998/1000\), so
\[
\sum_{c\in\mathrm{CORE}}\Lambda^{e_c}\le5\Lambda^{998/1000}.
\]
Likewise, every LONG exponent is at most \(19/20\), so \(\sum_c\Lambda^{e_c}\le7\Lambda^{19/20}\). An erroneous exponent addition such as \(\Lambda^{0.998+0.1}\) would correspond to multiplying two cell bounds, not summing disjoint pieces.

## 3. The epsilon and threshold court — an actual quantifier proof

`SourceUniformSublog` is **not** a vague asymptotic slogan. In `GoldC/QuillonSetup.lean:64–69` (and identically on the native Merivelle source), it quantifies:

> For every fixed positive squarefree \(q\) and \(\epsilon>0\), there exists an integer \(H_0\) such that **for every** coprime anchor \(a\) and every eligible \(h\ge H_0\), the signed source is bounded by \(\epsilon\log h\). If 2 does not divide \(q\), the original parity restriction on \(h\) remains.

The CORE proof obtains three eventual logarithmic thresholds:

- \(\Lambda_1(q,\delta)\) from the five-cell physical estimate;
- \(\Lambda_2\) from \((1+\log\Lambda)^8\le\Lambda^{1/1000}\);
- \(\Lambda_3(\epsilon)\) from \(1280e^{10}/\epsilon\le\Lambda^{1/1000}\).

It sets \(\Lambda_*=\max(\Lambda_1,\Lambda_2,\Lambda_3)\) and returns \(H_0=\lceil e^{\Lambda_*}\rceil+16\). LONG makes the same construction with \(1792e^{10}/\epsilon\le\Lambda^{49/1000}\). A reader can inspect the exact `obtain` / `refine` / `calc` clauses in `core_sublog` lines 118–214 and `long_sublog` lines 148–241. The `+16` supplies the numerical lower bound needed by Lemma G and the positivity/logarithm manipulations.

At the final source specialization, the theorems are **uniform in both cutoff functions** `Jlow` and `Jhigh`, because these are introduced *after* the logarithmic threshold in the per-decoration supplier. Thus the eventual threshold does not have to be rebuilt when `Jlow` is set to zero. Only fixed \(q,\delta\) and the requested \(\epsilon\) enter the choice of threshold.

The final constant absorption gives a striking numerical scale. For \(\epsilon=0.1\), the final steps alone require sufficient conditions approximately
\[
\log_{10}\Lambda\ge8450.15\quad\text{(CORE)},\qquad
\log_{10}\Lambda\ge175.43\quad\text{(LONG)}.
\]
These are **not** least possible validity thresholds, and they do not include the previous \(\Lambda_1,\Lambda_2\) requirements. They show that formal effective existence is not the same as computationally useful error control for accessible \(h\). This is the exact contrast the waterfall microscope illustrates.

## 4. Frequency and conductor losses: where Weil does, and does not, help

`GoldC.QuillonLWeil.WeilHyp` (`GoldC/QuillonLWeil.lean:32`) states the general-modulus Kloosterman estimate
\[
\|K_s(a,b)\|\le\tau(s)\sqrt{s\,\gcd(a,b,s)}.
\]
The source-matched court `Orienne/CSC3/WeilQuillonBridgeR0002.lean:7–23` proves `quillon_K_eq_rml` by `rfl`, with the important **argument order reversal** `K s a b = GenKloosterman.kSum s b a`, and obtains the actual `norm_quillon_K_weil` theorem. `Orienne/CSC3/PhysicalLongBridgeQ0001.lean:22–23` instantiates the previously named `WeilHyp`. Thus the eventual LONG rate does **not** depend on an unpaid Weil assumption.

For a squarefree source modulus \(s=\prod_{p\in P}p\), \(\tau(s)=2^{|P|}=4^{|P|/2}\) and
\[
\gcd(\gcd(b,c),s)\le\prod_{p\in P,\ p\mid c}p.
\]
The `norm_K_le_KW` theorem (`QuillonLWeil.lean:98`) makes these factors explicit in the majorant
\[
K_W(c)=4^{|P|/2}s^{1/2}\biggl(\prod_{p\in P,\ p\mid c}p\biggr)^{1/2}.
\]
For off-diagonal inverse terms \(c=c_0(\bar y-\bar y')\), `KW_offdiag` factors the gcd contribution into a piece supported on \(p\mid c_0\) and another on \(p\mid y-y'\). In `W_cell_coupled_W` (`QuillonLWeil.lean:227–360`) Cauchy square-mass accounting retains **three distinct cases**: equal \(y=y'\), unequal but congruent modulo \(s\), and general unequal pairs with weighted gcd. `gcd_moment_half` (line 147) handles the last family through a harmonic pair sum with factor \(\prod_{p\in P}(1+p^{-1/2})\).

After taking a square root, the gcd factor becomes a quarter-power, not zero. `GoldC/QuillonLWeilB.lean:675–825` uses `gcd_mode_sum` with exponent \(1/4\) to sum harmonic positive frequencies and control the common-prime contribution. The proof's frequencies in this step are `Icc 1 Jm`; this must **not** be misreported as proof that the source's zero/principal contribution was silently deleted. The original row has a separate exact mean/saw/class decomposition and four signed Fourier rows, with source-preserving bridges. In particular, `GoldC/QuillonLWR.lean:457–577` supplies all four `w1`, `w2`, `w3`, `w4` coefficient/phase variants to its final W-cell bound, using the actual \(\mu\) and \(\Gamma\) bounds.

The physical prime sets are not arbitrary: `GoldC.QuillonWPhysical.Tsrc_facts` proves primality, \(p\ge5\), \(p\nmid q\), coprimality to the reduced height, and \(p\le H^2\). In the LONG W stage those conditions are strengthened to coprimality with \(6q\), allowing CRT class manipulations with modulus \(M=6q\). The factors \(4+48q\) (row amplitude) and \(600q^2+8\) (R coefficient envelope) are allowed as fixed-\(q\) constants; nothing here claims a uniform theorem with \(q\to\infty\) as \(h\to\infty\).

## 5. Suzuki/VK: the difference between a true saving and a portable hypothesis

The parameters encoded in actual source files are
\[
\varepsilon_p=\Lambda^{-1/200},\quad \eta=\Lambda^{-1/10},\quad X_p=\lceil\Lambda^{200}\rceil,
\quad u_0(\delta)=\frac12\Bigl(\frac1{1+\delta}-\frac34\Bigr).
\]
Here \(u_0>0\) **requires** \(\delta<1/3\). At the final \(\delta=1/4\), \(u_0=1/40\), and the CORE prime-packet window ends near \(s^{1/40}\). The LONG-right window uses \(\lfloor s^\eta\rfloor\); the critical-edge boundary uses \(\lfloor s^{1/2+3\eta}\rfloor-1\). These cutoffs are not interchangeable, and the floors matter to the exact source partition.

The R-cell proof needs a lower bound on the logarithm of its short factor to apply a shifted Suzuki/Vinogradov–Korobov estimate. `GoldC.QuillonREv.R_exp_ev` requires \(L\ge5\Lambda^{\sigma_0-1/200}\); its LONG counterpart `GoldC.QuillonLR.R_exp_ev4` requires only \(L\ge4\Lambda^{\sigma_0-1/200}\). Both prove, for the relevant phase parameters, a saving as strong as \(\Lambda^{-200}\) at the local exponential stage. The crucial power in the comparison is **exactly**
\[
3\sigma_0-\frac3{200}-2
=\frac3{200}>0.
\]
The change \(5\to4\) changes the cubic multiplicative constant \(125\to64\), but not this positive exponent. LONG thus preserves the saving despite weaker source geometry, *after* re-proving the altered numerical inequality. This is a load-bearing parameter transport, not an innocuous renaming.

The `GoldB.shiftedSuzukiCore_unconditional` result pays the separately named Suzuki input in `PaperB/Gate3/SuzukiCentralOnly.lean`; the Central R/RL cells also call the relevant shifted reciprocal estimate. Do not count the one GoldB supplier as two independent proofs, or confuse it with a separate conditional `GoldC.VKCore` formulation.

## 6. Rates beyond CORE and LONG: HIGH, LOW, folded and literal Central

HIGH does not use the preceding decoration lift. `Orienne/Central/HighCardGrowingR0001.lean:18–~70` proves the entire **physical** HIGH sector, at `orienneCentralHighCut h = elowrynHighCutFromY(log(h²))`, is bounded by
\[
C_{\rm high}(q)=8e^{75}(4+48q)
\]
for \(h\ge3\), every anchor and even an arbitrary gate. Then `HighCardRateR0002.lean:20–46` uses the eventual elementary fact \(\log h\ge C_{\rm high}(q)/\epsilon\) to get `SourceUniformSublog`. **There is no hidden extra \(\Lambda^{1/1000}\) decoration factor here.**

LOW is an exact identity, not an estimate: `Thistle.LOW.lowSector_zero_exact` proves `lowSector (fun _=>0)=0`, and `lowSector_zero_sublog` chooses \(H_0=1\). `GoldC/QuillonCoreFinal.core_sublog` and `QuillonLongFinal.long_sublog` are already uniform in cutoff functions, so changing `Jlow` to zero reallocates the formerly LOW source parents into MIDDLE under the exact three-sector identity, without removing or changing them.

Within MIDDLE, `PaperB/Gate3/CentralTransfer/MiddleLongCoreConsumer.lean:~20–65` proves the **exact** source split `MIDDLE=LONG+CORE`. To get MIDDLE at tolerance \(\epsilon\), it requests LONG and CORE separately at \(\epsilon/2\). Then `ThreeSectorConsumer.lean:130–194` requests LOW, MIDDLE and HIGH each at \(\epsilon/3\) to obtain the folded Central rate. For a desired folded Central \(\epsilon\), this nested bookkeeping asks each of CORE and LONG for \(\epsilon/6\). In the next transport, `ThreeSectorTerminalAssembly.lean:66–110` itself requests folded Central at \(\epsilon/2\), and separately spends \(\epsilon/2\) on the error, so **CORE/LONG are ultimately requested at \(\epsilon/12\)** when proving the active Central rate at \(\epsilon\). These are successive *uses of separately quantified sublog theorems*, not additive exponent losses.

The folded-to-active comparison has the exact signed identity
\[
\mathrm{activeCentral}=\mathrm{folded}+(\mathrm{invRow}+\mathrm{densRow})
\]
with
\[
|\mathrm{activeCentral}-\mathrm{folded}|\le(6q+2)\,\mathrm{baseRate}(h),
\quad \mathrm{baseRate}(h)=4(1+\Lambda)^3Z(h)^{-1/2}e^{K_0}.
\]
`GoldC/QuarterFold.lean:838,894` proves `baseRate_small`, which tends to zero, not merely below \(\log h\). The comparison therefore requests `baseRate ≤ ε/[2(6q+2)]` and \(\log h\ge1\), enough to pay the remaining \(\epsilon\log h/2\). `ThreeSectorTerminalAssembly.lean:23–110` keeps original signed source equations, and lines 112–142 bridge the result into the literal R0056 Central consumer and then the paid Suzuki-only terminal assembly. `Orienne/CSC3/LowZeroTerminalR0001.lean:8–42` applies \(\delta=1/4\) and `Jlow≡0` to obtain the unconditional named native theorem.

Finally, `Orienne/Publication/PaperBPrintedTerminalR0001.lean:10–28` applies the **separately proved** literal Euler equality to rewrite printed A minus printed B into the named native kernel difference. It reuses the native \(h_0\) and epsilon; that is a semantic bridge, *not another analytic asymptotic estimate*. The frozen publication/cold-referee court remains separate from this source audit.

## 7. What would have broken the quantitative proof?

The companion `07_FALSIFIER_AND_REPAIR_COURT.md` contains a focused matrix of twelve threats and their source protections. The three most revealing are:

1. **Multiply the cell estimates when they should be added**: exponent \(0.998+0.1\) would exceed 1. The exact `split5`/`split7` equalities and triangle inequalities instead take the maximum exponent and multiply only by the cell count.
2. **Pay the decoration factor twice**: CORE would exceed exponent 1 if a second \(+1/1000\) were charged. The Lean `core_sublog` and `long_sublog` each apply the decoration majorant exactly once.
3. **Infer a theorem for growing q**: the source's q-dependent constants and eventual thresholds are fixed-*q* only. The quantifier order establishes uniformity in anchor and allowed heights, not a simultaneously growing conductor.

## 8. Verdict and next move

**Pass 5 source audit: complete at its advertised scope.** The public exponents, outer costs, decoration lift, epsilon conversions, original signed source identities, and terminal transports form a coherent quantitative route in the inspected immutable R0003 source. Archive hash and seal are checked; exact rational arithmetic is independently checked by Python. **No full Lean replay or independent mathematical referee certification is claimed.**

**Recommendation: CONTINUE to Pass 6.** The important next move is to unify Passes 1–5 into an atlas with a single navigable dependency/mechanism/estimate ontology. Preserve the conservative audit boundaries: source import reachability is not full proof-term reachability; paper-level originality is a different question from logical validity; and inherited/copy-normalized supplier interfaces must remain attributed. The visual waterfall already provides a usable prototype for the integrated atlas.
