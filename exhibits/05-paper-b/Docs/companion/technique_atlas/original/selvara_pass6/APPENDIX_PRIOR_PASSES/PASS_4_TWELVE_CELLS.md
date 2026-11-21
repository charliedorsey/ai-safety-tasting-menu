# Paper B Mathematical Technique Atlas — Pass 4
## Twelve ways to control one signed physical source

**Research edition R0001 · October 23, 2026 · Selvara / FACET**  
**Evidence:** read-only inspection of `PAPERB_PRINTED_TERMINAL_RC_R0003_TRIMMED_20261023.zip` (source SHA register included). **No Lean build or fresh kernel replay.** The independent release/referee review proceeds separately.  
**Notation:** `LEAN/GoldC/Foo.lean:L20-L40` points to exact lines in the attached source archive. `Λ = log h`, `ε = Λ^{-1/200}`, `η = Λ^{-1/10}`, `σ₀ = 2/3 + 1/100`. The source's `δ` is a fixed number with `0 < δ < 1/3`; it is *not* ε.

---

## Executive mathematical finding

The result is not one long application of Vinogradov–Korobov, or Weil, or sieve theory. It is a **source-preserving decision tree** that chooses among methods according to the geometry of the two coprime ordered parent products and their available prime packets. Five cells cover CORE; seven cover LONG. The **dominant** cell in each family is paid by *mass on a narrow geometric region*, not an oscillatory estimate:

- **Band** (CORE) is bounded by `Λ^{998/1000}`: a multiplicatively narrow near-diagonal strip and a roughness count.
- **EdgeL** (LONG) is bounded by `Λ^{19/20}`: a shrinking square-root-edge strip and a roughness count. It avoids asking Weil–Cauchy for a saving precisely where its extracted cofactor is too short.
- **WRL** (LONG) reaches `Λ^{-80}` using **Weil–Estermann** on a non-edge, *packet-bearing* region, retaining conductor gcd and zero/high-gcd Fourier modes rather than deleting them.

The wild negative powers in W, R, and C are not the global bottleneck; the thin-region cells set the global logarithmic exponents. This is a feature of the exact partition, not an informal heuristic. The proof's weak margins survive summation over decorations: CORE's `0.998` becomes `0.999`, LONG's `0.950` becomes `0.951`. See `LEAN/GoldC/QuillonCoreFinal.lean:L75-L157` and `LEAN/GoldC/QuillonLongFinal.lean:L88-L187`.

## 1. What exactly is being summed?

Fix the original squarefree conductor `q`, the anchor `a`, height `h`, a decoration `d`, and reduced height `H = h / primeSetProduct d`. The source defines a **finite ordinary-prime support** `Tsrc q h d`. A selected ordered pair `(B,C)` consists of nonempty disjoint subsets of `Tsrc`, with

\[
 r=\prod_{p\in B}p,\qquad s=\prod_{p\in C}p,\qquad
 \omega(B)\omega(C)=\prod_{p\in B\cup C}\frac{1}{p-3}.
\]

Every cell sums **the same signed physical row** `foldRow q a D H r s`, weighted by `ω(B)ω(C)`; `D = primeSetProduct d`. The row is an exact combination of a reciprocal sawtooth with a centered periodic potential difference. It retains the source CRT-residue selection and *both proper ordered orientations*. The physical admissibility includes the original sharp `Z(h)` floor, cardinality window `Jlow ≤ |B|+|C| < Jhigh`, and `centralGate` constraints

\[
 rs\le H\exp[-\Lambda^{1/4}],\qquad s\le r^2,\qquad r\le s^2,
\]

alongside the relevant additional masks. The exact definitions and the signed row occur in `LEAN/GoldC/QuillonPairParam.lean:L31-L126`, `LEAN/GoldC/QuillonCopyF.lean:L26-L30,L317-L325`, `LEAN/GoldC/QuillonWPhysical.lean:L37-L59`, and `LEAN/GoldC/QuillonLW.lean:L412-L429`. The guards cannot be replaced with a larger ambient region just because that would make an estimate attractive.

**Why double counting is absent.** `pairSum_eq_double` reindexes the original finite parent source into this disjoint ordered-pair form. `split5` and `split7` prove Boolean identities of the form `if actual source mask then f else 0 = sum of exactly one branch's f`, *for arbitrary signed f*. Summing those identities yields the physical equations

\[
\mathrm{CORE}_d=W_d+C_d+R_d+\mathrm{ResA}_d+\mathrm{Band}_d,
\]
\[
\mathrm{LONG}_d=WL_d+CL_d+RL_d+\mathrm{ManyL}_d+\mathrm{EdgeL}_d+\mathrm{ResL}_d+WRL_d.
\]

This is stronger than a heuristic dissection of a diagram: **the identity preserves every source summand and its sign**, including zero modes. Source: `LEAN/GoldC/QuillonCoreFinal.lean:L25-L71`; `LEAN/GoldC/QuillonLongFinal.lean:L27-L87`.

## 2. The physical cell ledger

The displayed exponents are *eventual per-decoration* bounds on the absolute value of the entire indicated signed cell. They hold with the specific source masks and hypotheses in the theorem files; they are not absolute bounds for arbitrary parent sets or all heights.

| Sector | Cell | Literal decision on admissible source | Technique doing the work | Per-decoration bound |
|:--|:--|:--|:--|--:|
| CORE | **W** | `B` has a W′ prime in `[X, s^{u₀}]` | Ramaré, coupled Cauchy, elementary fourth-moment Kloosterman | `Λ^-80` |
| CORE | **C** | no W′, `r ≥ s^{1+ε}` | Parseval-W for longer cofactor, Vaughan for shorter, Rankin tail | `Λ^-15` |
| CORE | **R** | no W′, no C, `s ≥ r^{1+3ε}`, `C` has an R prime packet | Ramaré on C, reciprocity, Suzuki AP, Abel summation | `Λ^-75` |
| CORE | **ResA** | as R but `C` misses its packet | double roughness + upper-bound sieve | `Λ^(1/10)` |
| CORE | **Band** | no W′, neither growth comparison | narrow multiplicative interval + weighted mass + rough B | `Λ^(998/1000)` |
| LONG | **WL** | LONG-left `s^{1+δ}<r`, B has W′ packet | elementary Kloosterman W′ (not Weil) | `Λ^-80` |
| LONG | **CL** | LONG-left, B misses packet | region-C Parseval/Vaughan/Rankin, constant-4 adapter | `Λ^-15` |
| LONG | **RL** | LONG-right `r^{1+δ}<s`, C has R packet | signed Suzuki AP + reciprocity + Abel; constant-4 | `Λ^-75` |
| LONG | **ManyL** | LONG-right, no R packet, `|C|≥⌈100 log Λ⌉` | Rankin many-prime-factor suppression | `Λ^-50` |
| LONG | **EdgeL** | LONG-right, no R packet, `|C|<K₀`, `r<s^{1/2+3η}` | rough C + thin B interval mass | `Λ^(19/20)` |
| LONG | **ResL** | no R, small C, outside edge, no B W′ packet | rough B × rough C | `Λ^(7/10)` |
| LONG | **WRL** | no R, small C, outside edge, **has** B W′ packet | Weil–Estermann, packet extraction, Cauchy, gcd-frequency ledger | `Λ^-80` |

This table is a navigational index. Source-precise decision masks, theorem anchors, falsifiers, and hashes are in `02_TWELVE_PHYSICAL_CELLS.csv` and `03_MECHANISM_CARDS.json`.

## 3. Why CORE has five cells

Set `ε=Λ^{-1/200}`; `X=ceil(Λ^200)`; and choose `u₀>0` using `δ<1/3`. For each CORE pair:

1. **W present:** `B` contains a usable prime in `[X,⌊s^{u₀}⌋]`. Extract it by the Ramaré identity; Cauchy and completion convert the row into a Kloosterman problem. The elementary `s^{3/4}`-strength majorant suffices because the CORE shape and `δ<1/3` keep the cofactor long enough. Outer harmonic parent mass is at most a constant times `Λ^10`. The fixed-outer saving `Λ^-95` becomes a physical `Λ^-80`. `QuillonWPhysical.lean:L48-L163`.
2. **W absent, r large:** `r≥s^{1+ε}`. The C method splits the extracted cofactor: for large `n`, use Parseval-W and bilinear orthogonality; for small `n`, Vaughan's prime decomposition and a Rankin bad-set estimate. Its per-fixed-C bound `Λ^-30` survives the outer `Λ^10` to `Λ^-15`. `QuillonCPhysical.lean:L514-L680`, `QuillonCContext2.lean`, `QuillonCFinal.lean`.
3. **W and C absent, s large:** `s≥r^{1+3ε}`. If C contains a prime in the R packet `J_R(B)`, extract that prime. Reciprocity and class splitting turn the oscillatory sum into a shifted reciprocal exponential sum; `suzuki_AP` invokes the unconditional **GoldB shifted Suzuki** theorem, including negative frequencies by complex conjugation, and `class_amp_bound` uses Abel variation on the genuine source coefficients. `QuillonRPhysical.lean:L385-L515`; `QuillonRLemma.lean:L52-L90`; `QuillonRMode.lean:L88-L100`.
4. **Same geometry but no R packet:** the missing packet creates **actual arithmetic roughness** on the C side, while W absence makes B rough. A crude upper-bound sieve becomes cheaper than trying to recover an unavailable oscillatory variable. `QuillonResPhysical.lean:L208-L399`.
5. **Neither growth condition:** `r<s^{1+ε}` and `s<r^{1+3ε}`. This is Band, where weighted interval counting beats oscillation. `QuillonResPhysical.lean:L220-L229,L404-L587`.

**Methodological point:** W and R only work after a physical packet has been proved to exist. The complementary cases have their own proofs; “assume a convenient prime exists” is not a legitimate gap-filler.

## 4. Why LONG has seven cells

The LONG test asks whether `s^{1+δ}<r` (left) or `r^{1+δ}<s` (right). The two orientations are disjoint when `δ>0`. On the LONG-left, the CORE W/C methods survive after careful adaptation: W′ if B contains a packet, C otherwise. On LONG-right, the R method works if C has its packet. Otherwise there are *four* genuinely different situations:

- `|C|≥K₀`: many-prime-factor Rankin suppression (**ManyL**).
- `|C|<K₀` and `r<s^{1/2+3η}`: an exceptionally thin edge (**EdgeL**).
- `|C|<K₀`, outside that edge, and B has **no** W′ packet: rough B times rough C (**ResL**).
- same non-edge but B **has** a W′ packet: enough cofactor range to use Weil-strength W′ (**WRL**).

Here `η=Λ^{-1/10}`, `K₀=ceil(100 log Λ)`. `GoldC/QuillonLRP.lean:L1-L76`, `GoldC/QuillonLongFinal.lean:L27-L87` show that the distinction is exhaustive. The no-packet regime is **explicitly** part of the same partition; no universal packet assumption has been smuggled into LONG.

## 5. The EdgeL versus WRL experiment

These are neighboring cells with incompatible mathematical needs. Both sit on LONG-right, after excluding R packets and many-factor C. The remaining first question is whether `r` lies too near `√s`.

### EdgeL: count the troublesome region

The central gate yields `s≤r²`, hence `r≥s^{1/2}`. The EdgeL guard supplies `r<s^{1/2+3η}`. Thus, for fixed `s`,

\[
\boxed{s^{1/2}\le r<s^{1/2+3\eta}},\qquad \eta=\Lambda^{-1/10}.
\]

That is narrow on a logarithmic scale: `log(v/u) ≤ 1+3η log s ≤ 1+3Λ^{9/10}` after the source's floor adjustments. `interval_mass` controls weighted B-products in this window without cancellation. C misses the R packet, so a source-derived C-roughness estimate applies. The exact numerical budget in `EdgeL_physical` is

\[
\underbrace{\tfrac1{4000}}_{\text{roughness overhead}}+
\underbrace{\tfrac1{40}}_{(\varepsilon/2)^{-5}}+
\underbrace{\tfrac1{100}}_{\text{interval-mass overhead}}+
\underbrace{\tfrac9{10}}_{\eta\Lambda}
=\tfrac{3741}{4000}<\tfrac{19}{20}.
\]

The slack `59/4000` absorbs a fixed source-dependent constant (including the bound for `foldRow`). Nothing here invokes `WeilHyp`. `GoldC/QuillonLRP.lean:L385-L566`.

### WRL: extract arithmetic cancellation away from that edge

On the complement, `r≥s^{1/2+3η}` and B contains a prime in `[X,⌊s^η⌋]`. Write the extracted factor `r=y n` with `y≤s^η`: the remaining cofactor has room to be at least on the order of `s^{1/2+2η}`, which is the critical geometric margin. `QuillonLWR.lean:L25-L35` records the floor and eventual-threshold details.

The complete Kloosterman bound used in WRL is the **general-modulus Weil–Estermann** inequality, with conductor and divisor factors:

\[
\|K_s(a,b)\|\le\tau(s)\sqrt{s\,\gcd(a,b,s)}.
\]

For squarefree `s=∏P`, the source bounds the frequency-dependent majorant using `4^{|P|/2} s^{1/2}` times the square root of the relevant gcd contribution, then applies a frequency-moment estimate. Its coupled Cauchy square contains the diagonal `1/X`, the trivial `1/s` term, and a term involving `s^{1/2}/N`, *with its frequency gcd retained*. The `η` margin turns `s^{1/2}/N` into a negative power `s^{-2η}`; the eventual exponential lower bound in `log s` beats the polylogarithmic multipliers. `QuillonLWeil.lean:L32-L121`; `QuillonLWeilB.lean:L31-L42`; `QuillonLWR.lean:L103-L110`.

At fixed C, four source Fourier modes and class amplitudes are controlled together to get `4Λ^-95`. Summation over C costs at most `Λ^10`; a fixed constant is absorbed and the stated physical rate is `Λ^-80`. Source: `QuillonLWR.lean:L457-L571`; `QuillonLRP.lean:L156-L244`.

**Why the split is necessary:** near the precise half-power edge the Weil/Cauchy cofactor is too short for the desired fixed saving, but the edge's logarithmic width is cheap. Away from the edge, that cofactor is long and the W′ prime packet gives a variable on which Weil can act. Neither argument silently extends into the other's masked region.

## 6. The R → RL port: a quantitative warning about constants

`QuillonRLemma.suzuki_AP` is a literal residue-class form of `GoldB.shiftedSuzukiCore_unconditional`. The substitution `θ=ρ/Q` and `Y/Q` changes the phase to the sharp progression `1/(ρ+Qt)`, with both signs handled. `class_amp_bound` then applies Abel summation to the actual varying Fourier coefficients. In CORE R and LONG RL the mechanism is the same, but the *admissibility constant is not*.

CORE's geometric condition supplies a lower logarithm of the shorter factor with coefficient 5 in the `R_exp_ev` supplier. LONG only has the gate `r≤s², s≤r²` and `Z(h)<rs`, giving the honest threshold `4Λ^{σ₀}` (`QuillonLSetup.lean:L94-L149`). `RL` therefore uses `R_exp_ev4` and different fixed arithmetic constants. The positive exponent still survives:

\[
3\sigma_0-\frac3{200}-2
=3\left(\frac23+\frac1{100}\right)-\frac3{200}-2
=\frac3{200}>0.
\]

Changing 5 to 4 is not changing the terminal theorem, but reusing the stronger CORE hypothesis without proof would make the LONG port incorrect. `QuillonLR.lean:L53-L82,L528-L645`; `QuillonREv.lean:L34-L62`.

## 7. The absolute mass cells are not discarded errors

For **ResA**, absence of W′ and R packets creates double roughness, leading to `Λ^(1/10)` rather than a sign-saving estimate. For **ResL**, outside EdgeL, absent B and C packets likewise gives `Λ^(7/10)`. Both are strictly smaller than `Λ`, so the strategy has no obligation to find cancellation where it lacks a variable.

For **ManyL**, the inequality `|C|≥K₀=ceil(100 log Λ)` provides a `3^{-K₀}` Rankin penalty. Its large factor `Λ^{-100}` dominates a crude `Λ^{30}` moment and the outer `Λ^{10}` mass: the pre-constant exponent is `-60`, relaxed to `-50`. See `QuillonLRes.lean:L194-L207` and `QuillonLRP.lean:L91-L152`.

For **Band**, the interval 
\[
 r^{1/(1+\varepsilon)}<s<r^{1+3\varepsilon}
\]
has logarithmic width `O(ε log r)`, hence `O(Λ^{199/200})`. Weighted interval mass and rough B each contribute `Λ^{1/4000}`. The exact total is
\[
\tfrac1{4000}+\tfrac1{4000}+\tfrac{199}{200}=\tfrac{1991}{2000},
\]
leaving only `1/400` logarithmic exponent to absorb fixed constants before the claimed `Λ^{998/1000}`. This is the **narrowest** cell-level margin among the geometric mechanisms. See `QuillonResPhysical.lean:L404-L587`.

## 8. How the twelve bounds recombine

The precise physical estimates are not twelve independent `o(log h)` claims about any imaginable sum: they control source-filtered cells for `Λ≥Λ₀` where `Λ₀` depends on fixed parameters. The sum identities then give, at each decoration `d`,

\[
|\mathrm{CORE}_d|\le 5\Lambda^{998/1000},
\qquad
|\mathrm{LONG}_d|\le7\Lambda^{19/20}.
\]

The cell inequalities include all original source coefficients and sharp masks, and the outside factor ``decorationWeight`` is nonnegative. `QuillonCoreFinal.core_sublog` and `QuillonLongFinal.long_sublog` supply a source-specific decoration-mass estimate of at most an eventually arbitrarily mild positive power, and explicitly use an extra `Λ^{1/1000}`. The global rate budgets are therefore

\[
\boxed{\mathrm{CORE}=O(\Lambda^{999/1000})},\qquad
\boxed{\mathrm{LONG}=O(\Lambda^{951/1000})}.
\]

Because both exponents are **strictly** below one, the final proofs select an eventual threshold for each requested `eps>0` and obtain `SourceUniformSublog`. The fixed conductor `q` and anchor-uniformity are carried through the statement and proof; they are not reconstructed by an after-the-fact asymptotic claim.

Both `core_sublog` and `long_sublog` quantify over **arbitrary** `Jlow,Jhigh` functions. That becomes decisive in the native terminal, where `Jlow≡0` empties LOW *without dropping source parents*: the low-to-middle exact partition moves them into MIDDLE, now controlled by CORE+LONG. Source: `QuillonCoreFinal.lean:L118-L196`, `QuillonLongFinal.lean:L148-L235`, `PaperB/Gate3/CentralTransfer/ThreeSectorConsumer.lean:L30-L92`, `PaperB/Gate3/CentralTransfer/MiddleLongCoreConsumer.lean:L10-L65`.

## 9. Source-fidelity and theorem-standing court

- The archive was inspected read-only. This pass introduces **no replacement Lean lemmas**, no new axioms, and no changes to the mathematical source.
- The attached source itself contains Lean proofs of `split5`, `split7`, `pair_decomp`, `long_pair_decomp` and the twelve `*_physical` estimates. Their statements and proof bodies were inspected. **No fresh kernel replay** was run; independent full-build and referee verification are separate.
- `QuillonLongFinal.long_sublog` is **conditional on a named `WeilHyp`** at its own declaration. The curated bridge `Orienne.CSC3.norm_quillon_K_weil` discharges that hypothesis using a generalized Kloosterman theorem after an exact normalization identity. Calling LONG “unconditional” before binding that bridge would be misleading.
- “Per-decoration” means a bound on the weighted, signed B,C pair sum **for fixed decoration d**, not a bound on an individual parent pair. The outside decoration sum is a separate proof operation.
- The source contains complicated masks, floors, CRT residue conventions, and exceptional zero/high-gcd frequencies. A prose description is deliberately less precise than the exact source definitions. The CSV/JSON provides source locations and what breaks if a mask is weakened.
- The stored report is **mathematical archaeology** of source proofs, not an independent correctness certification of the printed theorem.

## 10. What is distinctive and reusable?

The individual tools are largely classical: Cauchy–Schwarz, Parseval, Abel summation, Vaughan, Ramaré, Rankin, sieves, Vinogradov–Korobov, elementary and Weil-strength Kloosterman bounds. What is distinctive *inside this proof* is their **source-preserving assembly**: a precise decision tree pays different geometric regimes by different tools, carries the original signed source through transforms, and exposes every factor in the numerical saving ledger.

The most transferable lemma-design lesson is not “find a stronger exponential-sum theorem”. It is **separate the region where an estimate has room to save from the region small enough that saving is unnecessary**. In LONG that principle is literal: EdgeL and WRL are adjoining children of a single exact Boolean split. In CORE the same principle appears between the cancellation cells and Band.

---

### Companion artifacts

- `02_TWELVE_PHYSICAL_CELLS.csv` — complete cells/masks/arguments/results/source references
- `03_MECHANISM_CARDS.json` — typed cards, source SHA256, failure-of-generalization notes
- `04_POWER_LEDGER.csv` — all twelve rational exponent calculations
- `05_SOURCE_HASH_REGISTER.csv` — relevant exact-source hashes
- `07_EDGE_VS_WRL_MICROSCOPE.md` — detailed side-by-side derivation
- `08_EXACT_PARTITION_DECISION_TREE.md` — exact-support decision tree and coverage proof
- `09_R_VS_RL_CROSSWALK.md` — shared Suzuki machinery and critical constants
- `10_INTERACTIVE_TWELVE_CELLS.html` — standalone search/filter and exponent comparison
- `11_PASS5_COMMISSION.md` — proposed next source court
