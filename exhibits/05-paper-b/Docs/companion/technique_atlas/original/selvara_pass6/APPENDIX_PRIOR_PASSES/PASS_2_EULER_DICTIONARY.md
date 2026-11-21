# Paper B Mathematical Technique Atlas - Pass 2
## The finite dictionary and printed Euler-product bridge

**Selvara / FACET | 23 October 2026 source snapshot | Read-only mathematical inspection**

**Standing:** A source-grounded mathematical reconstruction of the supplied release-candidate's F-01 bridge and finite dictionary. No new Lean build, axiom replay, or claim of independent mathematical refereeing. All file/line references below are relative to the archive's `LEAN/` and `MANUSCRIPT/` roots. The archive's outer SHA-256 is `e8bccaf4c607a3b2458a47833bdd98f598a59229f7af0175927b994318d7b2a1`. The frozen TeX SHA-256 is `9004c20d63218b529ea392d13914c17a347c485fd43814eb88bf8612a8512070`.

## Executive mathematical finding

The independently defined printed singular series is not merely assigned a new name in Lean. Its passage to the final kernels uses two different exact mechanisms:

- **A, the anchored three-point term:** an admissible Euler product is divided by a provably **nonzero** two-point Euler product. Primewise quotient identities separate the exceptional primes 2 and 3 from the high primes. The resulting product is precisely the product appearing in `manuscriptA1Kernel`. The subtraction is the *exact* admissible count, not its mean.
- **B, the two boundary terms:** the two-point Euler product factors into a fixed high-prime baseline, finite exceptional-prime factors, and a finitely supported squarefree divisor selector. A separate absolutely convergent Euler identity proves that the baseline times the reciprocal-divisor mass is exactly 1. This licenses a centered infinite divisor sum. The second endpoint is then turned into the first by `y -> h-y` and a congruence-based coprimality equivalence.

The public theorem performs one `rw` with the joint printed difference identity and then applies the already proved native asymptotic theorem (`Orienne/Publication/PaperBPrintedTerminalR0001.lean:8-28`). Thus the F-01 bridge changes **representation**, not the final analytic estimate.

## 1. Freeze the actual printed objects

The frozen manuscript, `paper_b_frozen.canonical.tex:51-63`, defines

\[
\mathfrak S_q(H)=\prod_{p\nmid q}\left(1-\frac{\nu_p(H)}p\right)\left(1-\frac1p\right)^{-|H|},
\qquad \nu_p(H)=|H\bmod p|.
\]

The independent Lean definitions (`Orienne/Publication/F01PrintedLiteralBridgeR0001.lean:13-21`) are:

```
occupiedResidues p H := H.image (fun x => x % p)
printedLocal p H := (1 - (occupiedResidues p H).card / p) / (1 - 1/p)^H.card
printedRestrictedSingularSeries q H :=
  tprod p, if p.Prime && not (p | q) then printedLocal p H else 1
```

Here `tprod` denotes Lean's `\prod'` infinite product. The inactive prime factor is literally 1, including primes dividing `q`. The printed terminal's `A` is independent of `b` as a formula, though the manuscript writes `A_{1,q}(a,b;h)` because `b` determines the permitted height progression. The `B` expression uses `b` through endpoint compatibility in the reflection theorem.

The manuscript's actual level-one definitions (`TeX:198-222`) are

\[
I_q(a;h)=\{y:0<y<h,\ (a+y,q)=1\},\quad N_q(a;h)=|I_q(a;h)|,
\]
\[
A_{1,q}=\sum_{y\in I_q(a;h)}\left(\frac{\mathfrak S_q(\{0,y,h\})}{\mathfrak S_q(\{0,h\})}-1\right),
\]
\[
B_{1,q}=\sum_{y\in I_q(a;h)}(\mathfrak S_q(\{0,y\})-1)+
\sum_{y\in I_q(a;h)}(\mathfrak S_q(\{h,y\})-1).
\]

They are stated this way in `printedA1Literal` (`F01:574-579`) and `printedB1Literal` (`F01:1432-1440`), respectively. The equality of the printed B sum with the original Boolean-connected expression uses singleton normalization in the TeX (`TeX:211-222`); the F-01 file starts from the simplified explicit B expression.

## 2. A: a complete source-to-kernel equality chain

Define for each prime `p`

\[
F_p(H)=\frac{1-\nu_p(H)/p}{(1-1/p)^{|H|}},\qquad
\rho_p(h,y)=\frac{1-\nu_p(\{0,y,h\})/p}{1-\nu_p(\{0,h\})/p}\cdot\frac1{1-1/p}.
\]

The intended local identity is exactly

\[
F_p(\{0,y,h\})=F_p(\{0,h\})\rho_p(h,y)
\]

whenever `0<y<h` and the pair denominator is nonzero. `printed_triple_local_quotient` proves this for `p>=5` (`F01:205-232`), while `printed_active_local_quotient_eq_occupied` proves the **quotient** identity for *every active prime*, including 2 and 3, under the parity condition (`F01:363-410`). No triple-factor nonzero hypothesis is needed: an inadmissible triple is allowed to have local factor zero.

### 2a. Why an infinite-product quotient is legal

The proof establishes three different properties, which must not be conflated:

1. **Endpoint-product convergence.** Above `p>max(4,h)`, the pair has distinct residue classes and its printed local factor equals the already summably controlled baseline `normalizationBaseline q 0 p`. At every sufficiently large active prime, this is
   \(c_1(p)=p(p-2)/(p-1)^2=1-1/(p-1)^2\), so deviations from 1 have summable `p^{-2}` size. The Lean route is `printedLocal_pair_eq_baseline` -> `printed_pair_summable_deviation` -> `printed_pair_multipliable` (`F01:41-104,146-157`; existing baseline summability in `PaperB/FixedQ/DivisorExpansion.lean:863-899`).
2. **Every active pair factor is nonzero.** For `p>=3`, the pair occupies at most two classes, so `1 - nu_p/p > 0`. At the exceptional prime 2, the pair is admissible if the prime is excluded by `p|q` or the height is even. The latter is supplied by `not (2|q) -> 2|h`. See `printed_pair_local_positive_high`, `printed_pair_local_positive_two`, `printed_pair_factor_ne_zero` (`F01:108-178`).
3. **The whole endpoint product is nonzero.** Pointwise nonzero factors alone do not suffice for an infinite product. The file combines summable deviations from 1 with `tprod_one_add_ne_zero_of_summable` to prove `printed_pair_tprod_ne_zero` (`F01:182-195`). It also proves printed triple-product convergence from the high-ratio convergence and a *finite* exceptional-prime correction (`F01:268-334`). Only then can `Multipliable.tprod_div0` be applied (`F01:342-356`).

### 2b. The small primes are not silently absorbed

`lowPrimeSet={2,3}` is an explicit finite set (`PaperB/FixedQ/DivisorExpansion.lean:1569`, used at `F01:417-500`). Every prime not dividing `q` contributes its actual occupied triple/pair quotient. The factorization separates

\[
\frac{\mathfrak S_q(\{0,y,h\})}{\mathfrak S_q(\{0,h\})}
=\left(\prod_{p\in\{2,3\},\,p\nmid q}\rho_p(h,y)\right)
\left(\prod_{\substack{p\ge5\text{ prime}\\ p\nmid q}}\rho_p(h,y)\right).
\]

This is `printed_quotient_eq_occupied_euler` (`F01:453-500`). The low product is literal, not a harmless unnamed `O_q(1)` factor. The high product is `occupiedActiveHighLocalRatio`. The proof carefully distinguishes `printedSmallCorrection` (a temporary finite support mechanism for *triple convergence*) from `printedOccupiedLowRatio` (the actual low-prime quotient when splitting the infinite quotient).

### 2c. Put the genuine arithmetic indicator back

`manuscriptAnchoredSummand` is defined by

\[
\mathbf 1_{(a+y,q)=1}\prod_{p\in\{2,3\},p\nmid q}\rho_p(h,y)
\cdot\prod_{p\ge5,p\nmid q}\rho_p(h,y),
\]

in `PaperB/FixedQ/SourceBridge.lean:17-30`, via `occupiedFixedQLowWeight` and `occupiedActiveHighLocalRatio`. The source's `printedA1Weighted` is exactly

\[
\sum_{0<y<h}\mathbf1_{(a+y,q)=1}
  \frac{\mathfrak S_q(\{0,y,h\})}{\mathfrak S_q(\{0,h\})}
  -N_q(a;h).
\]

The local quotient equality applies **per admissible interior y** (`printedA1Weighted_eq_manuscriptA1Kernel`, `F01:517-532`). The remaining conversion is elementary but source-critical:

\[
\sum_{y\in I_q}(R_y-1)=\sum_{0<y<h}\mathbf1_{(a+y,q)=1}R_y-N_q(a;h).
\]

`printed_admissible_count_eq` proves the exact translated-cardinality bijection (with no approximation) and `printedA1Literal_eq_weighted` uses `Finset.sum_boole` (`F01:539-611`). Therefore `printedA1Literal_eq_manuscriptA1Kernel` follows (`F01:613-617`). It assumes **only** the parity implication, not a new analytic saving.

**Complete A chain** (each arrow has a named source theorem):

```
TeX eq:S_q, eq:A1q
 -> printedRestrictedSingularSeries + printedA1Literal
 -> printed_pair_multipliable + printed_pair_tprod_ne_zero
 -> printed_triple_multipliable + printed_triple_endpoint_quotient
 -> printed_active_local_quotient_eq_occupied
 -> printed_occupied_factor_split + printed_quotient_eq_occupied_euler
 -> printedA1Weighted_eq_manuscriptA1Kernel
 -> printed_admissible_count_eq + printedA1Literal_eq_weighted
 -> printedA1Literal_eq_manuscriptA1Kernel
```

## 3. The actual A high-prime selector algebra

The high-prime machinery in the native kernel is not simply a mysterious arithmetic weight. With

\[
c_0(p)=\frac{p(p-3)}{(p-1)(p-2)},\qquad
c_1(p)=\frac{p(p-2)}{(p-1)^2},
\]

`PaperB/FixedQ/DivisorExpansion.lean:33-83` proves the following local cases for `p>=5` (with `y<=h`):

| Prime geometry | Anchored local ratio | Baseline and selector |
|---|---|---|
| `p|h` and `p|y` | `p/(p-1)` | `c1(p) * (1+1/(p-2))` |
| `p|h` and `p` does not divide `y` | `c1(p)` | `c1(p)` |
| `p` does not divide `h`, but `p|y` or `p|(h-y)` | `p/(p-1)` | `c0(p) * (1+1/(p-3))` |
| `p` divides none of `h,y,h-y` | `c0(p)` | `c0(p)` |

For `p` not dividing `h`, the left/right conditions cannot both occur, which makes the selector partition exact. The high baseline is a product of `c0` or `c1` according to `p|h`; the selectors encode the divisibility of the actual interior point and its reflected offset. The pair of selectors is the exact algebraic gateway to two-dimensional divisor constraints, rather than an estimate. `fixedQLevelOneKernel_divisorExpansion` (`DivisorExpansion:1581-1606`) and the manuscript source bridge (`SourceBridge:47-72`) connect this kernel to the later double-divisor sum. We do **not** attempt its full downstream analytic evaluation in Pass 2.

## 4. B: product -> squarefree divisor sum -> centered row

For the free two-point pair `{0,y}`, every high active prime has baseline `c1(p)`:

\[
F_p(\{0,y\})=c_1(p)
  \left(1+\frac{\mathbf1_{p\mid y}}{p-2}\right),
\qquad p\ge5,\ p\nmid q.
\]

This is `printed_pair_high_eq_baseline_selector` (`F01:631-664`). Since `y>0`, the nontrivial selector primes divide `y`, giving *finite* support (`F01:670-682`). Separating `p=2,3` and multiplying the three convergent products yields

\[
\mathfrak S_q(\{0,y\})=L_{q}^{\rm free}(y)\,C_{f,q}
       \prod_{\substack{p\mid y\\p\ge5,\,p\nmid q}}
          \left(1+\frac1{p-2}\right),
\]

where `L_free` is the exact low-prime factor and
\(C_{f,q}=\prod_{p\ge5,p\nmid q}c_1(p)=\mathrm{freeHighBaseline}(q)\).
Source: `printed_pair_factor_split` + `printed_pair_tprod_factorization` (`F01:687-772`); native `freeLowPrimeFactor` and `freeHighBaseline` in `PaperB/FixedQ/PrincipalOneDimensionalCancellation.lean:42-51,509-510`.

Define the *squarefree* high-divisor coefficient

\[
\eta_q(e)=\mu^2(e)\mathbf1_{(e,6q)=1}
 \prod_{p\mid e}\frac1{p-2}.
\]

This is `etaCoeff` in `PaperB/FixedQ/PetermannInterface.lean:25-29`, not an informal replacement coefficient. Each prime subset of `y.primeFactors` corresponds to a distinct squarefree divisor of `y`; inactive primes give zero coefficients, and higher prime powers give zero. `Finset.prod_one_add`, `printedEtaCoeff_primeSubsetProduct`, and `printed_eta_divisors_eq_powerset` (`F01:779-938`) establish

\[
\prod_{p\mid y,\,p\ge5,\,p\nmid q}
  \left(1+\frac1{p-2}\right)=\sum_{e\mid y}\eta_q(e).
\]

This is finally `printed_pair_divisorExpansion` (`F01:952-969`):

\[
\boxed{\mathfrak S_q(\{0,y\})=
 L_q^{\rm free}(y) C_{f,q}\sum_{e\mid y}\eta_q(e).}
\]

### 4a. The infinite normalization is a separate theorem

One must show

\[
\boxed{C_{f,q}\sum_{e\ge1}\frac{\eta_q(e)}e=1.}
\]

It is *not* inferred from the preceding finite expansion. The proof defines `etaReciprocalTerm(q,e)=etaCoeff(q,e)/e`, proves this is a multiplicative arithmetic function, zero on prime powers `p^nu` with `nu>=2`, and absolutely summable (`PaperB/FixedQ/EtaReciprocalTail.lean:9-142,545-624`). The summability proof itself is a piece of classical finite analysis: a Rankin-type control of the unweighted partial sums, followed by discrete Abel/partial summation to obtain an `O(1/X)` reciprocal tail (see `EtaReciprocalTail:158-215,250-290,447-538,611-624,659-680`).

Mathlib's `ArithmeticFunction.IsMultiplicative.eulerProduct_tprod` converts the infinite divisor series to the prime-power Euler product (`F01:978-1044`). At each active high prime its Euler factor is

\[
1+\frac1{p(p-2)}=\frac{(p-1)^2}{p(p-2)}=c_1(p)^{-1},
\]

and it is 1 at inactive primes. Multiplying by `C_f` gives 1 using `tprod_inv0` and the nonzero baseline product (`F01:998-1061`). The absolute summability and nonvanishing steps are necessary to make these identities legal for infinite products and sums.

### 4b. A finite numerator, but an infinite centered tail

Let

\[
W_{q,r}(y)=\mathbf1_{(r+y,q)=1}L_q^{\rm free}(y),\qquad
R_e=\sum_{\substack{0<y<h\\e\mid y}}W_{q,r}(y),\qquad N=N_q(r;h).
\]

By the printed pair expansion, the first B boundary sum satisfies

\[
S_{q,r}(h)=C_{f,q}\sum_{0<y<h}W_{q,r}(y)
      \sum_{e\mid y}\eta_q(e)-N.
\]

For every *fixed* interior `y<h`, all divisors `e|y` satisfy `e<h`. This allows an exact **finite** change of summation order:

\[
C_{f,q}\sum_{e<h}\eta_q(e)R_e-N.
\]

`printed_free_weighted_divisor_swap` proves the finite Fubini identity (`F01:1074-1128`). Since `R_e=0` for `e>=h`, `printed_free_row_tsum_eq_finite` extends only the numerator to an infinite sum (`F01:1130-1153`). The reciprocal eta sum is separately absolutely summable. Thus

\[
\begin{aligned}
S_{q,r}(h)
&=C_{f,q}\sum_{e\ge1}\eta_q(e)R_e-N\\
&=C_{f,q}\sum_{e\ge1}\eta_q(e)
    \left(R_e-\frac Ne\right).
\end{aligned}
\]

The second line uses the exact normalization in Section 4a and summability of *both* components (`printed_free_centered_sum`, `F01:1185-1253`). **Important nuance:** for `e>=h`, `R_e=0`, but `-N/e` does not vanish. Therefore the centered infinite series cannot be truncated at `e<h` without restoring its normalization tail. This is the main technical lesson of the B bridge.

The Lean target is `manuscriptFreeBoundaryDelta(q,r,h,e)=R_e-N/e` and `manuscriptS1Kernel(q,r,h)=C_f \sum_e eta_q(e)(R_e-N/e)` (`PaperB/Closure.lean:140-155`). `printedS1Literal_eq_manuscriptS1Kernel` proves the complete equality (`F01:1266-1330`) with no new asymptotic hypothesis.

### 4c. Reflection pays the second boundary term

For the printed term at the right endpoint, `y` is replaced by `z=h-y`. The set of occupied residue classes for `{h,y}` is a translate of that for `{0,h-y}`. Cardinalities agree for every prime, so the whole restricted singular series agrees (`printed_pair_occupied_translate`, `printed_pair_local_translate`, `printed_pair_singularSeries_translate`, `F01:1340-1378`).

The **admissibility indicator** also has to move. Under `a+h = b (mod q)`, the two numbers

\[
a+(h-z)\quad\text{and}\quad (-b\bmod q)+z
\]

sum to a multiple of `q`. Hence each is coprime to `q` precisely when the other is (`PaperB/Closure.lean:40-122`). The row bijection itself is `rowConstrainedMass_reflect` (`PaperB/FixedQ/RowReflection.lean:7-46`). Together these prove

\[
\sum_{y\in I_q(a;h)}\bigl(\mathfrak S_q(\{h,y\})-1\bigr)
   =S_{q,-b}(h).
\]

`printed_reflected_anchor_eq_S1` (`F01:1392-1428`) carries both the series and the indicator; `printedB1Literal_eq_manuscriptB1Kernel` (`F01:1432-1455`) then proves

\[
\boxed{B_{1,q}(a,b;h)=S_{q,a}(h)+S_{q,-b}(h)
=\mathrm{manuscriptB1Kernel}(q,a,b,h).}
\]

The reflected class `-b` is represented canonically by `(q - b%q)%q`; the proof does not assume an ordinary integer equality `a+h=b`.

## 5. The finite Boolean dictionary and fixed-period counting

These are distinct mathematical techniques of the manuscript. Do **not** assume that every lemma here occurs in the final `paperB_printed_terminal` proof term just because its module is in the import closure: the exhaustive constant-DAG extraction remains pending.

### Boolean endpoint contraction

`PaperB/Boolean/EndpointContraction.lean:33-170` formalizes the Boolean Mobius transform

\[
(Mf)(S)=\sum_{T\subseteq S}(-1)^{|S|-|T|}f(T).
\]

On the endpoint fiber, zeta summation cancels Mobius inversion and returns evaluation at the full endpoint set. Applying the free-label Mobius transform and using pointwise evaluation gives the exact paper formula (`TeX:83-120`):

\[
\boxed{Z_E M_E M_T f=M_T(\mathrm{ev}_E f).}
\]

The proof is finite incidence algebra (`zeta_mobius_on`, `mobius_apply`, `endpointContractionPointwise`), not an estimate and not the eventual signed Central cancellation. The theorem is polymorphic in the coefficient abelian group and does not import Euler products. In particular, the paper's singleton-connected A/B identities are mathematically motivated by this dictionary; the printed Euler F-01 proof starts from their explicit level-one formulas rather than redoing this Mobius contraction inside every term.

### Exact admissible-position counting

`PaperB/FixedQ/PeriodicCount.lean:29-135` defines

\[
N_q(a;h)=\#\{a<x<a+h:\gcd(x,q)=1\}
\]

and proves that adjoining a complete period of length `q` adds exactly `phi(q)` points (using Mathlib's `Nat.filter_coprime_Ico_eq_totient`). On each compatible height progression,

\[
N_q(a;h)=\frac{\varphi(q)}q h+\epsilon_q(a,b)
\]

**as an exact equality**, with `epsilon_q(a,b)` independent of the positive representative chosen in that class. `printed_admissible_count_eq` separately translates the range to `0<y<h` (`F01:539-570`).

The exact equation explains the fixed-period arithmetic, but the F-01 bridge does **not** substitute `phi(q)h/q` for `N_q(a;h)` at either A or B. All normalizations remain exact, and the periodic-error lemma is not a license to discard a term from an identity.

### Where CRT is and is not being used in Pass 2

The finite dictionary is Boolean algebra. The F-01 bridge's low factors use explicit residue counts and coprimality modulo `q` and `lcm(6,q)`; the divisor swap uses direct divisibility. We have not traced the full selected CRT class and physical row-fold mechanics needed for Central. Those are later-pass obligations, not proved anew by the 1,481-line F-01 file. The lack of a full CRT trace here is deliberate scope control, not a statement that the full proof lacks CRT.

## 6. An exact assumption ledger

| Source step | Hypotheses consumed locally | Why they matter |
|---|---|---|
| Printed pair product convergence | `0<h` | Eventual equality to baseline once `p>h` |
| Pair nonzero product | `0<h`, `2|q OR 2|h` | Prevent the only possible active pair obstruction at `p=2` |
| Triple/pair quotient | `0<y<h`, pair parity | Triple may vanish; denominator may not |
| Printed A bridge | `not (2|q) -> 2|h` | Converts to disjunction and pays low-prime ratio |
| Printed free pair divisor expansion | `0<y` | Nontrivial selectors supported on primes dividing `y` |
| Reciprocal-eta Euler identity | `q` is a natural number; native support assumptions encoded in coefficient | Absolute summability and factor inversion; no `h` |
| First boundary S1 bridge | No separate `q>0` or parity hypothesis in its declaration | Finite sum, exact coefficient and centering algebra |
| Reflected second boundary | `0<q`, `a+h equiv b (mod q)` | Coprimality translated to reflected residue class |
| Joint A/B difference bridge | `0<q`, compatibility, parity implication | Rewrites two independent equalities |
| Public terminal asymptotic | `q>0`, `Squarefree q`, `epsilon>0`, reduced endpoints, compatibility, parity, `0<h`, eventual `h` | All analytic uniformity originates from native terminal, not F-01 |

The **cutoff parameters** `Jlow/Jhigh`, the `delta` used for LONG/CORE, the frequency gcd and the log exponents do not enter this printed identity bridge. They belong to the separate asymptotic proof branch. Their absence is a virtue: the public bridge does not buy a hidden estimate by imposing another analytic hypothesis.

## 7. Typed mechanism summary

| Mechanism | Kind | Source declaration | Key mathematical discipline |
|---|---|---|---|
| Prime-residue occupancy | Exact arithmetic | `occupiedResidues`, `printedLocal` | Distinguish `{0,h}` from `{0,y,h}` and their cardinalities |
| Euler-product convergence | Infinite analysis | `printed_pair_multipliable`, `printed_triple_multipliable` | Summable deviations and finite exceptional factors |
| Euler-product nonvanishing | Positivity/analysis | `printed_pair_tprod_ne_zero` | Nonzero each factor is insufficient by itself |
| Printed local quotient | Exact factorization | `printed_active_local_quotient_eq_occupied` | Preserve active p=2 and p=3 |
| A admissible-subtraction bridge | Exact finite reindexing | `printedA1Literal_eq_manuscriptA1Kernel` | Count exactly, no density proxy |
| High-prime c0/c1 selectors | Exact arithmetic | `highPrimeLocalRatio_eq_baseline_mul_selector` | Distinguish p dividing h, y, h-y |
| Finite squarefree Euler expansion | Exact combinatorics | `printed_eta_divisors_eq_powerset` | High-prime powers vanish; support finite |
| Reciprocal eta normalization | Absolute convergence and Euler product | `printed_free_eta_normalization` | Only then insert N/e inside sum |
| Weighted divisor Fubini | Exact finite reordering | `printed_free_weighted_divisor_swap` | e<h is necessary for numerator only |
| Centered infinite series | Summable series algebra | `printed_free_centered_sum` | Retain e>=h negative centering tail |
| Boundary reflection | Exact involution + congruence | `printed_reflected_anchor_eq_S1` | Swap orientation and admissibility together |
| Boolean endpoint contraction | Finite incidence algebra | `endpointContraction` | Complementary paper dictionary, not an estimate |
| Totient-period counting | Exact finite counting | `exactPeriodicCount` | Periodic error belongs in identity if used |

## 8. Source confidence, boundaries, and audit debt

**Established in this pass:** source text of the printed definitions matches the manuscript formulas `eq:S_q`, `eq:A1q`, and simplified `eq:B1q`, including active-prime restriction, original strict interior, and exact subtraction. The named Lean theorem chain from those definitions to A and B manuscript kernels is explicitly present. Detailed local formulas, convergence and summability gates, and the finite/infinite reordering boundary are identified by declaration and line.

**Not established by this pass:** independent re-elaboration of Lean; exhaustive transitive proof-constant DAG; a new analytic proof of the named native theorem; a separate external referee verdict; public release. The supplied seal reports an isolated compilation and standard axioms, but the user has requested no full replay, so this pass performs no Lean build.

**Two interesting audit candidates for later, not failures:**

1. Confirm that downstream documentation never treats the *centered* B sum as finite by simply truncating at `e<h`. The numerator is finite but the centered tail is infinite; the F-01 proof retains it correctly.
2. In the final public exposition, make explicit that the parity assumption is needed for dividing by the endpoint singular series at `p=2`, while triple singular series may legitimately vanish. Neither is an analytic smallness assumption.

## 9. Pass decision

**CONTINUE to Pass 3, as planned. No mathematical pivot.**

This pass closes the foundational printed-identity question at the level of a transparent source chain and gives us a reusable distinction between (i) equality/normalization machinery and (ii) asymptotic cancellation. Pass 3 should now trace the analytic suppliers that turn the exact native identities into an `o(log h)` estimate, beginning with a precise Suzuki low-Y/high-Y theorem and then the Karatsuba/Vinogradov-Korobov parameter hierarchy. Track the Weil-Estermann chain separately. Do not rerun the whole release candidate while the referee has it.

**Stop point:** We need no further material from Charlie for Pass 3; the same sealed archive contains the relevant sources.
