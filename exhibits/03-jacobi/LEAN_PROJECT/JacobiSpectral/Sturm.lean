import JacobiSpectral.Continuant
import Mathlib.Topology.Algebra.Polynomial
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Analysis.Polynomial.Basic

/-!
# `JacobiSpectral.Sturm` — real roots, simplicity and strict interlacing from the recurrence

For real coefficients with nonzero off-diagonals, the polynomial continuants
`p_k = jpoly d b k` (the characteristic polynomials of the leading blocks) satisfy:

* `p_k` splits over `ℝ` with `k` **distinct** roots;
* the roots of `p_k` **strictly interlace** those of `p_{k+1}`;
* consecutive `p_k`, `p_{k+1}` have **no common root**.

The proof is the classical Sturm-sequence argument run *on the recurrence*: at a root `t` of
`p_{k+1}`, `p_{k+2}(t) = −b_k² p_k(t)`, the signs of `p_k` at the sorted roots of `p_{k+1}`
alternate (by interlacing), and the intermediate value theorem produces one root of `p_{k+2}` in
each of the `k+2` gaps. Nothing is assumed about eigenvalues.
-/

open Polynomial Finset

namespace JacobiSpectral

/-! ### Generic real-polynomial facts -/

/-- A sign change on `[a, c]` gives a root in `(a, c)`. -/
lemma exists_root_Ioo_of_mul_neg (p : ℝ[X]) {a c : ℝ} (hac : a < c)
    (h : p.eval a * p.eval c < 0) : ∃ x, a < x ∧ x < c ∧ p.eval x = 0 := by
  have hcont : ContinuousOn (fun x => p.eval x) (Set.Icc a c) := p.continuous.continuousOn
  rcases lt_or_gt_of_ne (show p.eval a ≠ 0 by intro h0; rw [h0, zero_mul] at h; exact lt_irrefl _ h)
    with ha | ha
  · have hc : 0 < p.eval c := by
      by_contra hc; push Not at hc; nlinarith
    obtain ⟨x, ⟨h1, h2⟩, hx⟩ := intermediate_value_Ioo hac.le hcont ⟨ha, hc⟩
    exact ⟨x, h1, h2, hx⟩
  · have hc : p.eval c < 0 := by
      by_contra hc; push Not at hc; nlinarith
    obtain ⟨x, ⟨h1, h2⟩, hx⟩ := intermediate_value_Ioo' hac.le hcont ⟨hc, ha⟩
    exact ⟨x, h1, h2, hx⟩

/-- A monic polynomial of positive degree that is negative at `a` has a root to the right of `a`. -/
lemma exists_root_gt_of_monic (p : ℝ[X]) (hm : p.Monic) (hd : 0 < p.natDegree) {a : ℝ}
    (ha : p.eval a < 0) : ∃ x, a < x ∧ p.eval x = 0 := by
  have ht := Polynomial.tendsto_atTop_of_leadingCoeff_nonneg p
    (by rw [degree_eq_natDegree hm.ne_zero]; exact_mod_cast hd) (by rw [hm.leadingCoeff]; norm_num)
  obtain ⟨c, hc⟩ := (ht.eventually_gt_atTop 0).and (Filter.eventually_gt_atTop a) |>.exists
  obtain ⟨x, h1, -, hx⟩ := exists_root_Ioo_of_mul_neg p hc.2 (by nlinarith [hc.1])
  exact ⟨x, h1, hx⟩

/-- A monic polynomial of degree `m ≥ 1` with `(-1)^m p(a) < 0` has a root to the left of `a`. -/
lemma exists_root_lt_of_monic (p : ℝ[X]) (hm : p.Monic) (hd : 0 < p.natDegree) {a : ℝ}
    (ha : (-1) ^ p.natDegree * p.eval a < 0) : ∃ x, x < a ∧ p.eval x = 0 := by
  set m := p.natDegree with hmdef
  set q : ℝ[X] := C ((-1) ^ m) * p.comp (-X) with hq
  have hnegX : (-X : ℝ[X]).natDegree = 1 := by rw [natDegree_neg, natDegree_X]
  have hcomp_deg : (p.comp (-X)).natDegree = m := by rw [natDegree_comp, hnegX, mul_one]
  have hcomp_lc : (p.comp (-X)).leadingCoeff = (-1) ^ m := by
    rw [leadingCoeff_comp (by rw [hnegX]; exact one_ne_zero), hm.leadingCoeff, one_mul,
      leadingCoeff_neg, leadingCoeff_X]
  have hsq : ((-1 : ℝ) ^ m) * (-1) ^ m = 1 := by rw [← mul_pow]; norm_num
  have hqm : q.Monic := by
    rw [Monic, hq, leadingCoeff_C_mul_of_isUnit (by exact (isUnit_neg_one.pow m)), hcomp_lc, hsq]
  have hqd : q.natDegree = m := by
    rw [hq, natDegree_C_mul (pow_ne_zero _ (by norm_num)), hcomp_deg]
  have hqa : q.eval (-a) < 0 := by
    simp only [hq, eval_mul, eval_C, eval_comp, eval_neg, eval_X, neg_neg]; exact ha
  obtain ⟨y, hy, hy0⟩ := exists_root_gt_of_monic q hqm (by rw [hqd]; exact hd) hqa
  refine ⟨-y, by linarith, ?_⟩
  have : q.eval y = (-1) ^ m * p.eval (-y) := by
    simp only [hq, eval_mul, eval_C, eval_comp, eval_neg, eval_X]
  rw [hy0] at this
  have h1 : ((-1 : ℝ) ^ m) ≠ 0 := pow_ne_zero _ (by norm_num)
  exact (mul_eq_zero.1 this.symm).resolve_left h1

/-- Sign of `∏ (x − r_j)` when exactly the first `i` of the sorted `r_j` lie below `x`. -/
lemma sign_prod_sub {n : ℕ} (r : Fin n → ℝ) (x : ℝ) (i : ℕ) (hi : i ≤ n)
    (hlt : ∀ j : Fin n, j.val < i → r j < x) (hgt : ∀ j : Fin n, i ≤ j.val → x < r j) :
    0 < (-1) ^ (n - i) * ∏ j, (x - r j) := by
  classical
  rw [← prod_filter_mul_prod_filter_not univ (fun j : Fin n => j.val < i)]
  have hcard : #(univ.filter fun j : Fin n => ¬ j.val < i) = n - i := by
    have h1 := card_filter_add_card_filter_not (s := (univ : Finset (Fin n)))
      (fun j : Fin n => j.val < i)
    rw [card_univ, Fintype.card_fin, Fin.card_filter_val_lt, min_eq_right hi] at h1
    omega
  have hneg : ∏ j ∈ univ.filter (fun j : Fin n => ¬ j.val < i), (x - r j) =
      (-1) ^ (n - i) * ∏ j ∈ univ.filter (fun j : Fin n => ¬ j.val < i), (r j - x) := by
    rw [← hcard, ← prod_neg]
    exact prod_congr rfl fun j _ => by ring
  rw [hneg]
  have hpos1 : 0 < ∏ j ∈ univ.filter (fun j : Fin n => j.val < i), (x - r j) :=
    prod_pos fun j hj => by rw [mem_filter] at hj; linarith [hlt j hj.2]
  have hpos2 : 0 < ∏ j ∈ univ.filter (fun j : Fin n => ¬ j.val < i), (r j - x) :=
    prod_pos fun j hj => by rw [mem_filter] at hj; linarith [hgt j (by omega)]
  have hsq : ((-1 : ℝ) ^ (n - i)) * (-1) ^ (n - i) = 1 := by rw [← mul_pow]; norm_num
  calc (0 : ℝ) < (∏ j ∈ univ.filter (fun j : Fin n => j.val < i), (x - r j)) *
        ∏ j ∈ univ.filter (fun j : Fin n => ¬ j.val < i), (r j - x) := mul_pos hpos1 hpos2
    _ = _ := by rw [← mul_assoc, mul_comm ((-1 : ℝ) ^ (n - i)), mul_assoc, ← mul_assoc _ _ (∏ j ∈ _, _),
          mul_comm ((-1 : ℝ) ^ (n - i)), mul_assoc, ← mul_assoc ((-1 : ℝ) ^ (n - i)), hsq, one_mul]

/-- A monic real polynomial of degree `n` with `n` distinct roots `u` is `∏ (X − u_i)`. -/
lemma eq_prod_of_roots {n : ℕ} (p : ℝ[X]) (hm : p.Monic) (hd : p.natDegree = n)
    (u : Fin n → ℝ) (hu : Function.Injective u) (hroot : ∀ i, p.eval (u i) = 0) :
    p = ∏ i, (X - C (u i)) := by
  classical
  have hsub : (univ.image u).val ≤ p.roots := by
    rw [Multiset.le_iff_subset (univ.image u).nodup]
    intro x hx
    rw [Finset.mem_val, mem_image] at hx
    obtain ⟨i, -, rfl⟩ := hx
    exact (mem_roots hm.ne_zero).2 (hroot i)
  have hcard : p.roots.card ≤ (univ.image u).val.card := by
    rw [Finset.card_val, card_image_of_injective _ hu, card_univ, Fintype.card_fin, ← hd]
    exact card_roots' p
  have heq : (univ.image u).val = p.roots := Multiset.eq_of_le_of_card_le hsub hcard
  have hroots_card : p.roots.card = p.natDegree := by
    rw [← heq, Finset.card_val, card_image_of_injective _ hu, card_univ, Fintype.card_fin, hd]
  rw [← prod_multiset_X_sub_C_of_monic_of_roots_card_eq hm hroots_card, ← heq,
    Finset.image_val_of_injOn (hu.injOn), Multiset.map_map]
  rfl

/-! ### The Sturm/interlacing induction -/

/-- `r` is the strictly increasing list of the (simple) roots of `p`. -/
def IsRootVec (p : ℝ[X]) {n : ℕ} (r : Fin n → ℝ) : Prop :=
  StrictMono r ∧ p = ∏ i, (X - C (r i))

/-- Strict interlacing `t₀ < r₀ < t₁ < r₁ < ⋯ < r_{n-1} < t_n`. -/
def StrictInterlace {n : ℕ} (t : Fin (n + 1) → ℝ) (r : Fin n → ℝ) : Prop :=
  ∀ i : Fin n, t i.castSucc < r i ∧ r i < t i.succ

lemma eval_prod_X_sub_C {n : ℕ} (r : Fin n → ℝ) (x : ℝ) :
    (∏ i, (X - C (r i))).eval x = ∏ i, (x - r i) := by
  rw [eval_prod]; simp

/-- **One Sturm step.** If the roots `t` of `p_{n+1}` strictly interlace with the roots `r` of
`p_n` and `b_n ≠ 0`, then `p_{n+2}` has `n+2` simple roots strictly interlacing `t`. -/
theorem sturm_step (d b : ℕ → ℝ) (n : ℕ) (hbn : b n ≠ 0)
    (t : Fin (n + 1) → ℝ) (r : Fin n → ℝ)
    (ht : IsRootVec (jpoly d b (n + 1)) t) (hr : IsRootVec (jpoly d b n) r)
    (hI : StrictInterlace t r) :
    ∃ u : Fin (n + 2) → ℝ, IsRootVec (jpoly d b (n + 2)) u ∧ StrictInterlace u t := by
  set p := jpoly d b (n + 2) with hp
  -- sign of `p_n` at the roots of `p_{n+1}`
  have hsign_n : ∀ i : Fin (n + 1), 0 < (-1) ^ (n - i.val) * (jpoly d b n).eval (t i) := by
    intro i
    rw [hr.2, eval_prod_X_sub_C]
    refine sign_prod_sub r (t i) i.val (by omega) (fun j hj => ?_) (fun j hj => ?_)
    · -- r_j < t_{j+1} ≤ t_i
      have h1 := (hI j).2
      have h2 : t j.succ ≤ t i := ht.1.monotone (by rw [Fin.le_def, Fin.val_succ]; omega)
      linarith
    · -- t_i ≤ t_j < r_j
      have h1 := (hI j).1
      have h2 : t i ≤ t j.castSucc := ht.1.monotone (by rw [Fin.le_def, Fin.val_castSucc]; omega)
      linarith
  -- values of `p_{n+2}` at the roots of `p_{n+1}`
  have hval : ∀ i : Fin (n + 1), p.eval (t i) = -(b n ^ 2) * (jpoly d b n).eval (t i) := by
    intro i
    have h0 : (jpoly d b (n + 1)).eval (t i) = 0 := by
      rw [ht.2, eval_prod_X_sub_C]; exact prod_eq_zero (mem_univ i) (sub_self _)
    rw [hp, jpoly_succ_succ]
    simp only [eval_sub, eval_mul, h0, mul_zero, eval_C, zero_sub]; ring
  have hb2 : 0 < b n ^ 2 := by positivity
  have hsign : ∀ i : Fin (n + 1), (-1) ^ (n - i.val) * p.eval (t i) < 0 := by
    intro i
    rw [hval i]
    have := hsign_n i
    nlinarith
  have hpm : p.Monic := jpoly_monic d b (n + 2)
  have hpd : p.natDegree = n + 2 := natDegree_jpoly d b (n + 2)
  -- one root in each gap
  have hgap : ∀ k : Fin (n + 2), ∃ x : ℝ, (∀ j : Fin (n + 1), j.val < k.val → t j < x) ∧
      (∀ j : Fin (n + 1), k.val ≤ j.val → x < t j) ∧ p.eval x = 0 := by
    intro k
    rcases Nat.eq_zero_or_pos k.val with hk0 | hkpos
    · -- leftmost gap
      have h0 := hsign 0
      have hlt : (-1) ^ p.natDegree * p.eval (t 0) < 0 := by
        rw [hpd]
        have e : ((-1 : ℝ) ^ (n + 2)) = (-1) ^ (n - (0 : Fin (n + 1)).val) := by
          simp only [Fin.val_zero, Nat.sub_zero, pow_add]; norm_num
        rw [e]; exact h0
      obtain ⟨x, hx, hx0⟩ := exists_root_lt_of_monic p hpm (by omega) hlt
      refine ⟨x, fun j hj => by omega, fun j _ => ?_, hx0⟩
      exact lt_of_lt_of_le hx (ht.1.monotone (Fin.zero_le j))
    rcases Nat.lt_or_ge k.val (n + 1) with hkn | hkn
    · -- interior gap `(t_{k-1}, t_k)`
      set i₁ : Fin (n + 1) := ⟨k.val - 1, by omega⟩
      set i₂ : Fin (n + 1) := ⟨k.val, hkn⟩
      have h1 := hsign i₁
      have h2 := hsign i₂
      have hlt : t i₁ < t i₂ := ht.1 (by rw [Fin.lt_def]; simp only [i₁, i₂]; omega)
      have hprod : p.eval (t i₁) * p.eval (t i₂) < 0 := by
        have e : n - i₁.val = (n - i₂.val) + 1 := by simp only [i₁, i₂]; omega
        rw [e, pow_succ] at h1
        have hs : ((-1 : ℝ) ^ (n - i₂.val)) ^ 2 = 1 := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
        set s := ((-1 : ℝ) ^ (n - i₂.val))
        have hA : 0 < s * p.eval (t i₁) := by linarith
        have hAB := mul_neg_of_pos_of_neg hA h2
        have e2 : (s * p.eval (t i₁)) * (s * p.eval (t i₂)) = p.eval (t i₁) * p.eval (t i₂) := by
          rw [show (s * p.eval (t i₁)) * (s * p.eval (t i₂)) = s ^ 2 * (p.eval (t i₁) * p.eval (t i₂))
            by ring, hs, one_mul]
        rw [e2] at hAB; exact hAB
      obtain ⟨x, hx1, hx2, hx0⟩ := exists_root_Ioo_of_mul_neg p hlt hprod
      refine ⟨x, fun j hj => ?_, fun j hj => ?_, hx0⟩
      · exact lt_of_le_of_lt (ht.1.monotone (by rw [Fin.le_def]; simp only [i₁]; omega)) hx1
      · exact lt_of_lt_of_le hx2 (ht.1.monotone (by rw [Fin.le_def]; simp only [i₂]; omega))
    · -- rightmost gap
      have hk : k.val = n + 1 := by omega
      have h0 := hsign (Fin.last n)
      have hneg : p.eval (t (Fin.last n)) < 0 := by
        rw [Fin.val_last, Nat.sub_self, pow_zero, one_mul] at h0; exact h0
      obtain ⟨x, hx, hx0⟩ := exists_root_gt_of_monic p hpm (by omega) hneg
      refine ⟨x, fun j _ => lt_of_le_of_lt (ht.1.monotone (Fin.le_last j)) hx,
        fun j hj => by omega, hx0⟩
  choose u hu1 hu2 hu0 using hgap
  have hmono : StrictMono u := by
    intro k k' hkk'
    have hk : k.val < n + 1 := by have := k'.isLt; rw [Fin.lt_def] at hkk'; omega
    have a1 := hu2 k ⟨k.val, hk⟩ le_rfl
    have a2 := hu1 k' ⟨k.val, hk⟩ hkk'
    linarith
  refine ⟨u, ⟨hmono, eq_prod_of_roots p hpm hpd u hmono.injective hu0⟩, fun i => ⟨?_, ?_⟩⟩
  · exact hu2 i.castSucc i (by simp)
  · exact hu1 i.succ i (by simp)

/-- **Real-rootedness and strict interlacing for all leading blocks.** If `b_k ≠ 0` for
`k < n`, then `p_{n+1}` and `p_n` have simple real roots `t`, `r` with `t₀ < r₀ < t₁ < ⋯ < t_n`. -/
theorem jpoly_interlace (d b : ℕ → ℝ) : ∀ n : ℕ, (∀ k < n, b k ≠ 0) →
    ∃ (t : Fin (n + 1) → ℝ) (r : Fin n → ℝ),
      IsRootVec (jpoly d b (n + 1)) t ∧ IsRootVec (jpoly d b n) r ∧ StrictInterlace t r
  | 0 => fun _ => ⟨fun _ => d 0, Fin.elim0, ⟨fun i j h => absurd h (by
        rw [Fin.lt_def]; omega), by simp⟩, ⟨fun i => i.elim0, by simp⟩, fun i => i.elim0⟩
  | (n + 1) => fun hb => by
      obtain ⟨t, r, ht, hr, hI⟩ := jpoly_interlace d b n (fun k hk => hb k (by omega))
      obtain ⟨u, hu, hIu⟩ := sturm_step d b n (hb n (by omega)) t r ht hr hI
      exact ⟨u, t, hu, ht, hIu⟩

end JacobiSpectral
