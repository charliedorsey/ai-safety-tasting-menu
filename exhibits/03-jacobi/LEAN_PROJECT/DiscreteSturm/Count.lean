/-
Copyright (c) 2026 Charlie Dorsey. Released under Apache 2.0 license.
-/
import JacobiSpectral.Spectrum

/-!
# Counting roots above a point, for strictly interlacing root vectors

For root vectors `t` (of `p_{m+1}`) and `r` (of `p_m`) with `t₀ < r₀ < t₁ < ⋯ < r_{m-1} < t_m`,
the counts `cntAbove t x = #{i | x < t i}` and `cntAbove r x` satisfy:

* `cntAbove r x ≤ cntAbove t x ≤ cntAbove r x + 1` (for every `x`);
* equality `cntAbove t x = cntAbove r x` at a root `x = t j`;
* `cntAbove t x = cntAbove r x + 1` at a root `x = r j`.

Together with the sign of `∏ (x − t i)` (positive iff `cntAbove t x` is even) these drive the
Sturm-count induction in `DiscreteSturm.Oscillation`.
-/

open Polynomial Finset JacobiSpectral

namespace DiscreteSturm

/-- `#{i | x < t i}`. -/
noncomputable def cntAbove {n : ℕ} (t : Fin n → ℝ) (x : ℝ) : ℕ := (univ.filter fun i => x < t i).card

lemma cntAbove_eq_sum {n : ℕ} (t : Fin n → ℝ) (x : ℝ) :
    cntAbove t x = ∑ i, if x < t i then 1 else 0 := by
  rw [cntAbove, Finset.card_filter]

variable {m : ℕ} {t : Fin (m + 1) → ℝ} {r : Fin m → ℝ}

lemma cntAbove_le_of_interlace (hI : StrictInterlace t r) (x : ℝ) :
    cntAbove r x ≤ cntAbove t x := by
  rw [cntAbove_eq_sum, cntAbove_eq_sum, Fin.sum_univ_succ]
  refine le_add_left (Finset.sum_le_sum fun i _ => ?_)
  have h := (hI i).2
  split_ifs with h1 h2 <;> first | omega | (exfalso; linarith)

lemma cntAbove_le_succ_of_interlace (hI : StrictInterlace t r) (x : ℝ) :
    cntAbove t x ≤ cntAbove r x + 1 := by
  rw [cntAbove_eq_sum, cntAbove_eq_sum, Fin.sum_univ_castSucc]
  refine add_le_add (Finset.sum_le_sum fun i _ => ?_) (by split_ifs <;> omega)
  have h := (hI i).1
  split_ifs with h1 h2 <;> first | omega | (exfalso; linarith)

lemma cntAbove_root_left (ht : StrictMono t) (hI : StrictInterlace t r) (j : Fin (m + 1)) :
    cntAbove t (t j) = cntAbove r (t j) := by
  refine le_antisymm ?_ (cntAbove_le_of_interlace hI _)
  rw [cntAbove_eq_sum, cntAbove_eq_sum, Fin.sum_univ_succ]
  have h0 : ¬ t j < t 0 := not_lt.mpr (ht.monotone (Fin.zero_le j))
  simp only [h0, ↓reduceIte, zero_add]
  refine Finset.sum_le_sum fun i _ => ?_
  by_cases h1 : t j < t i.succ
  · have hji : j < i.succ := ht.lt_iff_lt.mp h1
    have hle : j ≤ i.castSucc := Fin.le_castSucc_iff.mpr hji
    have h2 : t j < r i := lt_of_le_of_lt (ht.monotone hle) (hI i).1
    simp [h1, h2]
  · simp [h1]

lemma cntAbove_root_right (hI : StrictInterlace t r) (j : Fin m) :
    cntAbove t (r j) = cntAbove r (r j) + 1 := by
  refine le_antisymm (cntAbove_le_succ_of_interlace hI _) ?_
  rw [cntAbove_eq_sum, cntAbove_eq_sum, Fin.sum_univ_succ]
  have hlt : ∑ i : Fin m, (if r j < r i then 1 else 0) <
      ∑ i : Fin m, (if r j < t i.succ then 1 else 0) := by
    refine Finset.sum_lt_sum (fun i _ => ?_) ⟨j, mem_univ _, ?_⟩
    · have h := (hI i).2
      split_ifs with h1 h2 <;> first | omega | (exfalso; linarith)
    · have h := (hI j).2
      simp [h]
  omega

/-! ### Roots of a root-vector polynomial and the sign of its value -/

lemma roots_filter_card_of_isRootVec {p : ℝ[X]} {n : ℕ} {t : Fin n → ℝ} (ht : IsRootVec p t)
    (x : ℝ) : (p.roots.filter (fun y => x < y)).card = cntAbove t x := by
  have hroots : p.roots = Multiset.map t univ.val := by
    rw [ht.2]
    have : (∏ i, (X - C (t i)) : ℝ[X]) = ((Multiset.map t univ.val).map fun a => X - C a).prod := by
      rw [Multiset.map_map]; rfl
    rw [this, roots_multiset_prod_X_sub_C]
  rw [hroots, Multiset.filter_map, Multiset.card_map, cntAbove]
  rfl

/-- For nonzero factors, `0 < ∏ (x − t i)` iff the number of `t i` above `x` is even. -/
lemma prod_pos_iff_even {n : ℕ} (t : Fin n → ℝ) (x : ℝ) (hx : ∀ i, t i ≠ x) :
    0 < ∏ i, (x - t i) ↔ Even (cntAbove t x) := by
  have h1 : ∏ i, (x - t i) = ∏ i, ((if x < t i then (-1 : ℝ) else 1) * |x - t i|) := by
    refine Finset.prod_congr rfl fun i _ => ?_
    split_ifs with h
    · rw [abs_of_neg (by linarith)]; ring
    · rw [abs_of_nonneg (by linarith [not_lt.mp h])]; ring
  have hpos : 0 < ∏ i, |x - t i| :=
    Finset.prod_pos fun i _ => abs_pos.mpr (sub_ne_zero.mpr (hx i).symm)
  rw [h1, Finset.prod_mul_distrib, Finset.prod_ite, Finset.prod_const, Finset.prod_const, one_pow,
    mul_one, cntAbove]
  constructor
  · intro h
    by_contra hodd
    rw [Nat.not_even_iff_odd] at hodd
    rw [hodd.neg_one_pow] at h
    linarith
  · intro he
    rw [he.neg_one_pow, one_mul]
    exact hpos

end DiscreteSturm
