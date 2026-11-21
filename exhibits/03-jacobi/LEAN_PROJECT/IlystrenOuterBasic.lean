import AsterCertificate

open AsterCertificate

namespace Ilystren.Jacobi

private theorem all_pos_signVariations_zero (l : List ℚ)
    (h : ∀ x ∈ l, 0 < x) : l.signVariations = 0 := by
  induction l with
  | nil => simp
  | cons a tail ih =>
    cases tail with
    | nil => simp
    | cons b rest =>
      have ha : 0 < a := h a (by simp)
      have hb : 0 < b := h b (by simp)
      have hr : ∀ x ∈ b :: rest, 0 < x := by
        intro x hx
        exact h x (by simp [hx])
      rw [List.signVariations_cons_cons_of_ne_zero rest (ne_of_gt ha) (ne_of_gt hb)]
      have hsa : SignType.sign a = 1 := sign_eq_one_iff.mpr ha
      have hsb : SignType.sign b = 1 := sign_eq_one_iff.mpr hb
      simp [hsa, hsb, ih hr]

private theorem qCont_rising_to (d b : ℕ → ℚ) (n : ℕ) (x : ℚ)
    (hfirst : 1 < x - d 0)
    (hstep : ∀ k, k + 1 < n → 1 + (b k)^2 < x - d (k + 1)) :
    ∀ k, k < n → 0 < qCont d b x k ∧
      qCont d b x k < qCont d b x (k + 1) := by
  intro k
  induction k with
  | zero =>
    intro hk
    constructor
    · norm_num [qCont]
    · simpa [qCont] using hfirst
  | succ k ih =>
    intro hk
    obtain ⟨hp, hdif⟩ := ih (by omega)
    have hpos : 0 < qCont d b x (k + 1) := lt_trans hp hdif
    have hcoef := hstep k hk
    constructor
    · exact hpos
    · change qCont d b x (k + 1) <
        (x - d (k + 1)) * qCont d b x (k + 1) -
          (b k)^2 * qCont d b x k
      have hgap : 0 < x - d (k + 1) - (1 + (b k)^2) := by linarith
      nlinarith [mul_pos hgap hpos,
        mul_nonneg (sq_nonneg (b k)) (sub_nonneg.mpr hdif.le)]

private theorem qCont_all_positive (d b : ℕ → ℚ) (n : ℕ) (x : ℚ)
    (hn : 0 < n)
    (hfirst : 1 < x - d 0)
    (hstep : ∀ k, k + 1 < n → 1 + (b k)^2 < x - d (k + 1)) :
    ∀ k, k ≤ n → 0 < qCont d b x k := by
  intro k hk
  have hg := qCont_rising_to d b n x hfirst hstep
  by_cases hkn : k < n
  · exact (hg k hkn).1
  · have hkn' : k = n := by omega
    subst k
    have ht := hg (n - 1) (by omega)
    have hr : n - 1 + 1 = n := by omega
    rw [← hr]
    exact lt_trans ht.1 ht.2

theorem qCount_zero_of_coeff_dominance (d b : ℕ → ℚ) (n : ℕ) (x : ℚ)
    (hn : 0 < n)
    (hfirst : 1 < x - d 0)
    (hstep : ∀ k, k + 1 < n → 1 + (b k)^2 < x - d (k + 1)) :
    qCount d b n x = 0 := by
  unfold qCount
  apply all_pos_signVariations_zero
  intro y hy
  obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hy
  exact qCont_all_positive d b n x hn hfirst hstep k (by
    have := List.mem_range.mp hk
    omega)

#print axioms qCount_zero_of_coeff_dominance

theorem qCount_positive_of_left_of_d0
    (d b : ℕ → ℚ) (n : ℕ) (x : ℚ)
    (hn : 0 < n) (hx : x < d 0) :
    0 < qCount d b n x := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  unfold qCount
  have hrange : List.range (m + 1 + 1) =
      (0 : ℕ) :: 1 :: List.range' 2 m := by
    rw [List.range_eq_range']
    rfl
  rw [hrange]
  simp only [List.map_cons, qCont]
  have hxneg : x - d 0 < 0 := sub_neg.mpr hx
  rw [List.signVariations_cons_cons_of_ne_zero
    (List.map (qCont d b x) (List.range' 2 m))
    (by norm_num : (1 : ℚ) ≠ 0) (ne_of_lt hxneg)]
  have ha : SignType.sign (1 : ℚ) = 1 :=
    sign_eq_one_iff.mpr (by norm_num)
  have hb : SignType.sign (x - d 0) = -1 :=
    sign_eq_neg_one_iff.mpr hxneg
  simp [ha, hb]

#print axioms qCount_positive_of_left_of_d0

/-- A finite, executable rational budget from the literal Jacobi coefficients. -/
def sourceOuterBudget (d b : ℕ → ℚ) (n : ℕ) : ℚ :=
  2 * ∑ k ∈ Finset.range n, (|d k| + (b k)^2 + 2)

private theorem sourceOuterBudget_nonneg (d b : ℕ → ℚ) (n : ℕ) :
    0 ≤ sourceOuterBudget d b n := by
  unfold sourceOuterBudget
  positivity

private theorem sourceOuterBudget_term_le (d b : ℕ → ℚ) (n i : ℕ)
    (hi : i < n) :
    2 * (|d i| + (b i)^2 + 2) ≤ sourceOuterBudget d b n := by
  have h := Finset.single_le_sum
    (s := Finset.range n)
    (f := fun j => |d j| + (b j)^2 + 2)
    (fun j hj => by positivity) (Finset.mem_range.mpr hi)
  unfold sourceOuterBudget
  linarith

/-- No spectral search: choose a rational radius larger than both
the supplied inner radius and the finite Jacobi coefficient budget. -/
def sourceOuterRadiusFromInner (d b : ℕ → ℚ) (n : ℕ) (τ inner : ℚ) : ℚ :=
  inner + |τ| + sourceOuterBudget d b n + 2

/-- The executable initializer has a zero right Sturm count and a
positive left Sturm count. No eigenvalue is selected. -/
theorem sourceOuterRadiusFromInner_spec
    (d b : ℕ → ℚ) (n : ℕ) (τ inner : ℚ)
    (hn : 0 < n) (hin : 0 ≤ inner) :
    inner < sourceOuterRadiusFromInner d b n τ inner ∧
    qCount d b n (τ + sourceOuterRadiusFromInner d b n τ inner) = 0 ∧
    0 < qCount d b n (τ - sourceOuterRadiusFromInner d b n τ inner) := by
  have hbudget := sourceOuterBudget_nonneg d b n
  have htabs := abs_nonneg τ
  have htpos := neg_le_abs τ
  have htneg := le_abs_self τ
  have hterm0 := sourceOuterBudget_term_le d b n 0 hn
  have hd0 := le_abs_self (d 0)
  have hd0neg := neg_abs_le (d 0)
  have horder : inner < sourceOuterRadiusFromInner d b n τ inner := by
    unfold sourceOuterRadiusFromInner
    linarith
  have hfirst : 1 < (τ + sourceOuterRadiusFromInner d b n τ inner) - d 0 := by
    unfold sourceOuterRadiusFromInner
    nlinarith [sq_nonneg (b 0)]
  have hstep :
      ∀ k, k + 1 < n →
      1 + (b k)^2 <
        (τ + sourceOuterRadiusFromInner d b n τ inner) - d (k + 1) := by
    intro k hk
    have hterm := sourceOuterBudget_term_le d b n (k + 1) hk
    have htermk := sourceOuterBudget_term_le d b n k (by omega)
    have hd := le_abs_self (d (k+1))
    have hnon1 := sq_nonneg (b (k+1))
    have hnon2 := abs_nonneg (d k)
    unfold sourceOuterRadiusFromInner
    linarith
  have hright := qCount_zero_of_coeff_dominance d b n
    (τ + sourceOuterRadiusFromInner d b n τ inner) hn hfirst hstep
  have hleftineq : τ - sourceOuterRadiusFromInner d b n τ inner < d 0 := by
    unfold sourceOuterRadiusFromInner
    nlinarith [sq_nonneg (b 0)]
  have hleft := qCount_positive_of_left_of_d0 d b n
    (τ - sourceOuterRadiusFromInner d b n τ inner) hn hleftineq
  exact ⟨horder, hright, hleft⟩

#print axioms sourceOuterRadiusFromInner_spec

end Ilystren.Jacobi
