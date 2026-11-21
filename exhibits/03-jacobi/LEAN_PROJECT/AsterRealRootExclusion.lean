import AsterRealContinuantInduction

namespace AsterCertificate

/-- Kestrelle's computable rational radius excludes *real* roots of the
original Jacobi continuant. -/
theorem continuant_inner_radius_real_nonroot
    (d b : ℕ → ℚ) (τ : ℚ) (n : ℕ)
    (hq : qCont d b τ n ≠ 0)
    (x : ℝ)
    (hx : |x| ≤ (continuantInnerRadius d b τ n : ℝ)) :
    realContinuant d b ((τ : ℝ) + x) n ≠ 0 := by
  let r : ℚ := continuantInnerRadius d b τ n
  let L : ℚ := contSlope d b τ n
  let c : ℚ := qCont d b τ n
  have hrhalf : r ≤ 1 / 2 := min_le_left _ _
  have hrbound : r ≤ |c| / (2 * (L + 1)) := min_le_right _ _
  have hrnonneg : 0 ≤ (r : ℝ) :=
    le_of_lt (by exact_mod_cast continuantInnerRadius_pos d b τ n hq)
  have hLnonneg : 0 ≤ (L : ℝ) := by
    exact_mod_cast contSlope_nonneg d b τ n
  have hcpos : 0 < |(c : ℝ)| := abs_pos.mpr (by exact_mod_cast hq)
  have hrhalfR : (r : ℝ) ≤ 1 / 2 := by
    have ht : (r : ℝ) ≤ ((1 / 2 : ℚ) : ℝ) := by exact_mod_cast hrhalf
    norm_num at ht
    exact ht
  have hxunit : |x| ≤ 1 := by linarith
  have hbound :
      |realContinuant d b ((τ : ℝ) + x) n -
        realContinuant d b (τ : ℝ) n| ≤ |x| * (L : ℝ) :=
    (realContinuant_perturbation d b τ x hxunit n).2
  have hbase : realContinuant d b (τ : ℝ) n = (c : ℝ) :=
    realContinuant_at_rational d b τ n
  have hden : 0 < (L : ℝ) + 1 := by linarith
  have hrboundR :
      (r : ℝ) * (2 * ((L : ℝ) + 1)) ≤ |(c : ℝ)| := by
    have hd : (0 : ℚ) < 2 * (L + 1) := by
      have hn := contSlope_nonneg d b τ n
      linarith
    have ht := (le_div_iff₀ hd).mp hrbound
    exact_mod_cast ht
  have hsmall : |x| * (L : ℝ) < |(c : ℝ)| := by
    have ha : |x| * (L : ℝ) ≤ (r : ℝ) * (L : ℝ) :=
      mul_le_mul_of_nonneg_right hx hLnonneg
    have hb : (r : ℝ) * (L : ℝ) ≤ |(c : ℝ)| / 2 := by
      nlinarith [mul_nonneg hrnonneg hLnonneg]
    linarith
  intro hz
  rw [hz, hbase, zero_sub, abs_neg] at hbound
  linarith

#print axioms continuant_inner_radius_real_nonroot
end AsterCertificate
