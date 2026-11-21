import AsterContinuantEnvelope
import AsterRealPerturbationStep

namespace AsterCertificate

/-- The same three-term Jacobi continuant, evaluated at an arbitrary *real* energy. -/
def realContinuant (d b : ℕ → ℚ) (t : ℝ) : ℕ → ℝ
  | 0 => 1
  | 1 => t - (d 0 : ℝ)
  | k + 2 => (t - (d (k + 1) : ℝ)) * realContinuant d b t (k + 1) -
      (b k : ℝ)^2 * realContinuant d b t k

/-- Real continuant agrees with the original exact rational source at rational energies. -/
theorem realContinuant_at_rational (d b : ℕ → ℚ) (t : ℚ) (k : ℕ) :
    realContinuant d b (t : ℝ) k = (qCont d b t k : ℝ) := by
  induction k using Nat.twoStepInduction with
  | zero => simp [realContinuant, qCont]
  | one => simp [realContinuant, qCont]
  | more k ih0 ih1 =>
      rw [realContinuant, qCont, ih0, ih1]
      push_cast
      ring

/-- The recurrence controls *both* its magnitude and its change at
arbitrary real shifts, simultaneously. Kestrelle's two sequences supply
the exactly matched right-hand sides. -/
theorem realContinuant_perturbation
    (d b : ℕ → ℚ) (τ : ℚ) (x : ℝ) (hx : |x| ≤ 1) :
    ∀ k : ℕ,
      |realContinuant d b ((τ : ℝ) + x) k| ≤ (contEnvelope d b τ k : ℝ) ∧
      |realContinuant d b ((τ : ℝ) + x) k -
          realContinuant d b (τ : ℝ) k| ≤ |x| * (contSlope d b τ k : ℝ) := by
  intro k
  induction k using Nat.twoStepInduction with
  | zero =>
      constructor
      · norm_num [realContinuant, contEnvelope]
      · norm_num [realContinuant, contSlope]
  | one =>
      constructor
      · rw [realContinuant, contEnvelope]
        have hbound : |((τ : ℝ) - (d 0 : ℝ)) + x| ≤
            |(τ : ℝ) - (d 0 : ℝ)| + 1 :=
          (abs_add_le _ _).trans (add_le_add_right hx _)
        simpa only [Rat.cast_sub, Rat.cast_neg, Rat.cast_abs, sq_abs, Rat.cast_add, Rat.cast_one, add_comm, add_left_comm, add_assoc, sub_eq_add_neg] using hbound
      · rw [realContinuant, realContinuant, contSlope]
        convert le_refl (|x| : ℝ) using 1 <;> norm_num <;> ring
  | more k ih0 ih1 =>
      let a : ℝ := ((τ - d (k + 1) : ℚ) : ℝ)
      let B : ℝ := ((b k : ℚ) : ℝ)^2
      have hB : 0 ≤ B := sq_nonneg _
      have hC : 0 ≤ (contEnvelope d b τ (k+1) : ℝ) := by
        exact_mod_cast contEnvelope_nonneg d b τ (k+1)
      have hD : 0 ≤ (contEnvelope d b τ k : ℝ) := by
        exact_mod_cast contEnvelope_nonneg d b τ k
      constructor
      · rw [realContinuant, contEnvelope]
        have hmain := real_affine_step_bound a x
          (realContinuant d b ((τ : ℝ)+x) (k+1))
          (realContinuant d b ((τ : ℝ)+x) k)
          B (contEnvelope d b τ (k+1) : ℝ)
          (contEnvelope d b τ k : ℝ)
          hx hB hC hD ih1.1 ih0.1
        convert hmain using 1 <;> simp only [a, B, Rat.cast_add, Rat.cast_sub, Rat.cast_neg, Rat.cast_mul, Rat.cast_pow, Rat.cast_abs, sq_abs] <;> ring
      · rw [realContinuant, realContinuant, contSlope]
        have hmain := real_affine_difference_bound a x
          (realContinuant d b ((τ : ℝ)+x) (k+1))
          (realContinuant d b (τ : ℝ) (k+1))
          (realContinuant d b ((τ : ℝ)+x) k)
          (realContinuant d b (τ : ℝ) k)
          B (contEnvelope d b τ (k+1) : ℝ)
          (contSlope d b τ (k+1) : ℝ)
          (contSlope d b τ k : ℝ)
          hB ih1.1 ih1.2 ih0.2
        convert hmain using 1 <;> simp only [a, B, Rat.cast_add, Rat.cast_sub, Rat.cast_neg, Rat.cast_mul, Rat.cast_pow, Rat.cast_abs, sq_abs] <;> ring

#print axioms realContinuant_at_rational
#print axioms realContinuant_perturbation

end AsterCertificate
