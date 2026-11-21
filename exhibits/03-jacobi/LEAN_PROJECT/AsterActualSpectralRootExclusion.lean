import AsterRealRootExclusion

/-!
# Kestrelle's radius excludes actual Jacobi characteristic roots

The real recurrence is identified with the real characteristic
polynomial at every real test energy. Its certified root-free ball
therefore concerns the physical Jacobi matrix, not merely an auxiliary
recurrence.
-/

namespace AsterCertificate

open Polynomial JacobiSpectral

/-- The source-native real continuant is precisely the evaluated
Jacobi characteristic polynomial at *arbitrary real energies*. -/
theorem realContinuant_eq_jpoly_eval
    (d b : ℕ → ℚ) (t : ℝ) (n : ℕ) :
    realContinuant d b t n =
      (jpoly (fun i => (d i : ℝ))
         (fun i => (b i : ℝ)) n).eval t := by
  induction n using Nat.twoStepInduction with
  | zero =>
      simp [realContinuant, jpoly]
  | one =>
      simp [realContinuant, jpoly]
  | more k ih0 ih1 =>
      rw [realContinuant, jpoly_succ_succ,
        Polynomial.eval_sub, Polynomial.eval_mul,
        Polynomial.eval_sub, Polynomial.eval_X,
        Polynomial.eval_C, Polynomial.eval_mul,
        Polynomial.eval_C, ih0, ih1]

/-- Actual characteristic root exclusion, at every real energy within
the explicitly calculated rational radius. -/
theorem continuant_inner_radius_jpoly_ne_zero
    (d b : ℕ → ℚ) (τ : ℚ) (n : ℕ)
    (hq : qCont d b τ n ≠ 0)
    (t : ℝ)
    (ht : |t - (τ : ℝ)| ≤ (continuantInnerRadius d b τ n : ℝ)) :
    (jpoly (fun i => (d i : ℝ))
       (fun i => (b i : ℝ)) n).eval t ≠ 0 := by
  have h :=
    continuant_inner_radius_real_nonroot d b τ n hq
      (t - (τ : ℝ)) ht
  have hshift : (τ : ℝ) + (t - (τ : ℝ)) = t := by ring
  rw [hshift, realContinuant_eq_jpoly_eval] at h
  exact h

/-- The same root exclusion for the actual shifted Jacobi determinant. -/
theorem continuant_inner_radius_det_ne_zero
    (d b : ℕ → ℚ) (τ : ℚ) (n : ℕ)
    (hq : qCont d b τ n ≠ 0)
    (t : ℝ)
    (ht : |t - (τ : ℝ)| ≤ (continuantInnerRadius d b τ n : ℝ)) :
    (Matrix.scalar (Fin n) t -
      jacobi (fun i => (d i : ℝ)) (fun i => (b i : ℝ)) n).det ≠ 0 := by
  rw [← JacobiSpectral.eval_jpoly]
  exact continuant_inner_radius_jpoly_ne_zero d b τ n hq t ht

#print axioms realContinuant_eq_jpoly_eval
#print axioms continuant_inner_radius_jpoly_ne_zero
#print axioms continuant_inner_radius_det_ne_zero

end AsterCertificate
