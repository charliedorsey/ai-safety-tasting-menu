import AsterSingularity

/-!
# Exact singularity in the matrix, not only its characteristic polynomial

The tested rational characteristic polynomial is identified with
the determinant of the shifted finite Jacobi matrix.
-/

namespace AsterCertificate

/-- The exact rational singularity decision certifies singularity
of the real Jacobi matrix shifted by the target energy. -/
theorem checkSingular_shifted_det_zero
    (d b : ℕ → ℚ) (n : ℕ) (τ : ℚ)
    (h : checkSingular d b n τ = true) :
    (Matrix.scalar (Fin n) (τ : ℝ) -
      JacobiSpectral.jacobi (fun k => (d k : ℝ))
        (fun k => (b k : ℝ)) n).det = 0 := by
  rw [← JacobiSpectral.eval_jpoly]
  exact checkSingular_sound d b n τ h

#print axioms checkSingular_shifted_det_zero

end AsterCertificate
