import AsterCertificate

/-!
# Exact rational singularity detection

The producer may test singularity at the target before attempting any
gap search. This branch is decidable by rational arithmetic, and its
spectral meaning is proved independently of the decision procedure.
-/

namespace AsterCertificate

/-- Rational characteristic-polynomial zero test at the target. -/
def checkSingular (d b : ℕ → ℚ) (n : ℕ) (τ : ℚ) : Bool :=
  decide (qCont d b τ n = 0)

/-- An accepted singularity check certifies an exact real polynomial root. -/
theorem checkSingular_sound (d b : ℕ → ℚ) (n : ℕ) (τ : ℚ)
    (h : checkSingular d b n τ = true) :
    (JacobiSpectral.jpoly
      (fun i => (d i : ℝ)) (fun i => (b i : ℝ)) n).eval (τ : ℝ) = 0 := by
  have hz : qCont d b τ n = 0 := by
    simpa only [checkSingular, decide_eq_true_eq] using h
  have hcast := qCont_cast d b τ n
  simpa [hz] using hcast.symm

#print axioms checkSingular_sound

end AsterCertificate
