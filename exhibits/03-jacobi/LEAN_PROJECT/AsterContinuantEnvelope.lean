import AsterCertificate

namespace AsterCertificate

/-- Executable rational majorant for the continuant on the unit target ball. -/
def contEnvelope (d b : ℕ → ℚ) (τ : ℚ) : ℕ → ℚ
  | 0 => 1
  | 1 => |τ - d 0| + 1
  | k + 2 => (|τ - d (k+1)| + 1) * contEnvelope d b τ (k+1) +
      |b k| ^ 2 * contEnvelope d b τ k

/-- Executable rational Lipschitz coefficient, computed without polynomial translation. -/
def contSlope (d b : ℕ → ℚ) (τ : ℚ) : ℕ → ℚ
  | 0 => 0
  | 1 => 1
  | k + 2 => contEnvelope d b τ (k+1) +
      |τ - d (k+1)| * contSlope d b τ (k+1) +
      |b k| ^ 2 * contSlope d b τ k

theorem contEnvelope_nonneg (d b : ℕ → ℚ) (τ : ℚ) (k : ℕ) :
    0 ≤ contEnvelope d b τ k := by
  induction k using Nat.twoStepInduction with
  | zero => simp [contEnvelope]
  | one =>
      rw [contEnvelope]
      positivity
  | more k h0 h1 =>
      rw [contEnvelope]
      exact add_nonneg (mul_nonneg (by positivity) h1) (mul_nonneg (by positivity) h0)

theorem contSlope_nonneg (d b : ℕ → ℚ) (τ : ℚ) (k : ℕ) :
    0 ≤ contSlope d b τ k := by
  induction k using Nat.twoStepInduction with
  | zero => simp [contSlope]
  | one => simp [contSlope]
  | more k h0 h1 =>
      rw [contSlope]
      exact add_nonneg (add_nonneg (contEnvelope_nonneg d b τ (k+1)) (mul_nonneg (by positivity) h1)) (mul_nonneg (by positivity) h0)

/-- A computable rational inner radius based on the actual continuant. -/
def continuantInnerRadius (d b : ℕ → ℚ) (τ : ℚ) (n : ℕ) : ℚ :=
    min (1/2) (|qCont d b τ n| / (2 * (contSlope d b τ n + 1)))

theorem continuantInnerRadius_pos (d b : ℕ → ℚ) (τ : ℚ) (n : ℕ)
    (hroot : qCont d b τ n ≠ 0) :
    0 < continuantInnerRadius d b τ n := by
  unfold continuantInnerRadius
  apply lt_min (by norm_num)
  have hc : 0 < |qCont d b τ n| := abs_pos.mpr hroot
  have hl := contSlope_nonneg d b τ n
  positivity

#print axioms contEnvelope_nonneg
#print axioms contSlope_nonneg
#print axioms continuantInnerRadius_pos

end AsterCertificate
