import AsterRadialBracket

/-!
# Sturm counts are antitone in the test energy

The strict-greater-than convention and the half-open interval
convention agree even when the test energy is an eigenvalue.
-/

namespace AsterCertificate

/-- Exact rational Sturm counts decrease as the test energy increases.
The original unreduced Jacobi hypothesis is unchanged. -/
theorem qCount_antitone
    (d b : ℕ → ℚ) (n : ℕ)
    (hn : 0 < n) (hb : ∀ k, k + 1 < n → b k ≠ 0)
    (x y : ℚ) (hxy : x ≤ y) :
    qCount d b n y ≤ qCount d b n x := by
  cases n with
  | zero => omega
  | succ m =>
    have hbR : ∀ k < m, (b k : ℝ) ≠ 0 := by
      intro k hk
      exact_mod_cast (hb k (by omega))
    have hx := DiscreteSturm.sturmCount_eq_card
      (d := fun k => (d k : ℝ))
      (b := fun k => (b k : ℝ)) m hbR (x : ℝ)
    have hy := DiscreteSturm.sturmCount_eq_card
      (d := fun k => (d k : ℝ))
      (b := fun k => (b k : ℝ)) m hbR (y : ℝ)
    rw [qCount_real_sturm, qCount_real_sturm, hx, hy]
    apply Finset.card_le_card
    intro i hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
    have hreal : (x : ℝ) ≤ (y : ℝ) := by exact_mod_cast hxy
    exact lt_of_le_of_lt hreal hi

#print axioms qCount_antitone

end AsterCertificate
