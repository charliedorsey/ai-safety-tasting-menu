import JacobiUnconditional

open JacobiSpectral JacobiDioph
namespace JacobiBridge

theorem spectrum_q_any (c β : ℝ) (hβ : β ≠ 0)
    (q : ℕ) (hq : 2 ≤ q) :
    spectrum ℝ (jacobi (fun _ => c) (fun _ => β) (q - 1)) =
      Set.range (fun i : Fin (q - 1) =>
        jacobiDisp c β (((i : ℕ) + 1 : ℝ) / q)) := by
  have h : 0 < β ∨ β < 0 := lt_or_gt_of_ne hβ.symm
  rcases h with hp | hn
  · rw [spectrum_q_sub_one c β hp q hq]
    congr 1
    funext i
    unfold jacobiDisp
    congr 1
    ring
  · rw [spectrum_q_negative c β hn q hq]
    congr 1
    funext i
    unfold jacobiDisp
    congr 1
    ring

theorem target_off_spectrum (c β α : ℝ) (hβ : β ≠ 0)
    (hα : α ∈ Set.Ioo (0 : ℝ) 1) (hirr : Irrational α)
    (q : ℕ) (hq : 2 ≤ q) :
    jacobiDisp c β α ∉
      spectrum ℝ (jacobi (fun _ => c) (fun _ => β) (q - 1)) := by
  rw [spectrum_q_any c β hβ q hq]
  rintro ⟨i, hi⟩
  have hi0 : (0 : ℝ) < (((i : ℕ) + 1 : ℝ) / q) := by positivity
  have hi1 : (((i : ℕ) + 1 : ℝ) / q) < 1 := by
    apply (div_lt_one (by exact_mod_cast (show 0 < q by omega))).mpr
    exact_mod_cast (show (i : ℕ) + 1 < q by have := i.isLt; omega)
  obtain ⟨K, hK, hlow⟩ := (cos_phaseHyp (c := c) hβ hα).lower
  have hlow' := hlow _ ⟨hi0, hi1⟩
  rw [← hi, sub_self, abs_zero] at hlow'
  have heq : (((i : ℕ) + 1 : ℝ) / q) = α := by
    rw [Real.rpow_one] at hlow'
    have hz : K * |(((i : ℕ) + 1 : ℝ) / q) - α| = 0 :=
      le_antisymm hlow' (by positivity)
    have habs : |(((i : ℕ) + 1 : ℝ) / q) - α| = 0 :=
      (mul_eq_zero.mp hz).resolve_left hK.ne'
    exact (sub_eq_zero.mp (abs_eq_zero.mp habs))
  have hne := hirr.ne_rational (((i : ℕ) + 1 : ℤ)) (q : ℤ)
  apply hne
  rw [← heq]
  push_cast
  rfl

#print axioms spectrum_q_any
#print axioms target_off_spectrum
end JacobiBridge
