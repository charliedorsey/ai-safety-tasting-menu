import Mathlib

/-!
# Two real inequalities for a perturbed Jacobi continuant

These are deliberately independent of the continuant and its indexing.
The recurrence induction will only substitute the correct real values.
-/

namespace AsterCertificate

private theorem abs_sub_le_sum (u v : ℝ) :
    |u - v| ≤ |u| + |v| := by
  simpa [sub_eq_add_neg, abs_neg] using (abs_add_le u (-v))

/-- Uniform magnitude of a single perturbed recurrence step. -/
theorem real_affine_step_bound
    (a x u v B C D : ℝ)
    (hx : |x| ≤ 1) (hB : 0 ≤ B) (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hu : |u| ≤ C) (hv : |v| ≤ D) :
    |(a + x) * u - B * v| ≤ (|a| + 1) * C + B * D := by
  have hax : |a + x| ≤ |a| + 1 :=
    (abs_add_le a x).trans (add_le_add_right hx _)
  have hfirst :
      |a + x| * |u| ≤ (|a| + 1) * C :=
    (mul_le_mul_of_nonneg_right hax (abs_nonneg u)).trans
      (mul_le_mul_of_nonneg_left hu (by positivity))
  have hsecond : B * |v| ≤ B * D :=
    mul_le_mul_of_nonneg_left hv hB
  calc
    |(a + x) * u - B * v|
        ≤ |(a + x) * u| + |B * v| :=
          abs_sub_le_sum _ _
    _ = |a + x| * |u| + B * |v| := by
          rw [abs_mul, abs_mul, abs_of_nonneg hB]
    _ ≤ (|a| + 1) * C + B * D :=
          add_le_add hfirst hsecond

/-- Lipschitz constant for a perturbed recurrence step. -/
theorem real_affine_difference_bound
    (a x u u₀ v v₀ B C D E : ℝ)
    (hB : 0 ≤ B)
    (hu : |u| ≤ C)
    (hdu : |u - u₀| ≤ |x| * D)
    (hdv : |v - v₀| ≤ |x| * E) :
    |((a + x) * u - B * v) - (a * u₀ - B * v₀)| ≤
      |x| * (C + |a| * D + B * E) := by
  have hident :
      ((a + x) * u - B * v) - (a * u₀ - B * v₀) =
        (x * u + a * (u - u₀)) - B * (v - v₀) := by ring
  have hfirst : |x| * |u| ≤ |x| * C :=
    mul_le_mul_of_nonneg_left hu (abs_nonneg x)
  have hsecond : |a| * |u - u₀| ≤ |a| * (|x| * D) :=
    mul_le_mul_of_nonneg_left hdu (abs_nonneg a)
  have hthird : B * |v - v₀| ≤ B * (|x| * E) :=
    mul_le_mul_of_nonneg_left hdv hB
  rw [hident]
  calc
    |(x * u + a * (u - u₀)) - B * (v - v₀)|
        ≤ |x * u + a * (u - u₀)| + |B * (v - v₀)| :=
          abs_sub_le_sum _ _
    _ ≤ (|x * u| + |a * (u - u₀)|) + |B * (v - v₀)| :=
          add_le_add_left (abs_add_le _ _) _
    _ = (|x| * |u| + |a| * |u - u₀|) + B * |v - v₀| := by
          rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg hB]
    _ ≤ (|x| * C + |a| * (|x| * D)) + B * (|x| * E) :=
          add_le_add (add_le_add hfirst hsecond) hthird
    _ = |x| * (C + |a| * D + B * E) := by ring

#print axioms real_affine_step_bound
#print axioms real_affine_difference_bound

end AsterCertificate
