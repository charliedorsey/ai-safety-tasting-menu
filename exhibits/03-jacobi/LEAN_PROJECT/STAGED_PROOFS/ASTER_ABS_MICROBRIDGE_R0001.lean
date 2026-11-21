import Mathlib

/-! Proof-engineering experiment, source-only, independent of Kestrelle's originals. -/

namespace AsterAbsMicrobridge

theorem abs_affine_mul_step
    (a x u v B C D : ℝ)
    (hx : |x| ≤ 1) (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hu : |u| ≤ C) (hv : |v| ≤ D) (hB : 0 ≤ B) :
    |(a + x) * u - B * v| ≤ (|a| + 1) * C + B * D := by
  have hax : |a + x| ≤ |a| + 1 := by
    calc
      |a + x| ≤ |a| + |x| := abs_add_le _ _
      _ ≤ |a| + 1 := by linarith
  calc
    |(a + x) * u - B * v| ≤ |(a + x) * u| + |B * v| := by
      simpa using (abs_sub_le ((a + x) * u) 0 (B * v))
    _ = |a + x| * |u| + B * |v| := by
      rw [abs_mul, abs_mul, abs_of_nonneg hB]
    _ ≤ (|a| + 1) * C + B * D := by
      apply add_le_add
      · exact mul_le_mul hax hu (abs_nonneg _) (by positivity)
      · exact mul_le_mul_of_nonneg_left hv hB

theorem abs_affine_diff_step
    (a x u u0 v v0 B C D E : ℝ)
    (hC : 0 ≤ C) (hD : 0 ≤ D) (hE : 0 ≤ E)
    (hu : |u| ≤ C)
    (hdu : |u - u0| ≤ |x| * D) (hdv : |v - v0| ≤ |x| * E)
    (hB : 0 ≤ B) :
    |((a + x) * u - B * v) - (a * u0 - B * v0)| ≤
      |x| * (C + |a| * D + B * E) := by
  have hident :
      ((a + x) * u - B * v) - (a * u0 - B * v0) =
        (x * u + a * (u - u0)) - B * (v - v0) := by ring
  rw [hident]
  calc
    |(x * u + a * (u - u0)) - B * (v - v0)| ≤
      |x * u + a * (u - u0)| + |B * (v - v0)| := by
        simpa using (abs_sub_le (x * u + a * (u - u0)) 0 (B * (v - v0)))
    _ ≤ |x * u| + |a * (u - u0)| + |B * (v - v0)| := by
      exact add_le_add_right (abs_add_le _ _) _
    _ = |x| * |u| + |a| * |u - u0| + B * |v - v0| := by
      rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg hB]
    _ ≤ |x| * C + |a| * (|x| * D) + B * (|x| * E) := by
      apply add_le_add
      · apply add_le_add
        · exact mul_le_mul_of_nonneg_left hu (abs_nonneg _)
        · exact mul_le_mul_of_nonneg_left hdu (abs_nonneg _)
      · exact mul_le_mul_of_nonneg_left hdv hB
    _ = |x| * (C + |a| * D + B * E) := by ring

#print axioms abs_affine_mul_step
#print axioms abs_affine_diff_step
end AsterAbsMicrobridge
