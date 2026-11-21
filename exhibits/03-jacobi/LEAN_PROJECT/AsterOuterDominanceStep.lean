import AsterCertificate

/-!
# A source-native outer-bound induction step

At a sufficiently remote rational energy, the Jacobi continuant
has a strictly controlled sign. This is the recurrence-side basis
for a computable occupied outer radius.
-/

namespace AsterCertificate

/-- If the current two continuants are positive and increasing,
a diagonal-dominant next step remains positive and increasing. -/
theorem positive_continuant_step
    (a B u v : ℚ)
    (hB : 0 ≤ B)
    (ha : 1 + B ≤ a)
    (hu : 0 < u)
    (hv : 0 ≤ v)
    (hvu : v ≤ u) :
    u ≤ a * u - B * v := by
  have hbu : B * v ≤ B * u := mul_le_mul_of_nonneg_left hvu hB
  have hcoef : (1 + B) * u ≤ a * u :=
    mul_le_mul_of_nonneg_right ha hu.le
  nlinarith

/-- The corresponding controlled alternating-sign step on the
negative side: set U_k=(-1)^k q_k(x). -/
theorem alternating_continuant_step
    (a B u v : ℚ)
    (hB : 0 ≤ B)
    (ha : 1 + B ≤ -a)
    (hu : 0 < u)
    (hv : 0 ≤ v)
    (hvu : v ≤ u) :
    u ≤ -a * u - B * v := by
  exact positive_continuant_step (-a) B u v hB ha hu hv hvu

#print axioms positive_continuant_step
#print axioms alternating_continuant_step

end AsterCertificate
