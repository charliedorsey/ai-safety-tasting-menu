import AsterRadialBracket

/-!
# A finite rational fuel budget

The program chooses one more than the natural ceiling of width/tolerance.
Because 2^k grows at least as fast as k, this intentionally generous
budget certifies the requested final width with no search or limit.
-/

namespace AsterCertificate

/-- Computable rational bisection fuel; no unbounded search. -/
def radialFuel (width ε : ℚ) : ℕ :=
  ⌈width / ε⌉₊ + 1

/-- An explicit proof of the width budget, using the elementary
growth estimate k ≤ 2^k. -/
theorem radialFuel_width_le
    (width ε : ℚ) (hw : 0 ≤ width) (hε : 0 < ε) :
    width / (2 : ℚ) ^ (radialFuel width ε) ≤ ε := by
  let k : ℕ := radialFuel width ε
  have hk : width / ε ≤ (k : ℚ) := by
    dsimp [k, radialFuel]
    have h := Nat.le_ceil (width / ε)
    exact h.trans (by exact_mod_cast Nat.le_succ (⌈width / ε⌉₊))
  have hkpow : (k : ℚ) ≤ (2 : ℚ)^k := by
    exact_mod_cast (Nat.le_of_lt k.lt_two_pow_self)
  have hpowpos : (0 : ℚ) < (2 : ℚ)^k :=
    pow_pos (by norm_num) _
  have hwidth : width ≤ ε * (k : ℚ) := by
    simpa [mul_comm] using (div_le_iff₀ hε).mp hk
  change width / (2 : ℚ)^k ≤ ε
  apply (div_le_iff₀ hpowpos).mpr
  exact hwidth.trans (mul_le_mul_of_nonneg_left hkpow hε.le)

/-- Every certified radial bracket is reduced to any requested
positive rational width by this total computable fuel function. -/
theorem radialFuel_refine_width
    {d b : ℕ → ℚ} {n : ℕ} {τ : ℚ}
    (w : RadialBracket d b n τ) (ε : ℚ) (hε : 0 < ε) :
    (w.refine (radialFuel (w.outer - w.inner) ε)).outer -
        (w.refine (radialFuel (w.outer - w.inner) ε)).inner ≤ ε := by
  rw [RadialBracket.refine_width]
  exact radialFuel_width_le (w.outer - w.inner) ε (sub_nonneg.mpr w.ordered.le) hε

#print axioms radialFuel_width_le
#print axioms radialFuel_refine_width

end AsterCertificate
