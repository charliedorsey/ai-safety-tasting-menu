import AsterRadialFuel
import Mathlib.Data.Nat.Log

/-!
Exact logarithmic iteration budget, replacing the initial linear-width fuel.
No real logarithm, no floating-point rounding, no unbounded loop.
-/
namespace AsterCertificate

def radialLogFuel (width ε : ℚ) : ℕ :=
  Nat.clog 2 (⌈width / ε⌉₊)

theorem radialLogFuel_width_le (width ε : ℚ)
    (hw : 0 ≤ width) (hε : 0 < ε) :
    width / (2 : ℚ) ^ (radialLogFuel width ε) ≤ ε := by
  have hceil : width / ε ≤ (⌈width / ε⌉₊ : ℚ) :=
    Nat.le_ceil _
  have hpow_nat :
      ⌈width / ε⌉₊ ≤ (2 : ℕ) ^ (radialLogFuel width ε) := by
    unfold radialLogFuel
    exact Nat.le_pow_clog (by norm_num) _
  have hpow :
      (⌈width / ε⌉₊ : ℚ) ≤ (2 : ℚ) ^ (radialLogFuel width ε) := by
    exact_mod_cast hpow_nat
  have hratio : width / ε ≤ (2 : ℚ) ^ (radialLogFuel width ε) :=
    hceil.trans hpow
  have hwidth : width ≤ ε * (2 : ℚ) ^ (radialLogFuel width ε) := by
    simpa only [mul_comm] using (div_le_iff₀ hε).mp hratio
  have hpos : (0 : ℚ) < (2 : ℚ) ^ (radialLogFuel width ε) := by positivity
  exact (div_le_iff₀ hpos).mpr hwidth

theorem radialLogFuel_refine_width
    {d b : ℕ → ℚ} {n : ℕ} {τ : ℚ}
    (w : RadialBracket d b n τ) (ε : ℚ) (hε : 0 < ε) :
    (w.refine (radialLogFuel (w.outer - w.inner) ε)).outer -
        (w.refine (radialLogFuel (w.outer - w.inner) ε)).inner ≤ ε := by
  rw [RadialBracket.refine_width]
  exact radialLogFuel_width_le _ ε (sub_nonneg.mpr w.ordered.le) hε

#eval radialLogFuel (97 / 5) (1 / (2 : ℚ)^40)
#print axioms radialLogFuel_width_le
#print axioms radialLogFuel_refine_width
end AsterCertificate
