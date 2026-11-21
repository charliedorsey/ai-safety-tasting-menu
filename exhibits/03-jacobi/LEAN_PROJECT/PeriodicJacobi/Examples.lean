import PeriodicJacobi.PhaseLaw
import PeriodicJacobi.Arith

/-!
# `PeriodicJacobi.Examples` — consistency checks and consumers

* `phase_self` : at `t₁ = t₂ = t > 0`, `φ(θ) = θ/2` for `θ ∈ (−π, π)`.
* `const_chain_even` : with `a = b`, `t₁ = t₂`, the even law is `(2m+3)·(θ/2) ∈ πℤ`, i.e. the
  constant-chain law at length `N = 2m+2` with single-site phase `θ/2` and `q = N + 1`
  (Hunt 1 `jacobiEig_const`; prior Jacobi–Diophantine return). The period-2 law contains the
  constant chain as a special case: falsifier F0 passes in Lean.
* `homogeneous_quantization` : the mechanism lemma applied to `F θ = (m+1)θ` (odd law) gives
  the exact two-sided bound `π‖(m+1)θ_E/π‖/(m+1)` with no `O(1/m)` loss.
-/

open Matrix JacobiSpectral
open scoped Real

namespace PeriodicJacobi

theorem phase_self {t θ : ℝ} (ht : 0 < t) (h1 : -π < θ) (h2 : θ < π) :
    phase t t θ = θ / 2 := by
  unfold phase
  have hc : 0 < Real.cos (θ / 2) := Real.cos_pos_of_mem_Ioo ⟨by linarith, by linarith⟩
  have hz : (⟨t + t * Real.cos θ, t * Real.sin θ⟩ : ℂ) =
      ((2 * t * Real.cos (θ / 2) : ℝ) : ℂ) *
        (Complex.cos ((θ / 2 : ℝ) : ℂ) + Complex.sin ((θ / 2 : ℝ) : ℂ) * Complex.I) := by
    have hcθ : Real.cos θ = 2 * Real.cos (θ / 2) ^ 2 - 1 := by
      have := Real.cos_two_mul (θ / 2); rwa [show 2 * (θ / 2) = θ by ring] at this
    have hsθ : Real.sin θ = 2 * Real.sin (θ / 2) * Real.cos (θ / 2) := by
      have := Real.sin_two_mul (θ / 2); rwa [show 2 * (θ / 2) = θ by ring] at this
    apply Complex.ext
    · simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.add_re,
        Complex.add_im, Complex.mul_im, Complex.I_re, Complex.I_im, ← Complex.ofReal_cos,
        ← Complex.ofReal_sin]
      rw [hcθ]; ring
    · simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.add_re,
        Complex.add_im, Complex.mul_im, Complex.I_re, Complex.I_im, ← Complex.ofReal_cos,
        ← Complex.ofReal_sin]
      rw [hsθ]; ring
  rw [hz, Complex.arg_real_mul _ (by positivity)]
  rw [Complex.arg_cos_add_sin_mul_I ⟨by linarith, by linarith⟩]

/-- Constant chain (`a = b`, `t₁ = t₂ = t`): the period-2 even law is the constant-chain law. -/
theorem const_chain_even {a t E θ : ℝ} (ht : 0 < t) (hθ0 : 0 < θ) (hθπ : θ < π)
    (hY : (E - a) * (E - a) - t ^ 2 - t ^ 2 = 2 * (t * t) * Real.cos θ) (m : ℕ) :
    E ∈ spectrum ℝ (jacobi (pd a a) (pd t t) (2 * m + 2)) ↔
      ∃ k : ℤ, ((2 * m + 2 : ℕ) + 1 : ℝ) * (θ / 2) = k * π := by
  have hs : Real.sin θ ≠ 0 := (Real.sin_pos_of_pos_of_lt_pi hθ0 hθπ).ne'
  rw [mem_spectrum_even_iff hY hs ht.ne' ht.ne', phase_self ht (by linarith) hθπ]
  constructor <;> rintro ⟨k, hk⟩ <;> exact ⟨k, by push_cast at hk ⊢; linarith⟩

/-- Mechanism lemma, homogeneous instance: `F θ = (m+1)θ` is exactly `(m+1)`-bi-Lipschitz. -/
theorem homogeneous_quantization (m : ℕ) (θE : ℝ) :
    (∀ θ (k : ℤ), ((m : ℝ) + 1) * θ = k * π →
        π * dZ (((m : ℝ) + 1) * θE / π) / ((m : ℝ) + 1) ≤ |θ - θE|) ∧
    (∀ θ, ((m : ℝ) + 1) * θ = (round (((m : ℝ) + 1) * θE / π) : ℝ) * π →
        |θ - θE| ≤ π * dZ (((m : ℝ) + 1) * θE / π) / ((m : ℝ) + 1)) := by
  have hm : (0 : ℝ) < (m : ℝ) + 1 := by positivity
  have hlip : ∀ x y : ℝ, |((m : ℝ) + 1) * x - ((m : ℝ) + 1) * y| = ((m : ℝ) + 1) * |x - y| := by
    intro x y; rw [← mul_sub, abs_mul, abs_of_pos hm]
  exact implicit_quantization (F := fun θ => ((m : ℝ) + 1) * θ) hm hm
    (fun x y => (hlip x y).ge) (fun x y => (hlip x y).le) θE

end PeriodicJacobi
