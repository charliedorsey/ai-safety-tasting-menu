import JacobiSpectral.Continuant
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# `PeriodicJacobi.PhaseLaw` — exact finite-volume phase law for the period-2 Jacobi chain

`J_N = jacobi (pd a b) (pd t₁ t₂) N`: diagonal `a, b, a, …`, off-diagonal `t₁, t₂, t₁, …`.

* `det_periodic` : `det (E − J_N) = cont (pd (E−a) (E−b)) (pd t₁ t₂) N`.
* `cont_odd`, `cont_even` : closed forms through the scaled Chebyshev sequence
  `W 0 = 1, W 1 = Y, W (m+2) = Y W (m+1) − P² W m`, with `Y = (E−a)(E−b) − t₁² − t₂²`, `P = t₁t₂`.
* `W_mul_sin` : if `Y = 2P cos θ` then `W m · sin θ = P^m sin((m+1)θ)`.
* `det_odd_eq_zero_iff` : `det (E − J_{2m+1}) = 0 ↔ ∃ k : ℤ, (m+1)θ = kπ`  (homogeneous).
* `det_even_eq_zero_iff` : `det (E − J_{2m+2}) = 0 ↔ ∃ k : ℤ, (m+1)θ + φ = kπ`,
  `φ = arg (t₂ + t₁ e^{iθ})`  (inhomogeneous, energy-dependent shift).
* `mem_spectrum_iff_det` : `E ∈ spectrum ℝ J ↔ det (E − J) = 0`.
-/

open Matrix JacobiSpectral

namespace PeriodicJacobi

section Ring
variable {R : Type*} [CommRing R]

/-- Period-2 sequence `u, v, u, v, …`. -/
def pd (u v : R) (i : ℕ) : R := if i % 2 = 0 then u else v

@[simp] lemma pd_even (u v : R) (k : ℕ) : pd u v (2 * k) = u := by simp [pd]
@[simp] lemma pd_odd (u v : R) (k : ℕ) : pd u v (2 * k + 1) = v := by
  simp [pd, Nat.add_mod]

/-- Scaled Chebyshev sequence: `W m = P^m U_m (Y / 2P)`. -/
def W (Y P : R) : ℕ → R
  | 0 => 1
  | 1 => Y
  | (m + 2) => Y * W Y P (m + 1) - P ^ 2 * W Y P m

@[simp] lemma W_zero (Y P : R) : W Y P 0 = 1 := rfl
@[simp] lemma W_one (Y P : R) : W Y P 1 = Y := rfl
lemma W_succ_succ (Y P : R) (m : ℕ) : W Y P (m + 2) = Y * W Y P (m + 1) - P ^ 2 * W Y P m := rfl

/-- Both parities at once. -/
theorem cont_pair (u v t₁ t₂ : R) (m : ℕ) :
    cont (pd u v) (pd t₁ t₂) (2 * m + 1) = u * W (u * v - t₁ ^ 2 - t₂ ^ 2) (t₁ * t₂) m ∧
    cont (pd u v) (pd t₁ t₂) (2 * m + 2) =
      W (u * v - t₁ ^ 2 - t₂ ^ 2) (t₁ * t₂) (m + 1) + t₂ ^ 2 * W (u * v - t₁ ^ 2 - t₂ ^ 2) (t₁ * t₂) m := by
  induction m with
  | zero =>
    refine ⟨by simp [pd], ?_⟩
    rw [show 2 * 0 + 2 = 0 + 2 from rfl, cont_succ_succ]
    simp [pd]; ring
  | succ m ih =>
    obtain ⟨h1, h2⟩ := ih
    have e1 : cont (pd u v) (pd t₁ t₂) (2 * (m + 1) + 1) =
        pd u v (2 * (m + 1)) * cont (pd u v) (pd t₁ t₂) (2 * m + 2) -
          pd t₁ t₂ (2 * m + 1) ^ 2 * cont (pd u v) (pd t₁ t₂) (2 * m + 1) := by
      rw [show 2 * (m + 1) + 1 = (2 * m + 1) + 2 by ring, cont_succ_succ]
      rw [show 2 * m + 1 + 1 = 2 * (m + 1) by ring, show 2 * (m + 1) = 2 * m + 2 by ring]
    have o1 : cont (pd u v) (pd t₁ t₂) (2 * (m + 1) + 1) =
        u * W (u * v - t₁ ^ 2 - t₂ ^ 2) (t₁ * t₂) (m + 1) := by
      rw [e1, h1, h2, pd_even, pd_odd]; ring
    refine ⟨o1, ?_⟩
    have e2 : cont (pd u v) (pd t₁ t₂) (2 * (m + 1) + 2) =
        pd u v (2 * (m + 1) + 1) * cont (pd u v) (pd t₁ t₂) (2 * (m + 1) + 1) -
          pd t₁ t₂ (2 * (m + 1)) ^ 2 * cont (pd u v) (pd t₁ t₂) (2 * m + 2) := by
      rw [show 2 * (m + 1) + 2 = (2 * m + 2) + 2 by ring, cont_succ_succ]
      rw [show 2 * m + 2 + 1 = 2 * (m + 1) + 1 by ring, show 2 * m + 2 = 2 * (m + 1) by ring]
    rw [e2, o1, h2, pd_even, pd_odd, show m + 1 + 1 = m + 2 by ring, W_succ_succ]; ring

theorem cont_odd (u v t₁ t₂ : R) (m : ℕ) :
    cont (pd u v) (pd t₁ t₂) (2 * m + 1) = u * W (u * v - t₁ ^ 2 - t₂ ^ 2) (t₁ * t₂) m :=
  (cont_pair u v t₁ t₂ m).1

theorem cont_even (u v t₁ t₂ : R) (m : ℕ) :
    cont (pd u v) (pd t₁ t₂) (2 * m + 2) =
      W (u * v - t₁ ^ 2 - t₂ ^ 2) (t₁ * t₂) (m + 1) + t₂ ^ 2 * W (u * v - t₁ ^ 2 - t₂ ^ 2) (t₁ * t₂) m :=
  (cont_pair u v t₁ t₂ m).2

/-- The continuant only sees squares of the off-diagonal. -/
lemma cont_neg_b (d b : ℕ → R) : ∀ n, cont d (fun i => -b i) n = cont d b n
  | 0 => rfl
  | 1 => rfl
  | (n + 2) => by
      rw [cont_succ_succ, cont_succ_succ, cont_neg_b d b (n + 1), cont_neg_b d b n, neg_sq]

/-- Continuants commute with ring homomorphisms. -/
lemma map_cont {S : Type*} [CommRing S] (f : R →+* S) (d b : ℕ → R) : ∀ n,
    f (cont d b n) = cont (fun i => f (d i)) (fun i => f (b i)) n
  | 0 => by simp
  | 1 => by simp
  | (n + 2) => by
      rw [cont_succ_succ, cont_succ_succ, ← map_cont f d b (n + 1), ← map_cont f d b n]
      simp [map_sub, map_mul, map_pow]

/-- `det (E − J)` of a Jacobi matrix is the continuant of the shifted diagonal. -/
theorem det_scalar_sub_jacobi (d b : ℕ → R) (n : ℕ) (E : R) :
    (scalar (Fin n) E - jacobi d b n).det = cont (fun i => E - d i) b n := by
  rw [← eval_jpoly, jpoly_eq_cont]
  have := map_cont (Polynomial.evalRingHom E) (fun i => Polynomial.X - Polynomial.C (d i))
    (fun i => -Polynomial.C (b i)) n
  simp only [Polynomial.coe_evalRingHom] at this
  rw [this]
  simp only [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C, Polynomial.eval_neg]
  exact cont_neg_b _ _ n

lemma pd_sub (E u v : R) : (fun i => E - pd u v i) = pd (E - u) (E - v) := by
  funext i; unfold pd; split_ifs <;> rfl

/-- **Periodic determinant.** -/
theorem det_periodic (a b t₁ t₂ E : R) (N : ℕ) :
    (scalar (Fin N) E - jacobi (pd a b) (pd t₁ t₂) N).det = cont (pd (E - a) (E - b)) (pd t₁ t₂) N := by
  rw [det_scalar_sub_jacobi, pd_sub]

end Ring

/-! ### Trigonometric form over `ℝ` -/

/-- **Chebyshev sine law** for the scaled sequence. -/
theorem W_mul_sin (P θ : ℝ) : ∀ m : ℕ,
    W (2 * P * Real.cos θ) P m * Real.sin θ = P ^ m * Real.sin ((m + 1 : ℝ) * θ)
  | 0 => by simp
  | 1 => by
      simp only [W_one, pow_one]
      rw [show ((1 : ℕ) + 1 : ℝ) * θ = θ + θ by push_cast; ring, Real.sin_add]; ring
  | (m + 2) => by
      have e1 := W_mul_sin P θ (m + 1)
      have e2 := W_mul_sin P θ m
      rw [W_succ_succ,
        show (2 * P * Real.cos θ * W (2 * P * Real.cos θ) P (m + 1) - P ^ 2 * W (2 * P * Real.cos θ) P m) *
            Real.sin θ = 2 * P * Real.cos θ * (W (2 * P * Real.cos θ) P (m + 1) * Real.sin θ) -
              P ^ 2 * (W (2 * P * Real.cos θ) P m * Real.sin θ) by ring, e1, e2]
      have h1 : ((m + 2 : ℕ) + 1 : ℝ) * θ = ((m + 1 : ℕ) + 1 : ℝ) * θ + θ := by push_cast; ring
      have h2 : ((m : ℕ) + 1 : ℝ) * θ = ((m + 1 : ℕ) + 1 : ℝ) * θ - θ := by push_cast; ring
      rw [h1, h2, Real.sin_add, Real.sin_sub]; ring

variable {a b t₁ t₂ E θ : ℝ}

/-- Odd trigonometric form. -/
theorem sin_mul_det_odd (hY : (E - a) * (E - b) - t₁ ^ 2 - t₂ ^ 2 = 2 * (t₁ * t₂) * Real.cos θ) (m : ℕ) :
    Real.sin θ * (scalar (Fin (2 * m + 1)) E - jacobi (pd a b) (pd t₁ t₂) (2 * m + 1)).det =
      (E - a) * (t₁ * t₂) ^ m * Real.sin ((m + 1 : ℝ) * θ) := by
  rw [det_periodic, cont_odd, hY, mul_comm (Real.sin θ), mul_assoc, W_mul_sin]; ring

/-- Even trigonometric form (sum of two sines). -/
theorem sin_mul_det_even (hY : (E - a) * (E - b) - t₁ ^ 2 - t₂ ^ 2 = 2 * (t₁ * t₂) * Real.cos θ) (m : ℕ) :
    Real.sin θ * (scalar (Fin (2 * m + 2)) E - jacobi (pd a b) (pd t₁ t₂) (2 * m + 2)).det =
      t₂ * (t₁ * t₂) ^ m *
        (t₁ * Real.sin ((m + 2 : ℝ) * θ) + t₂ * Real.sin ((m + 1 : ℝ) * θ)) := by
  rw [det_periodic, cont_even, hY, mul_add, mul_comm (Real.sin θ), W_mul_sin,
    mul_comm (Real.sin θ) (t₂ ^ 2 * _), mul_assoc (t₂ ^ 2), W_mul_sin]
  push_cast; ring_nf

/-- The end-bond phase `φ(θ) = arg (t₂ + t₁ e^{iθ})`, written without `exp`. -/
noncomputable def phase (t₁ t₂ θ : ℝ) : ℝ :=
  Complex.arg (⟨t₂ + t₁ * Real.cos θ, t₁ * Real.sin θ⟩ : ℂ)

/-- `t₁ sin((n+1)θ) + t₂ sin(nθ) = ρ sin(nθ + φ)` with `ρ = |t₂ + t₁e^{iθ}|`. -/
theorem two_sine_phase (t₁ t₂ θ x : ℝ) :
    t₁ * Real.sin (x + θ) + t₂ * Real.sin x =
      ‖(⟨t₂ + t₁ * Real.cos θ, t₁ * Real.sin θ⟩ : ℂ)‖ * Real.sin (x + phase t₁ t₂ θ) := by
  set z : ℂ := ⟨t₂ + t₁ * Real.cos θ, t₁ * Real.sin θ⟩
  have hc : ‖z‖ * Real.cos (Complex.arg z) = t₂ + t₁ * Real.cos θ := Complex.norm_mul_cos_arg z
  have hs : ‖z‖ * Real.sin (Complex.arg z) = t₁ * Real.sin θ := Complex.norm_mul_sin_arg z
  have hp : phase t₁ t₂ θ = Complex.arg z := rfl
  rw [hp, Real.sin_add, Real.sin_add]
  linear_combination (-Real.sin x) * hc + (-Real.cos x) * hs

/-- **Odd phase law (homogeneous).** -/
theorem det_odd_eq_zero_iff
    (hY : (E - a) * (E - b) - t₁ ^ 2 - t₂ ^ 2 = 2 * (t₁ * t₂) * Real.cos θ)
    (hθ : Real.sin θ ≠ 0) (ht : t₁ * t₂ ≠ 0) (hEa : E ≠ a) (m : ℕ) :
    (scalar (Fin (2 * m + 1)) E - jacobi (pd a b) (pd t₁ t₂) (2 * m + 1)).det = 0 ↔
      ∃ k : ℤ, (m + 1 : ℝ) * θ = k * Real.pi := by
  have key := sin_mul_det_odd hY m
  constructor
  · intro h
    rw [h, mul_zero] at key
    have : Real.sin ((m + 1 : ℝ) * θ) = 0 := by
      rcases mul_eq_zero.mp key.symm with h' | h'
      · exact absurd h' (mul_ne_zero (sub_ne_zero.mpr hEa) (pow_ne_zero _ ht))
      · exact h'
    obtain ⟨k, hk⟩ := Real.sin_eq_zero_iff.mp this
    exact ⟨k, hk.symm⟩
  · rintro ⟨k, hk⟩
    have : Real.sin ((m + 1 : ℝ) * θ) = 0 := Real.sin_eq_zero_iff.mpr ⟨k, hk.symm⟩
    rw [this, mul_zero] at key
    exact (mul_eq_zero.mp key).resolve_left hθ

/-- **Even phase law (inhomogeneous, energy-dependent boundary shift).** -/
theorem det_even_eq_zero_iff
    (hY : (E - a) * (E - b) - t₁ ^ 2 - t₂ ^ 2 = 2 * (t₁ * t₂) * Real.cos θ)
    (hθ : Real.sin θ ≠ 0) (h₁ : t₁ ≠ 0) (h₂ : t₂ ≠ 0) (m : ℕ) :
    (scalar (Fin (2 * m + 2)) E - jacobi (pd a b) (pd t₁ t₂) (2 * m + 2)).det = 0 ↔
      ∃ k : ℤ, (m + 1 : ℝ) * θ + phase t₁ t₂ θ = k * Real.pi := by
  have key := sin_mul_det_even hY m
  have hx : t₁ * Real.sin ((m + 2 : ℝ) * θ) + t₂ * Real.sin ((m + 1 : ℝ) * θ) =
      ‖(⟨t₂ + t₁ * Real.cos θ, t₁ * Real.sin θ⟩ : ℂ)‖ *
        Real.sin ((m + 1 : ℝ) * θ + phase t₁ t₂ θ) := by
    rw [← two_sine_phase]; congr 2; ring
  have hz : ‖(⟨t₂ + t₁ * Real.cos θ, t₁ * Real.sin θ⟩ : ℂ)‖ ≠ 0 := by
    rw [norm_ne_zero_iff]; intro h
    have := congrArg Complex.im h
    simp only [Complex.zero_im] at this
    exact mul_ne_zero h₁ hθ this
  have hpre : t₂ * (t₁ * t₂) ^ m ≠ 0 := mul_ne_zero h₂ (pow_ne_zero _ (mul_ne_zero h₁ h₂))
  rw [hx] at key
  constructor
  · intro h
    rw [h, mul_zero] at key
    have : Real.sin ((m + 1 : ℝ) * θ + phase t₁ t₂ θ) = 0 := by
      rcases mul_eq_zero.mp key.symm with h' | h'
      · exact absurd h' hpre
      · exact (mul_eq_zero.mp h').resolve_left hz
    obtain ⟨k, hk⟩ := Real.sin_eq_zero_iff.mp this
    exact ⟨k, hk.symm⟩
  · rintro ⟨k, hk⟩
    have : Real.sin ((m + 1 : ℝ) * θ + phase t₁ t₂ θ) = 0 := Real.sin_eq_zero_iff.mpr ⟨k, hk.symm⟩
    rw [this, mul_zero, mul_zero] at key
    exact (mul_eq_zero.mp key).resolve_left hθ

/-- Spectrum of a real square matrix = zeros of `det (E − J)`. -/
theorem mem_spectrum_iff_det {n : ℕ} (J : Matrix (Fin n) (Fin n) ℝ) (E : ℝ) :
    E ∈ spectrum ℝ J ↔ (scalar (Fin n) E - J).det = 0 := by
  rw [spectrum.mem_iff, Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero, not_not]
  rfl

/-- **Theorem 1 (spectral form, odd length).** -/
theorem mem_spectrum_odd_iff
    (hY : (E - a) * (E - b) - t₁ ^ 2 - t₂ ^ 2 = 2 * (t₁ * t₂) * Real.cos θ)
    (hθ : Real.sin θ ≠ 0) (ht : t₁ * t₂ ≠ 0) (hEa : E ≠ a) (m : ℕ) :
    E ∈ spectrum ℝ (jacobi (pd a b) (pd t₁ t₂) (2 * m + 1)) ↔
      ∃ k : ℤ, (m + 1 : ℝ) * θ = k * Real.pi := by
  rw [mem_spectrum_iff_det]; exact det_odd_eq_zero_iff hY hθ ht hEa m

/-- **Theorem 1 (spectral form, even length).** -/
theorem mem_spectrum_even_iff
    (hY : (E - a) * (E - b) - t₁ ^ 2 - t₂ ^ 2 = 2 * (t₁ * t₂) * Real.cos θ)
    (hθ : Real.sin θ ≠ 0) (h₁ : t₁ ≠ 0) (h₂ : t₂ ≠ 0) (m : ℕ) :
    E ∈ spectrum ℝ (jacobi (pd a b) (pd t₁ t₂) (2 * m + 2)) ↔
      ∃ k : ℤ, (m + 1 : ℝ) * θ + phase t₁ t₂ θ = k * Real.pi := by
  rw [mem_spectrum_iff_det]; exact det_even_eq_zero_iff hY hθ h₁ h₂ m

/-- At an interior energy `E ≠ a` is automatic (with `t₁, t₂ > 0`). -/
theorem ne_a_of_interior (ht₁ : 0 < t₁) (ht₂ : 0 < t₂)
    (hY : (E - a) * (E - b) - t₁ ^ 2 - t₂ ^ 2 = 2 * (t₁ * t₂) * Real.cos θ)
    (hθ : Real.sin θ ≠ 0) : E ≠ a := by
  intro h; subst h
  have hc : Real.cos θ ≠ -1 := by
    intro hc; apply hθ
    have := Real.sin_sq_add_cos_sq θ; rw [hc] at this; nlinarith [sq_nonneg (Real.sin θ)]
  have hc' : -1 < Real.cos θ := lt_of_le_of_ne (Real.neg_one_le_cos θ) (Ne.symm hc)
  have : 0 < t₁ * t₂ := mul_pos ht₁ ht₂
  nlinarith [sq_nonneg (t₁ - t₂)]

end PeriodicJacobi
