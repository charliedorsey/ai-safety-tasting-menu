import JacobiSpectral.Spectrum
import Mathlib.RingTheory.Polynomial.Chebyshev
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Basic

/-!
# `JacobiSpectral.Chebyshev` — constant coefficients, Chebyshev `U`, Dirichlet-chain spectrum

* `cont_map`, `cont_congr`, `cont_sq_congr`, `eval_jpoly`: bookkeeping for the continuant.
* `cont_cheb_corner`: diagonal `(β(2x+α), 2βx, 2βx, …)`, off-diagonal `β`:
  `cont = β^k (U_k(x) + α U_{k-1}(x))` (`U_{-1} = 0`). With `α = 0`: `β^k U_k(x)`.
* `eval_jpoly_const`: `p_n(λ) = β^n U_n((λ − c)/(2β))` for the constant chain.
* **`jacobiEig_const`** (Dirichlet chain): for `β > 0` the eigenvalues of the constant Jacobi
  matrix `J_n(c, β)` are `c + 2β cos((i+1)π/(n+1))`, `i = 0, …, n−1`, in decreasing order.
-/

open Polynomial Finset Matrix

namespace JacobiSpectral

variable {R : Type*} [CommRing R]

lemma cont_map {S : Type*} [CommRing S] (f : R →+* S) (d b : ℕ → R) :
    ∀ n, f (cont d b n) = cont (f ∘ d) (f ∘ b) n
  | 0 => by simp
  | 1 => by simp
  | (n + 2) => by
      rw [cont_succ_succ, cont_succ_succ, ← cont_map f d b (n + 1), ← cont_map f d b n]
      simp

/-- `cont d b n` only sees `d₀, …, d_{n-1}` and `b₀², …, b_{n-2}²`. -/
lemma cont_congr {d d' b b' : ℕ → R} : ∀ n, (∀ i < n, d i = d' i) →
    (∀ i, i + 1 < n → b i ^ 2 = b' i ^ 2) → cont d b n = cont d' b' n
  | 0 => fun _ _ => rfl
  | 1 => fun hd _ => by simp [hd 0 (by omega)]
  | (n + 2) => fun hd hb => by
      rw [cont_succ_succ, cont_succ_succ, hd (n + 1) (by omega), hb n (by omega),
        cont_congr (n + 1) (fun i hi => hd i (by omega)) (fun i hi => hb i (by omega)),
        cont_congr n (fun i hi => hd i (by omega)) (fun i hi => hb i (by omega))]

/-- Evaluation of the polynomial continuant at a scalar. -/
theorem eval_jpoly_eq_cont (d b : ℕ → R) (n : ℕ) (x : R) :
    (jpoly d b n).eval x = cont (fun i => x - d i) b n := by
  rw [jpoly_eq_cont, ← coe_evalRingHom, cont_map]
  exact cont_congr n (fun i _ => by simp) (fun i _ => by simp)

/-- **Chebyshev form of the corner-perturbed constant continuant.** -/
theorem cont_cheb_corner (β α x : R) : ∀ k : ℕ,
    cont (fun i => if i = 0 then β * (2 * x + α) else 2 * β * x) (fun _ => β) k =
      β ^ k * ((Chebyshev.U R (k : ℤ)).eval x + α * (Chebyshev.U R ((k : ℤ) - 1)).eval x)
  | 0 => by simp
  | 1 => by simp
  | (k + 2) => by
      rw [cont_succ_succ, cont_cheb_corner β α x (k + 1), cont_cheb_corner β α x k]
      have r2 := congrArg (eval x) (Chebyshev.U_add_two R (k : ℤ))
      have r1 := congrArg (eval x) (Chebyshev.U_add_one R (k : ℤ))
      simp only [eval_sub, eval_mul, eval_X, eval_ofNat] at r1 r2
      have i1 : ((k + 1 : ℕ) : ℤ) = (k : ℤ) + 1 := by push_cast; ring
      have i2 : ((k + 2 : ℕ) : ℤ) = (k : ℤ) + 2 := by push_cast; ring
      have i3 : (k : ℤ) + 1 - 1 = k := by ring
      have i4 : (k : ℤ) + 2 - 1 = k + 1 := by ring
      simp only [show k + 1 ≠ 0 by omega, ↓reduceIte]
      rw [i1, i2, i3, i4]
      linear_combination (-β ^ (k + 2)) * r2 + (-α * β ^ (k + 2)) * r1

/-- **Constant chain**: `cont (2βx, 2βx, …) (β, β, …) k = β^k U_k(x)`. -/
theorem cont_const_cheb (β x : R) (k : ℕ) :
    cont (fun _ => 2 * β * x) (fun _ => β) k = β ^ k * (Chebyshev.U R (k : ℤ)).eval x := by
  have h := cont_cheb_corner β 0 x k
  simp only [zero_mul, add_zero] at h
  rw [← h]
  exact cont_congr k (fun i _ => by split_ifs <;> ring) (fun i _ => rfl)

/-- The characteristic polynomial of the constant chain in Chebyshev form. -/
theorem eval_jpoly_const (c β : ℝ) (hβ : β ≠ 0) (n : ℕ) (x : ℝ) :
    (jpoly (fun _ => c) (fun _ => β) n).eval x =
      β ^ n * (Chebyshev.U ℝ (n : ℤ)).eval ((x - c) / (2 * β)) := by
  rw [eval_jpoly_eq_cont, ← cont_const_cheb]
  exact cont_congr n (fun i _ => by field_simp) (fun i _ => rfl)

/-- **Dirichlet chain spectrum.** For `β > 0` the `i`-th largest eigenvalue of the constant
Jacobi matrix (diagonal `c`, off-diagonal `β`) is `c + 2β cos((i+1)π/(n+1))`. -/
theorem jacobiEig_const (c β : ℝ) (hβ : 0 < β) (n : ℕ) (i : Fin n) :
    jacobiEig (fun _ => c) (fun _ => β) n i =
      c + 2 * β * Real.cos (((i : ℕ) + 1 : ℝ) * Real.pi / (n + 1)) := by
  set t : Fin n → ℝ := fun j => c + 2 * β * Real.cos (((n : ℝ) - j) * Real.pi / (n + 1)) with htdef
  have hn1 : (0 : ℝ) < n + 1 := by positivity
  have hang : ∀ j : Fin n, 0 < ((n : ℝ) - j) * Real.pi / (n + 1) ∧
      ((n : ℝ) - j) * Real.pi / (n + 1) < Real.pi := by
    intro j
    have hj : (j : ℝ) + 1 ≤ n := by exact_mod_cast j.isLt
    have hj0 : (0 : ℝ) ≤ j := Nat.cast_nonneg _
    constructor
    · apply div_pos (mul_pos (by linarith) Real.pi_pos) hn1
    · rw [div_lt_iff₀ hn1]; nlinarith [Real.pi_pos]
  have hmono : StrictMono t := by
    intro j k hjk
    simp only [htdef]
    have hjk' : (j : ℝ) < k := by exact_mod_cast hjk
    have := Real.cos_lt_cos_of_nonneg_of_le_pi (hang k).1.le (hang j).2.le
      (by apply div_lt_div_of_pos_right _ hn1; nlinarith [Real.pi_pos])
    nlinarith
  have hroot : ∀ j : Fin n, (jpoly (fun _ => c) (fun _ => β) n).eval (t j) = 0 := by
    intro j
    rw [eval_jpoly_const c β hβ.ne']
    have e : (t j - c) / (2 * β) = Real.cos (((n : ℝ) - j) * Real.pi / (n + 1)) := by
      simp only [htdef]; field_simp; ring
    rw [e]
    have hU := Chebyshev.U_real_cos (((n : ℝ) - j) * Real.pi / (n + 1)) (n : ℤ)
    have hsin : Real.sin ((((n : ℤ) : ℝ) + 1) * (((n : ℝ) - j) * Real.pi / (n + 1))) = 0 := by
      have : (((n : ℤ) : ℝ) + 1) * (((n : ℝ) - j) * Real.pi / (n + 1)) = ((n - j : ℕ) : ℝ) * Real.pi := by
        rw [Nat.cast_sub j.isLt.le]; push_cast; field_simp
      rw [this]; exact Real.sin_nat_mul_pi _
    rw [hsin] at hU
    have hs : Real.sin (((n : ℝ) - j) * Real.pi / (n + 1)) ≠ 0 :=
      (Real.sin_pos_of_pos_of_lt_pi (hang j).1 (hang j).2).ne'
    rw [(mul_eq_zero.1 hU).resolve_right hs, mul_zero]
  have hrv : IsRootVec (jpoly (fun _ => c) (fun _ => β) n) t :=
    ⟨hmono, eq_prod_of_roots _ (jpoly_monic _ _ n) (natDegree_jpoly _ _ n) t hmono.injective hroot⟩
  rw [jacobiEig_eq_of_isRootVec hrv i]
  simp only [htdef, Fin.val_rev]
  congr 3
  rw [Nat.cast_sub (by omega)]; push_cast; ring

end JacobiSpectral
