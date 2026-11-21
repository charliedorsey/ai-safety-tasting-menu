/-
Copyright (c) 2026 Charlie Dorsey. Released under Apache 2.0 license.
-/
import DiscreteSturm.MinMax
import DiscreteSturm.Oscillation
import Mathlib.LinearAlgebra.Matrix.PosDef

/-!
# Eigenvalue monotonicity under diagonal perturbation

Matrix forms of Weyl monotonicity (from `DiscreteSturm.MinMax`) and their Jacobi consequences.
Eigenvalues are in Mathlib's decreasing order (`eigenvalues₀`, `jacobiEig`).

* `eigenvalues₀_le_add`, `eigenvalues₀_le_of_posSemidef`: `xᵀAx ≤ xᵀBx + c‖x‖²` gives
  `λ_i(A) ≤ λ_i(B) + c`; in particular `A ≤ B` in the Loewner order gives `λ_i(A) ≤ λ_i(B)`.
* `jacobiEig_mono`: `d ≤ d'` gives `λ_i(J(d)) ≤ λ_i(J(d'))`, for any off-diagonals.
* `jacobiEig_lt_of_head_lt`: if moreover `d₀ < d'₀` and all `b_k ≠ 0`, then every eigenvalue
  strictly increases. (Strictness can fail for interior perturbations; see `Examples`.)
* `jacobiEig_add_const`: shifting the diagonal by `c` shifts every eigenvalue by `c`.
* `abs_jacobiEig_sub_le`: if `|d'_k − d_k| ≤ ε` then `|λ_i(J(d')) − λ_i(J(d))| ≤ ε`.
-/

open Matrix Finset JacobiSpectral

namespace DiscreteSturm

/-! ### Matrix forms -/

lemma inner_toEuclideanLin {N : ℕ} (A : Matrix (Fin N) (Fin N) ℝ) (v : EuclideanSpace ℝ (Fin N)) :
    inner ℝ (toEuclideanLin A v) v = (WithLp.ofLp v) ⬝ᵥ (A *ᵥ WithLp.ofLp v) := by
  rw [EuclideanSpace.inner_eq_star_dotProduct]
  simp [toEuclideanLin]

lemma inner_self_euclidean {N : ℕ} (v : EuclideanSpace ℝ (Fin N)) :
    inner ℝ v v = (WithLp.ofLp v) ⬝ᵥ (WithLp.ofLp v) := by
  rw [EuclideanSpace.inner_eq_star_dotProduct]
  simp

lemma eigenvalues₀_eq_isSymmetric {N : ℕ} {A : Matrix (Fin N) (Fin N) ℝ} (hA : A.IsHermitian) :
    hA.eigenvalues₀ =
      (isSymmetric_toEuclideanLin_iff.mpr hA).eigenvalues finrank_euclideanSpace := rfl

/-- **Weyl, matrix form.** `xᵀAx ≤ xᵀBx + c xᵀx` for all `x` gives `λ_i(A) ≤ λ_i(B) + c`. -/
theorem eigenvalues₀_le_add {N : ℕ} {A B : Matrix (Fin N) (Fin N) ℝ} (hA : A.IsHermitian)
    (hB : B.IsHermitian) (c : ℝ)
    (hle : ∀ x : Fin N → ℝ, x ⬝ᵥ (A *ᵥ x) ≤ x ⬝ᵥ (B *ᵥ x) + c * (x ⬝ᵥ x))
    (i : Fin (Fintype.card (Fin N))) :
    hA.eigenvalues₀ i ≤ hB.eigenvalues₀ i + c := by
  rw [eigenvalues₀_eq_isSymmetric, eigenvalues₀_eq_isSymmetric]
  refine eigenvalues_le_add_of_inner_le _ _ _ c (fun v => ?_) i
  rw [inner_toEuclideanLin, inner_toEuclideanLin, inner_self_euclidean]
  exact hle _

/-- **Weyl monotonicity in the Loewner order.** If `B − A` is positive semidefinite then
`λ_i(A) ≤ λ_i(B)` for all `i`. -/
theorem eigenvalues₀_le_of_posSemidef {N : ℕ} {A B : Matrix (Fin N) (Fin N) ℝ}
    (hA : A.IsHermitian) (hB : B.IsHermitian) (hAB : (B - A).PosSemidef)
    (i : Fin (Fintype.card (Fin N))) : hA.eigenvalues₀ i ≤ hB.eigenvalues₀ i := by
  have := eigenvalues₀_le_add hA hB 0 (fun x => by
    have h := hAB.dotProduct_mulVec_nonneg x
    rw [sub_mulVec, dotProduct_sub, star_trivial] at h
    linarith) i
  simpa using this

/-! ### Jacobi matrices -/

variable {d d' b : ℕ → ℝ}

lemma jacobi_sub_jacobi (N : ℕ) :
    jacobi d' b N - jacobi d b N = diagonal (fun k : Fin N => d' k - d k) := by
  ext i j
  rw [Matrix.sub_apply, jacobi_apply, jacobi_apply, diagonal_apply]
  by_cases h : i = j
  · subst h; simp
  · have h' : i.val ≠ j.val := fun e => h (Fin.ext e)
    simp only [h', h, ↓reduceIte, sub_self]

lemma quad_jacobi_sub (N : ℕ) (x : Fin N → ℝ) :
    x ⬝ᵥ (jacobi d' b N *ᵥ x) - x ⬝ᵥ (jacobi d b N *ᵥ x) = ∑ k : Fin N, (d' k - d k) * x k ^ 2 := by
  rw [← dotProduct_sub, ← sub_mulVec, jacobi_sub_jacobi, dotProduct]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [mulVec_diagonal]
  ring

/-- If `d'_k ≤ d_k + c` for `k < N`, then `λ_i(J(d')) ≤ λ_i(J(d)) + c`. -/
theorem jacobiEig_le_add (N : ℕ) (c : ℝ) (hd : ∀ k < N, d' k ≤ d k + c) (i : Fin N) :
    jacobiEig d' b N i ≤ jacobiEig d b N i + c := by
  unfold jacobiEig
  refine eigenvalues₀_le_add _ _ c (fun x => ?_) _
  have h := quad_jacobi_sub (d := d) (d' := d') (b := b) N x
  have hsum : ∑ k : Fin N, (d' k - d k) * x k ^ 2 ≤ c * (x ⬝ᵥ x) := by
    rw [dotProduct, Finset.mul_sum]
    refine Finset.sum_le_sum fun k _ => ?_
    have := hd k k.isLt
    nlinarith [sq_nonneg (x k)]
  linarith

/-- **Diagonal monotonicity.** If `d_k ≤ d'_k` for `k < N`, then `λ_i(J(d)) ≤ λ_i(J(d'))` for
every `i` (any off-diagonals). -/
theorem jacobiEig_mono (N : ℕ) (hd : ∀ k < N, d k ≤ d' k) (i : Fin N) :
    jacobiEig d b N i ≤ jacobiEig d' b N i := by
  have := jacobiEig_le_add (d := d') (d' := d) (b := b) N 0 (fun k hk => by simpa using hd k hk) i
  simpa using this

/-- **Exact diagonal shift.** -/
theorem jacobiEig_add_const (N : ℕ) (c : ℝ) (i : Fin N) :
    jacobiEig (fun k => d k + c) b N i = jacobiEig d b N i + c := by
  refine le_antisymm (jacobiEig_le_add N c (fun k _ => le_rfl) i) ?_
  have := jacobiEig_le_add (d := fun k => d k + c) (d' := d) (b := b) N (-c)
    (fun k _ => by simp) i
  linarith

/-- **Weyl perturbation bound for diagonal perturbations.** -/
theorem abs_jacobiEig_sub_le (N : ℕ) (ε : ℝ) (hd : ∀ k < N, |d' k - d k| ≤ ε) (i : Fin N) :
    |jacobiEig d' b N i - jacobiEig d b N i| ≤ ε := by
  have h1 := jacobiEig_le_add (d := d) (d' := d') (b := b) N ε
    (fun k hk => by have := (abs_le.mp (hd k hk)).2; linarith) i
  have h2 := jacobiEig_le_add (d := d') (d' := d) (b := b) N ε
    (fun k hk => by have := (abs_le.mp (hd k hk)).1; linarith) i
  rw [abs_le]
  constructor <;> linarith

/-- **Strict monotonicity for a perturbation that includes the first site.** If all off-diagonals
are nonzero, `d ≤ d'` and `d₀ < d'₀`, then every eigenvalue strictly increases. -/
theorem jacobiEig_lt_of_head_lt (n : ℕ) (hb : ∀ k < n, b k ≠ 0) (hd : ∀ k < n + 1, d k ≤ d' k)
    (h0 : d 0 < d' 0) (i : Fin (n + 1)) :
    jacobiEig d b (n + 1) i < jacobiEig d' b (n + 1) i := by
  unfold jacobiEig
  rw [eigenvalues₀_eq_isSymmetric, eigenvalues₀_eq_isSymmetric]
  refine eigenvalues_lt_of_inner_lt _ _ _ (fun v => ?_) (fun μ v hv0 hv => ?_) _
  · rw [inner_toEuclideanLin, inner_toEuclideanLin]
    have h := quad_jacobi_sub (d := d) (d' := d') (b := b) (n + 1) (WithLp.ofLp v)
    have hnn : 0 ≤ ∑ k : Fin (n + 1), (d' k - d k) * (WithLp.ofLp v) k ^ 2 :=
      Finset.sum_nonneg fun k _ => mul_nonneg (sub_nonneg.mpr (hd k k.isLt)) (sq_nonneg _)
    linarith
  · rw [inner_toEuclideanLin, inner_toEuclideanLin]
    set x := WithLp.ofLp v with hx
    have heig : jacobi d' b (n + 1) *ᵥ x = μ • x := by
      have := congrArg WithLp.ofLp hv
      simpa [toEuclideanLin, hx] using this
    have hx0 : x ≠ 0 := by
      intro h
      apply hv0
      have : v = WithLp.toLp 2 x := by simp [hx]
      rw [this, h]; rfl
    have hhead : x 0 ≠ 0 := fun h => hx0 (eigvec_eq_zero_of_head d' b n hb heig h)
    have h := quad_jacobi_sub (d := d) (d' := d') (b := b) (n + 1) x
    have hpos : 0 < ∑ k : Fin (n + 1), (d' k - d k) * x k ^ 2 := by
      refine Finset.sum_pos' (fun k _ => mul_nonneg (sub_nonneg.mpr (hd k k.isLt)) (sq_nonneg _))
        ⟨0, mem_univ _, ?_⟩
      exact mul_pos (sub_pos.mpr h0) (by positivity)
    linarith

end DiscreteSturm
