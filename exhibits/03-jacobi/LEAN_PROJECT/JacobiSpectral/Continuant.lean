import JacobiSpectral.Basic
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.LinearAlgebra.Matrix.Notation

/-!
# `JacobiSpectral.Continuant` — continuant recurrences for Jacobi determinants and charpolys

* `cont d b n` (scalar continuant): `1, d₀, d_{k+1} cont_{k+1} − b_k² cont_k`;
  `det_jacobi : (jacobi d b n).det = cont d b n`.
* `jpoly d b n` (polynomial continuant): `1, X − d₀, (X − d_{k+1}) p_{k+1} − b_k² p_k`;
  `charpoly_jacobi : (jacobi d b n).charpoly = jpoly d b n` — the characteristic polynomials of
  all leading principal blocks obey one three-term recurrence.
* Transfer-matrix form `transfer_vec`.
* Exact small-size checks for `n = 1, 2, 3` computed independently with `det_fin_two/three`.
-/

open Matrix Polynomial

namespace JacobiSpectral

variable {R : Type*} [CommRing R]

/-- Scalar continuant. -/
def cont (d b : ℕ → R) : ℕ → R
  | 0 => 1
  | 1 => d 0
  | (n + 2) => d (n + 1) * cont d b (n + 1) - b n ^ 2 * cont d b n

@[simp] lemma cont_zero (d b : ℕ → R) : cont d b 0 = 1 := rfl
@[simp] lemma cont_one (d b : ℕ → R) : cont d b 1 = d 0 := rfl
lemma cont_succ_succ (d b : ℕ → R) (n : ℕ) :
    cont d b (n + 2) = d (n + 1) * cont d b (n + 1) - b n ^ 2 * cont d b n := rfl

/-- **Continuant theorem for determinants.** -/
theorem det_jacobi (d b : ℕ → R) : ∀ n, (jacobi d b n).det = cont d b n
  | 0 => by simp
  | 1 => by
      rw [det_unique]
      simp [jacobi_apply]
  | (n + 2) => by
      rw [det_jacobi_succ_succ, det_jacobi d b (n + 1), det_jacobi d b n, cont_succ_succ]

/-- Polynomial continuant: the characteristic polynomials of the leading blocks. -/
noncomputable def jpoly (d b : ℕ → R) : ℕ → R[X]
  | 0 => 1
  | 1 => X - C (d 0)
  | (n + 2) => (X - C (d (n + 1))) * jpoly d b (n + 1) - C (b n ^ 2) * jpoly d b n

@[simp] lemma jpoly_zero (d b : ℕ → R) : jpoly d b 0 = 1 := rfl
@[simp] lemma jpoly_one (d b : ℕ → R) : jpoly d b 1 = X - C (d 0) := rfl
lemma jpoly_succ_succ (d b : ℕ → R) (n : ℕ) :
    jpoly d b (n + 2) = (X - C (d (n + 1))) * jpoly d b (n + 1) - C (b n ^ 2) * jpoly d b n := rfl

lemma jpoly_two (d b : ℕ → R) :
    jpoly d b 2 = (X - C (d 1)) * (X - C (d 0)) - C (b 0 ^ 2) := by
  rw [show (2 : ℕ) = 0 + 2 from rfl, jpoly_succ_succ]; simp

lemma jpoly_three (d b : ℕ → R) :
    jpoly d b 3 = (X - C (d 2)) * ((X - C (d 1)) * (X - C (d 0)) - C (b 0 ^ 2)) -
      C (b 1 ^ 2) * (X - C (d 0)) := by
  rw [show (3 : ℕ) = 1 + 2 from rfl, jpoly_succ_succ, jpoly_two]; rfl

/-- The characteristic matrix of a Jacobi matrix is a Jacobi matrix over `R[X]`. -/
theorem charmatrix_jacobi (d b : ℕ → R) (n : ℕ) :
    (jacobi d b n).charmatrix = jacobi (fun i => X - C (d i)) (fun i => -C (b i)) n := by
  ext i j
  rw [charmatrix_apply, jacobi_apply, jacobi_apply]
  by_cases hij : i = j
  · subst hij; simp
  · have hv : i.val ≠ j.val := fun h => hij (Fin.ext h)
    rw [diagonal_apply_ne _ hij, zero_sub]
    simp only [hv, ↓reduceIte]
    split_ifs <;> simp

lemma jpoly_eq_cont (d b : ℕ → R) : ∀ n,
    jpoly d b n = cont (fun i => X - C (d i)) (fun i => -C (b i)) n
  | 0 => rfl
  | 1 => rfl
  | (n + 2) => by
      rw [jpoly_succ_succ, cont_succ_succ, ← jpoly_eq_cont d b (n + 1), ← jpoly_eq_cont d b n]
      simp [C_pow]

/-- **Continuant theorem for characteristic polynomials of leading principal blocks.** -/
theorem charpoly_jacobi (d b : ℕ → R) (n : ℕ) : (jacobi d b n).charpoly = jpoly d b n := by
  rw [charpoly, charmatrix_jacobi, det_jacobi, jpoly_eq_cont]

theorem jpoly_monic (d b : ℕ → R) (n : ℕ) : (jpoly d b n).Monic := by
  rw [← charpoly_jacobi]; exact charpoly_monic _

theorem natDegree_jpoly [Nontrivial R] (d b : ℕ → R) (n : ℕ) : (jpoly d b n).natDegree = n := by
  rw [← charpoly_jacobi, charpoly_natDegree_eq_dim, Fintype.card_fin]

/-- Evaluation of the polynomial continuant is the determinant of `x − J_n`. -/
theorem eval_jpoly (d b : ℕ → R) (n : ℕ) (x : R) :
    (jpoly d b n).eval x = (scalar (Fin n) x - jacobi d b n).det := by
  rw [← charpoly_jacobi, eval_charpoly]

/-! ### Transfer-matrix formulation -/

/-- One-step transfer matrix `T_k = [[X − d_{k+1}, −b_k²], [1, 0]]`. -/
noncomputable def transfer (d b : ℕ → R) (k : ℕ) : Matrix (Fin 2) (Fin 2) R[X] :=
  !![X - C (d (k + 1)), -C (b k ^ 2); 1, 0]

/-- Ordered transfer products `T_{n-1} ⋯ T_0`. -/
noncomputable def transferProd (d b : ℕ → R) : ℕ → Matrix (Fin 2) (Fin 2) R[X]
  | 0 => 1
  | (n + 1) => transfer d b n * transferProd d b n

/-- **Transfer-matrix form of the recurrence**:
`(p_{n+1}, p_n) = T_{n-1} ⋯ T_0 · (X − d₀, 1)`. -/
theorem transfer_vec (d b : ℕ → R) : ∀ n,
    ![jpoly d b (n + 1), jpoly d b n] = transferProd d b n *ᵥ ![X - C (d 0), 1]
  | 0 => by simp [transferProd]
  | (n + 1) => by
      rw [transferProd, ← mulVec_mulVec, ← transfer_vec d b n]
      ext i; fin_cases i <;> simp [transfer, mulVec, dotProduct, Fin.sum_univ_two, jpoly_succ_succ]
      ring

/-! ### Exact small-size checks (independent of the recurrence) -/

example (d b : ℕ → R) : (jacobi d b 1).det = d 0 := by
  rw [det_unique]; simp [jacobi_apply]

example (d b : ℕ → R) : (jacobi d b 2).det = d 0 * d 1 - b 0 ^ 2 := by
  rw [det_fin_two]; simp [jacobi_apply]; ring

example (d b : ℕ → R) :
    (jacobi d b 3).det = d 0 * d 1 * d 2 - d 0 * b 1 ^ 2 - d 2 * b 0 ^ 2 := by
  rw [det_fin_three]; simp [jacobi_apply]; ring

example (d b : ℕ → R) :
    (jacobi d b 3).charpoly =
      (X - C (d 2)) * ((X - C (d 1)) * (X - C (d 0)) - C (b 0 ^ 2)) - C (b 1 ^ 2) * (X - C (d 0)) := by
  rw [charpoly_jacobi, jpoly_three]

end JacobiSpectral
