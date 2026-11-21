import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.Symmetric
import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.Basic.Real.Star

/-!
# `JacobiSpectral.Basic` — finite Jacobi matrices from coefficient sequences

A finite Jacobi matrix of size `n` is built from a diagonal sequence `d : ℕ → R` and an
off-diagonal sequence `b : ℕ → R`:

```
        ⎡ d₀  b₀                 ⎤
        ⎢ b₀  d₁  b₁             ⎥
J_n  =  ⎢     b₁  d₂  ⋱          ⎥
        ⎢          ⋱   ⋱  b_{n-2} ⎥
        ⎣             b_{n-2} d_{n-1} ⎦
```

Indexing by sequences makes every leading principal block a Jacobi matrix *of the same
sequences* (`jacobi_leading`), which is what the continuant recurrence and the interlacing
theorem are about.

* `det_jacobi_succ_succ`: `det J_{n+2} = d_{n+1} det J_{n+1} − b_n² det J_n`
  (expansion along the last row).
-/

open Matrix

namespace JacobiSpectral

variable {R : Type*} [CommRing R]

/-- The `n × n` Jacobi matrix with diagonal `d` and (symmetric) off-diagonal `b`. -/
def jacobi (d b : ℕ → R) (n : ℕ) : Matrix (Fin n) (Fin n) R :=
  Matrix.of fun i j =>
    if i.val = j.val then d i.val
    else if i.val + 1 = j.val then b i.val
    else if j.val + 1 = i.val then b j.val
    else 0

lemma jacobi_apply (d b : ℕ → R) (n : ℕ) (i j : Fin n) :
    jacobi d b n i j =
      if i.val = j.val then d i.val
      else if i.val + 1 = j.val then b i.val
      else if j.val + 1 = i.val then b j.val
      else 0 := rfl

lemma jacobi_apply_eq_zero (d b : ℕ → R) {n : ℕ} {i j : Fin n} (h1 : i.val + 1 < j.val ∨ j.val + 1 < i.val) :
    jacobi d b n i j = 0 := by
  rw [jacobi_apply]
  split_ifs <;> first | rfl | omega

/-- Jacobi matrices are symmetric. -/
theorem jacobi_isSymm (d b : ℕ → R) (n : ℕ) : (jacobi d b n).IsSymm := by
  ext i j
  simp only [transpose_apply, jacobi_apply]
  split_ifs <;> first | rfl | omega | congr 1

/-- Real Jacobi matrices are Hermitian. -/
theorem jacobi_isHermitian (d b : ℕ → ℝ) (n : ℕ) : (jacobi d b n).IsHermitian := by
  rw [IsHermitian, conjTranspose_eq_transpose_of_trivial]
  exact jacobi_isSymm d b n

/-- **Leading principal blocks**: deleting the last row and column of `J_{n+1}` gives `J_n`. -/
theorem jacobi_leading (d b : ℕ → R) (n : ℕ) :
    (jacobi d b (n + 1)).submatrix Fin.castSucc Fin.castSucc = jacobi d b n := by
  ext i j
  simp only [submatrix_apply, jacobi_apply, Fin.val_castSucc]

/-- Map of a Jacobi matrix under a ring hom. -/
theorem jacobi_map {S : Type*} [CommRing S] (f : R →+* S) (d b : ℕ → R) (n : ℕ) :
    (jacobi d b n).map f = jacobi (f ∘ d) (f ∘ b) n := by
  ext i j
  simp only [map_apply, jacobi_apply, Function.comp]
  split_ifs <;> simp

@[simp] lemma jacobi_zero (d b : ℕ → R) : jacobi d b 0 = (Matrix.of fun i _ => i.elim0) := by
  ext i; exact i.elim0

section Recurrence

private lemma sa_castSucc {n : ℕ} (k : Fin n) :
    (Fin.castSucc (Fin.last n) : Fin (n + 2)).succAbove k.castSucc = k.castSucc.castSucc :=
  Fin.succAbove_castSucc_of_lt _ _ (Fin.castSucc_lt_last k)

private lemma sa_last {n : ℕ} :
    (Fin.castSucc (Fin.last n) : Fin (n + 2)).succAbove (Fin.last n) = Fin.last (n + 1) := by
  rw [Fin.succAbove_of_le_castSucc _ _ le_rfl]; rfl

/-- **Three-term determinant recurrence** (last-row expansion):
`det J_{n+2} = d_{n+1} · det J_{n+1} − b_n² · det J_n`. -/
theorem det_jacobi_succ_succ (d b : ℕ → R) (n : ℕ) :
    (jacobi d b (n + 2)).det =
      d (n + 1) * (jacobi d b (n + 1)).det - b n ^ 2 * (jacobi d b n).det := by
  set A := jacobi d b (n + 2) with hA
  rw [det_succ_row A (Fin.last (n + 1)), Fin.sum_univ_castSucc, Fin.sum_univ_castSucc]
  -- columns `0, …, n-1` of the last row vanish
  have hz : ∑ k : Fin n, (-1 : R) ^ ((Fin.last (n + 1) : ℕ) + (k.castSucc.castSucc : ℕ)) *
      A (Fin.last (n + 1)) k.castSucc.castSucc *
      (A.submatrix (Fin.last (n + 1)).succAbove k.castSucc.castSucc.succAbove).det = 0 := by
    refine Finset.sum_eq_zero fun k _ => ?_
    rw [hA, jacobi_apply_eq_zero d b (by simp only [Fin.val_last, Fin.val_castSucc]; omega)]
    ring
  rw [hz, zero_add]
  -- the diagonal corner
  have hdiag : A.submatrix (Fin.last (n + 1)).succAbove (Fin.last (n + 1)).succAbove =
      jacobi d b (n + 1) := by
    rw [Fin.succAbove_last, hA, jacobi_leading]
  have hAd : A (Fin.last (n + 1)) (Fin.last (n + 1)) = d (n + 1) := by
    simp only [hA, jacobi_apply, Fin.val_last, ↓reduceIte]
  have hAb : A (Fin.last (n + 1)) (Fin.castSucc (Fin.last n)) = b n := by
    simp only [hA, jacobi_apply, Fin.val_last, Fin.val_castSucc]
    split_ifs <;> first | rfl | omega
  -- the off-diagonal minor: expand along its last column
  set M := A.submatrix (Fin.last (n + 1)).succAbove (Fin.castSucc (Fin.last n)).succAbove with hM
  have hMdet : M.det = b n * (jacobi d b n).det := by
    rw [det_succ_column M (Fin.last n), Fin.sum_univ_castSucc]
    have hz2 : ∑ k : Fin n, (-1 : R) ^ ((k.castSucc : ℕ) + (Fin.last n : ℕ)) * M k.castSucc (Fin.last n) *
        (M.submatrix k.castSucc.succAbove (Fin.last n).succAbove).det = 0 := by
      refine Finset.sum_eq_zero fun k _ => ?_
      have : M k.castSucc (Fin.last n) = 0 := by
        simp only [hM, submatrix_apply, Fin.succAbove_last, sa_last, hA]
        exact jacobi_apply_eq_zero d b (by simp only [Fin.val_last, Fin.val_castSucc]; omega)
      rw [this]; ring
    rw [hz2, zero_add]
    have hMb : M (Fin.last n) (Fin.last n) = b n := by
      simp only [hM, submatrix_apply, Fin.succAbove_last, sa_last, hA, jacobi_apply, Fin.val_last,
        Fin.val_castSucc]
      split_ifs <;> first | rfl | omega
    have hMs : M.submatrix (Fin.last n).succAbove (Fin.last n).succAbove = jacobi d b n := by
      ext i j
      simp only [hM, submatrix_apply, Fin.succAbove_last, sa_castSucc, hA, jacobi_apply,
        Fin.val_castSucc]
    rw [hMb, hMs, Fin.val_last]
    rw [← two_mul, pow_mul]; norm_num
  rw [hAd, hAb, hdiag, hMdet, Fin.val_last, Fin.val_castSucc, Fin.val_last]
  have e1 : ((-1 : R) ^ (n + 1 + (n + 1))) = 1 := by rw [← two_mul, pow_mul]; norm_num
  have e2 : ((-1 : R) ^ (n + 1 + n)) = -1 := by
    rw [show n + 1 + n = 2 * n + 1 by ring, pow_succ, pow_mul]; norm_num
  rw [e1, e2]
  ring

end Recurrence

/-! ### Congruence, reversal and the top-corner expansion -/

/-- `J_n` only sees `d₀, …, d_{n-1}` and `b₀, …, b_{n-2}`. -/
theorem jacobi_congr {d d' b b' : ℕ → R} {n : ℕ} (hd : ∀ i < n, d i = d' i)
    (hb : ∀ i, i + 1 < n → b i = b' i) : jacobi d b n = jacobi d' b' n := by
  ext i j
  simp only [jacobi_apply]
  split_ifs with h1 h2 h3
  · exact hd _ i.isLt
  · exact hb _ (by omega)
  · exact hb _ (by omega)
  · rfl

/-- **Reversal**: flipping both indices gives the Jacobi matrix of the reversed sequences. -/
theorem jacobi_rev (d b : ℕ → R) (n : ℕ) :
    (jacobi d b n).submatrix Fin.rev Fin.rev =
      jacobi (fun i => d (n - 1 - i)) (fun i => b (n - 2 - i)) n := by
  ext i j
  simp only [submatrix_apply, jacobi_apply, Fin.val_rev]
  have hi := i.isLt
  have hj := j.isLt
  split_ifs <;> first | rfl | omega | (congr 1; omega)

theorem det_jacobi_rev (d b : ℕ → R) (n : ℕ) :
    (jacobi d b n).det = (jacobi (fun i => d (n - 1 - i)) (fun i => b (n - 2 - i)) n).det := by
  rw [← jacobi_rev, show (Fin.rev : Fin n → Fin n) = Fin.revPerm from rfl,
    det_submatrix_equiv_self]

/-- **Top-corner expansion**: `det J_{n+2}(d,b) = d₀ det J_{n+1}(d∘(·+1), b∘(·+1)) −
b₀² det J_n(d∘(·+2), b∘(·+2))`. -/
theorem det_jacobi_top (d b : ℕ → R) (n : ℕ) :
    (jacobi d b (n + 2)).det =
      d 0 * (jacobi (fun i => d (i + 1)) (fun i => b (i + 1)) (n + 1)).det -
        b 0 ^ 2 * (jacobi (fun i => d (i + 2)) (fun i => b (i + 2)) n).det := by
  rw [det_jacobi_rev, det_jacobi_succ_succ, det_jacobi_rev _ _ (n + 1), det_jacobi_rev _ _ n]
  have e0 : n + 2 - 1 - (n + 1) = 0 := by omega
  have e1 : n + 2 - 2 - n = 0 := by omega
  rw [e0, e1]
  congr 3
  · exact jacobi_congr (fun i hi => by congr 1; omega) (fun i hi => by congr 1; omega)
  · exact jacobi_congr (fun i hi => by congr 1; omega) (fun i hi => by congr 1; omega)

end JacobiSpectral
