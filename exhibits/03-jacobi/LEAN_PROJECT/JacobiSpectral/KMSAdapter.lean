import JacobiSpectral.Chebyshev

/-!
# `JacobiSpectral.KMSAdapter` — the KMS tridiagonal layer as a specialization

The definitions below are **restated verbatim** (namespace changed) from the read-only KMS source
`KMS/Tridiag.lean` (R0008 copy; `ShiftedKMS.triDiag`, `cont`, `firstCorner`, `endMat`). The KMS
project is **not imported**. Each KMS theorem is then re-derived from the generic library:

| KMS (R0008)                        | here                          | generic input               |
|------------------------------------|-------------------------------|-----------------------------|
| `ShiftedKMS.det_triDiag_succ_succ` | `det_triDiag_succ_succ`       | `det_jacobi_top`            |
| `ShiftedKMS.det_triDiag_rev`       | `det_triDiag_rev`             | `det_jacobi_rev`            |
| `ShiftedKMS.det_leadBlock`         | `det_leadBlock`               | `det_jacobi`, `cont_congr`  |
| `ShiftedKMS.det_endMat`            | `det_endMat`                  | `det_jacobi_succ_succ`      |
| `ShiftedKMS.cont_cheb`             | `cont_cheb`                   | `cont_cheb_corner`          |
-/

open Matrix Polynomial

namespace JacobiSpectral.KMSAdapter

variable {R : Type*} [CommRing R]

/-- KMS `triDiag` (verbatim): diagonal `D`, constant off-diagonal `b`. -/
def triDiag {n : ℕ} (b : R) (D : Fin n → R) : Matrix (Fin n) (Fin n) R :=
  fun i j => if i = j then D i else if i.val + 1 = j.val ∨ j.val + 1 = i.val then b else 0

/-- KMS `cont` (verbatim): `P₀ = 1, P₁ = d, P_k = c P_{k-1} − b² P_{k-2}`. -/
def cont (b c d : R) : ℕ → R
  | 0 => 1
  | 1 => d
  | (k + 2) => c * cont b c d (k + 1) - b ^ 2 * cont b c d k

/-- KMS `firstCorner` (verbatim). -/
def firstCorner (k : ℕ) (d c : R) : Fin k → R := fun i => if i.val = 0 then d else c

/-- KMS `endMat` (verbatim). -/
def endMat (N : ℕ) (d₀ c d₁ : R) : Fin N → R :=
  fun i => if i.val = 0 then d₀ else if i.val + 1 = N then d₁ else c

/-- Extension of a `Fin n`-indexed diagonal to a sequence. -/
def ext {n : ℕ} (D : Fin n → R) : ℕ → R := fun i => if h : i < n then D ⟨i, h⟩ else 0

/-- **Adapter**: the KMS matrix is the generic Jacobi matrix with constant off-diagonal. -/
theorem triDiag_eq_jacobi {n : ℕ} (b : R) (D : Fin n → R) :
    triDiag b D = jacobi (ext D) (fun _ => b) n := by
  ext i j
  simp only [triDiag, jacobi_apply, ext, i.isLt, dite_true, Fin.eta]
  by_cases h : i = j
  · simp [h]
  · have hv : i.val ≠ j.val := fun hv => h (Fin.ext hv)
    simp only [h, hv, ↓reduceIte]
    split_ifs <;> first | rfl | omega

/-- **Adapter**: the KMS continuant is the generic continuant with first corner `d`. -/
theorem cont_eq (b c d : R) : ∀ k,
    cont b c d k = JacobiSpectral.cont (fun i => if i = 0 then d else c) (fun _ => b) k
  | 0 => rfl
  | 1 => rfl
  | (k + 2) => by
      rw [cont, JacobiSpectral.cont_succ_succ, cont_eq b c d (k + 1), cont_eq b c d k]
      simp

/-- Recovered `ShiftedKMS.det_triDiag_succ_succ`. -/
theorem det_triDiag_succ_succ {n : ℕ} (b : R) (D : Fin (n + 2) → R) :
    (triDiag b D).det =
      D 0 * (triDiag b (D ∘ Fin.succ)).det - b ^ 2 * (triDiag b (D ∘ Fin.succ ∘ Fin.succ)).det := by
  rw [triDiag_eq_jacobi, triDiag_eq_jacobi, triDiag_eq_jacobi, det_jacobi_top]
  have h0 : ext D 0 = D 0 := by simp [ext]
  rw [h0]
  congr 3
  · exact jacobi_congr (fun i hi => by simp [ext, hi, show i + 1 < n + 2 by omega]) (fun _ _ => rfl)
  · exact jacobi_congr (fun i hi => by simp [ext, hi, show i + 2 < n + 2 by omega]) (fun _ _ => rfl)

/-- Recovered `ShiftedKMS.det_triDiag_rev`. -/
theorem det_triDiag_rev {n : ℕ} (b : R) (D : Fin n → R) :
    (triDiag b (D ∘ Fin.rev)).det = (triDiag b D).det := by
  rw [triDiag_eq_jacobi, triDiag_eq_jacobi, det_jacobi_rev (ext D)]
  congr 1
  refine jacobi_congr (fun i hi => ?_) (fun _ _ => rfl)
  simp only [ext, Function.comp, hi, dite_true, show n - 1 - i < n by omega]
  congr 1; ext; simp only [Fin.val_rev]; omega

/-- Recovered `ShiftedKMS.det_leadBlock` (manuscript `P_k`). -/
theorem det_leadBlock (b c d : R) (k : ℕ) :
    (triDiag b (firstCorner k d c)).det = cont b c d k := by
  rw [triDiag_eq_jacobi, det_jacobi, cont_eq]
  exact cont_congr k (fun i hi => by simp [ext, firstCorner, hi]) (fun _ _ => rfl)

/-- Recovered `ShiftedKMS.det_endMat`. -/
theorem det_endMat {N : ℕ} (hN : 2 ≤ N) (b d₀ c d₁ : R) :
    (triDiag b (endMat N d₀ c d₁)).det =
      d₁ * cont b c d₀ (N - 1) - b ^ 2 * cont b c d₀ (N - 2) := by
  obtain ⟨m, rfl⟩ : ∃ m, N = m + 2 := ⟨N - 2, by omega⟩
  rw [triDiag_eq_jacobi, det_jacobi, cont_succ_succ, cont_eq, cont_eq,
    show m + 2 - 1 = m + 1 by omega, show m + 2 - 2 = m by omega]
  have hlast : ext (endMat (m + 2) d₀ c d₁) (m + 1) = d₁ := by
    simp [ext, endMat]
  rw [hlast]
  congr 2
  · exact cont_congr _ (fun i hi => by
      simp only [ext, endMat, show i < m + 2 by omega, dite_true]
      split_ifs <;> first | rfl | omega) (fun _ _ => rfl)
  · exact cont_congr _ (fun i hi => by
      simp only [ext, endMat, show i < m + 2 by omega, dite_true]
      split_ifs <;> first | rfl | omega) (fun _ _ => rfl)

/-- Recovered `ShiftedKMS.cont_cheb`. -/
theorem cont_cheb (a b x : ℝ) (k : ℕ) :
    cont b (2 * b * x) (b * (2 * x + a)) k =
      b ^ k * ((Chebyshev.U ℝ (k : ℤ)).eval x + a * (Chebyshev.U ℝ ((k : ℤ) - 1)).eval x) := by
  rw [cont_eq, ← cont_cheb_corner]

end JacobiSpectral.KMSAdapter
