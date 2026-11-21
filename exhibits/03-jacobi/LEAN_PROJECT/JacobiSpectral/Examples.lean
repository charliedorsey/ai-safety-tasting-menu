import JacobiSpectral.Norms
import JacobiSpectral.KMSAdapter

/-!
# `JacobiSpectral.Examples` — worked cases and falsifiers

* `n = 1`: `jacobiEig d b 1 0 = d₀`.
* `n = 2`: strict interlacing says the two eigenvalues of a `2 × 2` Jacobi matrix strictly straddle
  `d₀` whenever `b₀ ≠ 0`.
* `n = 3`: the Dirichlet chain `d ≡ 0`, `b ≡ 1` has eigenvalues `√2, 0, −√2`.
* nonconstant: `d = (0, 1, 2)`, `b = (1, 1)` has characteristic polynomial `X³ − 3X² + 2` and
  eigenvalues `1 + √3, 1, 1 − √3`.
* **falsifiers** (`b_k = 0`): repeated eigenvalues, a two-dimensional eigenspace, failure of strict
  interlacing; and a single vanishing *interior* off-diagonal already produces a double root.
-/

open Polynomial Matrix Finset

namespace JacobiSpectral.Examples

open JacobiSpectral

lemma isRootVec_one (d b : ℕ → ℝ) : IsRootVec (jpoly d b 1) (fun _ : Fin 1 => d 0) := by
  refine ⟨fun i j h => absurd h (by rw [Subsingleton.elim i j]; exact lt_irrefl _), ?_⟩
  rw [Fin.prod_univ_one]; rfl

/-! ### `n = 1` -/

example (d b : ℕ → ℝ) : jacobiEig d b 1 0 = d 0 := by
  rw [jacobiEig_eq_of_isRootVec (isRootVec_one d b)]

/-! ### `n = 2`: the two eigenvalues straddle `d₀` -/

example (d b : ℕ → ℝ) (hb : b 0 ≠ 0) :
    jacobiEig d b 2 1 < d 0 ∧ d 0 < jacobiEig d b 2 0 := by
  have h1 : jacobiEig d b 1 0 = d 0 := by rw [jacobiEig_eq_of_isRootVec (isRootVec_one d b)]
  have := jacobiEig_interlace d b 1 (fun k hk => by rw [show k = 0 by omega]; exact hb) 0
  rw [h1] at this
  exact this

/-! ### `n = 3`: Dirichlet chain `d ≡ 0`, `b ≡ 1` -/

example : jacobiEig (fun _ => 0) (fun _ => 1) 3 0 = Real.sqrt 2 := by
  rw [jacobiEig_const 0 1 one_pos 3]
  norm_num
  ring

example : jacobiEig (fun _ => 0) (fun _ => 1) 3 1 = 0 := by
  rw [jacobiEig_const 0 1 one_pos 3]
  norm_num
  rw [show 2 * Real.pi / 4 = Real.pi / 2 by ring, Real.cos_pi_div_two]

example : jacobiEig (fun _ => 0) (fun _ => 1) 3 2 = -Real.sqrt 2 := by
  rw [jacobiEig_const 0 1 one_pos 3]
  norm_num
  rw [show 3 * Real.pi / 4 = Real.pi - Real.pi / 4 by ring, Real.cos_pi_sub, Real.cos_pi_div_four]
  ring

/-! ### A nonconstant Jacobi matrix -/

/-- `d = (0, 1, 2, …)`, `b ≡ 1`. -/
def dNat : ℕ → ℝ := fun i => i

example : (jacobi dNat (fun _ => 1) 3).charpoly = X ^ 3 - 3 * X ^ 2 + 2 := by
  rw [charpoly_jacobi, jpoly_three]
  simp only [dNat]
  norm_num
  simp only [map_ofNat]
  ring

theorem nonconst_rootVec :
    IsRootVec (jpoly dNat (fun _ => 1) 3) ![1 - Real.sqrt 3, 1, 1 + Real.sqrt 3] := by
  have hs : 0 < Real.sqrt 3 := Real.sqrt_pos.2 (by norm_num)
  refine ⟨?_, ?_⟩
  · refine Fin.strictMono_iff_lt_succ.2 fun i => ?_
    fin_cases i <;> simp
  · rw [jpoly_three, Fin.prod_univ_three]
    simp only [dNat, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons]
    have h3 : (C (Real.sqrt 3)) ^ 2 = (3 : ℝ[X]) := by
      rw [← C_pow, Real.sq_sqrt (by norm_num)]; rfl
    simp only [map_sub, map_add, map_one, Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero, map_zero,
      one_pow, map_ofNat]
    linear_combination (X - 1) * h3

example : jacobiEig dNat (fun _ => 1) 3 0 = 1 + Real.sqrt 3 ∧
    jacobiEig dNat (fun _ => 1) 3 1 = 1 ∧
    jacobiEig dNat (fun _ => 1) 3 2 = 1 - Real.sqrt 3 := by
  refine ⟨?_, ?_, ?_⟩ <;> rw [jacobiEig_eq_of_isRootVec nonconst_rootVec] <;> rfl

/-- Strict interlacing for this example, from the general theorem: the eigenvalues
`(1 ± √5)/2` of the leading `2 × 2` block sit strictly between `1 − √3 < 1 < 1 + √3`. -/
example (i : Fin 2) :
    jacobiEig dNat (fun _ => 1) 3 i.succ < jacobiEig dNat (fun _ => 1) 2 i ∧
      jacobiEig dNat (fun _ => 1) 2 i < jacobiEig dNat (fun _ => 1) 3 i.castSucc :=
  jacobiEig_interlace dNat (fun _ => 1) 2 (fun _ _ => one_ne_zero) i

/-! ### Falsifiers: a vanishing off-diagonal -/

/-- With `b ≡ 0` and constant diagonal, `J₂ = c I`: the charpoly `(X − c)²` has a double root. -/
example (c : ℝ) : ¬ (jacobi (fun _ => c) (fun _ => 0) 2).charpoly.roots.Nodup := by
  rw [charpoly_jacobi, jpoly_two]
  simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, map_zero, sub_zero]
  rw [roots_mul (mul_ne_zero (X_sub_C_ne_zero c) (X_sub_C_ne_zero c)), roots_X_sub_C]
  simp

/-- …its `c`-eigenspace is the whole plane: dimension `2`, not `1`. -/
example (c : ℝ) :
    Module.finrank ℝ (Module.End.eigenspace (toLin' (jacobi (fun _ => c) (fun _ => 0) 2)) c) = 2 := by
  have hJ : jacobi (fun _ => c) (fun _ => (0 : ℝ)) 2 = c • (1 : Matrix (Fin 2) (Fin 2) ℝ) := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [jacobi_apply]
  have htop : Module.End.eigenspace (toLin' (jacobi (fun _ => c) (fun _ => 0) 2)) c = ⊤ := by
    rw [eq_top_iff]
    intro x _
    rw [Module.End.mem_eigenspace_iff, toLin'_apply, hJ, smul_mulVec, one_mulVec]
  rw [htop, finrank_top, Module.finrank_fin_fun]

/-- …and strict interlacing fails: `λ₁(J₂) < λ₀(J₁)` is false (both equal `c`). -/
example (c : ℝ) :
    ¬ (jacobiEig (fun _ => c) (fun _ => 0) 2 1 < jacobiEig (fun _ => c) (fun _ => 0) 1 0) := by
  have hA := jacobi_isHermitian (fun _ => c) (fun _ => (0 : ℝ)) 2
  have hroots : (jacobi (fun _ => c) (fun _ => (0 : ℝ)) 2).charpoly.roots = c ::ₘ {c} := by
    rw [charpoly_jacobi, jpoly_two]
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, map_zero, sub_zero]
    rw [roots_mul (mul_ne_zero (X_sub_C_ne_zero c) (X_sub_C_ne_zero c)), roots_X_sub_C]
    rfl
  have h2 : jacobiEig (fun _ => c) (fun _ => (0 : ℝ)) 2 1 = c := by
    have hmem : (RCLike.ofReal (K := ℝ) ∘ hA.eigenvalues₀) (Fin.cast (Fintype.card_fin 2).symm 1) ∈
        Multiset.map (RCLike.ofReal (K := ℝ) ∘ hA.eigenvalues₀) univ.val :=
      Multiset.mem_map_of_mem _ (mem_univ_val _)
    rw [← hA.roots_charpoly_eq_eigenvalues₀, hroots] at hmem
    simp only [Multiset.mem_cons, Multiset.mem_singleton, or_self] at hmem
    exact hmem
  rw [h2, jacobiEig_eq_of_isRootVec (isRootVec_one _ _)]
  exact lt_irrefl c

/-- A single vanishing **interior** off-diagonal already breaks simplicity:
`d = (0, 0, 1)`, `b = (1, 0)` gives `p₃ = (X − 1)²(X + 1)`. -/
example : ¬ (jacobi (fun i => if i = 2 then (1 : ℝ) else 0) (fun i => if i = 0 then (1 : ℝ) else 0) 3
    |>.charpoly.roots.Nodup) := by
  have h : (jacobi (fun i => if i = 2 then (1 : ℝ) else 0) (fun i => if i = 0 then (1 : ℝ) else 0) 3).charpoly
      = (X - C 1) * ((X - C 1) * (X - C (-1))) := by
    rw [charpoly_jacobi, jpoly_three]
    simp only [show (2 : ℕ) ≠ 0 by norm_num, show (1 : ℕ) ≠ 2 by norm_num,
      show (0 : ℕ) ≠ 2 by norm_num, show (1 : ℕ) ≠ 0 by norm_num, ↓reduceIte, map_one, map_zero,
      map_neg, sub_zero, one_pow, ne_eq, not_false_eq_true, zero_pow, zero_mul]
    ring
  rw [h, roots_mul (mul_ne_zero (X_sub_C_ne_zero _) (mul_ne_zero (X_sub_C_ne_zero _)
    (X_sub_C_ne_zero _))), roots_mul (mul_ne_zero (X_sub_C_ne_zero _) (X_sub_C_ne_zero _))]
  simp only [roots_X_sub_C]
  simp

end JacobiSpectral.Examples
