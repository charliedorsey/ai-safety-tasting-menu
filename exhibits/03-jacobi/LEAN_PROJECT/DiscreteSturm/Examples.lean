/-
Copyright (c) 2026 Charlie Dorsey. Released under Apache 2.0 license.
-/
import DiscreteSturm.Perturbation
import JacobiSpectral.Norms

/-!
# Consumers, worked examples and falsifiers

**Consumers.**
* `sineMode_signVariations`: the `j`-th standing wave of the discrete Dirichlet chain,
  `k ↦ sin((k+1)(j+1)π/(n+2))` for `k = 0, …, n`, has exactly `j` sign changes. This is derived from
  the oscillation theorem; no trigonometric sign analysis is used.
* `card_Ioc_eq_sturm`: bisection. The number of eigenvalues in `(a, c]` is
  `sturmCount a − sturmCount c`.

**Falsifiers.**
* `interior_perturbation_not_strict`: raising an interior diagonal entry can leave an eigenvalue
  unchanged (`d = 0 → d = (0,1,0)`, `b ≡ 1`: the middle eigenvalue stays `0`). So the head
  hypothesis of `jacobiEig_lt_of_head_lt` cannot be dropped.
* `nodal_fails_of_b_zero`: with `b ≡ 0`, an eigenvector of the 2nd eigenvalue has no sign change.
* `sturm_fails_of_b_zero`: with `b = (0, 1)`, the Sturm count at `0` is `0`, but `1` is an
  eigenvalue.
-/

open Matrix Finset JacobiSpectral Polynomial

namespace DiscreteSturm

/-! ### Consumer 1: standing waves of the discrete Dirichlet chain -/

/-- The angle `θ_j = (j+1)π/(n+2)` of the `j`-th standing wave on `n+1` sites. -/
noncomputable def theta (n j : ℕ) : ℝ := ((j : ℝ) + 1) * Real.pi / (((n + 1 : ℕ) : ℝ) + 1)

/-- The `j`-th standing wave `k ↦ sin((k+1) θ_j)`. -/
noncomputable def sineMode (n j : ℕ) : Fin (n + 1) → ℝ :=
  fun k => Real.sin (((k : ℕ) + 1 : ℝ) * theta n j)

lemma extN_sineMode (n j : ℕ) (m : ℕ) (hm : m ≤ n + 1) :
    extN (sineMode n j) m = Real.sin (((m : ℝ) + 1) * theta n j) := by
  by_cases h : m < n + 1
  · simp [extN, h, sineMode]
  · have hm' : m = n + 1 := by omega
    simp only [extN, h, ↓reduceDIte]
    subst hm'
    have : (((n + 1 : ℕ) : ℝ) + 1) * theta n j = ((j + 1 : ℕ) : ℝ) * Real.pi := by
      unfold theta
      have hpos : (((n + 1 : ℕ) : ℝ) + 1) ≠ 0 := by positivity
      field_simp
      push_cast; ring
    rw [this, Real.sin_nat_mul_pi]

/-- The standing waves are eigenvectors of the constant chain. -/
theorem sineMode_eigvec (c β : ℝ) (n j : ℕ) :
    jacobi (fun _ => c) (fun _ => β) (n + 1) *ᵥ sineMode n j =
      (c + 2 * β * Real.cos (theta n j)) • sineMode n j := by
  funext k
  rw [jacobi_mulVec_extN, Pi.smul_apply, smul_eq_mul]
  have hk := k.isLt
  set θ := theta n j
  rw [extN_sineMode n j k (by omega), extN_sineMode n j (k + 1) (by omega)]
  have hs : sineMode n j k = Real.sin (((k : ℕ) + 1 : ℝ) * θ) := rfl
  rw [hs]
  set a := (((k : ℕ) : ℝ) + 1) * θ
  have hplus : (((k.val + 1 : ℕ) : ℝ) + 1) * θ = a + θ := by push_cast; ring
  rw [hplus]
  by_cases h0 : 0 < k.val
  · rw [ite_eq_left h0, extN_sineMode n j (k.val - 1) (by omega)]
    have hminus : (((k.val - 1 : ℕ) : ℝ) + 1) * θ = a - θ := by
      rw [Nat.cast_sub (by omega)]; push_cast; ring
    rw [hminus, Real.sin_add, Real.sin_sub]
    ring
  · rw [ite_eq_right h0]
    have hk0 : (k : ℕ) = 0 := by omega
    have ha : a = θ := by simp [a, hk0]
    rw [ha, Real.sin_add]
    ring

lemma theta_mem (n j : ℕ) (hj : j < n + 1) : 0 < theta n j ∧ theta n j < Real.pi := by
  have hpos : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) + 1 := by positivity
  have hjn : (j : ℝ) + 1 < ((n + 1 : ℕ) : ℝ) + 1 := by
    have : (j : ℝ) < ((n + 1 : ℕ) : ℝ) := by exact_mod_cast hj
    linarith
  unfold theta
  constructor
  · positivity
  · rw [div_lt_iff₀ hpos]
    nlinarith [Real.pi_pos]

/-- **Standing waves have the right number of nodes.** On `n+1` sites, the `j`-th standing wave
`k ↦ sin((k+1)(j+1)π/(n+2))` has exactly `j` sign changes. -/
theorem sineMode_signVariations (n : ℕ) (j : Fin (n + 1)) :
    (List.ofFn (sineMode n j)).signVariations = j.val := by
  have heig := sineMode_eigvec 0 1 n j
  have hconst : jacobiEig (fun _ => (0 : ℝ)) (fun _ => 1) (n + 1) j =
      0 + 2 * 1 * Real.cos (theta n j) := jacobiEig_const 0 1 one_pos (n + 1) j
  refine signVariations_eigvec_of_pos (d := fun _ => 0) (b := fun _ => 1) n
    (fun _ _ => one_pos) j ?_ ?_
  · rw [heig, hconst]
  · intro h
    have h0 := congrFun h 0
    simp only [sineMode, Fin.val_zero, Nat.cast_zero, zero_add, one_mul, Pi.zero_apply] at h0
    have := Real.sin_pos_of_pos_of_lt_pi (theta_mem n j j.isLt).1 (theta_mem n j j.isLt).2
    linarith

/-! ### Consumer 2: eigenvalue counting in an interval (bisection) -/

/-- **Bisection count.** For nonzero off-diagonals and `a ≤ c`, the number of eigenvalues of
`J_{n+1}` in `(a, c]` is `sturmCount a − sturmCount c`. -/
theorem card_Ioc_eq_sturm {d b : ℕ → ℝ} (n : ℕ) (hb : ∀ k < n, b k ≠ 0) {a c : ℝ} (hac : a ≤ c) :
    (univ.filter fun i : Fin (n + 1) => a < jacobiEig d b (n + 1) i ∧ jacobiEig d b (n + 1) i ≤ c).card =
      sturmCount d b (n + 1) a - sturmCount d b (n + 1) c := by
  rw [sturmCount_eq_card n hb, sturmCount_eq_card n hb]
  have hsplit : (univ.filter fun i : Fin (n + 1) => a < jacobiEig d b (n + 1) i) =
      (univ.filter fun i => c < jacobiEig d b (n + 1) i) ∪
        (univ.filter fun i => a < jacobiEig d b (n + 1) i ∧ jacobiEig d b (n + 1) i ≤ c) := by
    ext i
    simp only [mem_filter, mem_univ, true_and, mem_union]
    constructor
    · intro h
      by_cases hc : c < jacobiEig d b (n + 1) i
      · exact Or.inl hc
      · exact Or.inr ⟨h, not_lt.mp hc⟩
    · rintro (h | h)
      · exact lt_of_le_of_lt hac h
      · exact h.1
  have hdisj : Disjoint (univ.filter fun i : Fin (n + 1) => c < jacobiEig d b (n + 1) i)
      (univ.filter fun i => a < jacobiEig d b (n + 1) i ∧ jacobiEig d b (n + 1) i ≤ c) := by
    rw [Finset.disjoint_filter]
    intro i _ h1 h2
    linarith [h2.2]
  rw [hsplit, card_union_of_disjoint hdisj]
  omega

/-! ### Falsifier 1: strict monotonicity fails for interior perturbations -/

/-- The diagonal `(0, 1, 0, 0, …)`. -/
noncomputable def dBump : ℕ → ℝ := fun k => if k = 1 then 1 else 0

lemma jpoly_dBump : jpoly dBump (fun _ => 1) 3 = ∏ i : Fin 3, (X - C (![(-1 : ℝ), 0, 2] i)) := by
  rw [jpoly_three, Fin.prod_univ_three]
  simp only [dBump, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons]
  simp only [show (2 : ℕ) ≠ 1 by decide, show (0 : ℕ) ≠ 1 by decide, ↓reduceIte, map_zero, map_one,
    one_pow, sub_zero, map_neg, C_ofNat]
  ring

lemma isRootVec_dBump : IsRootVec (jpoly dBump (fun _ => 1) 3) ![(-1 : ℝ), 0, 2] := by
  refine ⟨?_, jpoly_dBump⟩
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp_all [Fin.lt_def]
  all_goals norm_num

lemma jacobiEig_dBump_one : jacobiEig dBump (fun _ => 1) 3 1 = 0 := by
  rw [jacobiEig_eq_of_isRootVec isRootVec_dBump]
  rfl

lemma jacobiEig_zero_one : jacobiEig (fun _ => (0 : ℝ)) (fun _ => 1) 3 1 = 0 := by
  rw [jacobiEig_const 0 1 one_pos 3 1]
  have : (((1 : Fin 3) : ℕ) + 1 : ℝ) * Real.pi / ((3 : ℕ) + 1) = Real.pi / 2 := by
    simp only [Fin.val_one, Nat.cast_one, Nat.cast_ofNat]; ring
  rw [this, Real.cos_pi_div_two]
  ring

/-- **Falsifier.** `d = 0 ≤ d' = (0,1,0)` with `d'_1 > d_1` and nonzero off-diagonals, yet the
middle eigenvalue does not move. Strictness needs the perturbation to reach an end site. -/
theorem interior_perturbation_not_strict :
    (∀ k < 3, (fun _ => (0 : ℝ)) k ≤ dBump k) ∧ (0 : ℝ) < dBump 1 ∧ (∀ k < 2, (1 : ℝ) ≠ 0) ∧
      jacobiEig (fun _ => (0 : ℝ)) (fun _ => 1) 3 1 = jacobiEig dBump (fun _ => 1) 3 1 := by
  refine ⟨fun k _ => ?_, by simp [dBump], fun _ _ => one_ne_zero, ?_⟩
  · simp only [dBump]; split_ifs <;> norm_num
  · rw [jacobiEig_zero_one, jacobiEig_dBump_one]

/-! ### Falsifiers 2 and 3: a vanishing off-diagonal breaks oscillation and the Sturm count -/

lemma jacobi_zero_zero : jacobi (fun _ => (0 : ℝ)) (fun _ => 0) 2 = 0 := by
  ext i j
  simp only [jacobi_apply, Matrix.zero_apply]
  split_ifs <;> rfl

lemma jacobiEig_zero_zero (i : Fin 2) : jacobiEig (fun _ => (0 : ℝ)) (fun _ => 0) 2 i = 0 := by
  have h : jacobiEig (fun _ => (0 : ℝ)) (fun _ => 0) 2 i ∈ spectrum ℝ (jacobi (fun _ => (0 : ℝ)) (fun _ => 0) 2) := by
    rw [spectrum_jacobi]; exact ⟨i, rfl⟩
  rw [jacobi_zero_zero, spectrum.zero_eq] at h
  exact h

/-- **Falsifier.** For `b ≡ 0` (here `J = 0` on two sites), `(1, 0)` is an eigenvector of the
second eigenvalue but has no sign change. The oscillation theorem needs `b_k ≠ 0`. -/
theorem nodal_fails_of_b_zero :
    jacobi (fun _ => (0 : ℝ)) (fun _ => 0) 2 *ᵥ ![1, 0] =
        jacobiEig (fun _ => (0 : ℝ)) (fun _ => 0) 2 1 • ![1, 0] ∧
      ![(1 : ℝ), 0] ≠ 0 ∧ (List.ofFn ![(1 : ℝ), 0]).signVariations = 0 ∧ (1 : Fin 2).val = 1 := by
  refine ⟨?_, ?_, ?_, rfl⟩
  · rw [jacobi_zero_zero, jacobiEig_zero_zero, zero_mulVec, zero_smul]
  · intro h
    have := congrFun h 0
    simp at this
  · simp [List.ofFn_succ]

/-- The off-diagonal `(0, 1, 1, …)`. -/
noncomputable def bGap : ℕ → ℝ := fun k => if k = 0 then 0 else 1

/-- **Falsifier.** For `d = 0`, `b = (0, 1)` on three sites, the Sturm count at `x = 0` is `0`,
although `1` is an eigenvalue: the count theorem needs `b_k ≠ 0`. -/
theorem sturm_fails_of_b_zero :
    sturmCount (fun _ => (0 : ℝ)) bGap 3 0 = 0 ∧
      (1 : ℝ) ∈ spectrum ℝ (jacobi (fun _ => (0 : ℝ)) bGap 3) ∧
      sturmCount (fun _ => (0 : ℝ)) bGap 3 0 ≠
        (univ.filter fun i : Fin 3 => (0 : ℝ) < jacobiEig (fun _ => (0 : ℝ)) bGap 3 i).card := by
  have hcount : sturmCount (fun _ => (0 : ℝ)) bGap 3 0 = 0 := by
    simp [sturmCount, sturmSeq, List.range_succ, jpoly_succ_succ, bGap]
  have hev : jacobi (fun _ => (0 : ℝ)) bGap 3 *ᵥ ![0, 1, 1] = ![0, 1, 1] := by
    ext i
    fin_cases i <;> simp [jacobi_apply, mulVec, dotProduct, Fin.sum_univ_three, bGap]
  have hspec : (1 : ℝ) ∈ spectrum ℝ (jacobi (fun _ => (0 : ℝ)) bGap 3) := by
    rw [spectrum.mem_iff, Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero, not_not,
      ← Matrix.exists_mulVec_eq_zero_iff]
    refine ⟨![0, 1, 1], ?_, ?_⟩
    · intro h
      have := congrFun h 1
      simp at this
    · rw [map_one, sub_mulVec, one_mulVec, hev, sub_self]
  refine ⟨hcount, hspec, ?_⟩
  rw [hcount]
  rw [spectrum_jacobi] at hspec
  obtain ⟨i, hi⟩ := hspec
  have hmem : i ∈ univ.filter fun i : Fin 3 => (0 : ℝ) < jacobiEig (fun _ => (0 : ℝ)) bGap 3 i := by
    rw [mem_filter, hi]; exact ⟨mem_univ _, one_pos⟩
  exact (Finset.card_pos.mpr ⟨i, hmem⟩).ne

end DiscreteSturm
