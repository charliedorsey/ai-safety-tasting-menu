/-
Copyright (c) 2026 Charlie Dorsey. Released under Apache 2.0 license.
-/
import DiscreteSturm.Count
import DiscreteSturm.SignVar

/-!
# Discrete Sturm–Liouville oscillation for Jacobi matrices

`p_k = jpoly d b k` is the characteristic polynomial `det(x − J_k)` of the `k`-th leading block.

* **Sturm count** (`sturmCount_eq_card`): for nonzero off-diagonals, the number of sign variations
  (zeros deleted; Mathlib's `List.signVariations`) of `p_0(x), p_1(x), …, p_{n+1}(x)` equals the
  number of eigenvalues of `J_{n+1}` strictly greater than `x`, for every real `x`.
* **Index form** (`lt_jacobiEig_iff`): `x < λ_i ↔ i < sturmCount x`.
* **Oscillation / nodal theorem** (`signVariations_jpoly_jacobiEig`): at the `i`-th largest
  eigenvalue `λ_i` (Mathlib's decreasing order, `i = 0` the largest), the recurrence solution
  `p_0(λ_i), …, p_n(λ_i)` has exactly `i` sign variations.
* **Eigenvectors** (`eigvec_gauge`, `signVariations_eigvec`, `signVariations_eigvec_of_pos`): every
  eigenvector satisfies `(b_0⋯b_{k-1}) v_k = v_0 p_k(μ)` (no hypothesis on `b`); hence the
  gauge-normalized eigenvector of `λ_i` has exactly `i` sign changes, and if all `b_k > 0` the
  eigenvector itself does.
* **Recurrence solution** (`mulVec_recSol`): `u_k = p_k(μ)/(b_0⋯b_{k-1})` is an eigenvector of
  `J_{n+1}` for `μ` whenever `p_{n+1}(μ) = 0` (shooting method).
-/

open Polynomial Finset Matrix JacobiSpectral

namespace DiscreteSturm

variable (d b : ℕ → ℝ)

/-! ### The Sturm sequence -/

/-- The Sturm sequence `[p_0(x), …, p_n(x)]` of the leading principal minors. -/
noncomputable def sturmSeq (n : ℕ) (x : ℝ) : List ℝ :=
  (List.range (n + 1)).map fun k => (jpoly d b k).eval x

/-- The Sturm count: sign variations (zeros deleted) of `[p_0(x), …, p_n(x)]`. -/
noncomputable def sturmCount (n : ℕ) (x : ℝ) : ℕ := (sturmSeq d b n x).signVariations

/-- The Sturm sequence read from the top, `[p_n(x), …, p_0(x)]`. -/
noncomputable def sturmRev (x : ℝ) : ℕ → List ℝ
  | 0 => [(jpoly d b 0).eval x]
  | n + 1 => (jpoly d b (n + 1)).eval x :: sturmRev x n

lemma sturmSeq_eq_reverse (x : ℝ) : ∀ n, sturmSeq d b n x = (sturmRev d b x n).reverse
  | 0 => by simp [sturmSeq, sturmRev]
  | n + 1 => by
    rw [sturmSeq, List.range_succ, List.map_append, ← sturmSeq, sturmSeq_eq_reverse x n, sturmRev,
      List.reverse_cons]
    simp

lemma sturmCount_eq_rev (n : ℕ) (x : ℝ) :
    sturmCount d b n x = (sturmRev d b x n).signVariations := by
  rw [sturmCount, sturmSeq_eq_reverse, signVariations_reverse]

lemma sturmRev_eq_cons (x : ℝ) : ∀ n, ∃ tl, sturmRev d b x n = (jpoly d b n).eval x :: tl
  | 0 => ⟨[], rfl⟩
  | n + 1 => ⟨sturmRev d b x n, rfl⟩

/-! ### Roots above `x` -/

/-- Number of roots (with multiplicity) of `p_m` strictly above `x`. -/
noncomputable def rootsAbove (m : ℕ) (x : ℝ) : ℕ :=
  ((jpoly d b m).roots.filter (fun y => x < y)).card

variable {d b}

lemma rootsAbove_zero (x : ℝ) : rootsAbove d b 0 x = 0 := by simp [rootsAbove]

lemma eval_jpoly_eq_prod {m : ℕ} {t : Fin m → ℝ} (ht : IsRootVec (jpoly d b m) t) (x : ℝ) :
    (jpoly d b m).eval x = ∏ i, (x - t i) := by
  rw [ht.2, eval_prod_X_sub_C]

lemma rootsAbove_succ_of_root {m : ℕ} (hb : ∀ k < m, b k ≠ 0) {x : ℝ}
    (hx : (jpoly d b (m + 1)).eval x = 0) : rootsAbove d b (m + 1) x = rootsAbove d b m x := by
  obtain ⟨t, r, ht, hr, hI⟩ := jpoly_interlace d b m hb
  rw [rootsAbove, rootsAbove, roots_filter_card_of_isRootVec ht, roots_filter_card_of_isRootVec hr]
  rw [eval_jpoly_eq_prod ht, Finset.prod_eq_zero_iff] at hx
  obtain ⟨j, -, hj⟩ := hx
  have hxj : x = t j := by linarith
  rw [hxj]
  exact cntAbove_root_left ht.1 hI j

lemma rootsAbove_succ_of_root_prev {m : ℕ} (hb : ∀ k < m, b k ≠ 0) {x : ℝ}
    (hx : (jpoly d b m).eval x = 0) : rootsAbove d b (m + 1) x = rootsAbove d b m x + 1 := by
  obtain ⟨t, r, ht, hr, hI⟩ := jpoly_interlace d b m hb
  rw [rootsAbove, rootsAbove, roots_filter_card_of_isRootVec ht, roots_filter_card_of_isRootVec hr]
  rw [eval_jpoly_eq_prod hr, Finset.prod_eq_zero_iff] at hx
  obtain ⟨j, -, hj⟩ := hx
  have hxj : x = r j := by linarith
  rw [hxj]
  exact cntAbove_root_right hI j

lemma sign_eq_iff_pos_iff {a c : ℝ} (ha : a ≠ 0) (hc : c ≠ 0) :
    SignType.sign a = SignType.sign c ↔ (0 < a ↔ 0 < c) := by
  rcases lt_or_gt_of_ne ha with ha' | ha' <;> rcases lt_or_gt_of_ne hc with hc' | hc' <;>
    simp [sign_neg, sign_pos, ha', hc', not_lt.mpr ha'.le, not_lt.mpr hc'.le]

lemma rootsAbove_succ_generic {m : ℕ} (hb : ∀ k < m, b k ≠ 0) {x : ℝ}
    (h1 : (jpoly d b (m + 1)).eval x ≠ 0) (h0 : (jpoly d b m).eval x ≠ 0) :
    rootsAbove d b (m + 1) x = rootsAbove d b m x +
      (if SignType.sign ((jpoly d b (m + 1)).eval x) = SignType.sign ((jpoly d b m).eval x)
        then 0 else 1) := by
  obtain ⟨t, r, ht, hr, hI⟩ := jpoly_interlace d b m hb
  rw [rootsAbove, rootsAbove, roots_filter_card_of_isRootVec ht, roots_filter_card_of_isRootVec hr]
  have hnt : ∀ i, t i ≠ x := fun i hi => h1 (by
    rw [eval_jpoly_eq_prod ht]; exact Finset.prod_eq_zero (mem_univ i) (by rw [hi]; ring))
  have hnr : ∀ i, r i ≠ x := fun i hi => h0 (by
    rw [eval_jpoly_eq_prod hr]; exact Finset.prod_eq_zero (mem_univ i) (by rw [hi]; ring))
  have pt := prod_pos_iff_even t x hnt
  have pr := prod_pos_iff_even r x hnr
  rw [← eval_jpoly_eq_prod ht] at pt
  rw [← eval_jpoly_eq_prod hr] at pr
  have key : SignType.sign ((jpoly d b (m + 1)).eval x) = SignType.sign ((jpoly d b m).eval x) ↔
      (Even (cntAbove t x) ↔ Even (cntAbove r x)) := by
    rw [sign_eq_iff_pos_iff h1 h0, pt, pr]
  rcases Nat.le.dest (cntAbove_le_of_interlace hI x) with ⟨k, hk⟩
  have hk1 : k ≤ 1 := by have := cntAbove_le_succ_of_interlace hI x; omega
  by_cases hs : SignType.sign ((jpoly d b (m + 1)).eval x) = SignType.sign ((jpoly d b m).eval x)
  · simp only [hs, ↓reduceIte, add_zero]
    have hpar := key.mp hs
    interval_cases k
    · omega
    · exfalso
      rw [← hk, Nat.even_add_one] at hpar
      tauto
  · simp only [hs, ↓reduceIte]
    have hpar : ¬ (Even (cntAbove t x) ↔ Even (cntAbove r x)) := fun h => hs (key.mpr h)
    interval_cases k
    · exfalso
      rw [← hk] at hpar
      exact hpar Iff.rfl
    · omega

/-! ### The Sturm count theorem -/

/-- **Sturm count, polynomial form.** -/
theorem signVariations_sturmRev : ∀ m : ℕ, (∀ k, k + 1 < m → b k ≠ 0) → ∀ x : ℝ,
    (sturmRev d b x m).signVariations = rootsAbove d b m x := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro hb x
    match m, ih, hb with
    | 0, _, _ => simp [sturmRev, rootsAbove_zero]
    | m + 1, ih, hb =>
      have hbm : ∀ k < m, b k ≠ 0 := fun k hk => hb k (by omega)
      have ihm := ih m (by omega) (fun k hk => hb k (by omega)) x
      by_cases h1 : (jpoly d b (m + 1)).eval x = 0
      · -- top entry vanishes
        rw [sturmRev, h1, List.signVariations_zero_cons, ihm, rootsAbove_succ_of_root hbm h1]
      · by_cases h0 : (jpoly d b m).eval x = 0
        · -- previous entry vanishes: m ≥ 1, and p_{m-1}(x) = -p_{m+1}(x)/b_{m-1}² ≠ 0
          match m, ih, hb, hbm, ihm, h1, h0 with
          | 0, _, _, _, _, _, h0 => simp at h0
          | m' + 1, ih, hb, hbm, ihm, h1, h0 =>
            have hbm' : ∀ k < m', b k ≠ 0 := fun k hk => hbm k (by omega)
            have ihm' := ih m' (by omega) (fun k hk => hb k (by omega)) x
            have hrec : (jpoly d b (m' + 2)).eval x = -(b m' ^ 2) * (jpoly d b m').eval x := by
              rw [jpoly_succ_succ]; simp [h0]
            have hb2 : 0 < b m' ^ 2 := by have := hbm m' (by omega); positivity
            have hpm' : (jpoly d b m').eval x ≠ 0 := fun h => h1 (by rw [hrec, h, mul_zero])
            obtain ⟨tl, htl⟩ := sturmRev_eq_cons d b x m'
            have hsgn : SignType.sign ((jpoly d b (m' + 2)).eval x) ≠
                SignType.sign ((jpoly d b m').eval x) := by
              rw [ne_eq, sign_eq_iff_pos_iff h1 hpm', hrec]
              intro h
              rcases lt_or_gt_of_ne hpm' with hp | hp
              · have hpos : 0 < -(b m' ^ 2) * (jpoly d b m').eval x := by nlinarith
                exact absurd (h.mp hpos) (not_lt.mpr hp.le)
              · have hneg : ¬ 0 < -(b m' ^ 2) * (jpoly d b m').eval x := not_lt.mpr (by nlinarith)
                exact hneg (h.mpr hp)
            have hstr : sturmRev d b x (m' + 2) =
                (jpoly d b (m' + 2)).eval x :: 0 :: sturmRev d b x m' := by
              simp only [sturmRev, h0]
            rw [hstr, List.signVariations_cons_zero_cons, htl,
              List.signVariations_cons_cons_of_ne_zero _ h1 hpm', ← htl, ihm']
            simp only [hsgn, ↓reduceIte]
            rw [rootsAbove_succ_of_root_prev hbm h0, rootsAbove_succ_of_root hbm' h0]
        · -- generic step
          obtain ⟨tl, htl⟩ := sturmRev_eq_cons d b x m
          have hstr : sturmRev d b x (m + 1) = (jpoly d b (m + 1)).eval x :: sturmRev d b x m := rfl
          rw [hstr, htl, List.signVariations_cons_cons_of_ne_zero _ h1 h0, ← htl, ihm,
            rootsAbove_succ_generic hbm h1 h0]

/-- `#{i | x < t (rev i)} = #{i | x < t i}`. -/
lemma card_filter_rev {n : ℕ} (t : Fin n → ℝ) (x : ℝ) :
    (univ.filter fun i : Fin n => x < t (Fin.rev i)).card = cntAbove t x := by
  rw [cntAbove]
  exact Finset.card_equiv Fin.revPerm (by simp)

/-- **Sturm count theorem.** For nonzero off-diagonals `b_0, …, b_{n-1}` and every real `x`, the
number of sign variations of `p_0(x), …, p_{n+1}(x)` equals the number of eigenvalues of
`J_{n+1}` strictly greater than `x`. -/
theorem sturmCount_eq_card (n : ℕ) (hb : ∀ k < n, b k ≠ 0) (x : ℝ) :
    sturmCount d b (n + 1) x = (univ.filter fun i : Fin (n + 1) => x < jacobiEig d b (n + 1) i).card := by
  obtain ⟨t, r, ht, -, -⟩ := jpoly_interlace d b n hb
  rw [sturmCount_eq_rev, signVariations_sturmRev (n + 1) (fun k hk => hb k (by omega)) x,
    rootsAbove, roots_filter_card_of_isRootVec ht]
  have h2 : (univ.filter fun i : Fin (n + 1) => x < jacobiEig d b (n + 1) i) =
      univ.filter fun i => x < t (Fin.rev i) := by
    ext i; simp [jacobiEig_eq_of_isRootVec ht]
  rw [h2, card_filter_rev]

/-- Counting below: `#{i | λ_i ≤ x} = (n + 1) − sturmCount x`. -/
theorem card_le_eq (n : ℕ) (hb : ∀ k < n, b k ≠ 0) (x : ℝ) :
    (univ.filter fun i : Fin (n + 1) => jacobiEig d b (n + 1) i ≤ x).card =
      (n + 1) - sturmCount d b (n + 1) x := by
  rw [sturmCount_eq_card (d := d) n hb]
  have h := Finset.card_filter_add_card_filter_not (s := (univ : Finset (Fin (n + 1))))
    (fun i => x < jacobiEig d b (n + 1) i)
  simp only [not_lt, card_univ, Fintype.card_fin] at h
  omega

/-- **Index form.** `x < λ_i ↔ i < sturmCount x` (eigenvalues in decreasing order). -/
theorem lt_jacobiEig_iff (n : ℕ) (hb : ∀ k < n, b k ≠ 0) (x : ℝ) (i : Fin (n + 1)) :
    x < jacobiEig d b (n + 1) i ↔ i.val < sturmCount d b (n + 1) x := by
  have hanti := jacobiEig_strictAnti d b n hb
  rw [sturmCount_eq_card (d := d) n hb]
  constructor
  · intro hx
    have hsub : Finset.Iic i ⊆ univ.filter fun j => x < jacobiEig d b (n + 1) j := by
      intro j hj
      rw [Finset.mem_Iic] at hj
      rw [mem_filter]
      exact ⟨mem_univ _, lt_of_lt_of_le hx (hanti.antitone hj)⟩
    have := Finset.card_le_card hsub
    rw [Fin.card_Iic] at this
    omega
  · intro hc
    by_contra hx
    push Not at hx
    have hsub : (univ.filter fun j => x < jacobiEig d b (n + 1) j) ⊆
        univ.filter fun j : Fin (n + 1) => j < i := by
      intro j hj
      rw [mem_filter] at hj ⊢
      refine ⟨mem_univ _, ?_⟩
      by_contra hji
      push Not at hji
      have := hanti.antitone hji
      linarith [hj.2]
    have h2 := Finset.card_le_card hsub
    have h3 : (univ.filter fun j : Fin (n + 1) => j < i).card = i.val := by
      have := Fin.card_filter_val_lt (n := n + 1) (m := i.val)
      simp only [Fin.lt_def] at this ⊢
      rw [this]; omega
    omega

/-! ### Oscillation of the recurrence solution and of eigenvectors -/

lemma eval_jpoly_jacobiEig (n : ℕ) (hb : ∀ k < n, b k ≠ 0) (i : Fin (n + 1)) :
    (jpoly d b (n + 1)).eval (jacobiEig d b (n + 1) i) = 0 := by
  obtain ⟨t, r, ht, -, -⟩ := jpoly_interlace d b n hb
  rw [jacobiEig_eq_of_isRootVec ht, eval_jpoly_eq_prod ht]
  exact Finset.prod_eq_zero (mem_univ (Fin.rev i)) (sub_self _)

/-- **Oscillation (nodal) theorem for the recurrence solution.** At the `i`-th largest eigenvalue
`λ_i` of `J_{n+1}`, the sequence `p_0(λ_i), …, p_n(λ_i)` has exactly `i` sign variations. -/
theorem signVariations_jpoly_jacobiEig (n : ℕ) (hb : ∀ k < n, b k ≠ 0) (i : Fin (n + 1)) :
    (sturmSeq d b n (jacobiEig d b (n + 1) i)).signVariations = i.val := by
  have hanti := jacobiEig_strictAnti d b n hb
  have h0 := eval_jpoly_jacobiEig (d := d) n hb i
  have hcount := sturmCount_eq_card (d := d) n hb (jacobiEig d b (n + 1) i)
  rw [sturmCount_eq_rev] at hcount
  have hstr : sturmRev d b (jacobiEig d b (n + 1) i) (n + 1) =
      0 :: sturmRev d b (jacobiEig d b (n + 1) i) n := by
    simp only [sturmRev, h0]
  rw [hstr, List.signVariations_zero_cons] at hcount
  rw [sturmSeq_eq_reverse, signVariations_reverse, hcount]
  have hset : (univ.filter fun j : Fin (n + 1) => jacobiEig d b (n + 1) i < jacobiEig d b (n + 1) j) =
      univ.filter fun j : Fin (n + 1) => j < i := by
    ext j; simp [hanti.lt_iff_gt]
  rw [hset]
  have := Fin.card_filter_val_lt (n := n + 1) (m := i.val)
  simp only [Fin.lt_def] at this ⊢
  rw [this]; omega

/-- The gauge factor `b_0 b_1 ⋯ b_{k-1}`. -/
noncomputable def gauge (b : ℕ → ℝ) (k : ℕ) : ℝ := ∏ j ∈ range k, b j

lemma gauge_succ (k : ℕ) : gauge b (k + 1) = gauge b k * b k := by
  rw [gauge, gauge, prod_range_succ]

/-- `∑_j [j = m] f j` over `Fin N`. -/
lemma sum_fin_val_eq {N : ℕ} (m : ℕ) (f : Fin N → ℝ) :
    (∑ j : Fin N, if j.val = m then f j else 0) = if h : m < N then f ⟨m, h⟩ else 0 := by
  split_ifs with h
  · rw [Finset.sum_eq_single ⟨m, h⟩]
    · simp
    · intro j _ hj
      rw [ite_eq_right]
      exact fun e => hj (Fin.ext e)
    · intro hj; exact absurd (mem_univ _) hj
  · refine Finset.sum_eq_zero fun j _ => ?_
    rw [ite_eq_right]
    omega

/-- Row `k` of `J_N v`. -/
lemma jacobi_mulVec_apply {N : ℕ} (v : Fin N → ℝ) (k : Fin N) :
    (jacobi d b N *ᵥ v) k =
      d k * v k + (if h : k.val + 1 < N then b k * v ⟨k.val + 1, h⟩ else 0) +
        (if h : 0 < k.val then b (k.val - 1) * v ⟨k.val - 1, by omega⟩ else 0) := by
  have hpt : ∀ j : Fin N, jacobi d b N k j * v j =
      (if j.val = k.val then d k * v j else 0) + (if j.val = k.val + 1 then b k * v j else 0) +
        (if j.val + 1 = k.val then b j * v j else 0) := by
    intro j
    rw [jacobi_apply]
    by_cases h1 : k.val = j.val
    · simp only [h1, ↓reduceIte, show ¬ j.val = j.val + 1 by omega,
        show ¬ j.val + 1 = j.val by omega, add_zero]
    · by_cases h2 : k.val + 1 = j.val
      · simp only [h1, h2, ↓reduceIte, show ¬ j.val = k.val by omega,
          show ¬ j.val + 1 = k.val by omega, zero_add, add_zero]
      · by_cases h3 : j.val + 1 = k.val
        · simp only [h1, h2, h3, ↓reduceIte, show ¬ j.val = k.val by omega,
            show ¬ j.val = k.val + 1 by omega, zero_add]
        · simp only [h1, h2, h3, ↓reduceIte, show ¬ j.val = k.val by omega,
            show ¬ j.val = k.val + 1 by omega, zero_mul, add_zero]
  rw [mulVec, dotProduct]
  simp_rw [hpt]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, sum_fin_val_eq, sum_fin_val_eq]
  congr 1
  · congr 1
    rw [dite_eq_left k.isLt]
  · rcases Nat.eq_zero_or_pos k.val with hk | hk
    · rw [dite_eq_right (by omega)]
      refine Finset.sum_eq_zero fun j _ => ?_
      rw [ite_eq_right]; omega
    · rw [dite_eq_left hk]
      have : ∀ j : Fin N, (if j.val + 1 = k.val then b j * v j else 0) =
          if j.val = k.val - 1 then b j * v j else 0 := by
        intro j
        by_cases hj : j.val + 1 = k.val
        · rw [ite_eq_left hj, ite_eq_left (by omega)]
        · rw [ite_eq_right hj, ite_eq_right (by omega)]
      simp_rw [this]
      rw [sum_fin_val_eq, dite_eq_left (by omega)]

/-- Extension of `v : Fin N → ℝ` by zero to `ℕ`. -/
noncomputable def extN {N : ℕ} (v : Fin N → ℝ) (k : ℕ) : ℝ := if h : k < N then v ⟨k, h⟩ else 0

lemma extN_fin {N : ℕ} (v : Fin N → ℝ) (k : Fin N) : extN v k = v k := by
  simp [extN, k.isLt]

/-- Row `k` of `J_N v`, with the zero-extension of `v`. -/
lemma jacobi_mulVec_extN {N : ℕ} (v : Fin N → ℝ) (k : Fin N) :
    (jacobi d b N *ᵥ v) k = d k * extN v k + b k * extN v (k.val + 1) +
      (if 0 < k.val then b (k.val - 1) * extN v (k.val - 1) else 0) := by
  rw [jacobi_mulVec_apply, extN_fin]
  congr 1
  · congr 1
    by_cases h : k.val + 1 < N
    · rw [dite_eq_left h]; simp [extN, h]
    · rw [dite_eq_right h]; simp [extN, h]
  · by_cases h : 0 < k.val
    · rw [dite_eq_left h, ite_eq_left h]; simp [extN, show k.val - 1 < N by omega]
    · rw [dite_eq_right h, ite_eq_right h]

/-- **Every eigenvector is the recurrence solution** (no hypothesis on `b`):
`(b_0⋯b_{k-1}) v_k = v_0 p_k(μ)` for all `k`. -/
theorem eigvec_gauge {N : ℕ} {μ : ℝ} {v : Fin N → ℝ} (hv : jacobi d b N *ᵥ v = μ • v)
    (h0 : 0 < N) : ∀ k : Fin N, gauge b k * v k = v ⟨0, h0⟩ * (jpoly d b k).eval μ := by
  set w := extN v with hw
  have hw0 : w 0 = v ⟨0, h0⟩ := by simp [hw, extN, h0]
  have row : ∀ k (hk : k < N), d k * w k + b k * w (k + 1) +
      (if 0 < k then b (k - 1) * w (k - 1) else 0) = μ * w k := by
    intro k hk
    have h := jacobi_mulVec_extN (d := d) (b := b) v ⟨k, hk⟩
    rw [hv] at h
    simp only [Pi.smul_apply, smul_eq_mul] at h
    rw [← h, show v ⟨k, hk⟩ = w k by simp [hw, extN, hk]]
  have key : ∀ m, m + 1 < N → gauge b m * w m = w 0 * (jpoly d b m).eval μ ∧
      gauge b (m + 1) * w (m + 1) = w 0 * (jpoly d b (m + 1)).eval μ := by
    intro m
    induction m with
    | zero =>
      intro hm
      have h := row 0 (by omega)
      simp only [lt_irrefl, ↓reduceIte, add_zero, zero_add] at h
      refine ⟨by simp [gauge], ?_⟩
      simp only [zero_add, gauge, range_one, prod_singleton, jpoly_one, eval_sub, eval_X, eval_C]
      linarith
    | succ m ih =>
      intro hm
      obtain ⟨ihm, ihm1⟩ := ih (by omega)
      refine ⟨ihm1, ?_⟩
      have h := row (m + 1) (by omega)
      simp only [Nat.succ_pos, ↓reduceIte, Nat.add_sub_cancel] at h
      have hrec : (jpoly d b (m + 2)).eval μ =
          (μ - d (m + 1)) * (jpoly d b (m + 1)).eval μ - b m ^ 2 * (jpoly d b m).eval μ := by
        rw [jpoly_succ_succ]; simp
      rw [gauge_succ, gauge_succ] at *
      rw [show m + 1 + 1 = m + 2 from rfl, hrec]
      have e1 : b (m + 1) * w (m + 2) = (μ - d (m + 1)) * w (m + 1) - b m * w m := by linarith
      calc gauge b m * b m * b (m + 1) * w (m + 2)
          = gauge b m * b m * (b (m + 1) * w (m + 2)) := by ring
        _ = (μ - d (m + 1)) * (gauge b m * b m * w (m + 1)) - b m ^ 2 * (gauge b m * w m) := by
            rw [e1]; ring
        _ = _ := by rw [ihm1, ihm]; ring
  intro k
  rw [← hw0, show v k = w k by simp [hw, extN, k.isLt]]
  rcases Nat.eq_zero_or_pos k.val with hk | hk
  · rw [hk]; simp [gauge]
  · obtain ⟨m, hm⟩ : ∃ m, k.val = m + 1 := ⟨k.val - 1, by omega⟩
    rw [hm]
    exact (key m (by omega)).2

/-- **Oscillation theorem for eigenvectors.** For nonzero off-diagonals, every nonzero eigenvector
of `J_{n+1}` for its `i`-th largest eigenvalue, gauge-normalized by `b_0⋯b_{k-1}`, has exactly `i`
sign variations. -/
theorem signVariations_eigvec (n : ℕ) (hb : ∀ k < n, b k ≠ 0) (i : Fin (n + 1))
    {v : Fin (n + 1) → ℝ} (hv : jacobi d b (n + 1) *ᵥ v = jacobiEig d b (n + 1) i • v)
    (hv0 : v ≠ 0) :
    (List.ofFn fun k : Fin (n + 1) => gauge b k * v k).signVariations = i.val := by
  have hhead : v 0 ≠ 0 := fun h => hv0 (eigvec_eq_zero_of_head d b n hb hv h)
  have hg := eigvec_gauge hv (Nat.succ_pos n)
  have hlist : (List.ofFn fun k : Fin (n + 1) => gauge b k * v k) =
      (sturmSeq d b n (jacobiEig d b (n + 1) i)).map (fun y => v 0 * y) := by
    rw [sturmSeq, List.map_map, List.ofFn_eq_map, ← List.map_coe_finRange_eq_range, List.map_map]
    refine List.map_congr_left fun k _ => ?_
    rw [hg k]
    rfl
  rw [hlist, ← signVariations_jpoly_jacobiEig (d := d) n hb i]
  rcases lt_or_gt_of_ne hhead with hneg | hpos
  · exact List.signVariations_map_of_sign_eq_neg (fun y => by
      rw [sign_mul, sign_neg hneg]; simp) _
  · exact List.signVariations_map (fun y => by rw [sign_mul, sign_pos hpos, one_mul]) _

/-- **Oscillation theorem for eigenvectors, positive off-diagonals.** If all `b_k > 0`, every nonzero
eigenvector of the `i`-th largest eigenvalue of `J_{n+1}` has exactly `i` sign changes. -/
theorem signVariations_eigvec_of_pos (n : ℕ) (hb : ∀ k < n, 0 < b k) (i : Fin (n + 1))
    {v : Fin (n + 1) → ℝ} (hv : jacobi d b (n + 1) *ᵥ v = jacobiEig d b (n + 1) i • v)
    (hv0 : v ≠ 0) :
    (List.ofFn v).signVariations = i.val := by
  rw [← signVariations_eigvec (d := d) n (fun k hk => (hb k hk).ne') i hv hv0]
  refine List.signVariations_congr ?_
  simp only [List.map_ofFn]
  congr 1
  funext k
  simp only [Function.comp_apply]
  have hg : 0 < gauge b k := Finset.prod_pos fun j hj => hb j (by
    have := Finset.mem_range.mp hj; omega)
  rw [sign_mul, sign_pos hg, one_mul]

/-- The recurrence solution `u_k = p_k(μ) / (b_0⋯b_{k-1})`. -/
noncomputable def recSol (d b : ℕ → ℝ) (μ : ℝ) (N : ℕ) : Fin N → ℝ :=
  fun k => (jpoly d b k).eval μ / gauge b k

/-- The three-term recurrence in unified form. -/
lemma eval_jpoly_succ (μ : ℝ) (k : ℕ) :
    (jpoly d b (k + 1)).eval μ = (μ - d k) * (jpoly d b k).eval μ -
      (if 0 < k then b (k - 1) ^ 2 * (jpoly d b (k - 1)).eval μ else 0) := by
  rcases k with _ | k
  · simp
  · rw [jpoly_succ_succ]; simp

/-- **Shooting method.** For nonzero off-diagonals, the recurrence solution is an eigenvector of
`J_{n+1}` for `μ` whenever `p_{n+1}(μ) = 0`. -/
theorem mulVec_recSol (n : ℕ) (hb : ∀ k < n, b k ≠ 0) {μ : ℝ}
    (hμ : (jpoly d b (n + 1)).eval μ = 0) :
    jacobi d b (n + 1) *ᵥ recSol d b μ (n + 1) = μ • recSol d b μ (n + 1) := by
  have hg : ∀ k ≤ n, gauge b k ≠ 0 := fun k hk =>
    Finset.prod_ne_zero_iff.mpr fun j hj => hb j (by have := Finset.mem_range.mp hj; omega)
  funext k
  rw [jacobi_mulVec_extN, Pi.smul_apply, smul_eq_mul]
  have hk := k.isLt
  have hgk := hg k (by omega)
  have hext : ∀ j, j < n + 1 → extN (recSol d b μ (n + 1)) j = (jpoly d b j).eval μ / gauge b j :=
    fun j hj => by simp [extN, recSol, hj]
  rw [hext k hk, show recSol d b μ (n + 1) k = (jpoly d b k).eval μ / gauge b k from rfl]
  have hrec := eval_jpoly_succ (d := d) (b := b) μ k
  -- the forward term `b_k u_{k+1}`
  have hfwd : b k * extN (recSol d b μ (n + 1)) (k.val + 1) =
      (if k.val + 1 < n + 1 then (jpoly d b (k + 1)).eval μ / gauge b k else 0) := by
    by_cases h : k.val + 1 < n + 1
    · rw [hext _ h, ite_eq_left h, gauge_succ]
      have hbk := hb k (by omega)
      field_simp
    · rw [ite_eq_right h]; simp [extN, h]
  -- the backward term `b_{k-1} u_{k-1}`
  have hbwd : (if 0 < k.val then b (k.val - 1) * extN (recSol d b μ (n + 1)) (k.val - 1) else 0) =
      (if 0 < k.val then b (k.val - 1) ^ 2 * (jpoly d b (k.val - 1)).eval μ / gauge b k else 0) := by
    by_cases h : 0 < k.val
    · rw [ite_eq_left h, ite_eq_left h, hext _ (by omega)]
      have hgk' : gauge b k = gauge b (k.val - 1) * b (k.val - 1) := by
        rw [← gauge_succ, Nat.sub_add_cancel h]
      have hgm := hg (k.val - 1) (by omega)
      have hbm := hb (k.val - 1) (by omega)
      rw [hgk']
      field_simp
    · rw [ite_eq_right h, ite_eq_right h]
  rw [hfwd, hbwd]
  by_cases hlast : k.val + 1 < n + 1
  · rw [ite_eq_left hlast]
    by_cases h0 : 0 < k.val
    · rw [ite_eq_left h0] at hrec ⊢
      field_simp
      linarith
    · rw [ite_eq_right h0] at hrec ⊢
      field_simp
      linarith
  · rw [ite_eq_right hlast]
    have hkn : k.val = n := by omega
    have hμ' : (jpoly d b (k.val + 1)).eval μ = 0 := by rw [hkn]; exact hμ
    by_cases h0 : 0 < k.val
    · rw [ite_eq_left h0] at hrec ⊢
      field_simp
      linarith
    · rw [ite_eq_right h0] at hrec ⊢
      field_simp
      linarith

end DiscreteSturm
