import JacobiSpectral.Sturm
import Mathlib.Analysis.Matrix.Spectrum

/-!
# `JacobiSpectral.Spectrum` — simple spectrum and strict Cauchy interlacing for Jacobi matrices

Bridges the recurrence-level results of `JacobiSpectral.Sturm` to Mathlib's Hermitian spectral
API (`Matrix.IsHermitian.eigenvalues₀`, sorted decreasingly).

For real `d, b` with `b_k ≠ 0` (`k < n`):

* `no_common_root`: `p_{n+1}` and `p_n` have no common root (direct from the recurrence);
* `charpoly_roots_nodup`: the characteristic polynomial of `J_{n+1}` has simple roots;
* `jacobiEig_strictAnti`: the eigenvalues of `J_{n+1}` are pairwise distinct;
* `jacobiEig_interlace`: **strict interlacing**
  `λ_{i+1}(J_{n+1}) < λ_i(J_n) < λ_i(J_{n+1})` (decreasing order).
-/

open Polynomial Finset Matrix

namespace JacobiSpectral

/-- **No common root of consecutive continuants** (needs only the recurrence). -/
theorem no_common_root (d b : ℕ → ℝ) : ∀ n : ℕ, (∀ k < n, b k ≠ 0) → ∀ x : ℝ,
    (jpoly d b (n + 1)).eval x = 0 → (jpoly d b n).eval x ≠ 0
  | 0 => fun _ x _ => by simp
  | (n + 1) => fun hb x h2 h1 => by
      have hrec := congrArg (eval x) (jpoly_succ_succ d b n)
      rw [h2] at hrec
      simp only [eval_sub, eval_mul, h1, mul_zero, eval_C, zero_sub] at hrec
      have hb2 : b n ^ 2 ≠ 0 := pow_ne_zero _ (hb n (by omega))
      have h0 : (jpoly d b n).eval x = 0 := by
        have : b n ^ 2 * (jpoly d b n).eval x = 0 := by linarith
        exact (mul_eq_zero.1 this).resolve_left hb2
      exact no_common_root d b n (fun k hk => hb k (by omega)) x h1 h0

/-- The eigenvalues of `J_n`, in Mathlib's decreasing order, indexed by `Fin n`. -/
noncomputable def jacobiEig (d b : ℕ → ℝ) (n : ℕ) : Fin n → ℝ :=
  fun i => (jacobi_isHermitian d b n).eigenvalues₀ (Fin.cast (Fintype.card_fin n).symm i)

lemma map_rev_univ {n : ℕ} (f : Fin n → ℝ) :
    Multiset.map (fun i => f (Fin.rev i)) univ.val = Multiset.map f univ.val := by
  have h : Multiset.map (Fin.revPerm : Fin n → Fin n) univ.val = univ.val := by
    have := congrArg Finset.val (Finset.map_univ_equiv (Fin.revPerm (n := n)))
    rwa [Finset.map_val] at this
  calc Multiset.map (fun i => f (Fin.rev i)) univ.val
      = Multiset.map f (Multiset.map (Fin.revPerm : Fin n → Fin n) univ.val) := by
        rw [Multiset.map_map]; rfl
    _ = _ := by rw [h]

/-- The charpoly of `J_n` has root multiset `{t_i}` whenever `t` is a root vector of `p_n`. -/
lemma charpoly_roots_of_isRootVec {d b : ℕ → ℝ} {n : ℕ} {t : Fin n → ℝ}
    (ht : IsRootVec (jpoly d b n) t) :
    (jacobi d b n).charpoly.roots = Multiset.map t univ.val := by
  rw [charpoly_jacobi, ht.2]
  have : (∏ i, (X - C (t i)) : ℝ[X]) = ((Multiset.map t univ.val).map fun a => X - C a).prod := by
    rw [Multiset.map_map]; rfl
  rw [this, roots_multiset_prod_X_sub_C]

/-- **Eigenvalues = sorted roots.** If `t` is the increasing root vector of `p_n`, then the
`i`-th largest eigenvalue of `J_n` is `t_{n-1-i}`. -/
theorem jacobiEig_eq_of_isRootVec {d b : ℕ → ℝ} {n : ℕ} {t : Fin n → ℝ}
    (ht : IsRootVec (jpoly d b n) t) (i : Fin n) : jacobiEig d b n i = t (Fin.rev i) := by
  have hA := jacobi_isHermitian d b n
  have hsort := hA.sort_roots_charpoly_eq_eigenvalues₀
  rw [charpoly_roots_of_isRootVec ht, ← map_rev_univ t, Fin.univ_val_map] at hsort
  have hre : (List.ofFn fun i => t (Fin.rev i)).map (RCLike.re : ℝ → ℝ) =
      List.ofFn fun i => t (Fin.rev i) := by
    rw [List.map_ofFn]; rfl
  rw [Multiset.map_coe, hre, Multiset.coe_sort, List.mergeSort_of_pairwise] at hsort
  · have hlen := congrArg List.length hsort
    have hget := congrArg (fun l : List ℝ => l[i.val]?) hsort
    simp only [List.getElem?_ofFn] at hget
    simp only [jacobiEig]
    have hi : i.val < Fintype.card (Fin n) := by rw [Fintype.card_fin]; exact i.isLt
    simp only [hi, i.isLt, dite_true, Option.some.injEq] at hget
    exact hget.symm
  · simp_rw [decide_eq_true_eq]
    rw [← List.sortedGE_iff_pairwise]
    exact Antitone.sortedGE_ofFn fun i j hij => ht.1.monotone (Fin.rev_le_rev.2 hij)

/-- **Simple spectrum (algebraic).** With nonzero off-diagonals the characteristic polynomial of
`J_{n+1}` has `n + 1` distinct real roots. -/
theorem charpoly_roots_nodup (d b : ℕ → ℝ) (n : ℕ) (hb : ∀ k < n, b k ≠ 0) :
    (jacobi d b (n + 1)).charpoly.roots.Nodup := by
  obtain ⟨t, -, ht, -, -⟩ := jpoly_interlace d b n hb
  rw [charpoly_roots_of_isRootVec ht]
  exact (Multiset.nodup_map_iff_of_injective ht.1.injective).2 univ.nodup

/-- **Simple spectrum (eigenvalues).** The eigenvalues of `J_{n+1}` are strictly decreasing. -/
theorem jacobiEig_strictAnti (d b : ℕ → ℝ) (n : ℕ) (hb : ∀ k < n, b k ≠ 0) :
    StrictAnti (jacobiEig d b (n + 1)) := by
  obtain ⟨t, -, ht, -, -⟩ := jpoly_interlace d b n hb
  intro i j hij
  rw [jacobiEig_eq_of_isRootVec ht, jacobiEig_eq_of_isRootVec ht]
  exact ht.1 (Fin.rev_lt_rev.2 hij)

/-- **Strict Cauchy interlacing for Jacobi matrices.** With `b_k ≠ 0` for `k < n`, the
eigenvalues of the leading block `J_n` strictly interlace those of `J_{n+1}`:
`λ_{i+1}(J_{n+1}) < λ_i(J_n) < λ_i(J_{n+1})` (decreasing order). -/
theorem jacobiEig_interlace (d b : ℕ → ℝ) (n : ℕ) (hb : ∀ k < n, b k ≠ 0) (i : Fin n) :
    jacobiEig d b (n + 1) i.succ < jacobiEig d b n i ∧
      jacobiEig d b n i < jacobiEig d b (n + 1) i.castSucc := by
  obtain ⟨t, r, ht, hr, hI⟩ := jpoly_interlace d b n hb
  rw [jacobiEig_eq_of_isRootVec ht, jacobiEig_eq_of_isRootVec ht, jacobiEig_eq_of_isRootVec hr]
  have h1 : Fin.rev i.succ = (Fin.rev i).castSucc := by
    ext; simp only [Fin.val_rev, Fin.val_succ, Fin.val_castSucc]; omega
  have h2 : Fin.rev i.castSucc = (Fin.rev i).succ := by
    ext; simp only [Fin.val_rev, Fin.val_succ, Fin.val_castSucc]; omega
  rw [h1, h2]
  exact hI (Fin.rev i)

/-- The leading block `J_n` is literally the top-left submatrix of `J_{n+1}`, so
`jacobiEig_interlace` is interlacing of a matrix and its leading principal minor. -/
example (d b : ℕ → ℝ) (n : ℕ) :
    (jacobi d b (n + 1)).submatrix Fin.castSucc Fin.castSucc = jacobi d b n := jacobi_leading d b n

/-! ### Geometric simplicity: every eigenspace is a line -/

lemma jacobi_mulVec_row {d b : ℕ → ℝ} {n : ℕ} (v : Fin n → ℝ) (m : ℕ) (hm : m + 1 < n)
    (hv : ∀ j : Fin n, j.val ≤ m → v j = 0) :
    (jacobi d b n *ᵥ v) ⟨m, by omega⟩ = b m * v ⟨m + 1, hm⟩ := by
  rw [mulVec, dotProduct, Finset.sum_eq_single ⟨m + 1, hm⟩]
  · simp only [jacobi_apply]
    split_ifs <;> first | rfl | omega
  · intro j _ hj
    by_cases hjm : j.val ≤ m
    · rw [hv j hjm, mul_zero]
    · have : m + 1 < j.val := by
        have : j.val ≠ m + 1 := fun h => hj (Fin.ext h)
        omega
      rw [jacobi_apply_eq_zero d b (by simp only; omega), zero_mul]
  · intro h; exact absurd (Finset.mem_univ _) h

/-- An eigenvector of `J_{n+1}` (nonzero off-diagonals) vanishing at the first coordinate is zero:
the recurrence `b_m v_{m+1} = (μ − d_m) v_m − b_{m−1} v_{m−1}` determines `v` from `v₀`. -/
theorem eigvec_eq_zero_of_head (d b : ℕ → ℝ) (n : ℕ) (hb : ∀ k < n, b k ≠ 0) {μ : ℝ}
    {v : Fin (n + 1) → ℝ} (hv : jacobi d b (n + 1) *ᵥ v = μ • v) (h0 : v 0 = 0) : v = 0 := by
  have key : ∀ m : ℕ, ∀ j : Fin (n + 1), j.val ≤ m → v j = 0 := by
    intro m
    induction m with
    | zero => intro j hj; have : j = 0 := Fin.ext (by rw [Fin.val_zero]; omega); rw [this, h0]
    | succ m ih =>
      intro j hj
      rcases Nat.lt_or_ge j.val (m + 1) with hlt | hge
      · exact ih j (by omega)
      · have hjv : j.val = m + 1 := by omega
        have hm : m + 1 < n + 1 := by omega
        have hrow := congrFun hv ⟨m, by omega⟩
        rw [jacobi_mulVec_row v m hm ih, Pi.smul_apply, ih ⟨m, by omega⟩ le_rfl, smul_zero] at hrow
        have hj' : j = ⟨m + 1, hm⟩ := Fin.ext hjv
        rw [hj']
        exact (mul_eq_zero.1 hrow).resolve_left (hb m (by omega))
  funext j
  exact key j.val j le_rfl

/-- **Geometric simplicity.** Every eigenspace of `J_{n+1}` (nonzero off-diagonals) has
dimension at most one. -/
theorem finrank_eigenspace_le_one (d b : ℕ → ℝ) (n : ℕ) (hb : ∀ k < n, b k ≠ 0) (μ : ℝ) :
    Module.finrank ℝ (Module.End.eigenspace (toLin' (jacobi d b (n + 1))) μ) ≤ 1 := by
  set E := Module.End.eigenspace (toLin' (jacobi d b (n + 1))) μ
  let φ : E →ₗ[ℝ] ℝ := (LinearMap.proj (R := ℝ) (φ := fun _ : Fin (n + 1) => ℝ) 0).comp E.subtype
  have hφ : Function.Injective φ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro x hx
    have hmem := x.2
    rw [Module.End.mem_eigenspace_iff, toLin'_apply] at hmem
    exact Subtype.ext (eigvec_eq_zero_of_head d b n hb hmem hx)
  have := LinearMap.finrank_le_finrank_of_injective hφ
  rwa [Module.finrank_self] at this

/-- **Every eigenvalue is simple (geometric form).** For each eigenvalue of `J_{n+1}` the
eigenspace is exactly one-dimensional. -/
theorem finrank_eigenspace_jacobiEig (d b : ℕ → ℝ) (n : ℕ) (hb : ∀ k < n, b k ≠ 0)
    (i : Fin (n + 1)) :
    Module.finrank ℝ (Module.End.eigenspace (toLin' (jacobi d b (n + 1))) (jacobiEig d b (n + 1) i))
      = 1 := by
  refine le_antisymm (finrank_eigenspace_le_one d b n hb _) ?_
  obtain ⟨t, -, ht, -, -⟩ := jpoly_interlace d b n hb
  have hroot : (toLin' (jacobi d b (n + 1))).charpoly.IsRoot (jacobiEig d b (n + 1) i) := by
    rw [charpoly_toLin', charpoly_jacobi, jacobiEig_eq_of_isRootVec ht, IsRoot, ht.2,
      eval_prod_X_sub_C]
    exact prod_eq_zero (mem_univ (Fin.rev i)) (sub_self _)
  have hne := (Module.End.hasEigenvalue_iff_isRoot_charpoly _ _).2 hroot
  rw [Module.End.hasEigenvalue_iff] at hne
  rw [Nat.one_le_iff_ne_zero]
  intro h0
  exact hne (Submodule.finrank_eq_zero.1 h0)

end JacobiSpectral
