/-
Copyright (c) 2026 Charlie Dorsey. Released under Apache 2.0 license.
-/
import Mathlib.Analysis.InnerProductSpace.Spectrum
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# Weyl monotonicity of eigenvalues via the min–max dimension count

For symmetric operators `S, T` on a finite-dimensional real inner product space with
`⟪S v, v⟫ ≤ ⟪T v, v⟫` for all `v` (the Loewner order `S ≤ T`), the sorted eigenvalues satisfy
`λ_i(S) ≤ λ_i(T)` for every `i` (`eigenvalues_le_of_inner_le`).

Proof (Courant–Fischer, one direction): the span `V` of the top `i+1` eigenvectors of `S` and the
span `W` of the bottom `n−i` eigenvectors of `T` have dimensions summing to `n+1`, so they meet in
some `v ≠ 0`, and `λ_i(S)‖v‖² ≤ ⟪Sv, v⟫ ≤ ⟪Tv, v⟫ ≤ λ_i(T)‖v‖²`.

Strict version (`eigenvalues_lt_of_inner_lt`): if moreover `⟪S v, v⟫ < ⟪T v, v⟫` for every
eigenvector `v` of `T`, then `λ_i(S) < λ_i(T)` for every `i` (equality would force the common
vector `v` to be an eigenvector of `T` with `⟪Sv, v⟫ = ⟪Tv, v⟫`).

Eigenvalues are Mathlib's `LinearMap.IsSymmetric.eigenvalues` (sorted decreasingly, `i = 0` the
largest), with the matching sorted orthonormal eigenbasis `eigenvectorBasis`.
-/

open Module Submodule Finset

namespace DiscreteSturm

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable {n : ℕ} (hn : finrank ℝ E = n)

local notation "⟪" x ", " y "⟫" => @inner ℝ E _ x y

section Rayleigh

variable {T : E →ₗ[ℝ] E} (hT : T.IsSymmetric)

omit [FiniteDimensional ℝ E] in
lemma inner_self_eq_sum_repr (e : OrthonormalBasis (Fin n) ℝ E) (v : E) :
    ⟪v, v⟫ = ∑ j, (e.repr v j) ^ 2 := by
  rw [← e.sum_inner_mul_inner v v]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [OrthonormalBasis.repr_apply_apply, real_inner_comm, sq]

include hT in
lemma inner_apply_eq_sum_repr (v : E) :
    ⟪T v, v⟫ = ∑ j, hT.eigenvalues hn j * ((hT.eigenvectorBasis hn).repr v j) ^ 2 := by
  set e := hT.eigenvectorBasis hn
  rw [← e.sum_inner_mul_inner (T v) v]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [hT (v) (e j), hT.apply_eigenvectorBasis hn j, OrthonormalBasis.repr_apply_apply,
    real_inner_smul_right, real_inner_comm (e j) v]
  simp only [RCLike.ofReal_real_eq_id, id]
  ring

include hT in
/-- Rayleigh lower bound on the span of the top eigenvectors. -/
lemma le_inner_of_repr_eq_zero_gt (i : Fin n) (v : E)
    (hv : ∀ j, i < j → (hT.eigenvectorBasis hn).repr v j = 0) :
    hT.eigenvalues hn i * ⟪v, v⟫ ≤ ⟪T v, v⟫ := by
  rw [inner_apply_eq_sum_repr hn hT, inner_self_eq_sum_repr (hT.eigenvectorBasis hn), Finset.mul_sum]
  refine Finset.sum_le_sum fun j _ => ?_
  by_cases hij : i < j
  · rw [hv j hij]; simp
  · push Not at hij
    exact mul_le_mul_of_nonneg_right (hT.eigenvalues_antitone hn hij) (sq_nonneg _)

include hT in
/-- Rayleigh upper bound on the span of the bottom eigenvectors. -/
lemma inner_le_of_repr_eq_zero_lt (i : Fin n) (v : E)
    (hv : ∀ j, j < i → (hT.eigenvectorBasis hn).repr v j = 0) :
    ⟪T v, v⟫ ≤ hT.eigenvalues hn i * ⟪v, v⟫ := by
  rw [inner_apply_eq_sum_repr hn hT, inner_self_eq_sum_repr (hT.eigenvectorBasis hn), Finset.mul_sum]
  refine Finset.sum_le_sum fun j _ => ?_
  by_cases hji : j < i
  · rw [hv j hji]; simp
  · push Not at hji
    exact mul_le_mul_of_nonneg_right (hT.eigenvalues_antitone hn hji) (sq_nonneg _)

include hT in
/-- Equality in the upper Rayleigh bound forces an eigenvector. -/
lemma apply_eq_of_inner_eq (i : Fin n) (v : E)
    (hv : ∀ j, j < i → (hT.eigenvectorBasis hn).repr v j = 0)
    (heq : ⟪T v, v⟫ = hT.eigenvalues hn i * ⟪v, v⟫) :
    T v = hT.eigenvalues hn i • v := by
  set e := hT.eigenvectorBasis hn
  set μ := hT.eigenvalues hn i
  have hsum : ∑ j, (μ - hT.eigenvalues hn j) * (e.repr v j) ^ 2 = 0 := by
    have h1 := inner_apply_eq_sum_repr hn hT v
    have h2 := inner_self_eq_sum_repr e v
    simp only [sub_mul, Finset.sum_sub_distrib, ← Finset.mul_sum]
    rw [← h2, ← h1, heq]; ring
  have hnn : ∀ j ∈ (univ : Finset (Fin n)), 0 ≤ (μ - hT.eigenvalues hn j) * (e.repr v j) ^ 2 := by
    intro j _
    by_cases hji : j < i
    · rw [hv j hji]; simp
    · push Not at hji
      exact mul_nonneg (sub_nonneg.mpr (hT.eigenvalues_antitone hn hji)) (sq_nonneg _)
  have hz := (Finset.sum_eq_zero_iff_of_nonneg hnn).mp hsum
  have hcoef : ∀ j, e.repr v j * hT.eigenvalues hn j = μ * e.repr v j := by
    intro j
    rcases mul_eq_zero.mp (hz j (mem_univ _)) with h | h
    · have : hT.eigenvalues hn j = μ := by linarith
      rw [this, mul_comm]
    · rw [pow_eq_zero_iff two_ne_zero] at h
      rw [h]; ring
  conv_lhs => rw [← e.sum_repr v]
  conv_rhs => rw [← e.sum_repr v]
  rw [map_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_smul, hT.apply_eigenvectorBasis hn j, smul_smul, smul_smul]
  simp only [RCLike.ofReal_real_eq_id, id]
  rw [hcoef j]

end Rayleigh

section Spans

omit [FiniteDimensional ℝ E] in
/-- Coordinates of a vector in the span of some basis vectors vanish off those vectors. -/
lemma repr_eq_zero_of_mem_span (e : OrthonormalBasis (Fin n) ℝ E) (p : Fin n → Prop)
    {v : E} (hv : v ∈ span ℝ (Set.range fun j : {j // p j} => e j)) (k : Fin n) (hk : ¬ p k) :
    e.repr v k = 0 := by
  rw [OrthonormalBasis.repr_apply_apply]
  have hle : span ℝ (Set.range fun j : {j // p j} => e j) ≤ LinearMap.ker (innerₛₗ ℝ (e k)) := by
    rw [span_le]
    rintro _ ⟨j, rfl⟩
    rw [SetLike.mem_coe, LinearMap.mem_ker]
    have hne : (k : Fin n) ≠ j := fun h => hk (h ▸ j.2)
    exact e.orthonormal.2 hne
  exact LinearMap.mem_ker.mp (hle hv)

omit [FiniteDimensional ℝ E] in
lemma finrank_span_subtype (e : OrthonormalBasis (Fin n) ℝ E) (p : Fin n → Prop) [DecidablePred p] :
    finrank ℝ (span ℝ (Set.range fun j : {j // p j} => e j)) = Fintype.card {j // p j} :=
  finrank_span_eq_card (e.orthonormal.linearIndependent.comp _ Subtype.val_injective)

/-- Two subspaces whose dimensions add up to more than `finrank E` share a nonzero vector. -/
lemma exists_ne_zero_mem_inf (V W : Submodule ℝ E) (h : finrank ℝ E < finrank ℝ V + finrank ℝ W) :
    ∃ v, v ∈ V ∧ v ∈ W ∧ v ≠ 0 := by
  have h1 := Submodule.finrank_sup_add_finrank_inf_eq V W
  have h2 := Submodule.finrank_le (V ⊔ W)
  have hpos : 0 < finrank ℝ ↥(V ⊓ W) := by omega
  have hne : V ⊓ W ≠ ⊥ := fun hbot => by rw [hbot, finrank_bot] at hpos; exact lt_irrefl _ hpos
  obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  exact ⟨v, (Submodule.mem_inf.mp hv).1, (Submodule.mem_inf.mp hv).2, hv0⟩

end Spans

variable {S T : E →ₗ[ℝ] E} (hS : S.IsSymmetric) (hT : T.IsSymmetric)

include hS hT in
/-- The common vector of the min–max argument. -/
lemma exists_minmax_vector (i : Fin n) :
    ∃ v, v ≠ 0 ∧ (∀ j, i < j → (hS.eigenvectorBasis hn).repr v j = 0) ∧
      (∀ j, j < i → (hT.eigenvectorBasis hn).repr v j = 0) := by
  classical
  set V := span ℝ (Set.range fun j : {j : Fin n // j ≤ i} => hS.eigenvectorBasis hn j)
  set W := span ℝ (Set.range fun j : {j : Fin n // i ≤ j} => hT.eigenvectorBasis hn j)
  have hV : finrank ℝ V = i.val + 1 := by
    rw [finrank_span_subtype, Fintype.card_subtype]
    rw [show (univ.filter fun j : Fin n => j ≤ i) = Finset.Iic i by ext; simp, Fin.card_Iic]
  have hW : finrank ℝ W = n - i.val := by
    rw [finrank_span_subtype, Fintype.card_subtype]
    rw [show (univ.filter fun j : Fin n => i ≤ j) = Finset.Ici i by ext; simp, Fin.card_Ici]
  have hlt : finrank ℝ E < finrank ℝ V + finrank ℝ W := by
    rw [hV, hW, hn]; have := i.isLt; omega
  obtain ⟨v, hvV, hvW, hv0⟩ := exists_ne_zero_mem_inf V W hlt
  refine ⟨v, hv0, fun j hj => ?_, fun j hj => ?_⟩
  · exact repr_eq_zero_of_mem_span _ (fun j => j ≤ i) hvV j (not_le.mpr hj)
  · exact repr_eq_zero_of_mem_span _ (fun j => i ≤ j) hvW j (not_le.mpr hj)

include hS hT in
/-- **Shifted Weyl monotonicity.** If `⟪S v, v⟫ ≤ ⟪T v, v⟫ + c ⟪v, v⟫` for all `v`, then
`λ_i(S) ≤ λ_i(T) + c` for all `i`. -/
theorem eigenvalues_le_add_of_inner_le (c : ℝ) (hle : ∀ v, ⟪S v, v⟫ ≤ ⟪T v, v⟫ + c * ⟪v, v⟫)
    (i : Fin n) : hS.eigenvalues hn i ≤ hT.eigenvalues hn i + c := by
  obtain ⟨v, hv0, hvS, hvT⟩ := exists_minmax_vector hn hS hT i
  have h1 := le_inner_of_repr_eq_zero_gt hn hS i v hvS
  have h2 := inner_le_of_repr_eq_zero_lt hn hT i v hvT
  have hpos : 0 < ⟪v, v⟫ := real_inner_self_pos.mpr hv0
  have := (hle v)
  by_contra h
  push Not at h
  have : (hT.eigenvalues hn i + c) * ⟪v, v⟫ < hS.eigenvalues hn i * ⟪v, v⟫ :=
    mul_lt_mul_of_pos_right h hpos
  nlinarith

include hS hT in
/-- **Weyl monotonicity.** If `⟪S v, v⟫ ≤ ⟪T v, v⟫` for all `v`, then `λ_i(S) ≤ λ_i(T)` for all `i`. -/
theorem eigenvalues_le_of_inner_le (hle : ∀ v, ⟪S v, v⟫ ≤ ⟪T v, v⟫) (i : Fin n) :
    hS.eigenvalues hn i ≤ hT.eigenvalues hn i := by
  have := eigenvalues_le_add_of_inner_le hn hS hT 0 (fun v => by simpa using hle v) i
  simpa using this

include hS hT in
/-- **Strict Weyl monotonicity.** If `⟪S v, v⟫ ≤ ⟪T v, v⟫` for all `v`, with strict inequality on
every eigenvector of `T`, then `λ_i(S) < λ_i(T)` for all `i`. -/
theorem eigenvalues_lt_of_inner_lt (hle : ∀ v, ⟪S v, v⟫ ≤ ⟪T v, v⟫)
    (hstrict : ∀ (μ : ℝ) (v : E), v ≠ 0 → T v = μ • v → ⟪S v, v⟫ < ⟪T v, v⟫) (i : Fin n) :
    hS.eigenvalues hn i < hT.eigenvalues hn i := by
  obtain ⟨v, hv0, hvS, hvT⟩ := exists_minmax_vector hn hS hT i
  have h1 := le_inner_of_repr_eq_zero_gt hn hS i v hvS
  have h2 := inner_le_of_repr_eq_zero_lt hn hT i v hvT
  have hpos : 0 < ⟪v, v⟫ := real_inner_self_pos.mpr hv0
  have hweak := eigenvalues_le_of_inner_le hn hS hT hle i
  by_contra hnot
  have heqμ : hS.eigenvalues hn i = hT.eigenvalues hn i := le_antisymm hweak (not_lt.mp hnot)
  have hTv : ⟪T v, v⟫ = hT.eigenvalues hn i * ⟪v, v⟫ := by
    have := hle v
    rw [heqμ] at h1
    linarith
  have hST : ⟪S v, v⟫ = ⟪T v, v⟫ := by
    have := hle v
    rw [heqμ] at h1
    linarith
  have heig := apply_eq_of_inner_eq hn hT i v hvT hTv
  have := hstrict _ v hv0 heig
  linarith

end DiscreteSturm
