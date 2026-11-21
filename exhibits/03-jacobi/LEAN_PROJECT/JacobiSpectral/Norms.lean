import JacobiSpectral.Chebyshev
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Topology.MetricSpace.HausdorffDistance

/-!
# `JacobiSpectral.Norms` — operator 2-norm, condition number and distance to the spectrum

Generic for any real Hermitian (= symmetric) matrix `A` of size `n + 1`, using Mathlib's
spectral theorem (`IsHermitian.eigenvalues`, `eigenvectorBasis`) and Mathlib's induced
`2 → 2` operator norm (`Matrix.Norms.L2Operator`). For a shift `τ`:

* `opNorm_sub_smul_one`: `‖A − τ I‖₂ = max_i |λ_i − τ|`;
* `opNorm_inv_sub_smul_one`: if `τ` is not an eigenvalue, `‖(A − τ I)⁻¹‖₂ = (min_i |λ_i − τ|)⁻¹`;
* `gapMin_eq_infDist`: `min_i |λ_i − τ| = dist(τ, spec A)`;
* `inv_opNorm_inv_eq_infDist`: **`‖(A − τ I)⁻¹‖₂⁻¹ = dist(τ, spec A)`** (smallest singular value
  of `A − τ I` is the distance from `τ` to the spectrum);
* `condNumber_eq`: `‖A − τI‖₂ ‖(A − τI)⁻¹‖₂ = max_i |λ_i − τ| / min_i |λ_i − τ|`.

Jacobi consumers: `jacobi_inv_opNorm_eq_infDist`, and for the constant chain
`spectrum_jacobi_const` (explicit spectrum `{c + 2β cos(kπ/(n+1))}`).

This generalizes `ShiftedKMS.sigmaMax_eq_opNorm`, `sigmaMin_eq_inv_opNorm_inv`,
`kappa_eq_operator_twoNorm_conditionNumber`, `sigmaMin_eq_infDist` (stated there for one matrix).
-/

open Matrix Finset
open scoped Matrix.Norms.L2Operator RealInnerProductSpace

namespace JacobiSpectral

section Herm

variable {n : ℕ} {A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ} (hA : A.IsHermitian) (τ : ℝ)

/-- `max_i |λ_i − τ|`. -/
noncomputable def gapMax : ℝ := univ.sup' univ_nonempty fun i => |hA.eigenvalues i - τ|

/-- `min_i |λ_i − τ|`. -/
noncomputable def gapMin : ℝ := univ.inf' univ_nonempty fun i => |hA.eigenvalues i - τ|

lemma gap_bounds (i : Fin (n + 1)) :
    gapMin hA τ ≤ |hA.eigenvalues i - τ| ∧ |hA.eigenvalues i - τ| ≤ gapMax hA τ :=
  ⟨inf'_le _ (mem_univ i), le_sup' (fun i => |hA.eigenvalues i - τ|) (mem_univ i)⟩

lemma exists_gapMax : ∃ i, |hA.eigenvalues i - τ| = gapMax hA τ := by
  obtain ⟨i, -, hi⟩ := exists_mem_eq_sup' univ_nonempty fun i => |hA.eigenvalues i - τ|
  exact ⟨i, hi.symm⟩

lemma exists_gapMin : ∃ i, |hA.eigenvalues i - τ| = gapMin hA τ := by
  obtain ⟨i, -, hi⟩ := exists_mem_eq_inf' univ_nonempty fun i => |hA.eigenvalues i - τ|
  exact ⟨i, hi.symm⟩

lemma gapMin_nonneg : 0 ≤ gapMin hA τ := by
  obtain ⟨i, hi⟩ := exists_gapMin hA τ; rw [← hi]; exact abs_nonneg _

omit hA in
lemma isHermitian_sub_smul_one (hA : A.IsHermitian) (τ : ℝ) :
    (A - τ • (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)).IsHermitian :=
  hA.sub (by rw [IsHermitian, conjTranspose_smul, conjTranspose_one, star_trivial])

/-- The shifted operator on Euclidean space. -/
noncomputable abbrev shiftOp : EuclideanSpace ℝ (Fin (n + 1)) →L[ℝ] EuclideanSpace ℝ (Fin (n + 1)) :=
  toEuclideanCLM (n := Fin (n + 1)) (𝕜 := ℝ) (A - τ • (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ))

lemma shiftOp_bas (i : Fin (n + 1)) :
    shiftOp (A := A) τ (hA.eigenvectorBasis i) = (hA.eigenvalues i - τ) • hA.eigenvectorBasis i := by
  apply WithLp.ofLp_injective
  rw [ofLp_toEuclideanCLM, WithLp.ofLp_smul, sub_mulVec, smul_mulVec, one_mulVec,
    hA.mulVec_eigenvectorBasis i, sub_smul]

lemma inner_bas_shiftOp (i : Fin (n + 1)) (x : EuclideanSpace ℝ (Fin (n + 1))) :
    ⟪hA.eigenvectorBasis i, shiftOp (A := A) τ x⟫ = (hA.eigenvalues i - τ) * ⟪hA.eigenvectorBasis i, x⟫ := by
  have hsym := (isSymmetric_toEuclideanLin_iff.mpr (isHermitian_sub_smul_one hA τ))
    (hA.eigenvectorBasis i) x
  have h1 : ⟪hA.eigenvectorBasis i, shiftOp (A := A) τ x⟫ =
      ⟪shiftOp (A := A) τ (hA.eigenvectorBasis i), x⟫ := hsym.symm
  rw [h1, shiftOp_bas, real_inner_smul_left]

lemma norm_sq_eq_sum (x : EuclideanSpace ℝ (Fin (n + 1))) :
    ‖x‖ ^ 2 = ∑ i, ⟪hA.eigenvectorBasis i, x⟫ ^ 2 := by
  rw [← (hA.eigenvectorBasis).repr.norm_map x, EuclideanSpace.real_norm_sq_eq]
  simp only [OrthonormalBasis.repr_apply_apply]

lemma norm_shiftOp_sq (x : EuclideanSpace ℝ (Fin (n + 1))) :
    ‖shiftOp (A := A) τ x‖ ^ 2 = ∑ i, (hA.eigenvalues i - τ) ^ 2 * ⟪hA.eigenvectorBasis i, x⟫ ^ 2 := by
  rw [norm_sq_eq_sum hA]
  refine sum_congr rfl fun i _ => ?_
  rw [inner_bas_shiftOp]; ring

lemma norm_shiftOp_le (x : EuclideanSpace ℝ (Fin (n + 1))) :
    ‖shiftOp (A := A) τ x‖ ≤ gapMax hA τ * ‖x‖ := by
  have hs : 0 ≤ gapMax hA τ := (abs_nonneg _).trans (gap_bounds hA τ 0).2
  rw [← abs_of_nonneg (norm_nonneg (shiftOp (A := A) τ x)),
    ← abs_of_nonneg (mul_nonneg hs (norm_nonneg x)), ← sq_le_sq, mul_pow, norm_shiftOp_sq hA,
    norm_sq_eq_sum hA x, mul_sum]
  refine sum_le_sum fun i _ => mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)
  rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (gap_bounds hA τ i).2 2

lemma le_norm_shiftOp (x : EuclideanSpace ℝ (Fin (n + 1))) :
    gapMin hA τ * ‖x‖ ≤ ‖shiftOp (A := A) τ x‖ := by
  have hs := gapMin_nonneg hA τ
  rw [← abs_of_nonneg (norm_nonneg (shiftOp (A := A) τ x)),
    ← abs_of_nonneg (mul_nonneg hs (norm_nonneg x)), ← sq_le_sq, mul_pow, norm_shiftOp_sq hA,
    norm_sq_eq_sum hA x, mul_sum]
  refine sum_le_sum fun i _ => mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)
  rw [← sq_abs (hA.eigenvalues i - τ)]; exact pow_le_pow_left₀ hs (gap_bounds hA τ i).1 2

lemma norm_shiftOp_bas (i : Fin (n + 1)) :
    ‖shiftOp (A := A) τ (hA.eigenvectorBasis i)‖ = |hA.eigenvalues i - τ| := by
  rw [shiftOp_bas, norm_smul, (hA.eigenvectorBasis).orthonormal.1 i, mul_one, Real.norm_eq_abs]

/-- **`‖A − τI‖₂ = max_i |λ_i − τ|`.** -/
theorem opNorm_sub_smul_one : ‖A - τ • (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)‖ = gapMax hA τ := by
  rw [← l2_opNorm_toEuclideanCLM]
  apply le_antisymm
  · exact (shiftOp (A := A) τ).opNorm_le_bound ((abs_nonneg _).trans (gap_bounds hA τ 0).2)
      (norm_shiftOp_le hA τ)
  · obtain ⟨i, hi⟩ := exists_gapMax hA τ
    rw [← hi, ← norm_shiftOp_bas hA τ]
    calc ‖shiftOp (A := A) τ (hA.eigenvectorBasis i)‖
        ≤ ‖shiftOp (A := A) τ‖ * ‖hA.eigenvectorBasis i‖ := (shiftOp (A := A) τ).le_opNorm _
      _ = ‖shiftOp (A := A) τ‖ := by rw [(hA.eigenvectorBasis).orthonormal.1 i, mul_one]

/-- `τ` is not an eigenvalue iff the gap is positive iff `A − τI` is invertible. -/
theorem gapMin_pos_iff : 0 < gapMin hA τ ↔ ∀ i, hA.eigenvalues i ≠ τ := by
  constructor
  · intro h i hi
    have := (gap_bounds hA τ i).1
    rw [hi, sub_self, abs_zero] at this; linarith
  · intro h
    obtain ⟨i, hi⟩ := exists_gapMin hA τ
    rw [← hi]; exact abs_pos.2 (sub_ne_zero.2 (h i))

/-- **`‖(A − τI)⁻¹‖₂ = (min_i |λ_i − τ|)⁻¹`** when `τ` is not an eigenvalue. -/
theorem opNorm_inv_sub_smul_one (hτ : ∀ i, hA.eigenvalues i ≠ τ) :
    ‖(A - τ • (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ))⁻¹‖ = (gapMin hA τ)⁻¹ := by
  set B := A - τ • (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) with hB
  have hpos := (gapMin_pos_iff hA τ).2 hτ
  -- `B` is injective, hence invertible
  have hinjB : ∀ x : EuclideanSpace ℝ (Fin (n + 1)), shiftOp (A := A) τ x = 0 → x = 0 := by
    intro x hx
    have := le_norm_shiftOp hA τ x
    rw [hx, norm_zero] at this
    have : ‖x‖ = 0 := le_antisymm (by nlinarith [norm_nonneg x]) (norm_nonneg x)
    exact norm_eq_zero.1 this
  have hdet : IsUnit B.det := by
    rw [isUnit_iff_ne_zero]
    intro h0
    obtain ⟨v, hv0, hv⟩ := (Matrix.exists_mulVec_eq_zero_iff (M := B)).2 h0
    apply hv0
    have := hinjB (WithLp.toLp 2 v) (by
      apply WithLp.ofLp_injective; rw [ofLp_toEuclideanCLM]; simpa using hv)
    simpa using congrArg WithLp.ofLp this
  set S := toEuclideanCLM (n := Fin (n + 1)) (𝕜 := ℝ) B⁻¹ with hS
  have hTS : ∀ y, shiftOp (A := A) τ (S y) = y := by
    intro y
    apply WithLp.ofLp_injective
    rw [ofLp_toEuclideanCLM, ofLp_toEuclideanCLM, mulVec_mulVec, mul_nonsing_inv _ hdet, one_mulVec]
  have hST : ∀ z, S (shiftOp (A := A) τ z) = z := by
    intro z
    apply WithLp.ofLp_injective
    rw [ofLp_toEuclideanCLM, ofLp_toEuclideanCLM, mulVec_mulVec, nonsing_inv_mul _ hdet, one_mulVec]
  rw [← l2_opNorm_toEuclideanCLM]
  apply le_antisymm
  · refine S.opNorm_le_bound (by positivity) fun y => ?_
    have := le_norm_shiftOp hA τ (S y)
    rw [hTS] at this
    rw [inv_mul_eq_div, le_div_iff₀ hpos, mul_comm]
    exact this
  · obtain ⟨i, hi⟩ := exists_gapMin hA τ
    have hev0 : hA.eigenvalues i - τ ≠ 0 := sub_ne_zero.2 (hτ i)
    have hSb : S (hA.eigenvectorBasis i) = (hA.eigenvalues i - τ)⁻¹ • hA.eigenvectorBasis i := by
      have h2 : shiftOp (A := A) τ ((hA.eigenvalues i - τ)⁻¹ • hA.eigenvectorBasis i) =
          hA.eigenvectorBasis i := by
        rw [map_smul, shiftOp_bas, smul_smul, inv_mul_cancel₀ hev0, one_smul]
      conv_lhs => rw [← h2]
      exact hST _
    calc (gapMin hA τ)⁻¹ = ‖S (hA.eigenvectorBasis i)‖ := by
          rw [hSb, norm_smul, (hA.eigenvectorBasis).orthonormal.1 i, mul_one, norm_inv,
            Real.norm_eq_abs, hi]
      _ ≤ ‖S‖ * ‖hA.eigenvectorBasis i‖ := S.le_opNorm _
      _ = ‖S‖ := by rw [(hA.eigenvectorBasis).orthonormal.1 i, mul_one]

/-- **Condition number**: `‖A − τI‖₂ ‖(A − τI)⁻¹‖₂ = max_i |λ_i − τ| / min_i |λ_i − τ|`. -/
theorem condNumber_eq (hτ : ∀ i, hA.eigenvalues i ≠ τ) :
    ‖A - τ • (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)‖ *
        ‖(A - τ • (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ))⁻¹‖ = gapMax hA τ / gapMin hA τ := by
  rw [opNorm_sub_smul_one, opNorm_inv_sub_smul_one hA τ hτ, div_eq_mul_inv]

/-- **The gap is the distance from `τ` to the spectrum.** -/
theorem gapMin_eq_infDist : gapMin hA τ = Metric.infDist τ (spectrum ℝ A) := by
  rw [hA.spectrum_real_eq_range_eigenvalues]
  have hne : (Set.range hA.eigenvalues).Nonempty := Set.range_nonempty _
  apply le_antisymm
  · rw [Metric.le_infDist hne]
    rintro _ ⟨i, rfl⟩
    rw [Real.dist_eq, abs_sub_comm]
    exact (gap_bounds hA τ i).1
  · obtain ⟨i, hi⟩ := exists_gapMin hA τ
    refine (Metric.infDist_le_dist_of_mem (Set.mem_range_self i)).trans (le_of_eq ?_)
    rw [Real.dist_eq, abs_sub_comm, hi]

omit hA in
/-- **Smallest singular value = distance to the spectrum**:
`‖(A − τI)⁻¹‖₂⁻¹ = dist(τ, spec A)` for `τ ∉ spec A`. -/
theorem inv_opNorm_inv_eq_infDist (hA : A.IsHermitian) (τ : ℝ) (hτ : τ ∉ spectrum ℝ A) :
    ‖(A - τ • (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ))⁻¹‖⁻¹ = Metric.infDist τ (spectrum ℝ A) := by
  have hτ' : ∀ i, hA.eigenvalues i ≠ τ := by
    intro i hi; apply hτ; rw [hA.spectrum_real_eq_range_eigenvalues]; exact ⟨i, hi⟩
  rw [opNorm_inv_sub_smul_one hA τ hτ', inv_inv, gapMin_eq_infDist]

end Herm

/-! ### Jacobi consumers -/

/-- The spectrum of a real Jacobi matrix is the set of its sorted eigenvalues. -/
theorem spectrum_jacobi (d b : ℕ → ℝ) (n : ℕ) :
    spectrum ℝ (jacobi d b n) = Set.range (jacobiEig d b n) := by
  rw [(jacobi_isHermitian d b n).spectrum_real_eq_range_eigenvalues]
  ext μ
  simp only [Set.mem_range, IsHermitian.eigenvalues, jacobiEig]
  constructor
  · rintro ⟨i, rfl⟩
    exact ⟨Fin.cast (Fintype.card_fin n) ((Fintype.equivOfCardEq (Fintype.card_fin _)).symm i), rfl⟩
  · rintro ⟨i, rfl⟩
    exact ⟨(Fintype.equivOfCardEq (Fintype.card_fin _)) (Fin.cast (Fintype.card_fin n).symm i),
      by simp⟩

/-- **Explicit spectrum of the constant (Dirichlet) chain**, `β > 0`. -/
theorem spectrum_jacobi_const (c β : ℝ) (hβ : 0 < β) (n : ℕ) :
    spectrum ℝ (jacobi (fun _ => c) (fun _ => β) n) =
      Set.range fun i : Fin n => c + 2 * β * Real.cos (((i : ℕ) + 1 : ℝ) * Real.pi / (n + 1)) := by
  rw [spectrum_jacobi]
  congr 1
  funext i
  exact jacobiEig_const c β hβ n i

/-- **Jacobi corollary**: `‖(J − τI)⁻¹‖₂⁻¹ = dist(τ, spec J)`. -/
theorem jacobi_inv_opNorm_eq_infDist (d b : ℕ → ℝ) (n : ℕ) (τ : ℝ)
    (hτ : τ ∉ spectrum ℝ (jacobi d b (n + 1))) :
    ‖(jacobi d b (n + 1) - τ • (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ))⁻¹‖⁻¹ =
      Metric.infDist τ (spectrum ℝ (jacobi d b (n + 1))) :=
  inv_opNorm_inv_eq_infDist (jacobi_isHermitian d b (n + 1)) τ hτ

end JacobiSpectral
