import Mathlib.NumberTheory.DiophantineApproximation.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic.LinearCombination

/-!
# `PeriodicJacobi.Arith` — the arithmetic layer of the periodic phase law

* `implicit_quantization` (mechanism lemma, abstract form): if the eigenphases are `F⁻¹(πℤ)` and `F`
  is bi-Lipschitz with constants `L ≤ U`, then the distance from `θ_E` to the eigenphases is
  pinned between `π‖x‖/U` and `π‖x‖/L`, `x = F(θ_E)/π`. With `L = m − C`, `U = m + C` this is
  Theorem 2's reduction; the `O(1/m²)` correction is proportional to the distance itself.
* `inhom_floor` (Theorem 3(b), ε-form): for irrational `α`, **every** `β`, every `ε > 0` and
  every `M`, some `m > M` has `m · ‖mα + β‖ < 3/2 + ε`.
-/

namespace PeriodicJacobi

open Real
open scoped Real

/-- distance to the nearest integer -/
noncomputable def dZ (x : ℝ) : ℝ := |x - round x|

lemma dZ_le (x : ℝ) (j : ℤ) : dZ x ≤ |x - j| := round_le x j

/-! ### Mechanism lemma -/

theorem implicit_quantization {F : ℝ → ℝ} {L U : ℝ} (hL : 0 < L) (hU : 0 < U)
    (hlow : ∀ x y, L * |x - y| ≤ |F x - F y|) (hup : ∀ x y, |F x - F y| ≤ U * |x - y|)
    (θE : ℝ) :
    (∀ θ (k : ℤ), F θ = k * π → π * dZ (F θE / π) / U ≤ |θ - θE|) ∧
    (∀ θ, F θ = (round (F θE / π) : ℝ) * π → |θ - θE| ≤ π * dZ (F θE / π) / L) := by
  have hπ := Real.pi_pos
  have key : ∀ k : ℤ, |(k : ℝ) * π - F θE| = π * |F θE / π - k| := by
    intro k
    rw [show (k : ℝ) * π - F θE = -(π * (F θE / π - k)) by field_simp; ring, abs_neg, abs_mul,
      abs_of_pos hπ]
  constructor
  · intro θ k hk
    rw [div_le_iff₀ hU]
    calc π * dZ (F θE / π) ≤ π * |F θE / π - k| :=
          mul_le_mul_of_nonneg_left (dZ_le _ k) hπ.le
      _ = |F θ - F θE| := by rw [hk, key]
      _ ≤ U * |θ - θE| := hup θ θE
      _ = |θ - θE| * U := mul_comm _ _
  · intro θ hk
    rw [le_div_iff₀ hL]
    calc |θ - θE| * L = L * |θ - θE| := mul_comm _ _
      _ ≤ |F θ - F θE| := hlow θ θE
      _ = π * dZ (F θE / π) := by rw [hk, key]; rfl

/-! ### Theorem 3(b): universal quadratic floor -/

/-- Irrational `α` stays a fixed distance from the integers along any finite range of multipliers. -/
lemma exists_uniform_gap {α : ℝ} (hα : Irrational α) (Q : ℕ) :
    ∃ δ > 0, ∀ k : ℕ, 0 < k → k < Q → ∀ j : ℤ, δ ≤ |(k : ℝ) * α - j| := by
  induction Q with
  | zero => exact ⟨1, one_pos, fun k _ hk => absurd hk (Nat.not_lt_zero _)⟩
  | succ Q ih =>
    obtain ⟨δ, hδ, hδk⟩ := ih
    rcases Nat.eq_zero_or_pos Q with hQ | hQ
    · subst hQ; exact ⟨1, one_pos, fun k hk hk' => absurd hk' (by omega)⟩
    · have hirr : Irrational ((Q : ℝ) * α) := hα.natCast_mul (by omega)
      set g := |(Q : ℝ) * α - round ((Q : ℝ) * α)|
      have hg : 0 < g := abs_pos.mpr (sub_ne_zero.mpr (hirr.ne_int _))
      refine ⟨min δ g, lt_min hδ hg, fun k hk hkQ j => ?_⟩
      rcases Nat.lt_succ_iff_lt_or_eq.mp hkQ with h | h
      · exact (min_le_left _ _).trans (hδk k hk h j)
      · subst h; exact (min_le_right _ _).trans (round_le _ j)

/-- **Theorem 3(b), ε-form.** For irrational `α`, every real `β`, `ε > 0` and `M`, there is
`m > M` with `m · ‖mα + β‖ < 3/2 + ε`. (The paper proof gives `< 3/2` by a resonance split;
this shift argument avoids the split and is all that the exponent law uses.) -/
theorem inhom_floor {α : ℝ} (hα : Irrational α) (β : ℝ) {ε : ℝ} (hε : 0 < ε) (M : ℕ) :
    ∃ m : ℕ, M < m ∧ (m : ℝ) * dZ (m * α + β) < 3 / 2 + ε := by
  -- choose Q with 2(M+1)/Q < ε
  obtain ⟨Q, hQ⟩ := exists_nat_gt (2 * (M + 1) / ε)
  have hQpos : (0 : ℝ) < Q := lt_of_le_of_lt (by positivity) hQ
  have hQε : 2 * ((M : ℝ) + 1) / Q < ε := by
    rw [div_lt_iff₀ hQpos]; rw [div_lt_iff₀ hε] at hQ; linarith
  obtain ⟨δ, hδ, hgap⟩ := exists_uniform_gap hα Q
  obtain ⟨n₀, hn₀⟩ := exists_nat_gt (1 / δ)
  set n := max n₀ Q + 1 with hn
  have hnpos : 0 < n := Nat.succ_pos _
  have hnQ : (Q : ℝ) < n + 1 := by
    have : (Q : ℝ) ≤ (n : ℝ) := by exact_mod_cast (by omega : Q ≤ n)
    linarith
  have hnδ : 1 / ((n : ℝ) + 1) < δ := by
    have h1 : (n₀ : ℝ) ≤ (n : ℝ) := by exact_mod_cast (by omega : n₀ ≤ n)
    rw [div_lt_iff₀ (by positivity)]
    rw [div_lt_iff₀ hδ] at hn₀
    nlinarith
  -- Dirichlet in lowest terms
  obtain ⟨q, hq, hden⟩ := Real.exists_rat_abs_sub_le_and_den_le α hnpos
  set D : ℕ := q.den
  set N : ℤ := q.num
  have hD : (0 : ℝ) < D := Nat.cast_pos.mpr q.pos
  have hDα : |(D : ℝ) * α - N| ≤ 1 / ((n : ℝ) + 1) := by
    have : |α - q| = |(D : ℝ) * α - N| / D := by
      rw [eq_div_iff hD.ne', ← abs_of_pos hD, ← abs_mul, abs_of_pos hD]
      congr 1
      have hqc : (q : ℝ) = N / D := by rw [Rat.cast_def]
      rw [hqc]; field_simp
    rw [this, div_le_iff₀ hD] at hq
    calc |(D : ℝ) * α - N| ≤ 1 / ((n + 1) * D) * D := hq
      _ = 1 / ((n : ℝ) + 1) := by field_simp
  have hDQ : (Q : ℝ) ≤ D := by
    by_contra h
    push Not at h
    have := hgap D q.pos (by exact_mod_cast h) N
    linarith
  have hDn : (D : ℝ) ≤ n := by exact_mod_cast hden
  -- coprimality: a·N ≡ 1 (mod D)
  have hcop : Int.gcd N D = 1 := q.reduced
  have hbez : (1 : ℤ) = N * Int.gcdA N D + D * Int.gcdB N D := by
    have := Int.gcd_eq_gcd_ab N D; rw [hcop] at this; exact_mod_cast this
  -- shifted target
  set β' := β + ((M : ℝ) + 1) * α
  set s : ℤ := round (β' * D)
  set mz : ℤ := (-s * Int.gcdA N D) % (D : ℤ)
  have hmz0 : 0 ≤ mz := Int.emod_nonneg _ (by exact_mod_cast q.pos.ne')
  have hmzD : mz < D := Int.emod_lt_of_pos _ (by exact_mod_cast q.pos)
  -- mz·N + s is a multiple of D
  obtain ⟨w, hw⟩ : (D : ℤ) ∣ mz * N + s := by
    have h1 : (D : ℤ) ∣ (-s * Int.gcdA N D) - mz := by
      exact Int.ModEq.dvd (Int.mod_modEq _ _)
    obtain ⟨c, hc⟩ := h1
    refine ⟨s * Int.gcdB N D - c * N, ?_⟩
    have : mz = -s * Int.gcdA N D - D * c := by linarith
    rw [this]
    linear_combination s * hbez
  set m' : ℕ := mz.toNat
  have hm'z : (m' : ℤ) = mz := Int.toNat_of_nonneg hmz0
  have hm'D : (m' : ℝ) ≤ D - 1 := by
    have : (m' : ℤ) ≤ D - 1 := by omega
    exact_mod_cast this
  have hm'0 : (0 : ℝ) ≤ m' := Nat.cast_nonneg _
  refine ⟨m' + M + 1, by omega, ?_⟩
  -- the error estimate
  have hwR : (m' : ℝ) * N + s = D * w := by
    have : ((m' : ℤ) * N + s : ℤ) = D * w := by rw [hm'z]; exact hw
    exact_mod_cast this
  have hs : |β' * D - s| ≤ 1 / 2 := abs_sub_round _
  have hexp : ((m' + M + 1 : ℕ) : ℝ) * α + β - w =
      (m' : ℝ) / D * ((D : ℝ) * α - N) + (β' * D - s) / D := by
    have : (w : ℝ) = ((m' : ℝ) * N + s) / D := by rw [hwR]; field_simp
    rw [this]; simp only [β']; push_cast; field_simp; ring
  have herr : dZ (((m' + M + 1 : ℕ) : ℝ) * α + β) ≤ 1 / ((n : ℝ) + 1) + 1 / (2 * D) := by
    refine (dZ_le _ w).trans ?_
    rw [hexp]
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul, abs_div, abs_div, abs_of_nonneg hm'0, abs_of_pos hD]
    have hfrac : (m' : ℝ) / D ≤ 1 := by rw [div_le_one hD]; linarith
    have hA : (m' : ℝ) / D * |(D : ℝ) * α - N| ≤ 1 / ((n : ℝ) + 1) := by
      calc (m' : ℝ) / D * |(D : ℝ) * α - N| ≤ 1 * |(D : ℝ) * α - N| := by gcongr
        _ ≤ 1 / ((n : ℝ) + 1) := by rw [one_mul]; exact hDα
    have hB : |β' * D - s| / D ≤ 1 / (2 * D) := by
      rw [div_le_div_iff₀ hD (by positivity)]; nlinarith
    linarith
  -- final arithmetic
  have hmcast : ((m' + M + 1 : ℕ) : ℝ) = m' + M + 1 := by push_cast; ring
  rw [hmcast]
  rw [hmcast] at herr
  have hn1 : (0 : ℝ) < n + 1 := by positivity
  calc ((m' : ℝ) + M + 1) * dZ (((m' : ℝ) + M + 1) * α + β)
      ≤ ((D : ℝ) + M) * (1 / ((n : ℝ) + 1) + 1 / (2 * D)) :=
        mul_le_mul (by linarith) herr (abs_nonneg _) (by positivity)
    _ = D / ((n : ℝ) + 1) + 1 / 2 + M / ((n : ℝ) + 1) + M / (2 * D) := by field_simp <;> ring
    _ < 1 + 1 / 2 + ε := by
        have h1 : (D : ℝ) / ((n : ℝ) + 1) < 1 := by rw [div_lt_one hn1]; linarith
        have h2 : (M : ℝ) / ((n : ℝ) + 1) ≤ M / Q := by
          gcongr
        have h3 : (M : ℝ) / (2 * D) ≤ M / Q := by
          gcongr; nlinarith
        have h4 : (M : ℝ) / Q + M / Q < ε := by
          have : (M : ℝ) / Q + M / Q ≤ 2 * ((M : ℝ) + 1) / Q := by
            rw [← add_div]; gcongr; linarith
          linarith
        linarith
    _ = 3 / 2 + ε := by ring

end PeriodicJacobi
