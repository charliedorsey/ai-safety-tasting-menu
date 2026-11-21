import JacobiPhysical

open JacobiSpectral JacobiDioph
open scoped Matrix.Norms.L2Operator RealInnerProductSpace
namespace JacobiBridge

noncomputable def actualResolvent (c β α : ℝ) (q : ℕ) : ℝ :=
  ‖(jacobi (fun _ => c) (fun _ => β) (q - 1) -
    (jacobiDisp c β α) • (1 : Matrix (Fin (q - 1)) (Fin (q - 1)) ℝ))⁻¹‖

theorem resolvent_threshold_iff (c β α : ℝ) (hβ : β ≠ 0)
    (hα : α ∈ Set.Ioo (0 : ℝ) 1) (hirr : Irrational α) :
    ∀ q : ℕ, 2 ≤ q → ∀ ε > 0,
      (1 / ε < actualResolvent c β α q ↔
        ∃ k : ℕ, 0 < k ∧ k < q ∧
          |jacobiDisp c β (k / q) - jacobiDisp c β α| < ε) := by
  intro q hq ε hε
  let τ := jacobiDisp c β α
  let J := jacobi (fun _ => c) (fun _ => β) (q - 1)
  have hτ : τ ∉ spectrum ℝ J := target_off_spectrum c β α hβ hα hirr q hq
  have hn : q - 2 + 1 = q - 1 := by omega
  have hτ' : τ ∉ spectrum ℝ (jacobi (fun _ => c) (fun _ => β) (q - 2 + 1)) := by
    rw [hn]
    exact hτ
  have heq := jacobi_inv_opNorm_eq_infDist (fun _ => c) (fun _ => β) (q - 2) τ hτ' 
  have hclosed : IsClosed (spectrum ℝ J) := by
    rw [spectrum_q_any c β hβ q hq]
    exact Set.Finite.isClosed (Set.finite_range _)
  have hnonempty : (spectrum ℝ J).Nonempty := by
    rw [spectrum_q_any c β hβ q hq]
    exact ⟨_, ⟨⟨0, by omega⟩, rfl⟩⟩
  have hdist : 0 < Metric.infDist τ (spectrum ℝ J) :=
    (hclosed.notMem_iff_infDist_pos hnonempty).mp hτ
  have hnrm : actualResolvent c β α q = (Metric.infDist τ (spectrum ℝ J))⁻¹ := by
    have heq' : (actualResolvent c β α q)⁻¹ =
        Metric.infDist τ (spectrum ℝ J) := by
          have heq2 := heq
          rw [hn] at heq2
          simpa only [actualResolvent, τ, J] using heq2
    calc
      actualResolvent c β α q = ((actualResolvent c β α q)⁻¹)⁻¹ := by simp
      _ = _ := congrArg Inv.inv heq'
  rw [hnrm]
  have hdist' : Metric.infDist τ (spectrum ℝ J) < ε ↔
      ∃ i : Fin (q - 1),
        |jacobiDisp c β (((i : ℕ) + 1 : ℝ) / q) - τ| < ε := by
    rw [Metric.infDist_lt_iff]
    · rw [spectrum_q_any c β hβ q hq]
      simp only [Set.mem_range]
      constructor
      · rintro ⟨v, ⟨i, rfl⟩, hv⟩
        refine ⟨i, ?_⟩
        simpa [Real.dist_eq, abs_sub_comm] using hv
      · rintro ⟨i, hi⟩
        refine ⟨jacobiDisp c β (((i : ℕ) + 1 : ℝ) / q), ⟨i, rfl⟩, ?_⟩
        simpa [Real.dist_eq, abs_sub_comm] using hi
    · exact hnonempty
  rw [show (1 / ε : ℝ) = ε⁻¹ by ring]
  rw [inv_lt_inv₀ hε hdist]
  rw [hdist']
  constructor
  · rintro ⟨i, hi⟩
    refine ⟨(i : ℕ) + 1, by omega, by have := i.isLt; omega, ?_⟩
    simpa only [Nat.cast_add, Nat.cast_one] using hi
  · rintro ⟨k, hk, hkq, hi⟩
    let i : Fin (q - 1) := ⟨k - 1, by omega⟩
    refine ⟨i, ?_⟩
    have hv : (i : ℕ) + 1 = k := by dsimp [i]; omega
    have hvR : ((i : ℝ) + 1) / (q : ℝ) = (k : ℝ) / q := by
      have h : (i : ℝ) + 1 = (k : ℝ) := by exact_mod_cast hv
      rw [h]
    change |jacobiDisp c β (((i : ℝ) + 1) / q) - τ| < ε
    rw [hvR]
    exact hi

/-- Unconditional Jacobi matrix resolvent spikes are exactly Diophantine Liouville spikes. -/
theorem jacobi_matrix_liouville_unconditional
    {c β α p : ℝ} (hβ : β ≠ 0)
    (hα : α ∈ Set.Ioo (0 : ℝ) 1)
    (hirr : Irrational α) (hp : 0 < p) :
    (∃ A > 0, ∃ᶠ q : ℕ in Filter.atTop,
       (q : ℝ) ^ p / A < actualResolvent c β α q) ↔
      LiouvilleWith p α := by
  exact JacobiDioph.jacobi_resolvent_spike_iff hβ hα hirr hp
    (actualResolvent c β α)
    (resolvent_threshold_iff c β α hβ hα hirr)

#print axioms jacobi_matrix_liouville_unconditional
#print axioms resolvent_threshold_iff
end JacobiBridge
