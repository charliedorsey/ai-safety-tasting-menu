import JacobiSpectral.Norms
import DiscreteSturm
import JacobiDioph.Transfer

open JacobiSpectral

namespace JacobiBridge

/-- The physical `q` spectral sampling corresponds to the `(q-1)`-by-`(q-1)` matrix. -/
theorem spectrum_q_sub_one (c β : ℝ) (hβ : 0 < β)
    (q : ℕ) (hq : 2 ≤ q) :
    spectrum ℝ (jacobi (fun _ => c) (fun _ => β) (q - 1)) =
       Set.range (fun i : Fin (q - 1) =>
         c + 2 * β * Real.cos (((i : ℕ) + 1 : ℝ) * Real.pi / q)) := by
  have hq' : q - 1 + 1 = q := by omega
  have hden : ((q - 1 : ℕ) : ℝ) + 1 = (q : ℝ) := by exact_mod_cast hq'
  simpa only [hden] using (spectrum_jacobi_const c β hβ (q - 1))

/-- The unconditional analytic part of the bridge, with its exact matrix/numerical
resolvent correspondence exposed as the remaining host obligation. -/
theorem matrix_spikes_of_resolvent_equiv {c β α p : ℝ}
    (hβ : β ≠ 0) (hα : α ∈ Set.Ioo (0 : ℝ) 1)
    (hirr : Irrational α) (hp : 0 < p) (R : ℕ → ℝ)
    (hR : ∀ q : ℕ, 2 ≤ q → ∀ ε > 0,
      (1 / ε < R q ↔ ∃ k : ℕ, 0 < k ∧ k < q ∧
        |JacobiDioph.jacobiDisp c β (k / q) - JacobiDioph.jacobiDisp c β α| < ε)) :
    (∃ A > 0, ∃ᶠ q : ℕ in Filter.atTop, (q : ℝ) ^ p / A < R q) ↔
      LiouvilleWith p α := by
  exact JacobiDioph.jacobi_resolvent_spike_iff hβ hα hirr hp R hR

#print axioms spectrum_q_sub_one
#print axioms matrix_spikes_of_resolvent_equiv
end JacobiBridge
