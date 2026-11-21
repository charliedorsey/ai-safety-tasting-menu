import AsterNearest
import Mathlib.Algebra.Polynomial.Roots

/-!
# Finite rational endpoint escape

A polynomial of degree at most n cannot vanish at all n+1 distinct
rational grid points. The proof uses its root-count theorem, not a
search heuristic. It is the collision-avoidance primitive needed by
a rational Sturm-bisection certificate producer.
-/

namespace AsterCertificate

open Polynomial Finset

private def gridPoint (a δ : ℚ) (n : ℕ) (i : Fin (n + 1)) : ℚ :=
  a + (i.val : ℚ) * δ

private theorem gridPoint_injective (a δ : ℚ) (n : ℕ) (hδ : δ ≠ 0) :
    Function.Injective (fun i : Fin (n + 1) => (gridPoint a δ n i : ℝ)) := by
  intro i j hij
  have hδR : (δ : ℝ) ≠ 0 := by exact_mod_cast hδ
  have hmul : (i.val : ℝ) * (δ : ℝ) = (j.val : ℝ) * (δ : ℝ) := by
    dsimp [gridPoint] at hij
    norm_cast at hij ⊢
    exact add_left_cancel hij
  have hval : (i.val : ℝ) = (j.val : ℝ) := by
    exact (mul_right_cancel₀ hδR hmul)
  exact Fin.ext (by exact_mod_cast hval)

/-- A polynomial of degree at most n has a nonroot among any n+1
distinct points in a nondegenerate rational arithmetic progression. -/
theorem finite_rational_grid_escape
    (p : ℝ[X]) (n : ℕ) (a δ : ℚ)
    (hp : p ≠ 0) (hdeg : p.natDegree ≤ n) (hδ : δ ≠ 0) :
    ∃ i : Fin (n + 1), p.eval (gridPoint a δ n i : ℝ) ≠ 0 := by
  classical
  by_contra h
  push Not at h
  let f : Fin (n + 1) → ℝ := fun i => (gridPoint a δ n i : ℝ)
  let Z : Finset ℝ := Finset.univ.image f
  have hf : Function.Injective f := gridPoint_injective a δ n hδ
  have hroots : Z.val ⊆ p.roots := by
    intro x hx
    change x ∈ Finset.univ.image f at hx
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hx
    apply (Polynomial.mem_roots hp).mpr
    exact h i
  have hcard : Z.card = n + 1 := by
    rw [show Z = Finset.univ.image f by rfl,
      Finset.card_image_of_injective _ hf]
    simp
  have hbound := Polynomial.card_le_degree_of_subset_roots hroots
  omega

#print axioms finite_rational_grid_escape

end AsterCertificate
