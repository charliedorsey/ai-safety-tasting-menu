import AsterFiniteEndpointEscape
import Mathlib.Data.Fin.Tuple.Basic

/-!
# An executable rational nonroot selector

A search over `Fin (n + 1)` is intrinsically finite. A degree-`n`
characteristic polynomial guarantees a successful search when the step
is nonzero. Correctness is proved separately from computation.
-/

namespace AsterCertificate

open Polynomial

/-- The `i`-th point in a rational arithmetic progression. -/
def rationalGrid (a δ : ℚ) (i : ℕ) : ℚ :=
  a + i * δ

/-- Search at most `n + 1` rational grid points for a nonzero continuant.
This uses the computable finite search `Fin.find?`, not classical choice. -/
def findJacobiNonroot? (d b : ℕ → ℚ) (n : ℕ) (a δ : ℚ) :
    Option (Fin (n + 1)) :=
  Fin.find? (fun i => decide (qCont d b (rationalGrid a δ i) n ≠ 0))

/-- A returned grid index certifies a genuinely nonzero rational continuant. -/
theorem findJacobiNonroot?_sound
    (d b : ℕ → ℚ) (n : ℕ) (a δ : ℚ) (i : Fin (n + 1))
    (hi : findJacobiNonroot? d b n a δ = some i) :
    qCont d b (rationalGrid a δ i) n ≠ 0 := by
  have hmem :
      i ∈ Fin.find? (fun j : Fin (n + 1) =>
        decide (qCont d b (rationalGrid a δ j) n ≠ 0)) := by
    change i ∈ findJacobiNonroot? d b n a δ
    rw [hi]
    simp
  have htest := (Fin.mem_find?_iff.mp hmem).1
  simpa only [decide_eq_true_eq] using htest

/-- Nonzero steps ensure that a Jacobi continuant has a nonroot
among the first `n + 1` rational grid points. -/
theorem jacobi_grid_has_nonroot
    (d b : ℕ → ℚ) (n : ℕ) (a δ : ℚ) (hδ : δ ≠ 0) :
    ∃ i : Fin (n + 1),
      qCont d b (rationalGrid a δ i) n ≠ 0 := by
  let p : ℝ[X] := JacobiSpectral.jpoly
    (fun i => (d i : ℝ)) (fun i => (b i : ℝ)) n
  have hp : p ≠ 0 := by
    exact (JacobiSpectral.jpoly_monic
      (fun i => (d i : ℝ)) (fun i => (b i : ℝ)) n).ne_zero
  have hdeg : p.natDegree ≤ n := by
    dsimp [p]
    rw [JacobiSpectral.natDegree_jpoly]
  obtain ⟨i, hi⟩ :=
    finite_rational_grid_escape p n a δ hp hdeg hδ
  refine ⟨i, ?_⟩
  intro hz
  apply hi
  calc
    p.eval ((rationalGrid a δ i : ℚ) : ℝ) =
        (qCont d b (rationalGrid a δ i) n : ℝ) := by
          exact (qCont_cast d b (rationalGrid a δ i) n).symm
    _ = 0 := by exact_mod_cast hz

/-- The executable selector always succeeds with a correct nonroot.
The existence theorem is used only in this proof, not in the program. -/
theorem findJacobiNonroot?_complete
    (d b : ℕ → ℚ) (n : ℕ) (a δ : ℚ) (hδ : δ ≠ 0) :
    ∃ i : Fin (n + 1),
      findJacobiNonroot? d b n a δ = some i ∧
      qCont d b (rationalGrid a δ i) n ≠ 0 := by
  obtain ⟨i, hi⟩ := jacobi_grid_has_nonroot d b n a δ hδ
  have hExists : ∃ j : Fin (n + 1),
      decide (qCont d b (rationalGrid a δ j) n ≠ 0) := by
    exact ⟨i, by simp [hi]⟩
  let j : Fin (n + 1) :=
    Fin.find (fun k => decide (qCont d b (rationalGrid a δ k) n ≠ 0))
      hExists
  have hj : findJacobiNonroot? d b n a δ = some j := by
    exact Fin.find?_eq_some_find_of_exists hExists
  exact ⟨j, hj, findJacobiNonroot?_sound d b n a δ j hj⟩

#print axioms findJacobiNonroot?_sound
#print axioms jacobi_grid_has_nonroot
#print axioms findJacobiNonroot?_complete

end AsterCertificate
