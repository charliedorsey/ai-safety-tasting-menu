import AsterSturmAntitone
import Mathlib.Data.Nat.Find

/-!
# Exact, terminating outer-radius search

The program examines rational symmetric radii by integer increments,
testing the original rational Sturm count. Its termination proof uses
one actual Jacobi eigenvalue and the Archimedean property of the reals.

The bound for each *refinement* remains the explicit rational fuel
budget in AsterRadialFuel.
-/

namespace AsterCertificate

open JacobiSpectral Finset

/-- The kth integer-increment rational candidate outside an inner bound. -/
def outerRadiusCandidate (inner : ℚ) (k : ℕ) : ℚ :=
  inner + k + 1

theorem outerRadiusCandidate_gt (inner : ℚ) (k : ℕ) :
    inner < outerRadiusCandidate inner k := by
  unfold outerRadiusCandidate
  have hk : (0 : ℚ) ≤ k := by positivity
  linarith

/-- Every positive-dimensional unreduced Jacobi matrix has an eigenvalue
inside a sufficiently large rational symmetric interval. The count drop
is certified in the *original source representation*. -/
theorem exists_occupied_outer_candidate
    (d b : ℕ → ℚ) (n : ℕ)
    (hn : 0 < n) (hb : ∀ k, k + 1 < n → b k ≠ 0)
    (τ inner : ℚ) (hinner : 0 ≤ inner) :
    ∃ k : ℕ,
      qCount d b n (τ + outerRadiusCandidate inner k) <
        qCount d b n (τ - outerRadiusCandidate inner k) := by
  cases n with
  | zero => omega
  | succ m =>
    let eig : Fin (m + 1) → ℝ :=
      JacobiSpectral.jacobiEig
        (fun i => (d i : ℝ)) (fun i => (b i : ℝ)) (m + 1)
    obtain ⟨k, hk⟩ := exists_nat_gt (|eig 0 - (τ : ℝ)|)
    let R : ℚ := outerRadiusCandidate inner k
    have hR : |eig 0 - (τ : ℝ)| < (R : ℝ) := by
      have hr : (0 : ℝ) ≤ (inner : ℝ) := by exact_mod_cast hinner
      dsimp [R, outerRadiusCandidate]
      push_cast
      linarith
    have hinterval :
        (((τ - R) : ℚ) : ℝ) < eig 0 ∧
          eig 0 ≤ (((τ + R) : ℚ) : ℝ) := by
      have hpair := abs_lt.mp hR
      constructor
      · push_cast
        linarith
      · push_cast
        linarith
    have hbR : ∀ k < m, (b k : ℝ) ≠ 0 := by
      intro j hj
      exact_mod_cast (hb j (by omega))
    have horder : (τ - R : ℝ) ≤ (τ + R : ℝ) := by
      have h : 0 < R := lt_of_le_of_lt hinner
        (show inner < R from outerRadiusCandidate_gt inner k)
      have hh : (τ - R : ℚ) ≤ (τ + R : ℚ) := by linarith
      exact_mod_cast hh
    have hcount := DiscreteSturm.card_Ioc_eq_sturm
      (d := fun i => (d i : ℝ)) (b := fun i => (b i : ℝ))
      m hbR horder
    have hcardpos :
        0 < (Finset.univ.filter fun i : Fin (m + 1) =>
          ((τ - R : ℚ) : ℝ) < eig i ∧ eig i ≤ ((τ + R : ℚ) : ℝ)).card := by
      apply Finset.card_pos.mpr
      refine ⟨0, ?_⟩
      simpa only [Finset.mem_filter, Finset.mem_univ, true_and]
        using hinterval
    rw [← Rat.cast_sub, ← Rat.cast_add] at hcount
    rw [← qCount_real_sturm d b (m + 1) (τ - R),
        ← qCount_real_sturm d b (m + 1) (τ + R)] at hcount
    have hcardpos' :
        0 < (Finset.univ.filter fun i : Fin (m + 1) =>
          ((τ - R : ℚ) : ℝ) <
            jacobiEig (fun k => (d k : ℝ)) (fun k => (b k : ℝ)) (m + 1) i ∧
          jacobiEig (fun k => (d k : ℝ)) (fun k => (b k : ℝ)) (m + 1) i ≤
            ((τ + R : ℚ) : ℝ)).card := by
      simpa only [eig] using hcardpos
    refine ⟨k, ?_⟩
    change qCount d b (m + 1) (τ + R) <
      qCount d b (m + 1) (τ - R)
    omega

/-- The outer radius search is a total computable natural search:
the existence proof is erased; all tested predicates are decidable
from rational continuants and sign variations. -/
def outerSearchRadius
    (d b : ℕ → ℚ) (n : ℕ) (τ inner : ℚ)
    (hex : ∃ k : ℕ,
      qCount d b n (τ + outerRadiusCandidate inner k) <
        qCount d b n (τ - outerRadiusCandidate inner k)) : ℚ :=
  outerRadiusCandidate inner (Nat.find hex)

theorem outerSearchRadius_gt_inner
    (d b : ℕ → ℚ) (n : ℕ) (τ inner : ℚ)
    (hex : ∃ k : ℕ,
      qCount d b n (τ + outerRadiusCandidate inner k) <
        qCount d b n (τ - outerRadiusCandidate inner k)) :
    inner < outerSearchRadius d b n τ inner hex :=
  outerRadiusCandidate_gt inner (Nat.find hex)

theorem outerSearchRadius_occupied
    (d b : ℕ → ℚ) (n : ℕ) (τ inner : ℚ)
    (hex : ∃ k : ℕ,
      qCount d b n (τ + outerRadiusCandidate inner k) <
        qCount d b n (τ - outerRadiusCandidate inner k)) :
    qCount d b n (τ + outerSearchRadius d b n τ inner hex) <
      qCount d b n (τ - outerSearchRadius d b n τ inner hex) := by
  exact Nat.find_spec hex

#print axioms exists_occupied_outer_candidate
#print axioms outerSearchRadius_occupied

end AsterCertificate
