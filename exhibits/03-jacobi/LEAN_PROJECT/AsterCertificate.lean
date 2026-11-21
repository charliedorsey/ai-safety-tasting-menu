import DiscreteSturm.Examples
import Mathlib.Data.Rat.Cast.Order

open JacobiSpectral DiscreteSturm

namespace AsterCertificate

/-- A rational finite continuant at a rational test energy. -/
def qCont (d b : ℕ → ℚ) (x : ℚ) : ℕ → ℚ
  | 0 => 1
  | 1 => x - d 0
  | n + 2 => (x - d (n + 1)) * qCont d b x (n + 1) -
      (b n)^2 * qCont d b x n

def qCount (d b : ℕ → ℚ) (n : ℕ) (x : ℚ) : ℕ :=
  ((List.range (n + 1)).map (qCont d b x)).signVariations

theorem qCont_cast (d b : ℕ → ℚ) (x : ℚ) (n : ℕ) :
    (qCont d b x n : ℝ) =
      (jpoly (fun i => (d i : ℝ)) (fun i => (b i : ℝ)) n).eval (x : ℝ) := by
  induction n using Nat.twoStepInduction with
  | zero => simp [qCont]
  | one => simp [qCont, jpoly]
  | more n ih0 ih1 =>
      rw [qCont, jpoly_succ_succ, Polynomial.eval_sub, Polynomial.eval_mul]
      simp only [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C,
        Polynomial.eval_mul, Rat.cast_sub, Rat.cast_mul,
        Rat.cast_pow]
      rw [ih0, ih1]

theorem qCount_real_sturm (d b : ℕ → ℚ) (n : ℕ) (x : ℚ) :
    qCount d b n x =
      DiscreteSturm.sturmCount (fun i => (d i : ℝ)) (fun i => (b i : ℝ))
        n (x : ℝ) := by
  unfold qCount DiscreteSturm.sturmCount DiscreteSturm.sturmSeq
  rw [← List.signVariations_map (f := fun q : ℚ => (q : ℝ))
    (by intro q; simp [sign_apply])]
  rw [List.map_map]
  congr 1
  apply List.map_congr_left
  intro k hk
  exact qCont_cast d b x k

/-- A small independently checkable exclusion certificate:
    the two rational endpoints and the exact Sturm counts. -/
structure GapWitness where
  left : ℚ
  right : ℚ
  deriving Repr

/-- This checker uses only decidable rational comparisons and the rational recurrence. -/
def checkGap (d b : ℕ → ℚ) (n : ℕ) (τ : ℚ) (w : GapWitness) : Bool :=
  decide (w.left < τ) &&
  decide (τ < w.right) &&
  decide (qCount d b n w.left = qCount d b n w.right)

/-- Accepted certificates contain no eigenvalue in the surrounding open interval. -/
theorem checkGap_no_spectrum (d b : ℕ → ℚ) (n : ℕ)
    (hpos : 0 < n)
    (hb : ∀ k, k + 1 < n → b k ≠ 0)
    (τ : ℚ) (w : GapWitness)
    (h : checkGap d b n τ w = true) :
    ∀ i : Fin n, ¬ ((w.left : ℝ) < jacobiEig
      (fun j => (d j : ℝ)) (fun j => (b j : ℝ)) n i ∧
      jacobiEig (fun j => (d j : ℝ)) (fun j => (b j : ℝ)) n i ≤ (w.right : ℝ)) := by
  have hcases : (w.left < τ ∧ τ < w.right) ∧
      qCount d b n w.left = qCount d b n w.right := by
    simpa only [checkGap, Bool.and_eq_true, decide_eq_true_eq] using h
  have hle : (w.left : ℝ) ≤ (w.right : ℝ) := by
    exact_mod_cast (le_of_lt (lt_trans hcases.1.1 hcases.1.2))
  cases n with
  | zero => omega
  | succ m =>
    have hbR : ∀ k < m, (b k : ℝ) ≠ 0 := by
      intro k hk
      exact_mod_cast (hb k (by omega))
    have hcard := DiscreteSturm.card_Ioc_eq_sturm
      (d := fun i => (d i : ℝ)) (b := fun i => (b i : ℝ))
      m hbR hle
    rw [← qCount_real_sturm, ← qCount_real_sturm, hcases.2] at hcard
    simp only [Nat.sub_self] at hcard
    intro i hi
    have hmem : i ∈ (Finset.univ.filter fun i : Fin (m + 1) =>
      (w.left : ℝ) < jacobiEig
        (fun j => (d j : ℝ)) (fun j => (b j : ℝ)) (m + 1) i ∧
      jacobiEig (fun j => (d j : ℝ)) (fun j => (b j : ℝ)) (m + 1) i ≤ (w.right : ℝ)) := by
      simp [hi]
    have : 0 < (Finset.univ.filter fun i : Fin (m + 1) =>
      (w.left : ℝ) < jacobiEig
        (fun j => (d j : ℝ)) (fun j => (b j : ℝ)) (m + 1) i ∧
      jacobiEig (fun j => (d j : ℝ)) (fun j => (b j : ℝ)) (m + 1) i ≤ (w.right : ℝ)).card :=
      Finset.card_pos.mpr ⟨i, hmem⟩
    omega

/-- Candidate 3-by-3 witness, pending kernel-checked acceptance example. -/
def toyDiag : ℕ → ℚ := fun _ => 0
def toyHop : ℕ → ℚ := fun _ => 1

def toyWitness : GapWitness :=
  ⟨139 / 100, 141 / 100⟩

/- Evaluation is a demonstration, not a kernel-checked acceptance proof. -/
#eval checkGap toyDiag toyHop 3 (7 / 5) toyWitness

#print axioms qCont_cast
#print axioms qCount_real_sturm
#print axioms checkGap_no_spectrum

end AsterCertificate
