import IlystrenCheckedNonsingularConsumerR0001
import AsterRadialFuel

/-!
# Source-side requested-accuracy verification
This is intentionally a new checker predicate over witness DATA.
No spectral refinement is trusted. The caller-provided tolerance is tested.
-/

namespace AsterCertificate

def witnessLower (τ : ℚ) (w : NearestWitness) : ℚ :=
  min (τ - w.gap.left) (w.gap.right - τ)

def witnessUpper (τ : ℚ) (w : NearestWitness) : ℚ :=
  max |w.nearLeft - τ| |w.nearRight - τ|

def checkAccurate (d b : ℕ → ℚ) (n : ℕ)
    (τ ε : ℚ) (w : NearestWitness) : Bool :=
  checkNearest d b n τ w &&
  decide (0 < ε) &&
  decide (witnessUpper τ w - witnessLower τ w ≤ ε)

theorem checkAccurate_iff (d b : ℕ → ℚ) (n : ℕ)
    (τ ε : ℚ) (w : NearestWitness) :
    checkAccurate d b n τ ε w = true ↔
      checkNearest d b n τ w = true ∧
      0 < ε ∧ witnessUpper τ w - witnessLower τ w ≤ ε := by
  simp only [checkAccurate, Bool.and_eq_true, decide_eq_true_eq]
  tauto

theorem accurate_implies_spectral_bounds
    (d b : ℕ → ℚ) (n : ℕ) (τ ε : ℚ)
    (w : NearestWitness) (h : checkAccurate d b n τ ε w = true) :
    (∀ i : Fin n,
      (witnessLower τ w : ℝ) ≤
        |JacobiSpectral.jacobiEig
          (fun j => (d j : ℝ)) (fun j => (b j : ℝ)) n i - (τ : ℝ)|) ∧
    (∃ i : Fin n,
      |JacobiSpectral.jacobiEig
          (fun j => (d j : ℝ)) (fun j => (b j : ℝ)) n i - (τ : ℝ)| ≤
        (witnessUpper τ w : ℝ)) ∧
    witnessUpper τ w - witnessLower τ w ≤ ε := by
  obtain ⟨hcheck, _, hwidth⟩ := (checkAccurate_iff d b n τ ε w).mp h
  obtain ⟨hl, hu⟩ := checkNearest_distance_bounds d b n τ w hcheck
  exact ⟨by simpa only [witnessLower, Rat.cast_min, Rat.cast_sub] using hl,
    by simpa only [witnessUpper, Rat.cast_max, Rat.cast_abs, Rat.cast_sub] using hu,
    hwidth⟩

theorem radial_lower_eq {d b : ℕ → ℚ} {n : ℕ} {τ : ℚ}
    (w : RadialBracket d b n τ) :
    witnessLower τ w.toNearestWitness = w.inner := by
  simp [witnessLower, RadialBracket.toNearestWitness]

theorem radial_upper_eq {d b : ℕ → ℚ} {n : ℕ} {τ : ℚ}
    (w : RadialBracket d b n τ) :
    witnessUpper τ w.toNearestWitness = w.outer := by
  have houter : 0 < w.outer := lt_trans w.inner_pos w.ordered
  simp [witnessUpper, RadialBracket.toNearestWitness, abs_of_pos houter]

#print axioms checkAccurate_iff
#print axioms accurate_implies_spectral_bounds
#print axioms radial_lower_eq
#print axioms radial_upper_eq

end AsterCertificate
