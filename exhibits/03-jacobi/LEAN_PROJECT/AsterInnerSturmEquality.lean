import AsterActualSpectralRootExclusion
import AsterSturmAntitone

/-!
# The computed real root-free radius produces the exact inner Sturm gate.

This is the last bridge from Kestrelle's recurrence estimates into
the radial certificate's initial *empty* interval. The original
strict-greater Sturm convention is unchanged.
-/

namespace AsterCertificate

open JacobiSpectral Finset

/-- Exact rational Sturm equality across Kestrelle's computed radius.
The matrix hypotheses are precisely those of the original checker. -/
theorem continuant_inner_radius_sturm_equal
    (d b : ℕ → ℚ) (n : ℕ)
    (hn : 0 < n) (hb : ∀ k, k + 1 < n → b k ≠ 0)
    (τ : ℚ) (hq : qCont d b τ n ≠ 0) :
    qCount d b n (τ - continuantInnerRadius d b τ n) =
      qCount d b n (τ + continuantInnerRadius d b τ n) := by
  cases n with
  | zero => omega
  | succ m =>
    let r : ℚ := continuantInnerRadius d b τ (m + 1)
    have hr : 0 < r :=
      continuantInnerRadius_pos d b τ (m + 1) hq
    have hle : ((τ - r : ℚ) : ℝ) ≤ ((τ + r : ℚ) : ℝ) := by
      have h : τ - r ≤ τ + r := by linarith
      exact_mod_cast h
    have hbR : ∀ k < m, (b k : ℝ) ≠ 0 := by
      intro k hk
      exact_mod_cast (hb k (by omega))
    have hno (i : Fin (m + 1)) :
        ¬ (((τ - r : ℚ) : ℝ) <
            jacobiEig (fun k => (d k : ℝ)) (fun k => (b k : ℝ)) (m + 1) i ∧
          jacobiEig (fun k => (d k : ℝ)) (fun k => (b k : ℝ)) (m + 1) i ≤
            ((τ + r : ℚ) : ℝ)) := by
      rintro ⟨hl, hu⟩
      let t : ℝ :=
        jacobiEig (fun k => (d k : ℝ)) (fun k => (b k : ℝ)) (m + 1) i
      have ht : |t - (τ : ℝ)| ≤ (r : ℝ) := by
        apply abs_le.mpr
        constructor
        · have hlo : (τ : ℝ) - (r : ℝ) < t := by
            simpa only [Rat.cast_sub] using hl
          linarith
        · have hhi : t ≤ (τ : ℝ) + (r : ℝ) := by
            simpa only [Rat.cast_add] using hu
          linarith
      have hnon : (jpoly (fun k => (d k : ℝ))
        (fun k => (b k : ℝ)) (m + 1)).eval t ≠ 0 :=
        continuant_inner_radius_jpoly_ne_zero d b τ (m + 1) hq t ht
      have hzero : (jpoly (fun k => (d k : ℝ))
        (fun k => (b k : ℝ)) (m + 1)).eval t = 0 :=
        DiscreteSturm.eval_jpoly_jacobiEig (d := fun k => (d k : ℝ))
          (b := fun k => (b k : ℝ)) m hbR i
      exact hnon hzero
    have hzero :
        (univ.filter fun i : Fin (m + 1) =>
          ((τ - r : ℚ) : ℝ) <
            jacobiEig (fun k => (d k : ℝ)) (fun k => (b k : ℝ)) (m + 1) i ∧
          jacobiEig (fun k => (d k : ℝ)) (fun k => (b k : ℝ)) (m + 1) i ≤
            ((τ + r : ℚ) : ℝ)).card = 0 := by
      classical
      have hempty : (univ.filter fun i : Fin (m + 1) =>
        ((τ - r : ℚ) : ℝ) <
          jacobiEig (fun k => (d k : ℝ)) (fun k => (b k : ℝ)) (m + 1) i ∧
        jacobiEig (fun k => (d k : ℝ)) (fun k => (b k : ℝ)) (m + 1) i ≤
          ((τ + r : ℚ) : ℝ)) = ∅ := by
        ext i
        constructor
        · intro hi
          exact (hno i (Finset.mem_filter.mp hi).2).elim
        · intro hi
          simp at hi
      rw [hempty]
      rfl
    have hcount := DiscreteSturm.card_Ioc_eq_sturm
      (d := fun k => (d k : ℝ))
      (b := fun k => (b k : ℝ)) m hbR hle
    rw [← qCount_real_sturm d b (m + 1) (τ - r),
      ← qCount_real_sturm d b (m + 1) (τ + r), hzero] at hcount
    have hanti :
        qCount d b (m + 1) (τ + r) ≤ qCount d b (m + 1) (τ - r) := by
      apply qCount_antitone d b (m + 1) (by omega) hb
      linarith [hr]
    change qCount d b (m + 1) (τ - r) =
      qCount d b (m + 1) (τ + r)
    omega

#print axioms continuant_inner_radius_sturm_equal

end AsterCertificate
