import AsterCertificate

open JacobiSpectral DiscreteSturm
namespace AsterCertificate

/-- A complete finite witness: exclusion around the target plus a nearby interval
    certified to contain at least one eigenvalue. -/
structure NearestWitness where
  gap : GapWitness
  nearLeft : ℚ
  nearRight : ℚ

/-- Every assumption used by the spectral theorem is checked from rational input. -/
def checkUnreduced (b : ℕ → ℚ) (n : ℕ) : Bool :=
  decide (0 < n) &&
  (List.range n).all (fun k => if k + 1 < n then decide (b k ≠ 0) else true)

def checkNearest (d b : ℕ → ℚ) (n : ℕ) (τ : ℚ)
    (w : NearestWitness) : Bool :=
  checkUnreduced b n &&
  checkGap d b n τ w.gap &&
  decide (w.nearLeft < w.nearRight) &&
  decide (qCount d b n w.nearLeft > qCount d b n w.nearRight)

theorem checkUnreduced_sound (b : ℕ → ℚ) (n : ℕ)
    (h : checkUnreduced b n = true) :
    0 < n ∧ ∀ k, k + 1 < n → b k ≠ 0 := by
  have hs : (0 < n) ∧ (List.range n).all
    (fun k => if k + 1 < n then decide (b k ≠ 0) else true) = true := by
    simpa [checkUnreduced, Bool.and_eq_true, decide_eq_true_eq] using h
  refine ⟨hs.1, ?_⟩
  intro k hk
  have kmem : k ∈ List.range n := by simp; omega
  have one := (List.all_eq_true.mp hs.2) k kmem
  simp [hk] at one
  exact one

theorem checkNearest_sound (d b : ℕ → ℚ) (n : ℕ) (τ : ℚ)
    (w : NearestWitness) (h : checkNearest d b n τ w = true) :
    (∀ i : Fin n, ¬ ((w.gap.left : ℝ) < jacobiEig
      (fun j => (d j : ℝ)) (fun j => (b j : ℝ)) n i ∧
      jacobiEig (fun j => (d j : ℝ)) (fun j => (b j : ℝ)) n i ≤ (w.gap.right : ℝ))) ∧
    (∃ i : Fin n, (w.nearLeft : ℝ) < jacobiEig
      (fun j => (d j : ℝ)) (fun j => (b j : ℝ)) n i ∧
      jacobiEig (fun j => (d j : ℝ)) (fun j => (b j : ℝ)) n i ≤ (w.nearRight : ℝ)) := by
  have hv : ((checkUnreduced b n = true ∧
      checkGap d b n τ w.gap = true) ∧
      w.nearLeft < w.nearRight) ∧
      qCount d b n w.nearLeft > qCount d b n w.nearRight := by
    simpa only [checkNearest, Bool.and_eq_true, decide_eq_true_eq] using h
  obtain ⟨hn, hb⟩ := checkUnreduced_sound b n hv.1.1.1
  refine ⟨checkGap_no_spectrum d b n hn hb τ w.gap hv.1.1.2, ?_⟩
  cases n with
  | zero => omega
  | succ m =>
    have hbR : ∀ k < m, (b k : ℝ) ≠ 0 := by
      intro k hk
      exact_mod_cast (hb k (by omega))
    have hle : (w.nearLeft : ℝ) ≤ (w.nearRight : ℝ) := by
      exact_mod_cast (le_of_lt hv.1.2)
    have hc := DiscreteSturm.card_Ioc_eq_sturm
      (d := fun i => (d i : ℝ)) (b := fun i => (b i : ℝ))
      m hbR hle
    rw [← qCount_real_sturm, ← qCount_real_sturm] at hc
    have hgap : qCount d b (m + 1) w.nearRight < qCount d b (m + 1) w.nearLeft := hv.2
    have hpos : 0 < (Finset.univ.filter fun i : Fin (m + 1) =>
      (w.nearLeft : ℝ) < jacobiEig
        (fun j => (d j : ℝ)) (fun j => (b j : ℝ)) (m + 1) i ∧
      jacobiEig (fun j => (d j : ℝ)) (fun j => (b j : ℝ)) (m + 1) i ≤ (w.nearRight : ℝ)).card := by
      rw [hc]
      omega
    obtain ⟨i, hi⟩ := Finset.card_pos.mp hpos
    exact ⟨i, (Finset.mem_filter.mp hi).2⟩

/-- Sound certified two-sided bounds on the distance to the finite eigenvalue list.
    These bounds use no numerical approximation or eigenvalue computation. -/
theorem checkNearest_distance_bounds (d b : ℕ → ℚ) (n : ℕ) (τ : ℚ)
    (w : NearestWitness) (h : checkNearest d b n τ w = true) :
    (∀ i : Fin n,
       min ((τ : ℝ) - (w.gap.left : ℝ))
           ((w.gap.right : ℝ) - (τ : ℝ)) ≤
       |jacobiEig (fun j => (d j : ℝ)) (fun j => (b j : ℝ)) n i - (τ : ℝ)|) ∧
    (∃ i : Fin n,
       |jacobiEig (fun j => (d j : ℝ)) (fun j => (b j : ℝ)) n i - (τ : ℝ)| ≤
       max (|((w.nearLeft : ℝ) - (τ : ℝ))|)
           (|((w.nearRight : ℝ) - (τ : ℝ))|)) := by
  obtain ⟨hexclude, ⟨i, hinear⟩⟩ := checkNearest_sound d b n τ w h
  constructor
  · intro j
    let e := jacobiEig (fun k => (d k : ℝ)) (fun k => (b k : ℝ)) n j
    by_cases hl : e ≤ (w.gap.left : ℝ)
    · have hs : (τ : ℝ) - (w.gap.left : ℝ) ≤ (τ : ℝ) - e := by dsimp [e] at *; linarith
      have ha : (τ : ℝ) - e ≤ |e - (τ : ℝ)| := by
        rw [abs_sub_comm]
        exact le_abs_self _
      exact le_trans (le_trans (min_le_left _ _) hs) ha
    · have he : (w.gap.left : ℝ) < e := lt_of_not_ge hl
      have hr : (w.gap.right : ℝ) < e := by
        by_contra hnot
        exact (hexclude j) ⟨he, le_of_not_gt hnot⟩
      have hs : (w.gap.right : ℝ) - (τ : ℝ) ≤ e - (τ : ℝ) := by dsimp [e] at *; linarith
      exact le_trans (le_trans (min_le_right _ _) hs) (le_abs_self _)
  · refine ⟨i, ?_⟩
    let e := jacobiEig (fun k => (d k : ℝ)) (fun k => (b k : ℝ)) n i
    have hleft : (w.nearLeft : ℝ) < e := hinear.1
    have hright : e ≤ (w.nearRight : ℝ) := hinear.2
    have hal : - |(w.nearLeft : ℝ) - (τ : ℝ)| ≤ e - (τ : ℝ) := by
      have hh := neg_le_abs ((w.nearLeft : ℝ) - (τ : ℝ))
      linarith
    have har : e - (τ : ℝ) ≤ |(w.nearRight : ℝ) - (τ : ℝ)| := by
      have hh := le_abs_self ((w.nearRight : ℝ) - (τ : ℝ))
      linarith
    apply abs_le.mpr
    constructor
    · exact le_trans (neg_le_neg (le_max_left _ _)) hal
    · exact le_trans har (le_max_right _ _)

#print axioms checkNearest_distance_bounds

def toyNearest : NearestWitness :=
  ⟨toyWitness, 141 / 100, 142 / 100⟩

#eval checkNearest toyDiag toyHop 3 (7 / 5) toyNearest

#print axioms checkUnreduced_sound
#print axioms checkNearest_sound
end AsterCertificate
