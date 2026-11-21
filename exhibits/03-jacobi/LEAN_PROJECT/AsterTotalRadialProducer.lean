import AsterOuterSearch
import AsterKestrelleAccuracyAssembly
import AsterSingularMatrix

/-!
# Total exact Jacobi spectral-distance certificate producer

The certified algorithm uses only decidable rational arithmetic:
1. Detect exact target singularity.
2. Otherwise compute Kestrelle's positive source-native inner radius.
3. Search for the first occupied outer radius by rational Sturm counts;
   this search terminates by the already proved Jacobi eigenvalue existence.
4. Refine the radial bounds for an explicit rational finite fuel budget.
5. Return an independently accepted NearestWitness.

The outer search is well-founded but currently has no explicit *uniform
numerical bound* on the number of searched candidate radii.
-/

namespace AsterCertificate

/-- The checker data precondition is *equivalent to*, not stronger than,
the mathematical dimension and nonzero-hop hypotheses. -/
theorem checkUnreduced_complete
    (b : ℕ → ℚ) (n : ℕ)
    (hn : 0 < n) (hb : ∀ k, k + 1 < n → b k ≠ 0) :
    checkUnreduced b n = true := by
  simp only [checkUnreduced, Bool.and_eq_true, decide_eq_true_eq]
  constructor
  · exact hn
  · apply List.all_eq_true.mpr
    intro k hk
    by_cases hk' : k + 1 < n
    · simp [hk', hb k hk']
    · simp [hk']

/-- A certified positive inner radius and a terminating outer search,
assembled into the existing invariant-carrying radial bracket. -/
def totalInitialRadialBracket
    (d b : ℕ → ℚ) (n : ℕ) (τ : ℚ)
    (hn : 0 < n)
    (hb : ∀ k, k + 1 < n → b k ≠ 0)
    (hq : qCont d b τ n ≠ 0) :
    RadialBracket d b n τ := by
  let inner := continuantInnerRadius d b τ n
  have hinner : 0 ≤ inner :=
    (continuantInnerRadius_pos d b τ n hq).le
  let hex := exists_occupied_outer_candidate
    d b n hn hb τ inner hinner
  let outer := outerSearchRadius d b n τ inner hex
  exact kestrelleInitialRadialBracket d b n τ outer
    hn hb hq
    (outerSearchRadius_gt_inner d b n τ inner hex)
    (outerSearchRadius_occupied d b n τ inner hex)

/-- An actual total computation of one accepted rational certificate.
Only proof-only hypotheses are erased from the executable code. -/
def totalNonsingularWitness
    (d b : ℕ → ℚ) (n : ℕ) (τ ε : ℚ)
    (hn : 0 < n) (hb : ∀ k, k + 1 < n → b k ≠ 0)
    (hq : qCont d b τ n ≠ 0) : NearestWitness :=
  let w := totalInitialRadialBracket d b n τ hn hb hq
  (w.refine (radialFuel (w.outer - w.inner) ε)).toNearestWitness

/-- Both public-checker acceptance and the *actual* rational distance
enclosure width are certified at the requested precision. -/
theorem totalNonsingularWitness_correct
    (d b : ℕ → ℚ) (n : ℕ) (τ ε : ℚ)
    (hn : 0 < n) (hb : ∀ k, k + 1 < n → b k ≠ 0)
    (hq : qCont d b τ n ≠ 0)
    (hε : 0 < ε) :
    let v := totalNonsingularWitness d b n τ ε hn hb hq
    checkNearest d b n τ v = true ∧
      0 < v.gap.right - τ ∧
      v.nearRight - v.gap.right ≤ ε := by
  let w := totalInitialRadialBracket d b n τ hn hb hq
  let z := w.refine (radialFuel (w.outer - w.inner) ε)
  have hdata : checkUnreduced b n = true :=
    checkUnreduced_complete b n hn hb
  have hcheck : checkNearest d b n τ z.toNearestWitness = true :=
    RadialBracket.checkNearest_toNearestWitness z hdata
  have hwidth := radialFuel_refine_width w ε hε
  dsimp [totalNonsingularWitness]
  constructor
  · exact hcheck
  constructor
  · change 0 < (τ + z.inner) - τ
    simpa only [add_sub_cancel_left] using z.inner_pos
  · change (τ + z.outer) - (τ + z.inner) ≤ ε
    linarith [hwidth]

/-- A tiny, auditable sum type: exact singularity or a checked witness. -/
inductive NearestResult where
  | singular
  | certified (w : NearestWitness)

/-- Rational, terminating, two-branch nearest-spectrum producer. -/
def produceNearest
    (d b : ℕ → ℚ) (n : ℕ) (τ ε : ℚ)
    (hn : 0 < n) (hb : ∀ k, k + 1 < n → b k ≠ 0) :
    NearestResult :=
  if h : qCont d b τ n = 0 then
    .singular
  else
    .certified (totalNonsingularWitness d b n τ ε hn hb h)

/-- The producer's precise public contract.

The singular result is a zero determinant of the *actual shifted
Jacobi matrix*. The nonsingular result passes the independent
checker and provides a *positive* lower bound and a distance enclosure
of width at most epsilon. -/
theorem produceNearest_correct
    (d b : ℕ → ℚ) (n : ℕ) (τ ε : ℚ)
    (hn : 0 < n) (hb : ∀ k, k + 1 < n → b k ≠ 0)
    (hε : 0 < ε) :
    match produceNearest d b n τ ε hn hb with
    | .singular =>
        (Matrix.scalar (Fin n) (τ : ℝ) -
          JacobiSpectral.jacobi (fun k => (d k : ℝ))
            (fun k => (b k : ℝ)) n).det = 0
    | .certified v =>
        checkNearest d b n τ v = true ∧
          0 < v.gap.right - τ ∧
          v.nearRight - v.gap.right ≤ ε := by
  by_cases hq : qCont d b τ n = 0
  · have hs : checkSingular d b n τ = true := by
      simp [checkSingular, hq]
    simpa [produceNearest, hq] using
      (checkSingular_shifted_det_zero d b n τ hs)
  · simpa [produceNearest, hq] using
      (totalNonsingularWitness_correct d b n τ ε hn hb hq hε)

#print axioms checkUnreduced_complete
#print axioms totalNonsingularWitness_correct
#print axioms produceNearest_correct

end AsterCertificate
