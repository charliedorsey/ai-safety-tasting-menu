import AsterTotalRadialProducer

/-!
# The data-only Jacobi certificate producer

Only rational coefficient functions, dimension, target, and positive
accuracy are passed at runtime. Invalid Jacobi data are rejected with
none. Accepted results carry the original checker guarantee.
-/

namespace AsterCertificate

/-- A fully executable API: validated data produce an exact certificate. -/
def produceNearest?
    (d b : ℕ → ℚ) (n : ℕ) (τ ε : ℚ) :
    Option NearestResult :=
  if hdata : checkUnreduced b n = true then
    if 0 < ε then
      let hnhb := checkUnreduced_sound b n hdata
      some (produceNearest d b n τ ε hnhb.1 hnhb.2)
    else none
  else none

/-- Valid rational input always produces a result. -/
theorem produceNearest?_complete
    (d b : ℕ → ℚ) (n : ℕ) (τ ε : ℚ)
    (hdata : checkUnreduced b n = true) (hε : 0 < ε) :
    ∃ result, produceNearest? d b n τ ε = some result := by
  let hnhb := checkUnreduced_sound b n hdata
  refine ⟨produceNearest d b n τ ε hnhb.1 hnhb.2, ?_⟩
  simp [produceNearest?, hdata, hε]

/-- A stable semantic contract for the two output constructors. -/
def nearestResultSound (d b : ℕ → ℚ) (n : ℕ) (τ ε : ℚ) :
    NearestResult → Prop
  | .singular =>
      (Matrix.scalar (Fin n) (τ : ℝ) -
        JacobiSpectral.jacobi (fun k => (d k : ℝ))
          (fun k => (b k : ℝ)) n).det = 0
  | .certified v =>
      checkNearest d b n τ v = true ∧
        0 < v.gap.right - τ ∧
        v.nearRight - v.gap.right ≤ ε

/-- Any successful data-only computation satisfies the proved
singularity-or-accurate-certificate contract. -/
theorem produceNearest?_sound
    (d b : ℕ → ℚ) (n : ℕ) (τ ε : ℚ)
    (result : NearestResult)
    (hresult : produceNearest? d b n τ ε = some result) :
    nearestResultSound d b n τ ε result := by
  by_cases hdata : checkUnreduced b n = true
  · by_cases hε : 0 < ε
    · let hnhb := checkUnreduced_sound b n hdata
      have hv :
          produceNearest d b n τ ε hnhb.1 hnhb.2 = result := by
        simpa [produceNearest?, hdata, hε] using hresult
      have hc : nearestResultSound d b n τ ε
          (produceNearest d b n τ ε hnhb.1 hnhb.2) :=
        produceNearest_correct d b n τ ε hnhb.1 hnhb.2 hε
      rw [hv] at hc
      exact hc
    · simp [produceNearest?, hdata, hε] at hresult
  · simp [produceNearest?, hdata] at hresult

#print axioms produceNearest?_complete
#print axioms produceNearest?_sound

end AsterCertificate
