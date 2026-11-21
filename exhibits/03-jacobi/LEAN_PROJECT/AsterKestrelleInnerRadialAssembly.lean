import AsterInnerSturmEquality
import AsterRadialReady

/-!
# Kestrelle's constructive radius enters the certified radial producer.

The inner count invariant is now *proved from the actual continuant*.
Only the occupied outer radius is an initialization input; finite
refinement and checker acceptance are proved by existing modules.

This is a source-facing consumer, not a claim of producer totality.
-/

namespace AsterCertificate

/-- Source-native initial bracket, requiring only an outer occupied
radius beyond Kestrelle's explicitly computed inner radius. -/
def kestrelleInitialRadialBracket
    (d b : ℕ → ℚ) (n : ℕ) (τ outer : ℚ)
    (hn : 0 < n)
    (hb : ∀ k, k + 1 < n → b k ≠ 0)
    (hq : qCont d b τ n ≠ 0)
    (houter : continuantInnerRadius d b τ n < outer)
    (hoccupied : qCount d b n (τ + outer) < qCount d b n (τ - outer)) :
    RadialBracket d b n τ :=
  initialRadialBracket d b n τ
    (continuantInnerRadius d b τ n) outer
    hn hb
    (continuantInnerRadius_pos d b τ n hq)
    houter
    (continuant_inner_radius_sturm_equal d b n hn hb τ hq)
    hoccupied

/-- The *unchanged* independent checker accepts all finite refinements
of Kestrelle's source-native inner radius. The only unfinished
initialization witness is a strictly larger occupied outer radius. -/
theorem kestrelle_refinement_checkNearest
    (d b : ℕ → ℚ) (n : ℕ) (τ outer : ℚ)
    (hn : 0 < n)
    (hb : ∀ k, k + 1 < n → b k ≠ 0)
    (hq : qCont d b τ n ≠ 0)
    (houter : continuantInnerRadius d b τ n < outer)
    (hoccupied : qCount d b n (τ + outer) < qCount d b n (τ - outer))
    (hdata : checkUnreduced b n = true)
    (fuel : ℕ) :
    checkNearest d b n τ
      ((kestrelleInitialRadialBracket d b n τ outer
        hn hb hq houter hoccupied).refine fuel).toNearestWitness = true := by
  exact RadialBracket.checkNearest_toNearestWitness _ hdata

#print axioms kestrelle_refinement_checkNearest

end AsterCertificate
