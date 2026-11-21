import AsterRadialBracket

/-!
# A radial bracket produces the existing independent checker witness.

No eigenvalue index is computed, and the checker is not weakened.
-/

namespace AsterCertificate
namespace RadialBracket

variable {d b : ℕ → ℚ} {n : ℕ} {τ : ℚ}

/-- The exact existing checker representation of the two certified radii. -/
def toNearestWitness (w : RadialBracket d b n τ) : NearestWitness :=
  ⟨⟨τ - w.inner, τ + w.inner⟩,
    τ - w.outer, τ + w.outer⟩

/-- The independent checker accepts every radial bracket for which
its original matrix precondition passes. -/
theorem checkNearest_toNearestWitness
    (w : RadialBracket d b n τ)
    (hdata : checkUnreduced b n = true) :
    checkNearest d b n τ w.toNearestWitness = true := by
  have houter : 0 < w.outer := lt_trans w.inner_pos w.ordered
  have hleft : τ - w.inner < τ := by linarith [w.inner_pos]
  have hright : τ < τ + w.inner := by linarith [w.inner_pos]
  have hnear : τ - w.outer < τ + w.outer := by linarith
  simp [checkNearest, checkGap, toNearestWitness,
    hdata, hleft, hright, hnear, w.inner_empty, w.outer_occupied]

#print axioms checkNearest_toNearestWitness
end RadialBracket
end AsterCertificate
