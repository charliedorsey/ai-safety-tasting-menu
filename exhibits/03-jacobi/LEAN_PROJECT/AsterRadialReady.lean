import AsterRadialConsumer
import AsterSturmAntitone

/-!
# The checked radial certificate, conditional only on initial radii

All the algorithm's count invariants, monotonicity, termination at
specified fuel, and public checker acceptance are kernel-proved.

The separate producer task is to *compute* initial inner and outer
radii and finite fuel from rational data and a requested accuracy.
-/

namespace AsterCertificate

/-- From valid initial rational radii and the existing Jacobi
precondition, construct a certified radial bracket without supplying
any extra monotonicity hypothesis. -/
def initialRadialBracket
    (d b : ℕ → ℚ) (n : ℕ) (τ inner outer : ℚ)
    (hn : 0 < n) (hb : ∀ k, k + 1 < n → b k ≠ 0)
    (hinner : 0 < inner) (horder : inner < outer)
    (hempty : qCount d b n (τ - inner) = qCount d b n (τ + inner))
    (hoccupied : qCount d b n (τ + outer) < qCount d b n (τ - outer)) :
    RadialBracket d b n τ :=
  ⟨inner, outer, hinner, horder, qCount_antitone d b n hn hb,
    hempty, hoccupied⟩

/-- A fixed number of exact Sturm tests already constructs an
accepted checker witness; no eigenvalue index or root selection enters. -/
theorem radial_refinement_accepted
    (d b : ℕ → ℚ) (n : ℕ) (τ inner outer : ℚ)
    (hn : 0 < n) (hb : ∀ k, k + 1 < n → b k ≠ 0)
    (hinner : 0 < inner) (horder : inner < outer)
    (hempty : qCount d b n (τ - inner) = qCount d b n (τ + inner))
    (hoccupied : qCount d b n (τ + outer) < qCount d b n (τ - outer))
    (hdata : checkUnreduced b n = true) (fuel : ℕ) :
    checkNearest d b n τ
      ((initialRadialBracket d b n τ inner outer hn hb hinner horder
          hempty hoccupied).refine fuel).toNearestWitness = true := by
  exact RadialBracket.checkNearest_toNearestWitness _ hdata

#print axioms radial_refinement_accepted

end AsterCertificate
