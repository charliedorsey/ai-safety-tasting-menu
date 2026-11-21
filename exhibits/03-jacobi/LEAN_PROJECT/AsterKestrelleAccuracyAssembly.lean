import AsterKestrelleInnerRadialAssembly
import AsterRadialFuel

/-!
# One certified program with precise outer-radius dependency

From Kestrelle's explicitly computable inner radius and any valid
occupied outer radius, return a witness that passes the *unchanged*
checker and has the requested rational error width.
-/

namespace AsterCertificate

/-- The conditional producer's actual witness, a finite computation
of exact rational Sturm counts. -/
def kestrelleAccuracyWitness
    (d b : ℕ → ℚ) (n : ℕ) (τ outer ε : ℚ)
    (hn : 0 < n)
    (hb : ∀ k, k + 1 < n → b k ≠ 0)
    (hq : qCont d b τ n ≠ 0)
    (houter : continuantInnerRadius d b τ n < outer)
    (hoccupied : qCount d b n (τ + outer) < qCount d b n (τ - outer)) :
    NearestWitness :=
  let w := kestrelleInitialRadialBracket d b n τ outer
    hn hb hq houter hoccupied
  (w.refine (radialFuel (w.outer - w.inner) ε)).toNearestWitness

/-- The sole remaining *initialization* hypothesis is the existence of
a rational outer radius with a strict source Sturm-count drop.
The inner radius, finite termination, width and checker acceptance
are all constructed and kernel-checked. -/
theorem kestrelleAccuracyWitness_checked_and_narrow
    (d b : ℕ → ℚ) (n : ℕ) (τ outer ε : ℚ)
    (hn : 0 < n)
    (hb : ∀ k, k + 1 < n → b k ≠ 0)
    (hq : qCont d b τ n ≠ 0)
    (houter : continuantInnerRadius d b τ n < outer)
    (hoccupied : qCount d b n (τ + outer) < qCount d b n (τ - outer))
    (hdata : checkUnreduced b n = true)
    (hε : 0 < ε) :
    checkNearest d b n τ
      (kestrelleAccuracyWitness d b n τ outer ε hn hb hq houter hoccupied) = true ∧
    let w := kestrelleInitialRadialBracket d b n τ outer
      hn hb hq houter hoccupied
    (w.refine (radialFuel (w.outer - w.inner) ε)).outer -
      (w.refine (radialFuel (w.outer - w.inner) ε)).inner ≤ ε := by
  let w := kestrelleInitialRadialBracket d b n τ outer
    hn hb hq houter hoccupied
  have hcheck : checkNearest d b n τ
      (w.refine (radialFuel (w.outer - w.inner) ε)).toNearestWitness = true :=
    RadialBracket.checkNearest_toNearestWitness _ hdata
  have hwidth := radialFuel_refine_width w ε hε
  constructor
  · exact hcheck
  · exact hwidth

#print axioms kestrelleAccuracyWitness_checked_and_narrow

end AsterCertificate
