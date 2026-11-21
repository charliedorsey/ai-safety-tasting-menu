import AsterKestrelleAccuracyAssembly
import IlystrenOuterBasic

/-!
Executable outer initialization joined to Aster + Kestrelle.
This removes the supplied occupied-outer-radius hypothesis entirely.
All data are exact rationals, and no eigenvalue selection is performed.
-/
namespace AsterCertificate
open Ilystren.Jacobi

/-- Concrete rational outer radius from the same original input. -/
def computedOccupiedOuterRadius (d b : ℕ → ℚ) (n : ℕ) (τ : ℚ) : ℚ :=
  sourceOuterRadiusFromInner d b n τ
    (continuantInnerRadius d b τ n)

/-- The source Sturm gate, uniformly in the target, is proved by
the finite rational-coefficient budget. -/
theorem computedOccupiedOuterRadius_spec
    (d b : ℕ → ℚ) (n : ℕ) (τ : ℚ)
    (hn : 0 < n) (hq : qCont d b τ n ≠ 0) :
    continuantInnerRadius d b τ n <
        computedOccupiedOuterRadius d b n τ ∧
      qCount d b n (τ + computedOccupiedOuterRadius d b n τ) <
        qCount d b n (τ - computedOccupiedOuterRadius d b n τ) := by
  have hi : 0 ≤ continuantInnerRadius d b τ n :=
    (continuantInnerRadius_pos d b τ n hq).le
  have h := sourceOuterRadiusFromInner_spec d b n τ
    (continuantInnerRadius d b τ n) hn hi
  constructor
  · exact h.1
  · change qCount d b n
       (τ + sourceOuterRadiusFromInner d b n τ
         (continuantInnerRadius d b τ n)) <
       qCount d b n
       (τ - sourceOuterRadiusFromInner d b n τ
         (continuantInnerRadius d b τ n))
    rw [h.2.1]
    exact h.2.2

/-- Nonsingular end-to-end witness construction: only the ORIGINAL
Jacobi nonsingularity/unreduced preconditions are inputs, not radii. -/
def kestrelleComputedAccuracyWitness
    (d b : ℕ → ℚ) (n : ℕ) (τ ε : ℚ)
    (hn : 0 < n)
    (hb : ∀ k, k + 1 < n → b k ≠ 0)
    (hq : qCont d b τ n ≠ 0) : NearestWitness :=
  kestrelleAccuracyWitness d b n τ
    (computedOccupiedOuterRadius d b n τ) ε hn hb hq
    (computedOccupiedOuterRadius_spec d b n τ hn hq).1
    (computedOccupiedOuterRadius_spec d b n τ hn hq).2

/-- Replays Aster's exact independent checker and the requested rational
width for the fully COMPUTED inner and outer radii. -/
theorem kestrelleComputedAccuracyWitness_checked_and_narrow
    (d b : ℕ → ℚ) (n : ℕ) (τ ε : ℚ)
    (hn : 0 < n)
    (hb : ∀ k, k + 1 < n → b k ≠ 0)
    (hq : qCont d b τ n ≠ 0)
    (hdata : checkUnreduced b n = true)
    (hε : 0 < ε) :
    checkNearest d b n τ
      (kestrelleComputedAccuracyWitness d b n τ ε hn hb hq) = true ∧
    let w := kestrelleInitialRadialBracket d b n τ
      (computedOccupiedOuterRadius d b n τ) hn hb hq
      (computedOccupiedOuterRadius_spec d b n τ hn hq).1
      (computedOccupiedOuterRadius_spec d b n τ hn hq).2
    (w.refine (radialFuel (w.outer - w.inner) ε)).outer -
      (w.refine (radialFuel (w.outer - w.inner) ε)).inner ≤ ε := by
  exact kestrelleAccuracyWitness_checked_and_narrow d b n τ
    (computedOccupiedOuterRadius d b n τ) ε hn hb hq
    (computedOccupiedOuterRadius_spec d b n τ hn hq).1
    (computedOccupiedOuterRadius_spec d b n τ hn hq).2
    hdata hε

#print axioms computedOccupiedOuterRadius_spec
#print axioms kestrelleComputedAccuracyWitness_checked_and_narrow

end AsterCertificate
