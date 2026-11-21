import IlystrenFullNonsingularProducerR0001

/-!
Minimal source-facing nonsingular interface: accept the existing Boolean
unreduced check rather than separately asking for its consequences.
-/
namespace AsterCertificate

/-- The only prerequisites are the SAME executable source checker
and nonzero rational characteristic continuant. -/
def computedNonsingularWitnessOfCheck
    (d b : ℕ → ℚ) (n : ℕ) (τ ε : ℚ)
    (hdata : checkUnreduced b n = true)
    (hq : qCont d b τ n ≠ 0) : NearestWitness :=
  kestrelleComputedAccuracyWitness d b n τ ε
    (checkUnreduced_sound b n hdata).1
    (checkUnreduced_sound b n hdata).2
    hq

/-- No separately supplied dimension/nonzero-hop proofs or outer
radius: the original Boolean precondition checker certifies the input,
and the constructed witness satisfies the unchanged nearest checker. -/
theorem computedNonsingularWitnessOfCheck_accepted
    (d b : ℕ → ℚ) (n : ℕ) (τ ε : ℚ)
    (hdata : checkUnreduced b n = true)
    (hq : qCont d b τ n ≠ 0)
    (hε : 0 < ε) :
    checkNearest d b n τ
      (computedNonsingularWitnessOfCheck d b n τ ε hdata hq) = true := by
  exact (kestrelleComputedAccuracyWitness_checked_and_narrow
    d b n τ ε (checkUnreduced_sound b n hdata).1
    (checkUnreduced_sound b n hdata).2 hq hdata hε).1

#print axioms computedNonsingularWitnessOfCheck_accepted
end AsterCertificate
