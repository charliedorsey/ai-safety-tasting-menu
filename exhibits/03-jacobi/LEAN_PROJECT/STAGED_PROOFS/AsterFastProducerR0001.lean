import AsterAccuracyCheckR0001
import AsterLogFuelR0001
import IlystrenFullNonsingularProducerR0001
import AsterSingularMatrix

/-! Private staging: proof-carrying, logarithmic-fuel rational producer. -/

namespace AsterCertificate

def fastInitialBracket (d b : ℕ → ℚ) (n : ℕ) (τ : ℚ)
    (hdata : checkUnreduced b n = true)
    (hq : qCont d b τ n ≠ 0) : RadialBracket d b n τ :=
  let hb := checkUnreduced_sound b n hdata
  kestrelleInitialRadialBracket d b n τ
    (computedOccupiedOuterRadius d b n τ)
    hb.1 hb.2 hq
    (computedOccupiedOuterRadius_spec d b n τ hb.1 hq).1
    (computedOccupiedOuterRadius_spec d b n τ hb.1 hq).2

def fastWitness (d b : ℕ → ℚ) (n : ℕ) (τ ε : ℚ)
    (hdata : checkUnreduced b n = true)
    (hq : qCont d b τ n ≠ 0) : NearestWitness :=
  let w := fastInitialBracket d b n τ hdata hq
  (w.refine (radialLogFuel (w.outer - w.inner) ε)).toNearestWitness

theorem fastWitness_checked_accurate
    (d b : ℕ → ℚ) (n : ℕ) (τ ε : ℚ)
    (hdata : checkUnreduced b n = true)
    (hq : qCont d b τ n ≠ 0) (hε : 0 < ε) :
    checkAccurate d b n τ ε (fastWitness d b n τ ε hdata hq) = true := by
  let w := fastInitialBracket d b n τ hdata hq
  let v := w.refine (radialLogFuel (w.outer - w.inner) ε)
  have hc : checkNearest d b n τ v.toNearestWitness = true :=
    RadialBracket.checkNearest_toNearestWitness v hdata
  have hw : v.outer - v.inner ≤ ε :=
    radialLogFuel_refine_width w ε hε
  apply (checkAccurate_iff d b n τ ε (fastWitness d b n τ ε hdata hq)).mpr
  refine ⟨?_, hε, ?_⟩
  · exact hc
  · change witnessUpper τ v.toNearestWitness -
        witnessLower τ v.toNearestWitness ≤ ε
    rw [radial_upper_eq, radial_lower_eq]
    exact hw

inductive CertifiedOutcome (d b : ℕ → ℚ) (n : ℕ) (τ ε : ℚ) where
  | invalidData
  | invalidTolerance
  | singular
      (h : (Matrix.scalar (Fin n) (τ : ℝ) -
        JacobiSpectral.jacobi (fun i => (d i : ℝ)) (fun i => (b i : ℝ)) n).det = 0)
  | regular (w : NearestWitness)
      (verified : checkAccurate d b n τ ε w = true)

def produceCertified (d b : ℕ → ℚ) (n : ℕ) (τ ε : ℚ) :
    CertifiedOutcome d b n τ ε := by
  if hdata : checkUnreduced b n = true then
    if hε : 0 < ε then
      if hs : qCont d b τ n = 0 then
        have hcs : checkSingular d b n τ = true := by
          simp [checkSingular, hs]
        exact .singular (checkSingular_shifted_det_zero d b n τ hcs)
      else
        let w := fastWitness d b n τ ε hdata hs
        exact .regular w (fastWitness_checked_accurate d b n τ ε hdata hs hε)
    else exact .invalidTolerance
  else exact .invalidData

#print axioms fastWitness_checked_accurate
#print axioms produceCertified

end AsterCertificate
