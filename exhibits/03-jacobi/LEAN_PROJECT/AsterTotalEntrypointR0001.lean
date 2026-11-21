import IlystrenCheckedNonsingularConsumerR0001
import AsterSingularMatrix

/-! Research-only total decision wrapper. No public release. -/
namespace AsterCertificate

inductive CertificateOutcome (d b : ℕ → ℚ) (n : ℕ) (τ ε : ℚ) where
  | invalid
  | singular
      (h : (Matrix.scalar (Fin n) (τ : ℝ) -
        JacobiSpectral.jacobi (fun i => (d i : ℝ)) (fun i => (b i : ℝ)) n).det = 0)
  | regular (w : NearestWitness)
      (accepted : checkNearest d b n τ w = true)

def produceCertificate (d b : ℕ → ℚ) (n : ℕ) (τ ε : ℚ) :
    CertificateOutcome d b n τ ε := by
  if hdata : checkUnreduced b n = true then
    if hε : 0 < ε then
      if hs : checkSingular d b n τ = true then
        exact .singular (checkSingular_shifted_det_zero d b n τ hs)
      else
        have hq : qCont d b τ n ≠ 0 := by
          intro heq
          apply hs
          simp only [checkSingular, decide_eq_true_eq]
          exact heq
        let w := computedNonsingularWitnessOfCheck d b n τ ε hdata hq
        exact .regular w (computedNonsingularWitnessOfCheck_accepted
          d b n τ ε hdata hq hε)
    else
      exact .invalid
  else
    exact .invalid

#print axioms produceCertificate
end AsterCertificate
