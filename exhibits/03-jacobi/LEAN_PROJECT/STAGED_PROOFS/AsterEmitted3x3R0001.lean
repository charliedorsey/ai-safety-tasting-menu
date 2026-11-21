import AsterFastProducerR0001

/-!
One exact artifact from the ACTUAL Lean total producer. Serialized input:
  n=3, diag=[0,0,0], offdiag=[1,1], target=7/5, tolerance=1/32.
Here the physical off-diagonal sequence is canonically zero-padded.
-/
namespace AsterCertificate

def demoD : ℕ → ℚ := fun _ => 0
def demoB : ℕ → ℚ := fun k => if k < 2 then 1 else 0

private theorem demo_hdata : checkUnreduced demoB 3 = true := by
  decide

private theorem demo_hq : qCont demoD demoB (7 / 5) 3 ≠ 0 := by
  norm_num [qCont, demoD, demoB]

def demoEmitted : NearestWitness :=
  fastWitness demoD demoB 3 (7 / 5) (1 / 32) demo_hdata demo_hq

/-- Kernel proof that the producer's actual output meets the source checker
    and the requested rational error width. -/
theorem demoEmitted_verified :
    checkAccurate demoD demoB 3 (7 / 5) (1 / 32) demoEmitted = true :=
  fastWitness_checked_accurate demoD demoB 3 (7 / 5) (1 / 32)
    demo_hdata demo_hq (by norm_num)

-- This statement runs the full total public dispatcher, not just a hand-chosen witness.
#eval match produceCertified demoD demoB 3 (7 / 5) (1 / 32) with
  | .regular w _ =>
      some (w.gap.left, w.gap.right, w.nearLeft, w.nearRight)
  | _ => none

#print axioms demoEmitted_verified
end AsterCertificate
