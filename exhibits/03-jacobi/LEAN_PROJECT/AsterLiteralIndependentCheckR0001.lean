import AsterAccuracyCheckR0001

/-!
Independent kernel verification of the LITERAL four endpoints emitted by
AsterCertificate.produceCertified, with no import of the producer.
Serialized input: diag [0,0,0], hop [1,1] (constant-one function extension),
target=7/5, tolerance=1/32.
-/
namespace AsterIndependentCertificate

open AsterCertificate

def d : ℕ → ℚ := fun _ => 0
def b : ℕ → ℚ := fun _ => 1

def literalWitness : NearestWitness :=
  ⟨⟨4921 / 3520, 987 / 704⟩,
    77669 / 56320, 80027 / 56320⟩

private theorem count_gap_left :
    qCount d b 3 (4921 / 3520) = 1 := by
  have hvalues : (List.range 4).map (qCont d b (4921 / 3520 : ℚ)) =
      [1, (4921 / 3520 : ℚ), 11825841 / 12390400,
       -2778194839 / 43614208000] := by
    norm_num [qCont, d, b, List.range_succ]
  unfold qCount
  rw [hvalues]
  norm_num [List.signVariations, List.destutter]

private theorem count_gap_right :
    qCount d b 3 (987 / 704) = 1 := by
  have hvalues : (List.range 4).map (qCont d b (987 / 704 : ℚ)) =
      [1, (987 / 704 : ℚ), 478553 / 495616,
       -16841181 / 348913664] := by
    norm_num [qCont, d, b, List.range_succ]
  unfold qCount
  rw [hvalues]
  norm_num [List.signVariations, List.destutter]

private theorem count_near_left :
    qCount d b 3 (77669 / 56320) = 1 := by
  have hvalues : (List.range 4).map (qCont d b (77669 / 56320 : ℚ)) =
      [1, (77669 / 56320 : ℚ), 2860531161 / 3171942400,
       -24186999521891 / 178643795968000] := by
    norm_num [qCont, d, b, List.range_succ]
  unfold qCount
  rw [hvalues]
  norm_num [List.signVariations, List.destutter]

private theorem count_near_right :
    qCount d b 3 (80027 / 56320) = 0 := by
  have hvalues : (List.range 4).map (qCont d b (80027 / 56320 : ℚ)) =
      [1, (80027 / 56320 : ℚ), 3232378329 / 3171942400,
       4836506090083 / 178643795968000] := by
    norm_num [qCont, d, b, List.range_succ]
  unfold qCount
  rw [hvalues]
  norm_num [List.signVariations, List.destutter]

theorem emitted_literal_accepted :
    checkAccurate d b 3 (7 / 5) (1 / 32) literalWitness = true := by
  norm_num [checkAccurate, witnessLower, witnessUpper,
    checkNearest, checkUnreduced, checkGap, literalWitness,
    count_gap_left, count_gap_right, count_near_left, count_near_right, b]

theorem emitted_literal_spectral_bounds :
    (∀ i : Fin 3,
      (7 / 3520 : ℝ) ≤
        |JacobiSpectral.jacobiEig
          (fun _ => (0 : ℝ)) (fun _ => (1 : ℝ)) 3 i -
          (7 / 5 : ℝ)|) ∧
    (∃ i : Fin 3,
      |JacobiSpectral.jacobiEig
          (fun _ => (0 : ℝ)) (fun _ => (1 : ℝ)) 3 i -
          (7 / 5 : ℝ)| ≤ (1179 / 56320 : ℝ)) := by
  have h := accurate_implies_spectral_bounds
    d b 3 (7 / 5) (1 / 32) literalWitness emitted_literal_accepted
  norm_num [literalWitness, witnessLower, witnessUpper, d, b] at h
  exact h

#print axioms emitted_literal_accepted
#print axioms emitted_literal_spectral_bounds

end AsterIndependentCertificate
