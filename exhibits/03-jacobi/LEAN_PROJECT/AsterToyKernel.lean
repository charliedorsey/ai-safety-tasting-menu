import AsterNearest

/-!
# The three-site certificate, checked by the Lean kernel

This is a proof of checker acceptance, not merely runtime evaluation.
The rational continuant counts are derived independently at each endpoint.
-/

namespace AsterCertificate

private theorem left_count :
    qCount toyDiag toyHop 3 (139 / 100) = 1 := by
  have hvalues : (List.range 4).map (qCont toyDiag toyHop (139 / 100 : ℚ)) = [1, (139 / 100 : ℚ), 9321 / 10000, -94381 / 1000000] := by
    norm_num [qCont, toyDiag, toyHop, List.range_succ]
  unfold qCount
  rw [hvalues]
  norm_num [List.signVariations, List.destutter]

private theorem gap_right_count :
    qCount toyDiag toyHop 3 (141 / 100) = 1 := by
  have hvalues : (List.range 4).map (qCont toyDiag toyHop (141 / 100 : ℚ)) = [1, (141 / 100 : ℚ), 9881 / 10000, -16779 / 1000000] := by
    norm_num [qCont, toyDiag, toyHop, List.range_succ]
  unfold qCount
  rw [hvalues]
  norm_num [List.signVariations, List.destutter]

private theorem near_right_count :
    qCount toyDiag toyHop 3 (71 / 50) = 0 := by
  have hvalues : (List.range 4).map (qCont toyDiag toyHop (71 / 50 : ℚ)) = [1, (71 / 50 : ℚ), 2541 / 2500, 2911 / 125000] := by
    norm_num [qCont, toyDiag, toyHop, List.range_succ]
  unfold qCount
  rw [hvalues]
  norm_num [List.signVariations, List.destutter]

theorem toy_checkNearest :
    checkNearest toyDiag toyHop 3 (7 / 5) toyNearest = true := by
  norm_num [checkNearest, checkUnreduced, checkGap, toyNearest,
    toyWitness, left_count, gap_right_count, near_right_count, toyHop]

#print axioms toy_checkNearest

/-- The first numerical witness is a *theorem*, not a numerical experiment.
The bounds concern every eigenvalue and a witnessed nearby eigenvalue. -/
theorem toy_spectral_distance_bounds :
    (∀ i : Fin 3,
      (1 / 100 : ℝ) ≤
        |JacobiSpectral.jacobiEig (fun _ => (0 : ℝ))
          (fun _ => (1 : ℝ)) 3 i - (7 / 5 : ℝ)|) ∧
    (∃ i : Fin 3,
      |JacobiSpectral.jacobiEig (fun _ => (0 : ℝ))
        (fun _ => (1 : ℝ)) 3 i - (7 / 5 : ℝ)| ≤ (1 / 50 : ℝ)) := by
  have h := checkNearest_distance_bounds toyDiag toyHop 3 (7 / 5)
    toyNearest toy_checkNearest
  norm_num [toyNearest, toyWitness, toyDiag, toyHop] at h
  simpa using h

#print axioms toy_spectral_distance_bounds

end AsterCertificate
