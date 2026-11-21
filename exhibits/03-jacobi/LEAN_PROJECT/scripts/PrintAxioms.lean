import DiscreteSturm

-- G1: Sturm count / oscillation
#print axioms DiscreteSturm.signVariations_reverse
#print axioms DiscreteSturm.signVariations_sturmRev
#print axioms DiscreteSturm.sturmCount_eq_card
#print axioms DiscreteSturm.card_le_eq
#print axioms DiscreteSturm.lt_jacobiEig_iff
#print axioms DiscreteSturm.signVariations_jpoly_jacobiEig
#print axioms DiscreteSturm.eigvec_gauge
#print axioms DiscreteSturm.signVariations_eigvec
#print axioms DiscreteSturm.signVariations_eigvec_of_pos
#print axioms DiscreteSturm.mulVec_recSol
-- G2: min–max / perturbation
#print axioms DiscreteSturm.eigenvalues_le_add_of_inner_le
#print axioms DiscreteSturm.eigenvalues_le_of_inner_le
#print axioms DiscreteSturm.eigenvalues_lt_of_inner_lt
#print axioms DiscreteSturm.eigenvalues₀_le_add
#print axioms DiscreteSturm.eigenvalues₀_le_of_posSemidef
#print axioms DiscreteSturm.jacobiEig_le_add
#print axioms DiscreteSturm.jacobiEig_mono
#print axioms DiscreteSturm.jacobiEig_add_const
#print axioms DiscreteSturm.abs_jacobiEig_sub_le
#print axioms DiscreteSturm.jacobiEig_lt_of_head_lt
-- G3: consumers and falsifiers
#print axioms DiscreteSturm.sineMode_eigvec
#print axioms DiscreteSturm.sineMode_signVariations
#print axioms DiscreteSturm.card_Ioc_eq_sturm
#print axioms DiscreteSturm.interior_perturbation_not_strict
#print axioms DiscreteSturm.nodal_fails_of_b_zero
#print axioms DiscreteSturm.sturm_fails_of_b_zero
