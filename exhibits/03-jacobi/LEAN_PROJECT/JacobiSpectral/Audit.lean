import JacobiSpectral

/-! Axiom audit for the JacobiSpectral library (expected: `propext`, `Classical.choice`,
`Quot.sound` only). -/

-- G1 continuant
#print axioms JacobiSpectral.det_jacobi_succ_succ
#print axioms JacobiSpectral.det_jacobi_top
#print axioms JacobiSpectral.det_jacobi
#print axioms JacobiSpectral.charpoly_jacobi
#print axioms JacobiSpectral.transfer_vec
-- G2 Sturm / simple spectrum / interlacing
#print axioms JacobiSpectral.sturm_step
#print axioms JacobiSpectral.jpoly_interlace
#print axioms JacobiSpectral.no_common_root
#print axioms JacobiSpectral.charpoly_roots_nodup
#print axioms JacobiSpectral.jacobiEig_strictAnti
#print axioms JacobiSpectral.jacobiEig_interlace
#print axioms JacobiSpectral.finrank_eigenspace_le_one
#print axioms JacobiSpectral.finrank_eigenspace_jacobiEig
-- G3 Chebyshev / KMS adapter
#print axioms JacobiSpectral.cont_cheb_corner
#print axioms JacobiSpectral.eval_jpoly_const
#print axioms JacobiSpectral.jacobiEig_const
#print axioms JacobiSpectral.KMSAdapter.det_triDiag_succ_succ
#print axioms JacobiSpectral.KMSAdapter.det_triDiag_rev
#print axioms JacobiSpectral.KMSAdapter.det_leadBlock
#print axioms JacobiSpectral.KMSAdapter.det_endMat
#print axioms JacobiSpectral.KMSAdapter.cont_cheb
-- G4 spectral consumers
#print axioms JacobiSpectral.opNorm_sub_smul_one
#print axioms JacobiSpectral.opNorm_inv_sub_smul_one
#print axioms JacobiSpectral.condNumber_eq
#print axioms JacobiSpectral.gapMin_eq_infDist
#print axioms JacobiSpectral.inv_opNorm_inv_eq_infDist
#print axioms JacobiSpectral.spectrum_jacobi
#print axioms JacobiSpectral.spectrum_jacobi_const
#print axioms JacobiSpectral.jacobi_inv_opNorm_eq_infDist
-- G5 examples
#print axioms JacobiSpectral.Examples.nonconst_rootVec
