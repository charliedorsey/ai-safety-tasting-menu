import JacobiBridge

open JacobiSpectral
namespace JacobiBridge

theorem jpoly_const_flip_sign (c β : ℝ) :
    ∀ n : ℕ, jpoly (fun _ => c) (fun _ => β) n =
      jpoly (fun _ => c) (fun _ => -β) n
  | 0 => rfl
  | 1 => rfl
  | (n + 2) => by
    rw [jpoly_succ_succ, jpoly_succ_succ,
      ← jpoly_const_flip_sign c β (n + 1),
      ← jpoly_const_flip_sign c β n]
    ring

theorem spectrum_const_flip_sign (c β : ℝ) (n : ℕ) :
    spectrum ℝ (jacobi (fun _ => c) (fun _ => β) n) =
    spectrum ℝ (jacobi (fun _ => c) (fun _ => -β) n) := by
  ext τ
  rw [Matrix.mem_spectrum_iff_isRoot_charpoly,
    Matrix.mem_spectrum_iff_isRoot_charpoly,
    charpoly_jacobi, charpoly_jacobi,
    jpoly_const_flip_sign c β n]


theorem spectrum_q_negative (c β : ℝ) (hβ : β < 0)
    (q : ℕ) (hq : 2 ≤ q) :
    spectrum ℝ (jacobi (fun _ => c) (fun _ => β) (q - 1)) =
      Set.range (fun i : Fin (q - 1) =>
        c + 2 * β * Real.cos (((i : ℕ) + 1 : ℝ) * Real.pi / q)) := by
  have hpos : 0 < -β := neg_pos.mpr hβ
  rw [spectrum_const_flip_sign c β (q - 1)]
  rw [spectrum_q_sub_one c (-β) hpos q hq]
  ext x
  simp only [Set.mem_range]
  constructor
  · rintro ⟨i, rfl⟩
    refine ⟨i.rev, ?_⟩
    have hv : ((i.rev : Fin (q - 1)) : ℕ) + 1 + (i : ℕ) + 1 = q := by
      simp only [Fin.val_rev]
      omega
    have heq : (((i.rev : Fin (q - 1)) : ℕ) + 1 : ℝ) * Real.pi / q =
        Real.pi - (((i : ℕ) + 1 : ℝ) * Real.pi / q) := by
      have qpos : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
      apply (div_eq_iff qpos.ne').2
      field_simp
      have hvR : ((((i.rev : Fin (q - 1)) : ℕ) + 1 : ℝ) + (((i : ℕ) + 1 : ℝ))) = (q : ℝ) := by exact_mod_cast hv
      nlinarith [Real.pi_pos]
    rw [heq, Real.cos_pi_sub]
    ring
  · rintro ⟨i, rfl⟩
    refine ⟨i.rev, ?_⟩
    have hv : ((i.rev : Fin (q - 1)) : ℕ) + 1 + (i : ℕ) + 1 = q := by
      simp only [Fin.val_rev]
      omega
    have heq : (((i.rev : Fin (q - 1)) : ℕ) + 1 : ℝ) * Real.pi / q =
        Real.pi - (((i : ℕ) + 1 : ℝ) * Real.pi / q) := by
      have qpos : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
      apply (div_eq_iff qpos.ne').2
      field_simp
      have hvR : ((((i.rev : Fin (q - 1)) : ℕ) + 1 : ℝ) + (((i : ℕ) + 1 : ℝ))) = (q : ℝ) := by exact_mod_cast hv
      nlinarith [Real.pi_pos]
    rw [heq, Real.cos_pi_sub]
    ring

#print axioms spectrum_q_negative
#print axioms jpoly_const_flip_sign
#print axioms spectrum_const_flip_sign
end JacobiBridge
