import Mathlib

/-!
This integration fragment is concatenated after the independent parity,
alternating-form and determinant helpers by build_helper_probe.py. It is not
a standalone Lean module and not a full proof of MathOverflow 513259.
-/

namespace OMA.MO513259

lemma modTwoEight_zero_iff_two_mul (x : ZMod 8) :
    modTwoEight x = 0 ↔ ∃ y : ZMod 8, x = 2 * y := by
  constructor
  · intro hx
    change (x.val : ZMod 2) = 0 at hx
    fin_cases x
    · exact ⟨0, rfl⟩
    · exact False.elim ((by decide : (1 : ZMod 2) ≠ 0) hx)
    · exact ⟨1, rfl⟩
    · exact False.elim ((by decide : (1 : ZMod 2) ≠ 0) hx)
    · exact ⟨2, rfl⟩
    · exact False.elim ((by decide : (1 : ZMod 2) ≠ 0) hx)
    · exact ⟨3, rfl⟩
    · exact False.elim ((by decide : (1 : ZMod 2) ≠ 0) hx)
  · rintro ⟨y, rfl⟩
    change ((2 * y).val : ZMod 2) = 0
    fin_cases y <;> decide

variable {I : Type*} [Fintype I] [DecidableEq I]

lemma det_add_even_symm_pair (A : Matrix I I (ZMod 8))
    (hA : A.IsSymm) (hd : ∀ i, modTwoEight (A i i) = 0)
    (hunit : IsUnit A.det) (i j : I) (u : ZMod 8) :
    (A + Matrix.single i j (2 * u) + Matrix.single j i (2 * u)).det = A.det := by
  have hdi := map_inverse_diagonal_zero_mod_two modTwoEight A hA hd hunit i
  have hdj := map_inverse_diagonal_zero_mod_two modTwoEight A hA hd hunit j
  obtain ⟨bi, hi⟩ := (modTwoEight_zero_iff_two_mul ((A⁻¹) i i)).mp hdi
  obtain ⟨bj, hj⟩ := (modTwoEight_zero_iff_two_mul ((A⁻¹) j j)).mp hdj
  exact DetHelper.det_add_even_symm_pair_of_inv_even A hA hunit i j u bi bj hi hj

end OMA.MO513259
