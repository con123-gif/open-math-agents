import Mathlib

/-!
Two-dimensional permanent and exact optional-extension counterexamples for
MathOverflow 513259. These results do not prove its graph conjectures.
Credit: Cornelius Lytollis (@con123-gif), assisted by ChatGPT (GPT-6 Codex;
the exact model variant is not exposed). The runtime lane found the first
optional-extension counterexample; the algebra lane found the second.
-/

namespace OMA.MO513259

open scoped BigOperators Matrix

lemma permanent_fin_two {R : Type*} [CommSemiring R]
    (A : Matrix (Fin 2) (Fin 2) R) :
    A.permanent = A 0 0 * A 1 1 + A 1 0 * A 0 1 := by
  have hp : (Finset.univ : Finset (Equiv.Perm (Fin 2))) =
      {1, Equiv.swap 0 1} := by decide
  rw [Matrix.permanent, hp]
  simp [Fin.prod_univ_two]

def extensionEight : Matrix (Fin 2) (Fin 2) (ZMod 8) := !![2, 1; 1, 2]

def extensionEightInverse : Matrix (Fin 2) (Fin 2) (ZMod 8) := !![6, 5; 5, 6]

lemma extensionEight_mul_inverse : extensionEight * extensionEightInverse = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [extensionEight, extensionEightInverse, Matrix.mul_apply, Fin.sum_univ_two]

lemma extensionEight_inv : extensionEight⁻¹ = extensionEightInverse :=
  Matrix.inv_eq_right_inv extensionEight_mul_inverse

lemma even_diagonal_extension_eight_false :
    extensionEight.IsSymm ∧ (∀ i, ∃ x, extensionEight i i = 2 * x) ∧
      IsUnit extensionEight.det ∧ (extensionEight⁻¹).permanent ≠ 1 := by
  refine ⟨?_, ?_, Matrix.isUnit_det_of_right_inverse extensionEight_mul_inverse, ?_⟩
  · apply Matrix.IsSymm.ext
    intro i j
    fin_cases i <;> fin_cases j <;> rfl
  · intro i
    refine ⟨1, ?_⟩
    fin_cases i <;> decide
  · rw [extensionEight_inv, permanent_fin_two]
    decide

def extensionTwentyFour : Matrix (Fin 2) (Fin 2) (ZMod 24) := !![2, 1; 1, 6]

def extensionTwentyFourInverse : Matrix (Fin 2) (Fin 2) (ZMod 24) :=
  !![18, 13; 13, 22]

lemma extensionTwentyFour_mul_inverse :
    extensionTwentyFour * extensionTwentyFourInverse = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [extensionTwentyFour, extensionTwentyFourInverse,
      Matrix.mul_apply, Fin.sum_univ_two]

lemma extensionTwentyFour_inv : extensionTwentyFour⁻¹ = extensionTwentyFourInverse :=
  Matrix.inv_eq_right_inv extensionTwentyFour_mul_inverse

lemma even_diagonal_extension_twenty_four_false :
    extensionTwentyFour.IsSymm ∧ (∀ i, ∃ x, extensionTwentyFour i i = 2 * x) ∧
      IsUnit extensionTwentyFour.det ∧
      2 * extensionTwentyFour.permanent + (extensionTwentyFour⁻¹).permanent - 3 ≠ 0 := by
  refine ⟨?_, ?_, Matrix.isUnit_det_of_right_inverse extensionTwentyFour_mul_inverse, ?_⟩
  · apply Matrix.IsSymm.ext
    intro i j
    fin_cases i <;> fin_cases j <;> rfl
  · intro i
    fin_cases i
    · exact ⟨1, by decide⟩
    · exact ⟨3, by decide⟩
  · rw [extensionTwentyFour_inv, permanent_fin_two, permanent_fin_two]
    decide

end OMA.MO513259

#print axioms OMA.MO513259.permanent_fin_two
#print axioms OMA.MO513259.even_diagonal_extension_eight_false
#print axioms OMA.MO513259.even_diagonal_extension_twenty_four_false
