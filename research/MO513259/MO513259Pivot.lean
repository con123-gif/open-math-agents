import Mathlib

/-!
Pivot existence for the congruence-invariance proof of MO513259.
This fragment follows the parity and alternating helpers in combined probes.
It is not a complete solution of the source's graph conjectures.
-/

namespace OMA.MO513259

open scoped BigOperators Matrix

lemma isUnit_iff_modTwoEight_ne_zero (x : ZMod 8) :
    IsUnit x ↔ modTwoEight x ≠ 0 := by
  have hu : IsUnit x ↔ Nat.Coprime x.val 8 := by
    simpa using (ZMod.isUnit_iff_coprime x.val 8)
  rw [hu]
  change Nat.Coprime x.val 8 ↔ (x.val : ZMod 2) ≠ 0
  constructor <;> (fin_cases x <;> decide)

variable {I : Type*} [Fintype I] [DecidableEq I]

lemma exists_unit_offdiagonal (A : Matrix I I (ZMod 8))
    (hd : ∀ i, modTwoEight (A i i) = 0) (hunit : IsUnit A.det) (i : I) :
    ∃ j, i ≠ j ∧ IsUnit (A i j) := by
  classical
  have hAB : A.map modTwoEight * (A⁻¹).map modTwoEight = 1 := by
    have h := congrArg (fun M : Matrix I I (ZMod 8) => M.map modTwoEight)
      (Matrix.mul_nonsing_inv A hunit)
    simpa only [Matrix.map_mul, Matrix.map_one, map_zero, map_one] using h
  have hnz : ∃ j, modTwoEight (A i j) ≠ 0 := by
    by_contra h
    push_neg at h
    have he := congrFun (congrFun hAB i) i
    have hz : (0 : ZMod 2) = 1 := by
      simpa [Matrix.mul_apply, Matrix.map_apply, h] using he
    exact zero_ne_one hz
  obtain ⟨j, hj⟩ := hnz
  refine ⟨j, ?_, (isUnit_iff_modTwoEight_ne_zero _).mpr hj⟩
  intro hij
  subst j
  exact hj (hd i)

lemma offdiagonal_pivot_det_unit (A : Matrix I I (ZMod 8)) (hA : A.IsSymm)
    (hd : ∀ i, modTwoEight (A i i) = 0) (i j : I) (hij : IsUnit (A i j)) :
    IsUnit ((!![A i i, A i j; A j i, A j j] :
      Matrix (Fin 2) (Fin 2) (ZMod 8)).det) := by
  apply (isUnit_iff_modTwoEight_ne_zero _).mpr
  have hnz := (isUnit_iff_modTwoEight_ne_zero _).mp hij
  have hone : modTwoEight (A i j) = 1 := by
    have ht : ∀ x : ZMod 2, x ≠ 0 → x = 1 := by decide
    exact ht _ hnz
  rw [Matrix.det_fin_two]
  simp [map_sub, map_mul, hA.apply i j, hd, hone]

end OMA.MO513259
