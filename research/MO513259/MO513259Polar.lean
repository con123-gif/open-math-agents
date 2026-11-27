import Mathlib

/-!
Polarization over F2 and the closed copied-row-half formula for MO513259.
This fragment follows the orbit/minor helpers. It supplies the two-row part
of the congruence variation; the four-row/column part is still separate.
-/

namespace OMA.MO513259

open scoped BigOperators Matrix

variable {I : Type*} [Fintype I] [LinearOrder I]

lemma upperPairSum_polar (v x y : I → ZMod 2) :
    upperPairSum (fun k l => v k * v l * (x k * y l + y k * x l)) =
      (∑ k, v k * x k) * (∑ k, v k * y k) + ∑ k, v k * x k * y k := by
  classical
  have hprod : (∑ k, v k * x k) * (∑ k, v k * y k) =
      ∑ k, ∑ l, v k * v l * x k * y l := by
    rw [Finset.sum_mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    apply Finset.sum_congr rfl
    intro l _
    ring
  have hidem : ∀ z : ZMod 2, z * z = z := by decide
  have hdiag : (∑ k, v k * v k * x k * y k) = ∑ k, v k * x k * y k := by
    apply Finset.sum_congr rfl
    intro k _
    rw [hidem]
  have hoff : upperPairSum (fun k l =>
      v k * v l * x k * y l + v l * v k * x l * y k) =
      upperPairSum (fun k l => v k * v l * (x k * y l + y k * x l)) := by
    unfold upperPairSum
    apply Finset.sum_congr rfl
    intro k _
    apply Finset.sum_congr rfl
    intro l _
    by_cases h : k < l <;> simp only [h, if_true, if_false] <;> ring
  have hrel := sum_all_pairs (fun k l => v k * v l * x k * y l)
  rw [← hprod, hdiag, hoff] at hrel
  calc
    upperPairSum (fun k l => v k * v l * (x k * y l + y k * x l)) =
        ((∑ k, v k * x k * y k) + (∑ k, v k * x k * y k)) +
          upperPairSum (fun k l => v k * v l * (x k * y l + y k * x l)) := by
      rw [CharTwo.add_self_eq_zero, zero_add]
    _ = ((∑ k, v k * x k * y k) +
          upperPairSum (fun k l => v k * v l * (x k * y l + y k * x l))) +
          (∑ k, v k * x k * y k) := by ac_rfl
    _ = (∑ k, v k * x k) * (∑ k, v k * y k) + ∑ k, v k * x k * y k := by
      rw [← hrel]

lemma copyRowHalf_mod_two_closed (A : Matrix I I (ZMod 2)) (hA : IsUnit A.det)
    (i j : I) (hij : i ≠ j) :
    copyRowHalf A i j = ∑ k, A j k * (A⁻¹) k i * (A⁻¹) k j := by
  rw [copyRowHalf_mod_two_inverse A hA i j hij, upperPairSum_polar]
  have hzero : (∑ k, A j k * (A⁻¹) k i) = 0 := by
    have he := congrFun (congrFun (Matrix.mul_nonsing_inv A hA) j) i
    simpa [Matrix.mul_apply, Matrix.one_apply, hij, hij.symm] using he
  rw [hzero, zero_mul, zero_add]

lemma copyRowHalf_eight_reduction (A : Matrix I I (ZMod 8)) (hA : IsUnit A.det)
    (i j : I) (hij : i ≠ j) :
    modTwoEight (copyRowHalf A i j) =
      ∑ k, modTwoEight (A j k) * modTwoEight ((A⁻¹) k i) *
        modTwoEight ((A⁻¹) k j) := by
  have hunit : IsUnit (A.map modTwoEight).det := by
    have he : modTwoEight A.det = (A.map modTwoEight).det := modTwoEight.map_det A
    rw [← he]
    exact hA.map modTwoEight
  rw [map_copyRowHalf]
  have he := copyRowHalf_mod_two_closed (A.map modTwoEight) hunit i j hij
  have hinv : (A.map modTwoEight)⁻¹ = (A⁻¹).map modTwoEight :=
    (map_matrix_inverse modTwoEight A hA).symm
  simpa only [hinv, Matrix.map_apply] using he

end OMA.MO513259

#print axioms OMA.MO513259.upperPairSum_polar
#print axioms OMA.MO513259.copyRowHalf_eight_reduction
