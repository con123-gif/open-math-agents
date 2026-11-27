import Mathlib

/-!
Two forced rows as a rank-two determinant update. This integration fragment
uses the already checked row-replacement, row-expansion, parity and ordered
orbit helpers. The general graph theorem remains a separate obligation.
-/

namespace OMA.MO513259

open scoped BigOperators Matrix

variable {I R : Type*} [Fintype I] [DecidableEq I] [CommRing R]

lemma det_forceTwoRows (A : Matrix I I R) (hA : IsUnit A.det)
    (i j : I) (hij : i ≠ j) (k l : I) :
    (forceTwoRows A i j k l).det =
      A.det * ((A⁻¹) k i * (A⁻¹) l j - (A⁻¹) k j * (A⁻¹) l i) := by
  classical
  let selected : Fin 2 → I := ![i, j]
  let keys : Fin 2 → I := ![k, l]
  have hs : Function.Injective selected := by
    intro a b h
    fin_cases a <;> fin_cases b
    · rfl
    · exact False.elim (hij h)
    · exact False.elim (hij h.symm)
    · rfl
  have hm : coordinateRowReplacement A selected keys = forceTwoRows A i j k l := by
    ext a b
    by_cases hi : a = i
    · subst a
      change coordinateRowReplacement A selected keys (selected (0 : Fin 2)) b = _
      rw [coordinateRowReplacement_selected A selected keys hs (0 : Fin 2) b]
      by_cases hb : k = b
      · subst b
        simp [keys, forceTwoRows, Matrix.updateRow_apply, hij, hij.symm]
      · simp [keys, forceTwoRows, Matrix.updateRow_apply, hij, hij.symm,
          Pi.single_apply, Matrix.one_apply, hb, Ne.symm hb]
    · by_cases hj : a = j
      · subst a
        change coordinateRowReplacement A selected keys (selected (1 : Fin 2)) b = _
        rw [coordinateRowReplacement_selected A selected keys hs (1 : Fin 2) b]
        by_cases hb : l = b
        · subst b
          simp [keys, forceTwoRows, Matrix.updateRow_apply, hij, hij.symm]
        · simp [keys, forceTwoRows, Matrix.updateRow_apply, hij, hij.symm,
            Pi.single_apply, Matrix.one_apply, hb, Ne.symm hb]
      · have hn : ∀ q : Fin 2, a ≠ selected q := by
          intro q
          fin_cases q
          · exact hi
          · exact hj
        have he := coordinateRowReplacement_unselected A selected keys a b hn
        simpa [forceTwoRows, Matrix.updateRow_apply, hi, hj] using he
  rw [← hm, det_coordinateRowReplacement A hA selected keys hs, Matrix.det_fin_two]
  simp [selected, keys]

lemma map_forceTwoRows {S : Type*} [CommRing S] (f : R →+* S)
    (A : Matrix I I R) (i j k l : I) :
    (forceTwoRows A i j k l).map f = forceTwoRows (A.map f) i j k l := by
  classical
  have hb (a : I) : f ∘ (Pi.single a 1 : I → R) = (Pi.single a 1 : I → S) := by
    funext b
    by_cases h : b = a
    · subst b
      simp
    · simp [Pi.single_apply, h, Ne.symm h]
  simp only [forceTwoRows, Matrix.map_updateRow, hb]

section Ordered

variable [LinearOrder I]

lemma map_copyRowHalf {S : Type*} [CommRing S] (f : R →+* S)
    (A : Matrix I I R) (i j : I) :
    f (copyRowHalf A i j) = copyRowHalf (A.map f) i j := by
  classical
  simp only [copyRowHalf, upperPairSum, map_sum, apply_ite, map_mul,
    map_zero, map_permanent, map_forceTwoRows, Matrix.map_apply]

lemma copyRowHalf_mod_two_inverse (A : Matrix I I (ZMod 2)) (hA : IsUnit A.det)
    (i j : I) (hij : i ≠ j) :
    copyRowHalf A i j = upperPairSum (fun k l => A j k * A j l *
      ((A⁻¹) k i * (A⁻¹) l j + (A⁻¹) k j * (A⁻¹) l i)) := by
  classical
  have hdet : A.det = 1 := by
    have ht : ∀ x : ZMod 2, x ≠ 0 → x = 1 := by decide
    exact ht _ hA.ne_zero
  have hneg : ∀ x : ZMod 2, -x = x := by decide
  unfold copyRowHalf upperPairSum
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro l _
  by_cases h : k < l
  · simp only [if_pos h]
    rw [permanent_eq_det_mod_two, det_forceTwoRows A hA i j hij k l, hdet, one_mul]
    simp only [sub_eq_add_neg, hneg]
  · simp only [if_neg h]

end Ordered
end OMA.MO513259

#print axioms OMA.MO513259.det_forceTwoRows
#print axioms OMA.MO513259.copyRowHalf_mod_two_inverse
