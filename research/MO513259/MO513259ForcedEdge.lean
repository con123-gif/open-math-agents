import Mathlib

/-!
Exact forced-edge cleanup for permanent expansions. This fragment follows
MO513259Permanent.lean and is only infrastructure for MO513259.
-/

namespace OMA.MO513259

open scoped BigOperators Matrix

variable {I R : Type*} [Fintype I] [DecidableEq I] [CommSemiring R]

lemma permanent_forced_col_cleanup (A : Matrix I I R) (r c : I) :
    (A.updateCol c (Pi.single r 1)).permanent =
      ((A.updateCol c (Pi.single r 1)).updateRow r (Pi.single c 1)).permanent := by
  classical
  have hm : (A.updateCol c (Pi.single r 1)).updateRow r (Pi.single c 1) =
      (A.updateRow r (Pi.single c 1)).updateCol c (Pi.single r 1) := by
    ext a b
    by_cases ha : a = r <;> by_cases hb : b = c <;>
      simp [Matrix.updateRow_apply, Matrix.updateCol_apply,
        Pi.single_apply, ha, hb, eq_comm]
  rw [hm, permanent_updateCol_expansion, permanent_updateCol_expansion]
  apply Finset.sum_congr rfl
  intro p _
  by_cases hp : p c = r
  · have hone : (Pi.single r (1 : R)) (p c) = 1 := by simp [hp]
    simp only [hone, one_mul]
    apply Finset.prod_congr rfl
    intro k hk
    have hpk : p k ≠ r := by
      intro he
      exact (Finset.ne_of_mem_erase hk) (p.injective (he.trans hp.symm))
    simp [Matrix.updateRow_apply, hpk]
  · have hzero : (Pi.single r (1 : R)) (p c) = 0 := by
      simp [Pi.single_apply, hp, Ne.symm hp]
    simp only [hzero, zero_mul]

lemma permanent_forced_row_cleanup (A : Matrix I I R) (r c : I) :
    (A.updateRow r (Pi.single c 1)).permanent =
      ((A.updateRow r (Pi.single c 1)).updateCol c (Pi.single r 1)).permanent := by
  have h := permanent_forced_col_cleanup Aᵀ c r
  simpa only [← Matrix.updateRow_transpose, ← Matrix.updateCol_transpose,
    Matrix.permanent_transpose] using h

end OMA.MO513259

#print axioms OMA.MO513259.permanent_forced_col_cleanup
#print axioms OMA.MO513259.permanent_forced_row_cleanup
