import Mathlib

/-!
Exact signed-half infrastructure for the copied-row term in MO513259.
This uses Thomas Browning's existing positive/negative determinant API in
Mathlib.LinearAlgebra.Matrix.SemiringInverse (2024). It does not establish
the complementary-minor congruence needed for the full graph proof.
Cornelius Lytollis (@con123-gif), assisted by ChatGPT (GPT-6 Codex;
the exact serving variant is not exposed).
-/

namespace OMA.MO513259

open scoped BigOperators Matrix

variable {I R : Type*} [Fintype I] [DecidableEq I] [CommSemiring R]

lemma permanent_eq_detp_one_add_neg (A : Matrix I I R) :
    A.permanent = A.detp 1 + A.detp (-1) := by
  classical
  calc
    A.permanent = ∑ p : Equiv.Perm I, ∏ k, A k (p k) := by
      rw [← Matrix.permanent_transpose]
      rfl
    _ = A.detp 1 + A.detp (-1) := by
      rw [← Equiv.Perm.ofSign_disjUnion, Finset.sum_disjUnion]
      rfl

lemma permanent_of_equal_rows (A : Matrix I I R) (i j : I) (hij : i ≠ j)
    (hrow : A.row i = A.row j) : A.permanent = 2 * A.detp 1 := by
  have hh : A.detp 1 = A.detp (-1) := Matrix.detp_eq_of_row_eq hij hrow
  rw [permanent_eq_detp_one_add_neg, ← hh, two_mul]

lemma permanent_copyRow_eq_two_detp (A : Matrix I I R) (i j : I) (hij : i ≠ j) :
    (Matrix.updateRow A i (A j)).permanent =
      2 * (Matrix.updateRow A i (A j)).detp 1 := by
  apply permanent_of_equal_rows _ i j hij
  ext k
  change (Matrix.updateRow A i (A j)) i k = (Matrix.updateRow A i (A j)) j k
  simp [Matrix.updateRow_apply, hij, hij.symm]

lemma odd_skew_integer_det_zero (A : Matrix I I ℤ)
    (hskew : Aᵀ = -A) (hodd : Odd (Fintype.card I)) : A.det = 0 := by
  have he : A.det = -A.det := by
    calc
      A.det = Aᵀ.det := (Matrix.det_transpose A).symm
      _ = (-A).det := congrArg Matrix.det hskew
      _ = -A.det := by rw [Matrix.det_neg, hodd.neg_one_pow, neg_one_mul]
  omega

end OMA.MO513259

#print axioms OMA.MO513259.permanent_copyRow_eq_two_detp
#print axioms OMA.MO513259.odd_skew_integer_det_zero
