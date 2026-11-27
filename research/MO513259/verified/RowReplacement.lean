import Mathlib

/-!
Coordinate-row replacement and complementary inverse minors for MO513259.
This standard determinant identity is derived from Mathlib's rank-update
determinant lemma; no small minor is assumed invertible. It is infrastructure
for the general proof, not a solution by itself.
Cornelius Lytollis (@con123-gif), assisted by ChatGPT (GPT-6 Codex;
the exact serving variant is not exposed).
-/

namespace OMA.MO513259

open scoped BigOperators Matrix

variable {I J R : Type*} [Fintype I] [Fintype J]
  [DecidableEq I] [DecidableEq J] [CommRing R]

lemma rows_submatrix_mul (M N : Matrix I I R) (r : J → I) :
    M.submatrix r id * N = (M * N).submatrix r id := by
  simpa using Matrix.submatrix_mul_equiv M N r (Equiv.refl I) id

lemma rows_submatrix_mul_selector (M : Matrix I I R) (r c : J → I) :
    M.submatrix r id * (1 : Matrix I I R).submatrix id c = M.submatrix r c := by
  simpa using Matrix.submatrix_mul_equiv M (1 : Matrix I I R) r (Equiv.refl I) c

def coordinateRowReplacement (A : Matrix I I R) (selected keys : J → I) :
    Matrix I I R :=
  A + (1 : Matrix I I R).submatrix id selected *
    ((1 : Matrix I I R).submatrix keys id - A.submatrix selected id)

lemma det_coordinateRowReplacement (A : Matrix I I R) (hA : IsUnit A.det)
    (selected keys : J → I) (hs : Function.Injective selected) :
    (coordinateRowReplacement A selected keys).det =
      A.det * ((A⁻¹).submatrix keys selected).det := by
  let U : Matrix I J R := (1 : Matrix I I R).submatrix id selected
  let V : Matrix J I R :=
    (1 : Matrix I I R).submatrix keys id - A.submatrix selected id
  have hleft : V * A⁻¹ =
      (A⁻¹).submatrix keys id - (1 : Matrix I I R).submatrix selected id := by
    dsimp [V]
    rw [Matrix.sub_mul, rows_submatrix_mul, rows_submatrix_mul,
      Matrix.one_mul, Matrix.mul_nonsing_inv A hA]
  have hsmall : 1 + V * A⁻¹ * U = (A⁻¹).submatrix keys selected := by
    rw [hleft, Matrix.sub_mul]
    dsimp [U]
    rw [rows_submatrix_mul_selector, rows_submatrix_mul_selector,
      Matrix.submatrix_one selected hs]
    abel
  change (A + U * V).det = _
  rw [Matrix.det_add_mul U V hA, hsmall]

lemma coordinateRowReplacement_selected (A : Matrix I I R)
    (selected keys : J → I) (hs : Function.Injective selected) (a : J) (j : I) :
    coordinateRowReplacement A selected keys (selected a) j =
      (1 : Matrix I I R) (keys a) j := by
  classical
  simp [coordinateRowReplacement, Matrix.mul_apply, Matrix.one_apply, hs.eq_iff] <;> ring

lemma coordinateRowReplacement_unselected (A : Matrix I I R)
    (selected keys : J → I) (i j : I) (hi : ∀ a, i ≠ selected a) :
    coordinateRowReplacement A selected keys i j = A i j := by
  classical
  simp [coordinateRowReplacement, Matrix.mul_apply, Matrix.one_apply, hi]

end OMA.MO513259

#print axioms OMA.MO513259.det_coordinateRowReplacement
#print axioms OMA.MO513259.coordinateRowReplacement_selected
#print axioms OMA.MO513259.coordinateRowReplacement_unselected
