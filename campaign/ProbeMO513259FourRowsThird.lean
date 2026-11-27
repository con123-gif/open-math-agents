import Mathlib



/-!
Generic permanent multilinearity infrastructure for the independently reviewed
hand proof of MathOverflow 513259. This helper file alone is not a solution.
Credit: Cornelius Lytollis (@con123-gif), assisted by ChatGPT (GPT-6 Codex;
the exact model variant is not exposed in this interface).
-/

namespace OMA.MO513259

open scoped BigOperators Matrix

variable {I R : Type*} [Fintype I] [DecidableEq I] [CommSemiring R]

lemma permanent_updateCol_expansion (A : Matrix I I R) (j : I) (u : I → R) :
    (Matrix.updateCol A j u).permanent =
      ∑ p : Equiv.Perm I, u (p j) * ∏ i ∈ Finset.univ.erase j, A (p i) i := by
  classical
  simp only [Matrix.permanent, ← Finset.mul_prod_erase _ _ (Finset.mem_univ j),
    Matrix.updateCol_self]
  apply Finset.sum_congr rfl
  intro p _
  congr 1
  apply Finset.prod_congr rfl
  intro i hi
  simp only [ne_eq, Finset.ne_of_mem_erase hi, not_false_eq_true, Matrix.updateCol_ne]

lemma permanent_updateCol_add (A : Matrix I I R) (j : I) (u v : I → R) :
    (Matrix.updateCol A j (u + v)).permanent =
      (Matrix.updateCol A j u).permanent + (Matrix.updateCol A j v).permanent := by
  rw [permanent_updateCol_expansion, permanent_updateCol_expansion,
    permanent_updateCol_expansion]
  simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib]

lemma permanent_updateRow_add (A : Matrix I I R) (i : I) (u v : I → R) :
    (Matrix.updateRow A i (u + v)).permanent =
      (Matrix.updateRow A i u).permanent + (Matrix.updateRow A i v).permanent := by
  rw [← Matrix.permanent_transpose, ← Matrix.updateCol_transpose,
    permanent_updateCol_add, Matrix.updateCol_transpose, Matrix.updateCol_transpose,
    Matrix.permanent_transpose, Matrix.permanent_transpose]

def rowShear (A : Matrix I I R) (i j : I) (t : R) : Matrix I I R :=
  Matrix.updateRow A i (A i + t • A j)

def colShear (A : Matrix I I R) (i j : I) (t : R) : Matrix I I R :=
  (rowShear Aᵀ i j t)ᵀ

def copyRow (A : Matrix I I R) (i j : I) : Matrix I I R :=
  Matrix.updateRow A i (A j)

def copyCol (A : Matrix I I R) (i j : I) : Matrix I I R :=
  Matrix.updateCol A i (A.col j)

lemma permanent_rowShear (A : Matrix I I R) (i j : I) (t : R) :
    (rowShear A i j t).permanent =
      A.permanent + t * (copyRow A i j).permanent := by
  unfold rowShear copyRow
  rw [permanent_updateRow_add, Matrix.permanent_updateRow_smul]
  simp

lemma permanent_colShear (A : Matrix I I R) (i j : I) (t : R) :
    (colShear A i j t).permanent =
      A.permanent + t * (copyCol A i j).permanent := by
  unfold colShear
  rw [Matrix.permanent_transpose, permanent_rowShear, Matrix.permanent_transpose]
  congr 1
  congr 1
  unfold copyRow copyCol
  rw [← Matrix.permanent_transpose, Matrix.updateRow_transpose]
  rfl

lemma copyCol_rowShear (A : Matrix I I R) (i j : I) (t : R) :
    copyCol (rowShear A i j t) i j = rowShear (copyCol A i j) i j t := by
  ext a b
  simp only [copyCol, rowShear, Matrix.updateCol_apply, Matrix.updateRow_apply,
    Matrix.col_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  split_ifs <;> simp_all

lemma copyCol_copyRow (A : Matrix I I R) (i j : I) :
    copyCol (copyRow A i j) i j = copyRow (copyCol A i j) i j := by
  ext a b
  simp only [copyCol, copyRow, Matrix.updateCol_apply, Matrix.updateRow_apply,
    Matrix.col_apply]
  split_ifs <;> simp_all

lemma permanent_copyCol_of_symmetric (A : Matrix I I R) (hA : A.IsSymm)
    (i j : I) : (copyCol A i j).permanent = (copyRow A i j).permanent := by
  have hcol : A.col j = A j := by
    funext k
    exact congrFun (congrFun hA.eq j) k
  unfold copyCol copyRow
  rw [← Matrix.permanent_transpose, ← Matrix.updateRow_transpose, hA.eq, hcol]

lemma permanent_double_shear (A : Matrix I I R) (hA : A.IsSymm)
    (i j : I) (t : R) :
    (colShear (rowShear A i j t) i j t).permanent =
      A.permanent + 2 * t * (copyRow A i j).permanent +
        t ^ 2 * (copyCol (copyRow A i j) i j).permanent := by
  rw [permanent_colShear, permanent_rowShear, copyCol_rowShear,
    permanent_rowShear, permanent_copyCol_of_symmetric A hA, ← copyCol_copyRow]
  ring

end OMA.MO513259



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



/-!
Ordinary row multilinearity and coordinate expansion for MO513259.
This fragment follows MO513259Permanent.lean in a combined probe. No congruence
or full graph solution is asserted by these expansion identities alone.
Cornelius Lytollis (@con123-gif), assisted by ChatGPT (GPT-6 Codex;
the exact serving variant is not exposed).
-/

namespace OMA.MO513259

open scoped BigOperators Matrix

variable {I R : Type*} [Fintype I] [DecidableEq I] [CommSemiring R]

lemma permanent_updateRow_zero (A : Matrix I I R) (i : I) :
    (Matrix.updateRow A i 0).permanent = 0 := by
  rw [← Matrix.permanent_transpose, ← Matrix.updateCol_transpose,
    permanent_updateCol_expansion]
  simp

lemma permanent_updateRow_finset_sum {K : Type*} (A : Matrix I I R) (i : I)
    (s : Finset K) (v : K → I → R) :
    (Matrix.updateRow A i (∑ k ∈ s, v k)).permanent =
      ∑ k ∈ s, (Matrix.updateRow A i (v k)).permanent := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [permanent_updateRow_zero]
  | @insert k s hk ih =>
    rw [Finset.sum_insert hk, permanent_updateRow_add, ih, Finset.sum_insert hk]

lemma permanent_updateRow_basis_expansion (A : Matrix I I R) (i : I) (v : I → R) :
    (Matrix.updateRow A i v).permanent =
      ∑ k, v k * (Matrix.updateRow A i (Pi.single k 1)).permanent := by
  classical
  have hv : (∑ k, v k • Pi.single k 1) = v := by
    funext l
    simp [Pi.single_apply, eq_comm]
  calc
    (Matrix.updateRow A i v).permanent =
        (Matrix.updateRow A i (∑ k, v k • Pi.single k 1)).permanent := by rw [hv]
    _ = ∑ k, (Matrix.updateRow A i (v k • Pi.single k 1)).permanent :=
      permanent_updateRow_finset_sum A i Finset.univ _
    _ = ∑ k, v k * (Matrix.updateRow A i (Pi.single k 1)).permanent := by
      simp only [Matrix.permanent_updateRow_smul]

def forceTwoRows (A : Matrix I I R) (i j k l : I) : Matrix I I R :=
  (A.updateRow i (Pi.single k 1)).updateRow j (Pi.single l 1)

lemma permanent_update_two_rows (A : Matrix I I R) (i j : I) (hij : i ≠ j)
    (v w : I → R) :
    ((A.updateRow i v).updateRow j w).permanent =
      ∑ k, ∑ l, v k * w l * (forceTwoRows A i j k l).permanent := by
  classical
  calc
    ((A.updateRow i v).updateRow j w).permanent =
        ((A.updateRow j w).updateRow i v).permanent := by
      rw [Matrix.updateRow_comm A hij v w]
    _ = ∑ k, v k * ((A.updateRow j w).updateRow i (Pi.single k 1)).permanent :=
      permanent_updateRow_basis_expansion _ i v
    _ = ∑ k, v k * ((A.updateRow i (Pi.single k 1)).updateRow j w).permanent := by
      apply Finset.sum_congr rfl
      intro k _
      rw [Matrix.updateRow_comm A hij (Pi.single k 1) w]
    _ = ∑ k, ∑ l, v k * w l * (forceTwoRows A i j k l).permanent := by
      apply Finset.sum_congr rfl
      intro k _
      rw [permanent_updateRow_basis_expansion]
      simp only [Finset.mul_sum, mul_assoc, forceTwoRows]

end OMA.MO513259



/-!
Four forced rows as one coordinate-row determinant replacement for MO513259.
Prerequisites: the parent Permanent, RowReplacement and RowExpansion fragments.
Only the four replaced rows must be distinct; their first two keys are arbitrary.
Cornelius Lytollis (@con123-gif), assisted by Codex/GPT-6;
exact serving variant not exposed. Candidate awaits pinned checking.
-/

namespace OMA.MO513259

open scoped BigOperators Matrix

variable {I R : Type*} [Fintype I] [DecidableEq I] [CommRing R]

def forceFourRows (A : Matrix I I R) (i j r s k l : I) : Matrix I I R :=
  forceTwoRows (forceTwoRows A i j k l) r s i j

lemma det_forceFourRows (A : Matrix I I R) (hA : IsUnit A.det)
    (i j r s k l : I) (hij : i ≠ j) (hir : i ≠ r) (his : i ≠ s)
    (hjr : j ≠ r) (hjs : j ≠ s) (hrs : r ≠ s) :
    (forceFourRows A i j r s k l).det =
      A.det * ((A⁻¹).submatrix (![k, l, i, j] : Fin 4 → I)
        (![i, j, r, s] : Fin 4 → I)).det := by
  classical
  let selected : Fin 4 → I := ![i, j, r, s]
  let keys : Fin 4 → I := ![k, l, i, j]
  have hsel : Function.Injective selected := by
    intro a b he
    fin_cases a <;> fin_cases b <;> simp_all [selected, eq_comm]
  have hrows (q : Fin 4) (b : I) :
      forceFourRows A i j r s k l (selected q) b = (1 : Matrix I I R) (keys q) b := by
    fin_cases q <;>
      simp [selected, keys, forceFourRows, forceTwoRows, Matrix.updateRow_apply,
        Matrix.one_apply, Pi.single_apply, hij, hir, his, hjr, hjs, hrs, eq_comm] <;>
      split_ifs with h <;> simp only [h, if_true, if_false]
  have hm : coordinateRowReplacement A selected keys = forceFourRows A i j r s k l := by
    ext a b
    by_cases hi : a = i
    · subst a
      change coordinateRowReplacement A selected keys (selected (0 : Fin 4)) b = _
      rw [coordinateRowReplacement_selected A selected keys hsel (0 : Fin 4) b]
      exact (hrows 0 b).symm
    · by_cases hj : a = j
      · subst a
        change coordinateRowReplacement A selected keys (selected (1 : Fin 4)) b = _
        rw [coordinateRowReplacement_selected A selected keys hsel (1 : Fin 4) b]
        exact (hrows 1 b).symm
      · by_cases hr : a = r
        · subst a
          change coordinateRowReplacement A selected keys (selected (2 : Fin 4)) b = _
          rw [coordinateRowReplacement_selected A selected keys hsel (2 : Fin 4) b]
          exact (hrows 2 b).symm
        · by_cases hs : a = s
          · subst a
            change coordinateRowReplacement A selected keys (selected (3 : Fin 4)) b = _
            rw [coordinateRowReplacement_selected A selected keys hsel (3 : Fin 4) b]
            exact (hrows 3 b).symm
          · have hn : ∀ q : Fin 4, a ≠ selected q := by
              intro q
              fin_cases q
              · simpa [selected] using hi
              · simpa [selected] using hj
              · simpa [selected] using hr
              · simpa [selected] using hs
            have he := coordinateRowReplacement_unselected A selected keys a b hn
            simpa [forceFourRows, forceTwoRows, Matrix.updateRow_apply,
              hi, hj, hr, hs, eq_comm] using he
  calc
    (forceFourRows A i j r s k l).det =
        (coordinateRowReplacement A selected keys).det := congrArg Matrix.det hm.symm
    _ = A.det * ((A⁻¹).submatrix (![k, l, i, j] : Fin 4 → I)
        (![i, j, r, s] : Fin 4 → I)).det :=
      det_coordinateRowReplacement A hA selected keys hsel

end OMA.MO513259


#print axioms OMA.MO513259.det_forceFourRows
