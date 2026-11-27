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
  · have hone : (Pi.single r (1 : R) : I → R) (p c) = 1 := by simp [hp]
    simp only [hone, one_mul]
    apply Finset.prod_congr rfl
    intro k hk
    have hpk : p k ≠ r := by
      intro he
      exact (Finset.ne_of_mem_erase hk) (p.injective (he.trans hp.symm))
    simp [Matrix.updateRow_apply, hpk]
  · have hzero : (Pi.single r (1 : R) : I → R) (p c) = 0 := by
      simp [Pi.single_apply, hp, Ne.symm hp]
    simp only [hzero, zero_mul]

lemma permanent_forced_row_cleanup (A : Matrix I I R) (r c : I) :
    (A.updateRow r (Pi.single c 1)).permanent =
      ((A.updateRow r (Pi.single c 1)).updateCol c (Pi.single r 1)).permanent := by
  have h := permanent_forced_col_cleanup Aᵀ c r
  simpa only [Matrix.updateRow_transpose, Matrix.updateCol_transpose,
    Matrix.permanent_transpose] using h

end OMA.MO513259



/-!
Equivalent row and column representations of two forced matching edges.
This fragment follows the permanent, row-expansion and forced-edge helpers.
-/

namespace OMA.MO513259

open scoped Matrix

variable {I R : Type*} [Fintype I] [DecidableEq I] [CommSemiring R]

def forceTwoCols (A : Matrix I I R) (i j r s : I) : Matrix I I R :=
  (A.updateCol i (Pi.single r 1)).updateCol j (Pi.single s 1)

lemma permanent_cleanup_of_row (A : Matrix I I R) (r c : I)
    (hr : A r = Pi.single c 1) :
    A.permanent = (A.updateCol c (Pi.single r 1)).permanent := by
  have hself : A.updateRow r (Pi.single c 1) = A := by
    rw [← hr, Matrix.updateRow_eq_self]
  have h := permanent_forced_row_cleanup A r c
  simpa only [hself] using h

lemma permanent_cleanup_of_col (A : Matrix I I R) (r c : I)
    (hc : A.col c = Pi.single r 1) :
    A.permanent = (A.updateRow r (Pi.single c 1)).permanent := by
  have hself : A.updateCol c (Pi.single r 1) = A := by
    rw [← hc]
    exact Matrix.updateCol_eq_self A c
  have h := permanent_forced_col_cleanup A r c
  simpa only [hself] using h

lemma permanent_forceTwoCols_eq_rows (A : Matrix I I R) (i j r s : I)
    (hij : i ≠ j) (hrs : r ≠ s) :
    (forceTwoCols A i j r s).permanent = (forceTwoRows A r s i j).permanent := by
  classical
  let C := forceTwoCols A i j r s
  let P := forceTwoRows A r s i j
  have hm : forceTwoRows C r s i j = forceTwoCols P i j r s := by
    ext a b
    by_cases ha : a = r <;> by_cases hb : a = s <;>
      by_cases hc : b = i <;> by_cases hd : b = j <;>
        simp_all [C, P, forceTwoCols, forceTwoRows, Matrix.updateRow_apply,
          Matrix.updateCol_apply, Pi.single_apply, eq_comm]
  have hPr : P r = Pi.single i 1 := by
    funext a
    simp [P, forceTwoRows, Matrix.updateRow_apply, hrs, Ne.symm hrs]
  have hPs : P s = Pi.single j 1 := by
    funext a
    simp [P, forceTwoRows, Matrix.updateRow_apply]
  have hP1s : (P.updateCol i (Pi.single r 1)) s = Pi.single j 1 := by
    funext a
    by_cases ha : a = i
    · subst a
      simp [Matrix.updateCol_apply, Pi.single_apply, hrs, Ne.symm hrs, hij, Ne.symm hij]
    · simp [Matrix.updateCol_apply, ha, hPs]
  have hPper : P.permanent = (forceTwoCols P i j r s).permanent := by
    calc
      P.permanent = (P.updateCol i (Pi.single r 1)).permanent :=
        permanent_cleanup_of_row P r i hPr
      _ = ((P.updateCol i (Pi.single r 1)).updateCol j (Pi.single s 1)).permanent :=
        permanent_cleanup_of_row _ s j hP1s
      _ = _ := rfl
  have hCi : C.col i = Pi.single r 1 := by
    funext a
    simp [C, forceTwoCols, Matrix.col_apply, Matrix.updateCol_apply, hij, Ne.symm hij]
  have hCj : C.col j = Pi.single s 1 := by
    funext a
    simp [C, forceTwoCols, Matrix.col_apply, Matrix.updateCol_apply]
  have hC1j : (C.updateRow r (Pi.single i 1)).col j = Pi.single s 1 := by
    funext a
    by_cases ha : a = r
    · subst a
      simp [Matrix.col_apply, Matrix.updateRow_apply, Pi.single_apply,
        hrs, Ne.symm hrs, hij, Ne.symm hij]
    · have he := congrFun hCj a
      simpa [Matrix.col_apply, Matrix.updateRow_apply, ha] using he
  calc
    C.permanent = (C.updateRow r (Pi.single i 1)).permanent :=
      permanent_cleanup_of_col C r i hCi
    _ = (forceTwoRows C r s i j).permanent :=
      permanent_cleanup_of_col _ s j hC1j
    _ = (forceTwoCols P i j r s).permanent := congrArg Matrix.permanent hm
    _ = P.permanent := hPper.symm

lemma forceTwoRows_transpose_eq_cols (A : Matrix I I R) (i j r s : I) :
    (forceTwoRows Aᵀ i j r s)ᵀ = forceTwoCols A i j r s := by
  simp only [forceTwoRows, forceTwoCols, Matrix.updateRow_transpose, Matrix.transpose_transpose]

lemma permanent_forceTwoRows_transpose (A : Matrix I I R) (i j r s : I)
    (hij : i ≠ j) (hrs : r ≠ s) :
    (forceTwoRows Aᵀ i j r s).permanent = (forceTwoRows A r s i j).permanent := by
  rw [← Matrix.permanent_transpose, forceTwoRows_transpose_eq_cols]
  exact permanent_forceTwoCols_eq_rows A i j r s hij hrs

end OMA.MO513259


#print axioms OMA.MO513259.permanent_forceTwoRows_transpose
